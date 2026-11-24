#!/usr/bin/env python3
"""Python transport adapter for the Bend fast runner (build/runner).

All rules, transitions and observations are computed by the native Bend
program built from engine/runner.bend + engine/game.bend. This module only
spawns that process, writes request lines, reads response lines, and checks
provenance. It never computes game state. Stdlib only.

    from fast_runner import FastRunner
    with FastRunner() as r:                      # build/runner, engine/
        env = r.env(42, "bots")
        status, body = env.step("buy:0")
        status, body = r.replay(42, "manual", ["buy:0", "end"])  # == GET /api/game

Protocol and semantics: engine/runner.bend and docs/AGENTS-API.md.
"""
from __future__ import annotations

import collections
import hashlib
import json
import os
import selectors
import subprocess
import sys
import tempfile
import threading
import time

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
DEFAULT_BINARY = os.path.join(ROOT, "build", "runner")
DEFAULT_ENGINE = os.path.join(ROOT, "engine")
PIN = "52637f747b1f7e08263b7853ffd7204262d8e41e"
PROTOCOL = "fast-runner/1"
LINE_MAX = 262144
MAX_ENV_ID = 999999
SCRATCH_ENV = MAX_ENV_ID


_FOREIGN = []   # Popen objects inherited through fork; never finalized here


class RunnerError(RuntimeError):
    """Transport failure: spawn, timeout, crash, or a malformed response."""


class EnvLost(RunnerError):
    """The process holding this env died or was restarted; its state is gone.
    Rebuild it with reset + step(transcript) if needed."""


class StaleRunner(RunnerError):
    """The binary does not match its manifest or the engine sources."""


def _sha256_file(path):
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for chunk in iter(lambda: f.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


def _check_word(name, value):
    """A protocol word: no space and no transport control (C0, DEL)."""
    s = str(value)
    if any(c == " " or ord(c) < 0x20 or ord(c) == 0x7F for c in s):
        raise ValueError(f"{name} must not contain spaces or control characters: {s[:40]!r}")
    if len(s.encode()) > LINE_MAX // 2:
        raise ValueError(f"{name} is too long ({len(s.encode())} bytes)")
    return s


def _moves_text(moves):
    if moves is None:
        return ""
    if isinstance(moves, (list, tuple)):
        if len(moves) == 1 and str(moves[0]) == "":
            # "" on the wire means NO move; a lone empty move has no encoding
            # (the replay API would answer it with bad_move)
            raise ValueError("a lone empty move cannot be sent; use [] for no move")
        for m in moves:
            if "," in str(m):
                raise ValueError(f"a single move must not contain ',': {m!r}")
        moves = ",".join(str(m) for m in moves)
    return _check_word("moves", moves)


def _split_moves(text):
    # mirrors G.split_moves: "" is no move, otherwise split on every ','
    return [] if text == "" else text.split(",")


def verify_manifest(binary, engine_dir=None, runner_src=None):
    """Return the manifest dict, or raise StaleRunner naming the mismatch.

    Checks: manifest kind/version/protocol, binary sha256, game.bend and
    econ.bend in engine_dir, engine/runner.bend, and the compiler pin.
    """
    binary = os.path.abspath(binary)
    engine_dir = os.path.abspath(engine_dir or DEFAULT_ENGINE)
    runner_src = runner_src or os.path.join(ROOT, "engine", "runner.bend")
    mpath = binary + ".manifest.json"
    if not os.path.exists(binary):
        raise StaleRunner(f"runner binary missing: {binary} (bash scripts/build_runner.sh)")
    try:
        with open(mpath) as f:
            man = json.load(f)
    except (OSError, ValueError) as e:
        raise StaleRunner(f"runner manifest missing or unreadable: {mpath}: {e}")

    def need(field, want, got):
        if want != got:
            raise StaleRunner(f"stale runner {binary}: {field} manifest={want!r} actual={got!r}")

    need("kind", "bend-grounds-runner", man.get("kind"))
    need("manifestVersion", 1, man.get("manifestVersion"))
    need("protocol", PROTOCOL, man.get("protocol"))
    need("binary.sha256", man.get("binary", {}).get("sha256"), _sha256_file(binary))
    src = man.get("sources", {})
    for name in ("game.bend", "econ.bend"):
        p = os.path.join(engine_dir, name)
        if not os.path.exists(p):
            raise StaleRunner(f"engine source missing: {p}")
        need(f"sources.{name} vs {p}", src.get(name), _sha256_file(p))
    need("sources.runner.bend", src.get("runner.bend"), _sha256_file(runner_src))
    need("compiler.commit", PIN, man.get("compiler", {}).get("commit"))
    need("compiler.clean", True, man.get("compiler", {}).get("clean"))
    return man


class FastRunner:
    """One persistent runner process holding any number of envs.

    Calls are sequential (one request line, one response line). For
    parallel work use one FastRunner per worker thread or process.

    Failure policy: a timeout, crash or malformed response kills the
    process and invalidates EVERY env created in it (EnvLost). A request
    that timed out may already have been committed by the runner, so the
    adapter never retries it. The next call restarts the process lazily
    (at most max_restarts times); envs must then be reset again.
    """

    def __init__(self, binary=None, engine_dir=None, timeout=60.0, raw=False,
                 verify=True, max_restarts=3):
        self.binary = os.path.abspath(binary or os.environ.get("BG_RUNNER") or DEFAULT_BINARY)
        self.engine_dir = os.path.abspath(engine_dir or DEFAULT_ENGINE)
        self.timeout = float(timeout)
        self.raw = raw
        self.verify = verify
        self.max_restarts = max_restarts
        self.manifest = None
        if verify:
            self.manifest = verify_manifest(self.binary, self.engine_dir)
        else:
            print(f"fast_runner: WARNING provenance check disabled for {self.binary}",
                  file=sys.stderr)
            try:
                with open(self.binary + ".manifest.json") as f:
                    self.manifest = json.load(f)
            except (OSError, ValueError):
                self.manifest = None
        self._proc = None
        self._buf = bytearray()
        self._sel = None
        self._stderr = collections.deque(maxlen=50)
        self._errf = None
        self._gen = 0          # process generation; bumps on every (re)start
        self._starts = 0
        self._envs = {}        # env id -> token of the reset that created it
        self._tokens = 0       # unique per successful reset, never reused
        self._next_id = 0
        self._owner = os.getpid()
        self._lock = threading.Lock()

    # -- process management -------------------------------------------------

    def _start(self):
        if self._starts > self.max_restarts:
            raise RunnerError(f"runner restarted too often ({self._starts}); giving up")
        # stderr goes to an anonymous temp file, not a pipe: no reader thread,
        # nothing to block on, and the tail is still available for errors
        self._errf = tempfile.TemporaryFile()
        try:
            self._proc = subprocess.Popen([self.binary], stdin=subprocess.PIPE,
                                          stdout=subprocess.PIPE, stderr=self._errf,
                                          close_fds=True)
        except OSError as e:
            self._errf.close()
            self._errf = None
            raise RunnerError(f"cannot start runner {self.binary}: {e}")
        self._starts += 1
        self._gen += 1
        self._buf = bytearray()
        self._sel = selectors.DefaultSelector()
        self._sel.register(self._proc.stdout, selectors.EVENT_READ)
        if self.verify and self.manifest is not None:
            status, body = self._call("rules", raw=True)
            got = hashlib.sha256(body.encode("utf-8")).hexdigest()
            if status != 200 or got != self.manifest.get("rulesSha256"):
                self._kill()
                raise StaleRunner(f"stale runner {self.binary}: rulesSha256 manifest="
                                  f"{self.manifest.get('rulesSha256')!r} actual={got!r}")

    def _kill(self):
        p, self._proc = self._proc, None
        if p is None:
            self._close_errf()
        if self._sel is not None:
            try:
                self._sel.close()
            except Exception:
                pass
            self._sel = None
        if p is None:
            return
        for s in (p.stdin, p.stdout):
            try:
                s.close()
            except Exception:
                pass
        if p.poll() is None:
            p.kill()
        try:
            p.wait(timeout=5)
        except subprocess.TimeoutExpired:
            pass
        self._close_errf()

    def _close_errf(self):
        f, self._errf = self._errf, None
        if f is not None:
            try:
                f.seek(0, 2)
                n = f.tell()
                f.seek(max(0, n - 4096))
                for line in f.read().decode("utf-8", "replace").splitlines()[-5:]:
                    self._stderr.append(line)
            except Exception:
                pass
            finally:
                try:
                    f.close()
                except Exception:
                    pass

    def _fail(self, msg):
        """Kill the process and invalidate all of its envs."""
        self._kill()
        tail = " | ".join(list(self._stderr)[-3:])
        self._envs.clear()
        raise RunnerError(msg + (f" (stderr: {tail})" if tail else ""))

    def _foreign(self):
        """True in a forked child: the process belongs to the parent, so the
        child must neither talk to it nor kill or reap it."""
        return os.getpid() != self._owner

    def _forget(self):
        """Child side of a fork: close this process's COPIES of the pipe and
        temp-file descriptors (the parent keeps its own, so its runner is
        unaffected: no quit, no kill, no wait), and park the Popen object so
        no finalizer in the child ever signals or reaps the parent's runner."""
        p, self._proc = self._proc, None
        if p is not None:
            for f in (p.stdin, p.stdout):
                try:
                    f.close()
                except Exception:
                    pass
            _FOREIGN.append(p)
        if self._errf is not None:
            try:
                self._errf.close()
            except Exception:
                pass
        if self._sel is not None:
            try:
                self._sel.close()
            except Exception:
                pass
        self._sel = None
        self._errf = None
        self._envs.clear()

    def close(self):
        """Ask the runner to quit, then reap it. Idempotent. In a forked
        child it only forgets the parent's process."""
        if self._foreign():
            self._forget()
            return
        with self._lock:
            p = self._proc
            if p is not None and p.poll() is None:
                try:
                    p.stdin.write(b"quit\n")
                    p.stdin.flush()
                    p.wait(timeout=5)
                except Exception:
                    pass
            self._kill()
            self._envs.clear()

    def __enter__(self):
        return self

    def __exit__(self, *exc):
        self.close()

    def __del__(self):
        try:
            if self._foreign():
                self._forget()
            else:
                self._kill()
        except Exception:
            pass

    # -- one request --------------------------------------------------------

    def _readline(self, deadline):
        while True:
            i = self._buf.find(b"\n")
            if i >= 0:
                line = bytes(self._buf[:i])
                del self._buf[:i + 1]
                return line
            left = deadline - time.monotonic()
            if left <= 0:
                self._fail(f"runner timed out after {self.timeout}s")
            if not self._sel.select(left):
                continue
            chunk = os.read(self._proc.stdout.fileno(), 1 << 20)
            if not chunk:
                code = self._proc.poll()
                self._fail(f"runner exited (status {code}) without answering")
            self._buf += chunk

    def _call(self, line, raw=None):
        if os.getpid() != self._owner:
            raise RunnerError("FastRunner used in a forked child; create a new FastRunner per process")
        if self._proc is None or self._proc.poll() is not None:
            if self._proc is not None:
                self._kill()
                self._envs.clear()
            self._start()
        data = line.encode("utf-8") + b"\n"
        if len(data) > LINE_MAX:
            raise ValueError(f"request line too long ({len(data)} > {LINE_MAX} bytes)")
        try:
            self._proc.stdin.write(data)
            self._proc.stdin.flush()
        except (BrokenPipeError, OSError) as e:
            self._fail(f"runner pipe closed: {e}")
        out = self._readline(time.monotonic() + self.timeout)
        try:
            text = out.decode("utf-8")
            status_s, body = text.split(" ", 1)
            status = int(status_s)
        except (UnicodeDecodeError, ValueError):
            self._fail(f"malformed runner line: {out[:120]!r}")
        if raw if raw is not None else self.raw:
            return status, body
        try:
            return status, json.loads(body)
        except ValueError:
            self._fail(f"runner body is not JSON: {body[:120]!r}")

    def _env_call(self, env, line, raw=None, token=None):
        if self._proc is not None and self._proc.poll() is not None:
            # the process died since the last call: every env is gone
            self._kill()
            self._envs.clear()
        live = self._envs.get(env)
        if live is None or self._proc is None or (token is not None and token != live):
            raise EnvLost(f"env {env} is not live in this runner (closed, reset again, or process lost)")
        return self._call(line, raw)

    def _new_token(self, env):
        self._tokens += 1
        self._envs[env] = self._tokens
        return self._tokens

    # -- public API ---------------------------------------------------------

    def rules(self):
        with self._lock:
            return self._call("rules")

    def health(self):
        with self._lock:
            return self._call("health")

    def reset(self, env, seed, mode="bots"):
        """(status, body) == GET /api/game?seed=&mode= ; a 400 creates nothing."""
        env = int(env)
        if not 0 <= env <= MAX_ENV_ID:
            raise ValueError("env id must be in 0..999999")
        line = f"reset {env} {_check_word('seed', seed)} {_check_word('mode', mode)}"
        with self._lock:
            status, body = self._call(line)
            if status == 200:
                self._new_token(env)
            return status, body

    def step(self, env, moves, _token=None):
        """Apply moves (str 'a,b' or list) to env. (status, body) ==
        GET /api/game over transcript ++ moves. Moves before a rejected move
        stay applied; the rejected move and the rest do not."""
        line = f"step {int(env)} {_moves_text(moves)}"
        with self._lock:
            return self._env_call(int(env), line, token=_token)

    def observe(self, env, _token=None):
        with self._lock:
            return self._env_call(int(env), f"observe {int(env)}", token=_token)

    def close_env(self, env, _token=None):
        with self._lock:
            r = self._env_call(int(env), f"close {int(env)}", token=_token)
            self._envs.pop(int(env), None)
            return r

    def replay(self, seed, mode="bots", moves=""):
        """Stateless drop-in for GET /api/game?seed=&mode=&moves= ."""
        with self._lock:
            status, body = self._call(
                f"reset {SCRATCH_ENV} {_check_word('seed', seed)} {_check_word('mode', mode)}")
            if status != 200:
                return status, body
            self._new_token(SCRATCH_ENV)
            try:
                return self._call(f"step {SCRATCH_ENV} {_moves_text(moves)}")
            finally:
                if SCRATCH_ENV in self._envs and self._proc is not None:
                    self._call(f"close {SCRATCH_ENV}", raw=True)
                self._envs.pop(SCRATCH_ENV, None)

    def env(self, seed, mode="bots"):
        """A FastEnv on a fresh id. Raises ValueError if reset is refused."""
        with self._lock:
            for _ in range(MAX_ENV_ID):
                k = self._next_id
                self._next_id = (self._next_id + 1) % MAX_ENV_ID  # never SCRATCH_ENV
                if k not in self._envs:
                    break
        e = FastEnv(self, k, seed, mode)
        return e

    @property
    def generation(self):
        return self._gen

    @property
    def pid(self):
        return self._proc.pid if self._proc is not None else None


class FastEnv:
    """One game in a FastRunner, with its applied-move transcript.

    transcript is exactly the moves the runner applied, so
    GET /api/game?moves=','.join(transcript) answers the same body as
    observe(). After a crash every FastEnv of that process raises EnvLost.
    """

    def __init__(self, runner, env_id, seed, mode="bots"):
        self.runner = runner
        self.id = env_id
        self.seed = seed
        self.mode = mode
        self.transcript = []
        status, body = runner.reset(env_id, seed, mode)
        self.last = (status, body)
        if status != 200:
            raise ValueError(f"reset refused: {status} {body}")
        self.token = runner._envs.get(env_id)

    def _applied(self, body):
        if isinstance(body, str):
            body = json.loads(body)
        return body.get("movesApplied")

    def step(self, moves):
        text = _moves_text(moves)
        status, body = self.runner.step(self.id, text, _token=self.token)
        n = self._applied(body)
        if n is not None:
            k = n - len(self.transcript)
            batch = _split_moves(text)
            if not 0 <= k <= len(batch):
                raise RunnerError(f"movesApplied {n} inconsistent with transcript "
                                  f"{len(self.transcript)} + batch {len(batch)}")
            self.transcript.extend(batch[:k])
        self.last = (status, body)
        return status, body

    def observe(self):
        self.last = self.runner.observe(self.id, _token=self.token)
        return self.last

    def close(self):
        return self.runner.close_env(self.id, _token=self.token)

    @property
    def done(self):
        body = self.last[1]
        if isinstance(body, str):
            body = json.loads(body)
        return body.get("phase") == "finished"


if __name__ == "__main__":
    # tiny CLI: fast_runner.py SEED [MODE [MOVES]] prints the replay body
    args = sys.argv[1:]
    if not args:
        print("usage: fast_runner.py SEED [MODE [MOVES]]", file=sys.stderr)
        sys.exit(2)
    with FastRunner(raw=True) as r:
        st, b = r.replay(args[0], args[1] if len(args) > 1 else "bots",
                         args[2] if len(args) > 2 else "")
        print(b)
        sys.exit(0 if st == 200 else 1)
