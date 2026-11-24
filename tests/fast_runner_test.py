#!/usr/bin/env python3
"""Differential tests for the Bend fast runner (build/runner, scripts/fast_runner.py).

Oracles (both are the existing replay API, not the runner):
  * CLI   : build/server game SEED MODE MOVES   (engine G.api_game, replay from scratch)
  * HTTP  : GET /api/game on a private build/server serve PORT (unless --no-http)

The claim tested: every runner answer is byte-identical to the oracle's answer
for transcript ++ batch, the runner's state afterwards is the oracle's state for
the applied transcript, and errors never leak across envs or kill the process.
Finite tests, not a proof.

    python3 tests/fast_runner_test.py                 # full suite
    python3 tests/fast_runner_test.py --quick         # fewer games
    python3 tests/fast_runner_test.py --bench         # matched-workload benchmark only
Env: BG_RUNNER (binary), BG_ORACLE (server binary, default build/server).
"""
import argparse
import warnings
import hashlib
import json
import os
import random
import shutil
import signal
import socket
import subprocess
import sys
import tempfile
import time
import urllib.error
import urllib.parse
import urllib.request

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.join(ROOT, "scripts"))
from fast_runner import (FastRunner, FastEnv, RunnerError, EnvLost, StaleRunner,  # noqa: E402
                         verify_manifest, LINE_MAX)

ORACLE = os.environ.get("BG_ORACLE", os.path.join(ROOT, "build", "server"))
RUNNER = os.environ.get("BG_RUNNER", os.path.join(ROOT, "build", "runner"))

PASS = 0
FAILS = []


def check(cond, name, detail=""):
    global PASS
    if cond:
        PASS += 1
    else:
        FAILS.append(f"{name}: {detail}"[:600])
        print(f"FAIL {name}: {detail}"[:600], flush=True)


def read_bytes(p):
    with open(p, "rb") as f:
        return f.read()


def sha(b):
    return hashlib.sha256(b.encode() if isinstance(b, str) else b).hexdigest()


# -- oracles ---------------------------------------------------------------

def cli_oracle(seed, mode, moves, binary=None):
    """(status, body) from `server game` (engine api_game). CLI exit 0 == 200."""
    binary = binary or ORACLE
    args = [binary, "game", str(seed), mode, ",".join(moves)]
    p = subprocess.run(args, capture_output=True, text=True, timeout=120)
    body = p.stdout[:-1] if p.stdout.endswith("\n") else p.stdout
    if p.returncode == 0:
        return 200, body
    # exit 1 means a non-200 engine status; the engine only answers 200 or 400
    return 400, body


class HttpOracle:
    def __init__(self):
        s = socket.socket()
        s.bind(("127.0.0.1", 0))
        self.port = s.getsockname()[1]
        s.close()
        self.proc = subprocess.Popen([ORACLE, "serve", str(self.port)], stdout=subprocess.DEVNULL,
                                     stderr=subprocess.DEVNULL)
        for _ in range(100):
            try:
                with urllib.request.urlopen(f"http://127.0.0.1:{self.port}/api/health", timeout=1) as r:
                    r.read()
                break
            except Exception:
                time.sleep(0.05)

    def game(self, seed, mode, moves):
        q = urllib.parse.urlencode({"seed": str(seed), "mode": mode, "v": "3", "moves": ",".join(moves)})
        try:
            with urllib.request.urlopen(f"http://127.0.0.1:{self.port}/api/game?{q}", timeout=120) as r:
                return r.status, r.read().decode()
        except urllib.error.HTTPError as e:
            with e:
                return e.code, e.read().decode()

    def rules(self):
        with urllib.request.urlopen(f"http://127.0.0.1:{self.port}/api/rules?v=3", timeout=30) as r:
            return r.read().decode()

    def close(self):
        self.proc.terminate()
        try:
            self.proc.wait(5)
        except subprocess.TimeoutExpired:
            self.proc.kill()
            self.proc.wait(5)


# -- trajectory generation ---------------------------------------------------

BAD = ["buy:9", "play:8", "sell:7", "sellhand:6", "swap:0:0", "swap:4:9", "xyz", "buy", "buy:00",
       "BUY:0", "buy:-1", "end:1", "roll:", "upgrade", "invest", "", "buy:123", "play:0:1",
       "sell:99", "freeze"]


def pick_moves(rng, body, bad_rate):
    """A batch: usually one legal move, sometimes a bad one, sometimes a multi-move batch."""
    legal = body.get("legalActions") or ["end"]
    def one():
        if rng.random() < bad_rate:
            return rng.choice(BAD)
        rec = [a for a in legal if a not in ("end", "auto")]
        r = rng.random()
        if r < 0.18 or not rec:
            return "end"
        if r < 0.22:
            return "auto"
        return rng.choice(rec)
    if rng.random() < 0.12:
        return [one() for _ in range(rng.randint(2, 4))]
    m = one()
    return [m] if m != "" else ["", "end"]


def drive(runner, seed, mode, rng, oracle_cli, oracle_http, http_every, bad_rate=0.15, max_steps=400,
          name="game"):
    """Play one game in the runner, checking every step against the CLI oracle and
    every http_every-th step (plus all errors) against HTTP."""
    env = runner.env(seed, mode)
    st0, b0 = env.last
    o = oracle_cli(seed, mode, [])
    check(runner_raw(runner, env) == o, f"{name} reset parity")
    steps = errs = 0
    body = b0
    while steps < max_steps:
        batch = pick_moves(rng, body, bad_rate)
        before = list(env.transcript)
        before_obs = runner_raw(runner, env)
        status, raw = raw_step(runner, env, batch)
        steps += 1
        exp = oracle_cli(seed, mode, before + batch)
        check((status, raw) == exp, f"{name} step {steps} parity {batch}",
              f"runner {status} {sha(raw)[:12]} oracle {exp[0]} {sha(exp[1])[:12]}")
        if oracle_http and (status != 200 or steps % http_every == 0):
            if len(before) + len(batch) <= 1024:
                h = oracle_http.game(seed, mode, before + batch)
                check((status, raw) == h, f"{name} step {steps} http parity {batch}",
                      f"runner {status} http {h[0]} {h[1][:160]}")
        body = json.loads(raw)
        if status != 200:
            errs += 1
            # the reported state is the committed state: observe == oracle(transcript)
            now = runner_raw(runner, env)
            check(now == oracle_cli(seed, mode, env.transcript), f"{name} step {steps} committed state")
            if "error" in body and isinstance(body["error"], dict) and "index" in body["error"]:
                check(body["error"]["index"] == len(env.transcript) == body["movesApplied"],
                      f"{name} step {steps} error index", f"{body['error']} T={len(env.transcript)}")
                k = len(env.transcript) - len(before)
                check(env.transcript == before + batch[:k], f"{name} step {steps} applied prefix")
                if k == 0:
                    check(now[1] == before_obs[1], f"{name} step {steps} rejected leaves state unchanged")
        if body.get("phase") == "finished":
            # terminal: any further move is game_over, state unchanged
            s2, r2 = raw_step(runner, env, ["end"])
            check((s2, r2) == oracle_cli(seed, mode, env.transcript + ["end"]), f"{name} terminal parity")
            check(json.loads(r2)["error"]["code"] == "game_over", f"{name} terminal game_over")
            break
    env.close()
    return steps, errs, body.get("phase")


def raw_step(runner, env, batch):
    """Step through the FastEnv (keeps the transcript) and return the raw line body."""
    status, body = env.step(batch)
    return status, runner._last_raw


def runner_raw(runner, env):
    status, body = env.observe()
    return status, runner._last_raw


def instrument(runner):
    """Keep the raw body of the last call next to the parsed one (test only)."""
    orig = runner._call

    def call(line, raw=None):
        st, b = orig(line, raw=True)
        runner._last_raw = b
        if raw if raw is not None else runner.raw:
            return st, b
        return st, json.loads(b)
    runner._call = call
    return runner


# -- test groups -------------------------------------------------------------

def t_manifest():
    man = verify_manifest(RUNNER)
    check(man["sources"]["game.bend"] == sha(read_bytes(os.path.join(ROOT, "engine/game.bend"))),
          "manifest game hash = engine/game.bend")
    tmp = tempfile.mkdtemp(prefix="fr-man-")
    try:
        b = os.path.join(tmp, "runner")
        shutil.copy(RUNNER, b)
        good = json.loads(read_bytes(RUNNER + ".manifest.json"))
        def write(m):
            with open(b + ".manifest.json", "w") as f:
                json.dump(m, f)
        write(good)
        r = FastRunner(binary=b)
        check(r.health()[0] == 200, "copied binary + manifest verifies")
        r.close()
        for field, mut in [("sources.game.bend", lambda m: m["sources"].__setitem__("game.bend", "0" * 64)),
                           ("sources.econ.bend", lambda m: m["sources"].__setitem__("econ.bend", "0" * 64)),
                           ("sources.runner.bend", lambda m: m["sources"].__setitem__("runner.bend", "0" * 64)),
                           ("compiler.commit", lambda m: m["compiler"].__setitem__("commit", "1" * 40)),
                           ("binary.sha256", lambda m: m["binary"].__setitem__("sha256", "2" * 64)),
                           ("protocol", lambda m: m.__setitem__("protocol", "fast-runner/0"))]:
            m = json.loads(json.dumps(good))
            mut(m)
            write(m)
            try:
                FastRunner(binary=b)
                check(False, f"stale manifest {field} rejected")
            except StaleRunner as e:
                check(field.split(".")[0] in str(e), f"stale manifest {field} rejected", str(e))
        m = json.loads(json.dumps(good)); m["rulesSha256"] = "3" * 64; write(m)
        r = FastRunner(binary=b)
        try:
            r.health()
            check(False, "rules sha mismatch rejected at start")
        except StaleRunner:
            check(r.pid is None, "rules sha mismatch rejected at start; process reaped")
        write(good)
        with open(b, "ab") as f:
            f.write(b"\0")
        try:
            FastRunner(binary=b)
            check(False, "modified binary rejected")
        except StaleRunner:
            check(True, "modified binary rejected")
        os.remove(b + ".manifest.json")
        try:
            FastRunner(binary=b)
            check(False, "missing manifest rejected")
        except StaleRunner:
            check(True, "missing manifest rejected")
    finally:
        shutil.rmtree(tmp)


def t_v4_surface():
    """V4 (protocol 3) on the runner itself: rules identity fields and the
    removed hand sale. The byte parity with the oracle is checked elsewhere;
    this pins the meaning so a parity pass on stale V3 binaries cannot hide."""
    r = FastRunner()
    try:
        st, rules = r.rules()
        check(st == 200 and rules.get("protocolVersion") == 3 and rules.get("schemaVersion") == 3,
              "runner rules protocol 3", f"{st} {rules.get('protocolVersion')}")
        check(len(rules.get("cards", [])) == 44, "runner rules 44 cards", str(len(rules.get("cards", []))))
        costs = rules.get("costs", {})
        check(costs.get("startHp") == 40 and "sellHandRefund" not in costs, "runner costs: 40 HP, no hand-sale refund",
              str(costs))
        e = r.env(42, "manual")
        e.step("buy:0")
        st, body = e.step("sellhand:0")
        obs = json.loads(body) if isinstance(body, str) else body
        err = (obs or {}).get("error") or {}
        check(st == 400 and err.get("code") == "bad_move" and obs.get("movesApplied") == 1,
              "runner: sellhand is a bad_move", f"{st} {err}")
        check(all(not a.startswith("sellhand") for a in obs.get("legalActions", [])), "runner: no sellhand legal")
        check(all(p["hp"] == 40 for p in obs["players"]), "runner: 40 HP at start")
    finally:
        r.close()


def t_protocol():
    p = subprocess.Popen([RUNNER], stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    lines = ["health", "", "   ", "step", "step x", "step 1234567 end", "observe 5", "close 5",
             "reset 1 42", "reset 1 abc bots", "reset 1 42 weird", "reset 1 4294967296 bots",
             "reset 1 42 manual", "observe 1", "stép 1", "health extra", "reset 1 42 manual\r",
             "x" * (LINE_MAX + 5000), "observe 1", "step 1 end", "close 1", "observe 1", "rules"]
    data = ("\n".join(lines) + "\n").encode()
    out, err = p.communicate(data, timeout=60)
    got = out.decode().split("\n")
    check(got[-1] == "" and len(got) - 1 == len(lines), "one response line per request",
          f"{len(got) - 1} lines for {len(lines)}")
    check(p.returncode == 0 and err == b"", "EOF exits 0, stderr empty", f"{p.returncode} {err[:100]!r}")
    st = [g.split(" ", 1)[0] for g in got[:-1]]
    exp = ["200", "400", "400", "400", "400", "400", "404", "404", "400", "400", "400", "400",
           "200", "200", "400", "400", "200", "413", "200", "200", "200", "404", "200"]
    check(st == exp, "protocol statuses", f"{st}")
    codes = [json.loads(g.split(" ", 1)[1]).get("error", {}) for g in got[:-1]]
    check(codes[1]["code"] == "bad_command" and codes[6]["code"] == "unknown_env"
          and codes[17]["code"] == "line_too_long", "protocol error codes")
    for i, args in [(9, ("abc", "bots")), (10, ("42", "weird")), (11, ("4294967296", "bots"))]:
        o = cli_oracle(args[0], args[1], [])
        check(("400", got[i].split(" ", 1)[1]) == (str(o[0]), o[1]), f"reset error parity {args}")
    check(got[13].split(" ", 1)[1] == cli_oracle(42, "manual", [])[1], "reset 1 42 manual parity")
    check(got[16] == got[12], "CRLF line == LF line")
    # quit mid-stream: later lines are not answered
    p = subprocess.run([RUNNER], input=b"health\nquit\nhealth\n", capture_output=True, timeout=30)
    check(p.stdout.decode().count("\n") == 2 and p.returncode == 0, "quit stops the runner")
    # last line without newline is still answered
    p = subprocess.run([RUNNER], input=b"health", capture_output=True, timeout=30)
    check(p.stdout.decode().startswith("200 "), "final unterminated line answered")


def t_reset_and_multi(oracle_http):
    r = instrument(FastRunner())
    # reset on a live env replaces it; a refused reset keeps it
    r.reset(3, 11, "manual")
    r.step(3, "buy:0,end")
    keep = (r.observe(3)[0], r._last_raw)
    st, _ = r.reset(3, "notaseed", "manual")
    check(st == 400 and (r.observe(3)[0], r._last_raw) == keep, "refused reset keeps env")
    st, _ = r.reset(3, 12, "bots")
    check((st, r._last_raw) == cli_oracle(12, "bots", []), "reset replaces env")
    # many interleaved envs stay independent
    rng = random.Random(5)
    envs = [r.env(seed, mode) for seed, mode in [(1, "manual"), (2, "bots"), (3, "manual"), (4, "bots"),
                                                 (1, "manual"), (4294967295, "manual"), (0, "bots"),
                                                 (77, "manual")]]
    snap = {}
    for rnd in range(60):
        e = envs[rnd % len(envs)]
        if e.done:
            continue
        other = envs[(rnd + 3) % len(envs)]
        before_other = runner_raw(r, other)
        body = e.last[1] if isinstance(e.last[1], dict) else json.loads(e.last[1])
        e.step(pick_moves(rng, body, 0.2))
        check(runner_raw(r, other) == before_other, "env isolation", f"step on {e.id} moved {other.id}")
    for e in envs:
        o = cli_oracle(e.seed, e.mode, e.transcript)
        check(runner_raw(r, e) == o, f"multi-env final parity env {e.id}")
        if oracle_http:
            check(runner_raw(r, e) == oracle_http.game(e.seed, e.mode, e.transcript),
                  f"multi-env final http parity env {e.id}")
    # identity: a closed or re-reset id invalidates old handles
    a = envs[0]
    a.close()
    try:
        a.observe()
        check(False, "closed handle raises EnvLost")
    except EnvLost:
        check(True, "closed handle raises EnvLost")
    b = envs[1]
    r.reset(b.id, 99, "bots")
    try:
        b.step("end")
        check(False, "re-reset id invalidates old handle")
    except EnvLost:
        check(True, "re-reset id invalidates old handle")
    r.close()


def t_cap():
    r = instrument(FastRunner())
    e = r.env(1, "manual")
    st, _ = e.step(["freeze"] * 1023)
    check(st == 200 and len(e.transcript) == 1023, "1023 moves applied")
    st, _ = e.step(["freeze", "end"])
    check(st == 400 and r._last_raw == cli_oracle(1, "manual", ["freeze"] * 1025)[1],
          "batch past 1024 -> too_many_moves, error-only body == engine")
    check(len(e.transcript) == 1023 and e.observe()[1]["movesApplied"] == 1023, "over-cap batch commits nothing")
    st, _ = e.step("freeze")
    check(st == 200 and len(e.transcript) == 1024, "exactly 1024 allowed")
    check(runner_raw(r, e) == cli_oracle(1, "manual", ["freeze"] * 1024), "1024 parity")
    st, _ = e.step("end")
    check(st == 400 and json.loads(r._last_raw)["error"]["code"] == "too_many_moves", "1025th move refused")
    f = r.env(2, "bots")
    st, _ = f.step(["roll"] * 1025)
    check(st == 400 and f.transcript == [] and f.observe()[1]["movesApplied"] == 0,
          "single 1025 batch refused, nothing committed")
    r.close()


def t_failures():
    # crash: every env of the process is lost, the next env works on a new process
    r = FastRunner()
    envs = [r.env(s, "manual") for s in (1, 2, 3)]
    pid = r.pid
    os.kill(pid, signal.SIGKILL)
    time.sleep(0.1)
    lost = 0
    for e in envs:
        try:
            e.step("end")
        except EnvLost:
            lost += 1
    check(lost == 3, "crash invalidates all envs", f"{lost}/3")
    e = r.env(5, "manual")
    check(r.pid not in (None, pid) and e.step("end")[0] == 200, "lazy restart after crash")
    # timeout after a possibly committed step: no retry, all envs poisoned
    envs = [r.env(s, "bots") for s in (7, 8)]
    gen = r.generation
    r.timeout = 1e-4
    try:
        envs[0].step("end")          # a whole bots game; cannot answer in 0.1 ms
        check(False, "timeout raises")
    except EnvLost:
        check(False, "timeout raises RunnerError (not EnvLost on the in-flight call)")
    except RunnerError:
        check(r.pid is None, "timeout kills the process")
    r.timeout = 60
    for e in envs:
        try:
            e.observe()
            check(False, "timeout poisons every env")
        except EnvLost:
            check(True, "timeout poisons every env")
    check(envs[0].transcript == [], "timed-out step not recorded or retried")
    e = r.env(7, "bots")
    check(r.generation == gen + 1, "new process after timeout")
    r.close()
    # fork: the child must not use the parent's process
    r = FastRunner()
    r.health()
    with warnings.catch_warnings():
        warnings.simplefilter("ignore")
        pid = os.fork()
    if pid == 0:
        try:
            r.health()
            os._exit(1)
        except RunnerError:
            os._exit(0)
    _, status = os.waitpid(pid, 0)
    check(os.WEXITSTATUS(status) == 0 and r.health()[0] == 200, "forked child refused, parent fine")
    # a child that closes / drops the object must not quit, kill or reap the parent's runner
    ppid = r.pid
    with warnings.catch_warnings():
        warnings.simplefilter("ignore")
        pid = os.fork()
    if pid == 0:
        try:
            r.close()
            r.__del__()
            os._exit(0)
        except BaseException:
            os._exit(1)
    _, status = os.waitpid(pid, 0)
    check(os.WEXITSTATUS(status) == 0 and r.pid == ppid and r.health()[0] == 200,
          "child close/__del__ leaves the parent's runner alive")
    r.close()
    check(r.pid is None, "close reaps the process")
    # client-side guards against transport controls
    r = FastRunner()
    e = r.env(1, "manual")
    for bad in ["end\nhealth", "buy:0 end", "end\r", "end\t", "end\x0b", "end\x0c", "end\x1f",
                "end\x7f", "end\x00", "\x1b[0m"]:
        try:
            e.step(bad)
            check(False, f"control/space in moves refused {bad!r}")
        except ValueError:
            check(True, f"control/space in moves refused {bad!r}")
    for bad in ["4\x0b2", "42\x7f"]:
        try:
            r.reset(9, bad, "bots")
            check(False, f"control in seed refused {bad!r}")
        except ValueError:
            check(True, f"control in seed refused {bad!r}")
    try:
        r.replay(1, "bots\x0c", [])
        check(False, "control in mode refused")
    except ValueError:
        check(True, "control in mode refused")
    st, _ = e.step(["buy:9", "\u00e9nd"])      # non-ASCII is not a control: engine answers
    check(st == 400 and e.observe()[0] == 200, "non-ASCII move reaches the engine (bad_move)")
    try:
        e.step([""])
        check(False, "lone empty move refused")
    except ValueError:
        check(True, "lone empty move refused")
    try:
        e.step(["buy:0,end"])
        check(False, "comma inside a list item refused")
    except ValueError:
        check(True, "comma inside a list item refused")
    r.close()


def t_cleanup():
    """No leaked pipes: close/kill paths close stdin, stdout and stderr."""
    import gc
    with warnings.catch_warnings(record=True) as w:
        warnings.simplefilter("always", ResourceWarning)
        r = FastRunner(); r.health(); procs = [r._proc]; r.close()
        r = FastRunner(); r.env(1, "bots"); procs.append(r._proc); r._kill()
        r = FastRunner(); r.health(); procs.append(r._proc)
        os.kill(r.pid, signal.SIGKILL); time.sleep(0.05)
        try:
            r.observe(0)
        except RunnerError:
            pass
        r.close()
        del r
        gc.collect()
    check(all(p.stdin.closed and p.stdout.closed and p.stderr is None for p in procs),
          "all child pipes closed (stderr is a temp file, not a pipe)")
    check(all(p.returncode is not None for p in procs), "all children reaped")
    rw = [x for x in w if issubclass(x.category, ResourceWarning)]
    check(not rw, "no ResourceWarning", "; ".join(str(x.message) for x in rw)[:300])


def t_replay_api(oracle_http):
    r = FastRunner(raw=True)
    cases = [(42, "bots", []), (42, "bots", ["buy:0", "play:0", "end"]), (9, "manual", ["end"] * 4),
             (9, "manual", ["buy:0", "nope", "end"]), ("", "bots", []), ("01", "bots", []),
             (5, "", ["auto"]), (5, "manual", ["auto"] * 60)]
    for seed, mode, moves in cases:
        got = r.replay(seed, mode, moves) if seed != "" else None
        if got is None:
            continue
        check(got == cli_oracle(seed, mode, moves), f"replay() parity {seed} {mode} {len(moves)}")
        if oracle_http:
            check(got == oracle_http.game(seed, mode, moves), f"replay() http parity {seed} {mode} {len(moves)}")
    r.close()


# -- benchmark ---------------------------------------------------------------

def bench(games, oracle_http, out_dir):
    """Matched workload: the same real transcripts (many full rounds of end),
    issued as the balance harness does (one request per decision, i.e. per move
    here), through (a) HTTP replay of the whole prefix each time and (b) the
    runner stepping one move at a time. Only answers are compared; timing is
    wall clock on this (shared, loaded) machine."""
    rng = random.Random(2026)
    r = FastRunner()
    trans = []
    for g in range(games):
        e = r.env(1000 + g, "manual")
        while not e.done:
            e.step(pick_moves(rng, e.last[1], 0.0)[:1])
        trans.append((1000 + g, e.transcript))
    r.close()
    res = {"games": games, "moves": sum(len(t) for _, t in trans),
           "ends": sum(t.count("end") for _, t in trans), "machineLoad": os.getloadavg()}
    # (b) runner, full JSON per step
    r = FastRunner(raw=True)
    t0 = time.perf_counter(); lat = []
    finals_r = []
    for seed, t in trans:
        r.reset(1, seed, "manual")
        for m in t:
            a = time.perf_counter(); st, body = r.step(1, m); lat.append(time.perf_counter() - a)
        finals_r.append(body)
    res["runner"] = {"secs": time.perf_counter() - t0, "requests": len(lat),
                     "p50ms": 1000 * sorted(lat)[len(lat) // 2], "p95ms": 1000 * sorted(lat)[int(len(lat) * .95)]}
    r.close()
    # (a) HTTP replay of each prefix
    if oracle_http:
        t0 = time.perf_counter(); lat = []; finals_h = []
        for seed, t in trans:
            for i in range(1, len(t) + 1):
                a = time.perf_counter(); st, body = oracle_http.game(seed, "manual", t[:i]); lat.append(time.perf_counter() - a)
            finals_h.append(body)
        res["httpReplay"] = {"secs": time.perf_counter() - t0, "requests": len(lat),
                             "p50ms": 1000 * sorted(lat)[len(lat) // 2], "p95ms": 1000 * sorted(lat)[int(len(lat) * .95)]}
        res["finalBodiesIdentical"] = finals_h == finals_r
        res["speedup"] = res["httpReplay"]["secs"] / res["runner"]["secs"]
    # (c) CLI replay of each prefix (one process per request), on the first 2 games only
    t0 = time.perf_counter(); n = 0
    for seed, t in trans[:2]:
        for i in range(1, len(t) + 1):
            cli_oracle(seed, "manual", t[:i]); n += 1
    res["cliReplayFirst2"] = {"secs": time.perf_counter() - t0, "requests": n}
    res["loadAfter"] = os.getloadavg()
    os.makedirs(out_dir, exist_ok=True)
    with open(os.path.join(out_dir, "bench.json"), "w") as f:
        json.dump(res, f, indent=1)
    with open(os.path.join(out_dir, "bench-transcripts.json"), "w") as f:
        json.dump(trans, f)
    print(json.dumps(res, indent=1))
    return res


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--quick", action="store_true")
    ap.add_argument("--no-http", action="store_true")
    ap.add_argument("--bench", action="store_true")
    ap.add_argument("--bench-games", type=int, default=6)
    ap.add_argument("--games", type=int, default=0)
    ap.add_argument("--mutant", help="UNVERIFIED binary expected to FAIL (mutation check)")
    a = ap.parse_args()
    if a.mutant:
        import functools
        global FastRunner
        FastRunner = functools.partial(FastRunner, binary=a.mutant, verify=False)
        http = None
        for t in (lambda: drive(instrument(FastRunner()), 7, "manual", random.Random(1234), cli_oracle,
                                None, 7, name="mutant-game"),
                  lambda: t_reset_and_multi(None), t_cap):
            try:
                t()
            except Exception as e:   # an adapter consistency error also catches a mutant
                check(False, "mutant raised", repr(e))
        print(f"{PASS} passed, {len(FAILS)} failed")
        print("MUTANT CAUGHT" if FAILS else "MUTANT SURVIVED")
        sys.exit(0 if FAILS else 1)
    http = None if a.no_http else HttpOracle()
    try:
        r = FastRunner()
        rules_r = r.rules()
        r.close()
        if http:
            check(json.dumps(rules_r[1], separators=(",", ":")) is not None and
                  sha(http.rules()) == verify_manifest(RUNNER)["rulesSha256"],
                  "oracle server serves the same rules as the runner (same engine identity)")
        if a.bench:
            bench(a.bench_games, http, os.path.join(ROOT, "evidence", "fast-runner"))
            return
        t0 = time.time()
        t_manifest(); print(f"manifest ok {PASS}", flush=True)
        t_protocol(); print(f"protocol ok {PASS}", flush=True)
        t_v4_surface(); print(f"v4 surface ok {PASS}", flush=True)
        t_replay_api(http); print(f"replay ok {PASS}", flush=True)
        t_reset_and_multi(http); print(f"multi ok {PASS}", flush=True)
        t_cap(); print(f"cap ok {PASS}", flush=True)
        t_failures(); print(f"failures ok {PASS}", flush=True)
        t_cleanup(); print(f"cleanup ok {PASS}", flush=True)
        n = a.games or (3 if a.quick else 10)
        r = instrument(FastRunner())
        rng = random.Random(1234)
        summary = []
        for g in range(n):
            mode = "manual" if g % 3 else "bots"
            seed = rng.randrange(0, 2 ** 32)
            steps, errs, phase = drive(r, seed, mode, rng, cli_oracle, http, http_every=7,
                                       name=f"g{g}/{mode}/{seed}")
            summary.append((seed, mode, steps, errs, phase))
            print(f"  game {g} seed {seed} {mode}: {steps} steps, {errs} rejected, {phase}", flush=True)
        r.close()
        print(f"games: {summary}")
        print(f"elapsed {time.time() - t0:.1f}s")
    finally:
        if http:
            http.close()
    print(f"{PASS} passed, {len(FAILS)} failed")
    if FAILS:
        print("FAST RUNNER TEST FAIL")
        sys.exit(1)
    print("FAST RUNNER TEST PASS")


if __name__ == "__main__":
    main()
