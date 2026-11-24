#!/usr/bin/env python3
"""Shared engine backend for simulation consumers (stdlib only).

Simulation consumers (scripts/agent.py play/selfplay/bench/human and
tests/strategy_test.py) get their game states through open_engine(). All rules still run in Bend; this module only
chooses the transport.

Backends
  fast  (default) the accelerated native runner, build/runner, driven by
        scripts/fast_runner.py. A running Bend process keeps each game in
        memory and applies one move per step (G.g_apply), so a game costs
        O(moves) instead of one full replay per request.
  http  GET /api/game on a running server (--url / BG_URL). The HTTP,
        security, protocol and UI suites test HTTP directly and never use the
        fast backend.
  cli   build/cli, replays the whole transcript on every call. Slow. It is
        the replay oracle that the fast backend is checked against
        (tests/fast_runner_test.py).

No silent fallback: if build/runner (or build/cli) is missing or stale,
open_engine() raises EngineUnavailable with the build command. The fast
runner validates its own provenance manifest before every spawn
(scripts/fast_runner.py); build/cli is checked against build/cli.manifest.json
(scripts/build_manifest.py).

Interface of every engine
  session(seed, mode, moves=())-> Session, the incremental path for sequential
                                  games: s.obs, s.moves, s.step(action) ->
                                  (status, obs). A rejected single move leaves
                                  the session unchanged.
  game(seed, mode, moves)      -> (status, obs) with replay semantics, i.e. what
                                  /api/game?seed=&mode=&moves= returns. On the
                                  fast backend a call whose moves extend the
                                  previous call's transcript steps only the new
                                  suffix. Use it for one-off states, not loops.
  rules()                      -> dict, same JSON as /api/rules
  provenance()                 -> dict to record with results
  close()                      -> stop owned subprocesses (also context manager)

One engine per process. Multiprocessing harnesses open one engine per worker
(e.g. in a Pool initializer) and never share it across processes.
"""
import atexit
import collections
import hashlib
import json
import os
import subprocess
import sys
import urllib.error
import urllib.parse
import urllib.request

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.join(ROOT, 'scripts'))

BACKENDS = ('fast', 'http', 'cli')
DEFAULT_BACKEND = 'fast'
DEFAULT_URL = os.environ.get('BG_URL', 'http://127.0.0.1:8765')
DEFAULT_CLI = os.path.join(ROOT, 'build', 'cli')
# Game protocol (schemaVersion/protocolVersion of the JSON) that HTTP requests
# pin with `v=`; a server speaking another protocol answers 400
# unsupported_version instead of replaying under a different meaning. This is
# NOT the fast runner wire protocol (fast_runner.PROTOCOL, "fast-runner/1").
PROTOCOL = 3


def absolute(p):
    return p if os.path.isabs(p) else os.path.join(ROOT, p)


class EngineUnavailable(RuntimeError):
    """The requested backend cannot run (missing or stale build, unreachable server)."""


class EngineLost(EngineUnavailable):
    """The fast runner process died or timed out. Every env of that engine is
    poisoned: a step may or may not have been committed, so nothing is retried
    automatically. Open a new engine and rebuild the transcript explicitly."""


ACTION_CHARS = frozenset('abcdefghijklmnopqrstuvwxyz0123456789:')


def check_action(action):
    """A session step is exactly ONE action token: 1..32 characters from
    [a-z0-9:] (e.g. `buy:0`, `sell:2`, `end`). Batches (`,`), whitespace,
    control characters, percent-escapes and other bytes are refused before
    anything reaches the engine. Unknown tokens inside this domain go to the
    engine, which answers bad_move/illegal_move. This domain is a client-side
    rule; it makes no claim about HTTP parity for arbitrary query bytes (that
    is what tests/http_security_test.py and the HTTP protocol test cover)."""
    if not isinstance(action, str) or not 1 <= len(action) <= 32 or not set(action) <= ACTION_CHARS:
        raise ValueError(f'session step takes one action token [a-z0-9:]{{1,32}}, got {action!r}')
    return action


def sha256_file(path):
    h = hashlib.sha256()
    with open(path, 'rb') as f:
        for block in iter(lambda: f.read(1 << 20), b''):
            h.update(block)
    return h.hexdigest()


def _parse(raw):
    try:
        return json.loads(raw)
    except ValueError:
        return raw.decode('utf-8', 'replace') if isinstance(raw, bytes) else raw


def _ok(status, obs):
    return status == 200 and isinstance(obs, dict) and not obs.get('error')


def default_backend():
    """BG_BACKEND overrides the default for every consumer (fast|http|cli)."""
    b = os.environ.get('BG_BACKEND', DEFAULT_BACKEND)
    if b not in BACKENDS:
        raise SystemExit(f'BG_BACKEND={b!r}: expected one of {", ".join(BACKENDS)}')
    return b


# ---------------------------------------------------------------- sessions

class Session:
    """One game in progress on a replay transport (http/cli): each step
    replays the accepted transcript plus the new move. `moves` is an optional
    starting transcript (e.g. a resumed game); it must be fully legal."""

    def __init__(self, engine, seed, mode, moves=()):
        self.engine, self.seed, self.mode = engine, seed, mode or 'bots'
        self.moves, self.steps = list(moves), 0
        st, obs = engine.game(seed, self.mode, self.moves)
        if not _ok(st, obs):
            raise EngineUnavailable(f'initial state seed={seed} mode={self.mode}: {st} {str(obs)[:300]}')
        self.obs = obs

    def step(self, action):
        check_action(action)
        self.steps += 1
        st, obs = self.engine.game(self.seed, self.mode, self.moves + [action])
        if _ok(st, obs):
            self.moves.append(action)
            self.obs = obs
        return st, obs

    def close(self):
        pass

    def __enter__(self):
        return self

    def __exit__(self, *exc):
        self.close()


class FastSession(Session):
    """One game in progress inside the fast runner (in-memory G.g_apply).
    After close(), or once its engine is lost or used from a forked child,
    every call raises: a stale handle never reaches another game."""

    def __init__(self, engine, seed, mode, moves=()):
        self.engine, self.seed, self.mode = engine, seed, mode or 'bots'
        self.steps = 0
        self.closed = False
        self.env = engine._new_env(seed, self.mode)
        moves = list(moves)
        st, obs = engine._call(self.env.step, moves) if moves else engine._call(self.env.observe)
        if not _ok(st, obs):
            self.close()
            raise EngineUnavailable(f'initial state seed={seed} mode={self.mode}: {st} {str(obs)[:300]}')
        self.obs = obs

    @property
    def moves(self):
        return list(self.env.transcript)

    def step(self, action):
        check_action(action)
        if self.closed:
            raise EngineLost('session is closed')
        self.steps += 1
        self.engine.requests += 1
        st, obs = self.engine._call(self.env.step, [action])   # one move: rejected => unchanged
        if _ok(st, obs):
            self.obs = obs
        return st, obs

    def close(self):
        if not self.closed:
            self.closed = True
            self.engine._release(self.env)


# ---------------------------------------------------------------- engines

class _Engine:
    requests = 0

    def session(self, seed, mode='bots', moves=()):
        return Session(self, seed, mode, moves)

    def close(self):
        pass

    def __enter__(self):
        return self

    def __exit__(self, *exc):
        self.close()


class HttpEngine(_Engine):
    backend = 'http'

    def __init__(self, url=None, timeout=60.0):
        self.base = (url or DEFAULT_URL).rstrip('/')
        self.timeout = timeout
        self.requests = 0

    def get(self, path, params=None):
        url = self.base + path
        if params:
            url += '?' + urllib.parse.urlencode(params, safe=',:')
        self.requests += 1
        try:
            with urllib.request.urlopen(url, timeout=self.timeout) as r:
                return r.status, r.read()
        except urllib.error.HTTPError as e:
            with e:
                return e.code, e.read()
        except (urllib.error.URLError, OSError) as e:
            raise EngineUnavailable(f'cannot reach {self.base}: {e}') from e

    def rules(self):
        st, raw = self.get('/api/rules', {'v': str(PROTOCOL)})
        if st != 200:
            raise EngineUnavailable(f'{self.base}/api/rules -> HTTP {st}')
        return json.loads(raw)

    def game_raw(self, seed, mode, moves):
        params = {'seed': str(seed), 'v': str(PROTOCOL), 'moves': ','.join(moves)}
        if mode:
            params['mode'] = mode
        st, raw = self.get('/api/game', params)
        return st, _parse(raw), raw

    def game(self, seed, mode, moves):
        st, obs, _ = self.game_raw(seed, mode, moves)
        return st, obs

    def provenance(self):
        return {'backend': 'http', 'url': self.base}


class CliEngine(_Engine):
    """Replay oracle: build/cli replays the whole transcript on every call."""
    backend = 'cli'

    def __init__(self, binary=None, timeout=120, verify=True):
        import build_manifest
        self.binary = os.path.abspath(binary or DEFAULT_CLI)
        self.timeout = timeout
        self.requests = 0
        try:
            self._prov = build_manifest.verify_binary(self.binary) if verify else \
                {'binary': self.binary, 'binarySha256': sha256_file(self.binary), 'unverified': True}
        except (build_manifest.StaleBuild, OSError) as e:
            raise EngineUnavailable(str(e)) from e
        if not verify:
            print(f'WARNING: {self.binary} used WITHOUT provenance check (archival use only)', file=sys.stderr)

    def _run(self, *args):
        self.requests += 1
        r = subprocess.run([self.binary, *args], capture_output=True, timeout=self.timeout)
        raw = r.stdout.strip()
        if r.returncode != 0 and not raw:
            raise EngineUnavailable(f'{self.binary} exited {r.returncode}: {r.stderr[:300]!r}')
        return raw

    def rules(self):
        return json.loads(self._run('rules'))

    def game_raw(self, seed, mode, moves):
        raw = self._run(str(seed), mode or 'bots', ','.join(moves))
        obs = _parse(raw)
        return (200 if _ok(200, obs) else 400), obs, raw

    def game(self, seed, mode, moves):
        st, obs, _ = self.game_raw(seed, mode, moves)
        return st, obs

    def provenance(self):
        return dict(self._prov, backend='cli')


class FastEngine(_Engine):
    """build/runner via scripts/fast_runner.py; one runner process per engine,
    owned by the process that opened it (never shared across fork)."""
    backend = 'fast'
    CACHE = 4   # game() compatibility envs kept (LRU); sessions are separate

    def __init__(self, binary=None, engine_dir='engine', verify=True, timeout=60):
        try:
            import fast_runner
        except ImportError as e:
            raise EngineUnavailable('fast backend unavailable: scripts/fast_runner.py missing') from e
        self._fr = fast_runner
        self.requests = 0
        self._pid = os.getpid()
        self._owned = set()
        self._cache = collections.OrderedDict()   # (seed, mode) -> env for game()
        self._lost = None     # set once the runner died/timed out: every env is poisoned
        self.runner = None
        try:
            self.runner = fast_runner.FastRunner(binary=binary, timeout=timeout,
                                                 engine_dir=absolute(engine_dir), verify=verify)
            self._rcall('health')          # spawn now: rules hash checked at start
        except EngineUnavailable:
            raise
        except (fast_runner.RunnerError, OSError) as e:
            raise EngineUnavailable(f'fast backend unavailable: {e}; build with: bash scripts/build.sh') from e
        atexit.register(self.close)

    def _call(self, fn, *args):
        """Every runner interaction goes through here. A transport failure
        (process death, timeout, broken pipe, lost env) poisons the whole
        engine and is never retried: a batch may already be committed."""
        if os.getpid() != self._pid:
            raise EngineLost('fast engine used from a forked child; open one engine per process')
        if self._lost is not None:
            raise EngineLost(f'fast runner lost earlier ({self._lost}); open a new engine')
        if self.runner is None:
            raise EngineLost('fast engine is closed')
        try:
            return fn(*args)
        except self._fr.StaleRunner as e:
            self._poison(e)
            raise EngineUnavailable(f'{e}; build with: bash scripts/build.sh') from e
        except (self._fr.RunnerError, OSError, TimeoutError) as e:
            self._poison(e)
            raise EngineLost(f'fast runner lost: {self._lost}; nothing retried') from e

    def _rcall(self, name, *args):
        """_call on a runner method, resolved only after the liveness checks."""
        return self._call(lambda *a: getattr(self.runner, name)(*a), *args)

    def _poison(self, e):
        self._lost = f'{type(e).__name__}: {e}'
        self._owned.clear()
        self._cache.clear()
        r, self.runner = self.runner, None
        if r is not None:
            r.close()

    def _new_env(self, seed, mode):
        try:
            env = self._rcall('env', seed, mode)
        except ValueError as e:      # reset refused (bad seed/mode): an engine answer, not a transport fault
            raise EngineUnavailable(str(e)) from e
        self._owned.add(env)
        return env

    def _release(self, env):
        if env in self._owned:
            self._owned.discard(env)
            if self._lost is None and self.runner is not None and os.getpid() == self._pid:
                self._call(env.close)

    def session(self, seed, mode='bots', moves=()):
        return FastSession(self, seed, mode, moves)

    def rules(self):
        st, body = self._rcall('rules')
        if st != 200:
            raise EngineUnavailable(f'runner rules -> {st} {str(body)[:200]}')
        return body

    def game_raw(self, seed, mode, moves):
        st, obs = self.game(seed, mode, moves)
        return st, obs, json.dumps(obs, separators=(',', ':')).encode()

    def game(self, seed, mode, moves):
        """Replay semantics, for one-off states and legacy callers (sequential
        games should use session()). Keeps a small LRU of envs: when `moves`
        extends an env's committed transcript (full prefix compare) only the
        suffix is stepped; otherwise a fresh env applies `moves` as one batch.
        A partially rejected batch keeps its committed prefix, exactly as the
        runner contract (and /api/game's movesApplied) says."""
        mode = mode or 'bots'
        moves = list(moves)
        self.requests += 1
        key = (str(seed), mode)
        env = self._cache.get(key)
        if env is not None:
            done = env.transcript
            if len(moves) >= len(done) and moves[:len(done)] == done:
                self._cache.move_to_end(key)
                rest = moves[len(done):]
                return self._call(env.step, rest) if rest else self._call(env.observe)
            del self._cache[key]
            self._release(env)
        try:
            env = self._new_env(seed, mode)
        except EngineUnavailable:
            if self._lost is not None:
                raise
            return self._rcall('replay', seed, mode, moves)   # refused reset: engine's 400 body
        self._cache[key] = env
        while len(self._cache) > self.CACHE:
            _, old = self._cache.popitem(last=False)
            self._release(old)
        return self._call(env.step, moves) if moves else self._call(env.observe)

    def provenance(self):
        # The runner validated this manifest (and the rules hash) before spawning.
        return {'backend': 'fast', 'manifest': self.manifest}

    @property
    def manifest(self):
        return getattr(self.runner, 'manifest', None) if self.runner else self._manifest_cache

    _manifest_cache = None

    def close(self):
        if os.getpid() != self._pid:
            return            # never touch the parent's runner from a forked child
        r = self.runner
        if r is not None:
            self._manifest_cache = r.manifest
        self._owned.clear()
        self._cache.clear()
        self.runner = None
        if r is not None:
            r.close()


def same_engine_sources(cli_prov, fast_prov):
    """Differential CLI-vs-runner checks are only meaningful when both binaries
    were built from the same game.bend and econ.bend. Returns (ok, detail)."""
    cs = {os.path.basename(p): h for p, h in (cli_prov.get('sources') or {}).items()}
    fs = ((fast_prov.get('manifest') or {}).get('sources') or {})
    pairs = {n: (cs.get(n), fs.get(n)) for n in ('game.bend', 'econ.bend')}
    ok = all(a and a == b for a, b in pairs.values())
    return ok, {n: {'cli': a, 'runner': b} for n, (a, b) in pairs.items()}


def open_engine(backend=None, url=None, binary=None, engine_dir='engine', verify=True):
    """backend: fast (default; env BG_BACKEND), http (url / BG_URL) or cli
    (binary / build/cli). `binary`/`engine_dir` select an isolated build (e.g.
    a balance candidate). Raises EngineUnavailable; never falls back."""
    backend = backend or default_backend()
    if backend == 'fast':
        return FastEngine(binary or os.environ.get('BG_RUNNER'), engine_dir, verify)
    if backend == 'http':
        return HttpEngine(url)
    if backend == 'cli':
        return CliEngine(binary or os.environ.get('BG_CLI'), verify=verify)
    raise ValueError(f'unknown backend {backend!r}; expected one of {", ".join(BACKENDS)}')


def add_backend_args(ap):
    """Standard --backend/--url/--runner/--engine-dir flags."""
    ap.add_argument('--backend', choices=BACKENDS, default=default_backend(),
                    help='engine transport: fast (default; accelerated native runner), http '
                         '(running server at --url) or cli (build/cli replay oracle); env BG_BACKEND')
    ap.add_argument('--url', default=DEFAULT_URL, help='server base URL for --backend http (env BG_URL)')
    ap.add_argument('--runner', default=None,
                    help='native binary for --backend fast (default build/runner, env BG_RUNNER) '
                         'or cli (default build/cli, env BG_CLI)')
    ap.add_argument('--engine-dir', default='engine',
                    help='engine sources the --runner binary was built from (isolated candidate builds)')
    return ap


def engine_from_args(a):
    return open_engine(a.backend, url=a.url, binary=a.runner, engine_dir=a.engine_dir)
