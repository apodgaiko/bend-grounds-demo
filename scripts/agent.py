#!/usr/bin/env python3
"""Bend Grounds agent CLI -- a thin client for the Bend 2 backend.

This file contains NO game rules. Every state, legal action, bot move, combat
and result comes from the Bend engine (engine/*.bend). The client only:
  * reads rules and game states (same JSON as /api/rules and /api/game)
  * picks one of the engine-provided `legalActions` (policy = agent choice)
  * steps that action and reads the next state
  * saves/reproduces transcripts (seed + moves) as replay files

Backends (--backend, env BG_BACKEND; see scripts/bg_engine.py):
  fast  default: the accelerated native runner build/runner (one in-memory
        game per session, one move per step). Build: bash scripts/build.sh
  http  a running server; used automatically when --url is given
  cli   build/cli, the replay oracle (--cli PATH also selects it)
A missing or stale build is an error, never a silent switch to another backend.

Protocol 3: `buy:i` moves a shop unit into your private hand (max 7);
`play:i` deploys hand unit i to the board (max 5) for free and resolves its
play effects; `sell:i` sells a board unit (+1 gold, then its Sell abilities;
the engine reports the total as `sellGold`). Hand units cannot be sold. Three
regular copies of a card merge into a golden copy (engine-side; units carry
`golden`). Transcripts recorded under another protocol (1: buy went straight
to the board; 2: `sellhand:i` existed) do not mean the same thing and are
refused by `replay`.

Stdlib only. Usage: python3 scripts/agent.py --help
"""
import argparse
import hashlib
import json
import os
import random
import sys
import time
import urllib.error
import urllib.parse
import urllib.request

DEFAULT_URL = os.environ.get("BG_URL", "http://127.0.0.1:8765")
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import bg_engine  # noqa: E402
PROTOCOL = 3  # protocol this client and its policies were written for


class ApiError(Exception):
    def __init__(self, status, body):
        super().__init__(f"HTTP {status}: {body}")
        self.status = status
        self.body = body


class Client:
    def __init__(self, base=DEFAULT_URL, timeout=30.0):
        self.base = base.rstrip("/")
        self.timeout = timeout
        self.requests = 0

    def get(self, path, params=None):
        url = self.base + path
        if params:
            # keep ',' and ':' readable; values are plain ASCII
            url += "?" + urllib.parse.urlencode(params, safe=",:")
        self.requests += 1
        try:
            with urllib.request.urlopen(url, timeout=self.timeout) as r:
                raw = r.read().decode("utf-8")
                status = r.status
        except urllib.error.HTTPError as e:
            with e:
                raw = e.read().decode("utf-8", "replace")
                status = e.code
        try:
            body = json.loads(raw)
        except ValueError:
            body = raw
        return status, body

    def health(self):
        return self.get("/api/health")

    def rules(self):
        return self.get("/api/rules")

    def game(self, seed, moves, mode=None):
        return self._game_http(seed, moves, mode)

    def _game_http(self, seed, moves, mode=None):
        # v=PROTOCOL asks the server to refuse (400 unsupported_version) instead of
        # silently replaying our transcript under a different meaning.
        params = {"seed": str(seed), "v": str(PROTOCOL), "moves": ",".join(moves)}
        if mode:
            params["mode"] = mode
        return self.get("/api/game", params)


class CliClient(Client):
    """Offline transport: runs the native Bend replay binary build/cli
    (`cli <seed> <mode> <moves>`, `cli rules`) instead of HTTP. Same Bend
    engine and JSON, no server. The HTTP status is derived: 400 when the JSON
    carries an error, else 200. HTTP-only behaviour (routing, 404s, URL
    decoding, static files) is not exercised."""

    def __init__(self, binary):
        # build/cli takes no version argument; `cli rules` announces protocolVersion.
        super().__init__("cli:" + binary)
        self.binary = binary

    def _run(self, *args):
        import subprocess
        self.requests += 1
        r = subprocess.run([self.binary, *args], capture_output=True, text=True, timeout=120)
        try:
            body = json.loads(r.stdout)
        except ValueError:
            return 500, r.stdout + r.stderr
        return (400 if isinstance(body, dict) and body.get("error") else 200), body

    def get(self, path, params=None):
        if path == "/api/health":
            return 200, {"ok": True, "transport": "cli"}
        if path == "/api/rules":
            return self._run("rules")
        if path == "/api/game":
            p = params or {}
            return self._run(str(p.get("seed", "")), str(p.get("mode", "bots")), str(p.get("moves", "")))
        raise NotImplementedError(f"{path} is HTTP-only; not available with --cli")

    def game(self, seed, moves, mode=None):
        return self._run(str(seed), mode or "bots", ",".join(moves))


class EngineClient(Client):
    """Any bg_engine backend (default: the fast runner) behind the Client API.
    play() uses its incremental sessions. HTTP-only paths are refused."""

    def __init__(self, engine, url=DEFAULT_URL):
        self.engine = engine
        super().__init__(url)          # base is only used for web-UI links
        self.transport = engine.backend

    @property
    def requests(self):                # engine calls, incl. session steps
        return self.engine.requests

    @requests.setter
    def requests(self, n):
        self.engine.requests = n

    def get(self, path, params=None):
        if path == "/api/health":
            return 200, {"ok": True, "transport": self.engine.backend}
        if path == "/api/rules":
            return 200, self.engine.rules()
        if path == "/api/game":
            p = params or {}
            return self.engine.game(p.get("seed", ""), p.get("mode", "bots"), parse_moves(p.get("moves", "")))
        raise NotImplementedError(f"{path} is HTTP-only; use --backend http")

    def game(self, seed, moves, mode=None):
        return self.engine.game(seed, mode or "bots", list(moves))

    def session(self, seed, mode=None, moves=None):
        return self.engine.session(seed, mode or "bots", moves or [])

    def close(self):
        self.engine.close()


def make_client(url=DEFAULT_URL, cli=None, backend=None, runner=None, engine_dir="engine"):
    """Positional (url, cli) keeps the old HTTP/CLI meaning for HTTP test
    suites. backend='fast'|'http'|'cli' selects a bg_engine backend."""
    if backend is None:
        return CliClient(cli) if cli else Client(url)
    if backend == "http":
        return Client(url)
    return EngineClient(bg_engine.open_engine(backend, url=url, binary=runner or cli, engine_dir=engine_dir), url)


def protocol_of(body):
    """protocolVersion announced by a rules/game/health body. A body without
    the field predates versioning, i.e. protocol 1."""
    if isinstance(body, dict) and isinstance(body.get("protocolVersion"), int):
        return body["protocolVersion"]
    return 1


def server_protocol(client):
    st, r = client.rules()
    return protocol_of(r) if st == 200 else None


# ---------------------------------------------------------------- policies
# A policy sees the server observation and returns ONE string taken verbatim
# from obs["legalActions"]. It never invents actions or simulates rules.

def _parts(action):
    parts = action.split(":")
    if parts and parts[0][:1] == "p" and parts[0][1:].isdigit():
        parts = parts[1:]   # optional seat prefix 'p1:buy:0'
    return parts


def kind(action):
    """'p1:buy:0' -> 'buy'; 'play:2' -> 'play'; 'sell:0' -> 'sell'."""
    parts = _parts(action)
    return parts[0] if parts else action


def index(action, k=0):
    """k-th numeric argument: index('play:2') == 2, index('swap:0:3', 1) == 3."""
    parts = _parts(action)
    return int(parts[1 + k])


def actor(obs):
    """Seat whose decision is pending: obs["player"] (always 0 in bots mode)."""
    v = obs.get("player")
    return v if isinstance(v, int) else 0


def me(obs):
    seat = actor(obs)
    for p in obs.get("players", []):
        if p.get("id") == seat:
            return p
    ps = obs.get("players", [])
    return ps[seat] if seat < len(ps) else {}


def by_kind(legal):
    by = {}
    for a in legal:
        by.setdefault(kind(a), []).append(a)
    return by


def _turn_cap(obs, state, cap=20):
    """Free actions (freeze, swap, play) are legal without gold, so a naive
    policy could loop until the server's transcript cap. End the turn after
    `cap` actions."""
    key = ("cap", actor(obs), obs.get("round"))
    state[key] = state.get(key, 0) + 1
    return state[key] > cap and "end" in obs["legalActions"]


def policy_first(obs, rng, state):
    """First legal action (smoke-test baseline), ending the turn after 20 actions."""
    return "end" if _turn_cap(obs, state) else obs["legalActions"][0]


def policy_random(obs, rng, state):
    """Uniform over legal actions, ending the turn after 20 actions."""
    return "end" if _turn_cap(obs, state) else rng.choice(obs["legalActions"])


def _unit_power(u):
    if not u:
        return -1
    return (u.get("attack") or 0) + (u.get("health") or 0) + 2 * (u.get("tier") or 1)


def _at(xs, i):
    return xs[i] if 0 <= i < len(xs) else None


def _budget(state, obs):
    # per-turn action budget so a policy cannot loop forever on roll
    key = (actor(obs), obs.get("round"))
    state[key] = state.get(key, 0) + 1
    return state[key]


def policy_tempo(obs, rng, state):
    """Pure 'immediate power': deploy the strongest hand unit while the board
    has room, buy the strongest affordable shop unit into the hand, replace
    the weakest board unit when a clearly stronger one waits in hand, and
    end. Every choice is one of the server's legalActions."""
    legal = obs["legalActions"]
    n = _budget(state, obs)
    by = by_kind(legal)
    end = by.get("end", [legal[-1]])[0]
    if n > 25:
        return end
    p = me(obs)
    shop = p.get("shop") or []
    hand = p.get("hand") or []
    board = p.get("board") or []
    gold = p.get("gold") or 0
    if "play" in by:
        return max(by["play"], key=lambda a: _unit_power(_at(hand, index(a))))
    if "buy" in by:
        return max(by["buy"], key=lambda a: _unit_power(_at(shop, index(a))))
    best_hand = max([_unit_power(u) for u in hand if u] or [-1])
    if "sell" in by and len(board) >= 5 and board:
        weakest = min(by["sell"], key=lambda a: _unit_power(_at(board, index(a))))
        if best_hand > _unit_power(_at(board, index(weakest))) + 1:
            return weakest  # next decision plays the stronger hand unit
        best_shop = max([_unit_power(u) for u in shop if u] or [-1])
        if not hand and gold >= 3 and best_shop > _unit_power(_at(board, index(weakest))) + 2:
            return weakest
    if "upgrade" in by and len(board) >= 5:
        return by["upgrade"][0]  # full board: spend on tier for better shops
    if "roll" in by and gold >= 4 and n < 10:
        return by["roll"][0]
    return end


def policy_econ(obs, rng, state):
    """Invest/upgrade first in early rounds, then play like tempo.
    Demonstrates the 'invest vs immediate power' trade-off."""
    legal = obs["legalActions"]
    by = by_kind(legal)
    rnd = obs.get("round") or 1
    if rnd <= 4:
        if "invest" in by:
            return by["invest"][0]
        if "upgrade" in by:
            return by["upgrade"][0]
    if "upgrade" in by and rnd <= 7:
        return by["upgrade"][0]
    act = policy_tempo(obs, rng, state)
    # freeze a good shop we couldn't afford before ending
    if kind(act) == "end" and "freeze" in by and any(
        s for s in (me(obs).get("shop") or [])
    ) and not me(obs).get("frozen"):
        return by["freeze"][0]
    return act


def policy_climber(obs, rng, state):
    """Level first: upgrade whenever it is legal (towards the top tier), then
    play like tempo with what is left. The tier-rush end of the trade-off."""
    if "upgrade" in obs["legalActions"]:
        return "upgrade"
    return policy_tempo(obs, rng, state)


def policy_bot(obs, rng, state):
    """Delegate the whole turn to the built-in Bend bot ('auto' = bot + end)."""
    legal = obs["legalActions"]
    return "auto" if "auto" in legal else policy_first(obs, rng, state)


POLICIES = {
    "bot": policy_bot,
    "first": policy_first,
    "random": policy_random,
    "tempo": policy_tempo,
    "econ": policy_econ,
    "climber": policy_climber,
}


# ---------------------------------------------------------------- human play

def fmt_unit(u, text=False):
    if not u:
        return "(sold)"
    s = f"{u.get('name')} {u.get('attack')}/{u.get('health')} T{u.get('tier')} {u.get('tribe', '')}".rstrip()
    if u.get("golden") is True:
        s = "Golden " + s
    kw = [k for k in (u.get("keywords") or []) if k]
    if kw:
        s += " [" + ",".join(kw) + "]"
    if text and u.get("text"):
        s += f" ({u['text']})"
    return s


def _zone(units, text=False):
    return " | ".join(f"[{i}] {fmt_unit(u, text)}" for i, u in enumerate(units or [])) or "(empty)"


def render(obs, seat):
    p = me(obs)
    lines = [f"\n=== Round {obs.get('round')}/{obs.get('maxRounds')}  seat {seat} to act ==="]
    lines.append(f"You: hp={p.get('hp')} gold={p.get('gold')} tier={p.get('tier')} "
                 f"investment={p.get('investment')} upgradeCost={p.get('upgradeCost')} "
                 f"frozen={p.get('frozen')}")
    lines.append("  shop : " + _zone(p.get("shop"), True))
    lines.append(f"  hand : (private, {len(p.get('hand') or [])}/7) " + _zone(p.get("hand"), True))
    lines.append("  board: " + _zone(p.get("board"), True) + (f"   plays={p.get('plays')}" if "plays" in p else ""))
    opp = obs.get("nextOpponent")
    who = f"seat {opp}" if isinstance(opp, int) and opp >= 0 else "none (bye)"
    lines.append(f"Scout (next opponent: {who}); public info only:")
    for q in obs.get("players", []):
        if q.get("id") == seat:
            continue
        mark = "*" if q.get("id") == opp else " "
        board = ", ".join(fmt_unit(u) for u in q.get("board") or []) or "(empty)"
        lines.append(f" {mark}seat {q.get('id')} {q.get('name')}: hp={q.get('hp')} tier={q.get('tier')} "
                     f"investment={q.get('investment')} hand={q.get('handCount')} cards board: {board}")
    return "\n".join(lines)


def render_combat(obs, rnd):
    fights = [c for c in obs.get("combat") or [] if c.get("round") == rnd] or obs.get("combat") or []
    lines = []
    for c in fights:
        w = c.get("winner")
        res = "draw" if w == -1 else f"seat {w} wins, {c.get('damage')} damage"
        lines.append(f"  combat r{c.get('round')}: seat {c.get('a')} vs seat {c.get('b')}: {res}")
    return "\n".join(lines)


HUMAN_HELP = """Enter a move: its number in the list, or the exact text.
  buy:i       shop slot i -> your hand (3 gold; hand holds 7)
  play:i      hand unit i -> right end of the board (free; board holds 5; play effects resolve)
  sell:i      sell board unit i (+1 gold, then its Sell abilities; hand units cannot be sold)
  swap:i:j    reorder the board           roll / freeze / upgrade / invest / end / auto
Other commands: 'help', 'moves' (print transcript so far), 'quit' (stop; saves if --save)."""


def human_policy_factory(seat, inp=input, write=print):
    """Interactive policy: shows the observation, reads one legal action."""
    def pol(obs, rng, state):
        legal = obs["legalActions"]
        write(render(obs, seat))
        write("Legal: " + "  ".join(f"{i}){a}" for i, a in enumerate(legal)))
        while True:
            try:
                raw = inp("move> ").strip()
            except EOFError:
                raise KeyboardInterrupt
            if raw in ("quit", "q", "exit"):
                raise KeyboardInterrupt
            if raw in ("help", "h", "?"):
                write(HUMAN_HELP)
                continue
            if raw == "moves":
                write(",".join(state.get("_moves", [])) or "(none)")
                continue
            if raw.isdigit() and int(raw) < len(legal):
                return legal[int(raw)]
            if raw in legal:
                return raw
            write(f"Not legal now: {raw!r}. Choose from the list (or 'help').")
    return pol


# ---------------------------------------------------------------- driving

def state_hash(obs):
    return hashlib.sha256(json.dumps(obs, sort_keys=True).encode()).hexdigest()[:16]


def play(client, seed, policies, mode=None, max_steps=2000, verbose=False, rng_seed=0, seats=None,
         on_move=None, moves=None):
    """policies: dict seat -> policy fn, or {"*": fn}. In bots mode only seat 0
    is ever asked; in mode=manual every alive seat is asked in turn.
    If `seats` is a list, the acting seat of each move is appended to it."""
    rng = random.Random(rng_seed)
    moves = moves if moves is not None else []   # caller's list is extended in place
    state = {"_moves": moves}
    sess = None
    try:
        if hasattr(client, "session"):   # incremental: one engine step per action
            try:
                sess = client.session(seed, mode, list(moves))
            except bg_engine.EngineUnavailable as e:
                raise ApiError(400, str(e))
            status, obs = 200, sess.obs
        else:                            # replay transports: whole transcript per request
            status, obs = client.game(seed, moves, mode)
        if status != 200 or not isinstance(obs, dict):
            raise ApiError(status, obs)
        steps = 0
        while obs.get("phase") != "finished":
            if steps >= max_steps:
                raise RuntimeError(f"no finish after {max_steps} actions")
            legal = obs.get("legalActions") or []
            if not legal:
                raise RuntimeError(f"no legal actions in non-finished state: {obs}")
            seat = actor(obs)
            pol = policies.get(seat) or policies.get("*") or policy_first
            a = pol(obs, rng, state)
            if a not in legal:
                raise ValueError(f"policy for seat {seat} returned {a!r}, not in legalActions {legal}")
            if sess is not None:
                status, obs = sess.step(a)
            else:
                status, obs = client.game(seed, moves + [a], mode)
            if status != 200 or not isinstance(obs, dict) or obs.get("error"):
                raise ApiError(status, obs)
            moves.append(a)
            if seats is not None:
                seats.append(seat)
            if verbose:
                print(f"r{obs.get('round')} seat{seat} {a}", file=sys.stderr)
            if on_move:
                on_move(seat, a, obs)
            steps += 1
        return moves, obs
    finally:
        if sess is not None:
            sess.close()


def summary(obs):
    lines = [f"finished round={obs.get('round')} winner={obs.get('winner')} rank={obs.get('rank')}"]
    for p in obs.get("players", []):
        lines.append(f"  seat {p.get('id')} {p.get('name')}: hp={p.get('hp')} tier={p.get('tier')} "
                     f"hand={p.get('handCount')} board={[u.get('name') for u in p.get('board') or [] if u]}")
    return "\n".join(lines)


def load_policy(spec):
    """Built-in name (tempo, econ, ...) or 'path/to/file.py:func' for a custom
    policy func(obs, rng, state) -> one string from obs["legalActions"]."""
    if spec in POLICIES:
        return POLICIES[spec]
    path, sep, fn = spec.rpartition(":")
    if not sep or not path.endswith(".py"):
        raise SystemExit(f"unknown policy {spec!r}; use one of {sorted(POLICIES)} or file.py:func")
    import importlib.util
    mod_spec = importlib.util.spec_from_file_location("bg_custom_" + str(abs(hash(path))), path)
    mod = importlib.util.module_from_spec(mod_spec)
    mod_spec.loader.exec_module(mod)
    return getattr(mod, fn)


def parse_moves(s):
    s = (s or "").strip()
    return [m for m in s.split(",") if m] if s else []


def out(x):
    print(json.dumps(x, indent=2, sort_keys=True))


def run_human(c, a):
    others = [x for x in range(4) if x != a.seat]
    specs = [x for x in a.policies.split(",") if x]
    if len(specs) == 1:
        specs = specs * 3
    if len(specs) != 3:
        raise SystemExit("--policies needs 1 or 3 entries (for the three other seats)")
    pols = {seat: load_policy(sp) for seat, sp in zip(others, specs)}
    pols[a.seat] = human_policy_factory(a.seat)
    print(f"Bend Grounds, seed {a.seed}, manual mode. You are seat {a.seat}; "
          + ", ".join(f"seat {s}={sp}" for s, sp in zip(others, specs)) + ".")
    print(HUMAN_HELP)
    moves = parse_moves(a.moves)
    last_round = [None]

    def on_move(seat, act, obs):
        if seat != a.seat:
            print(f"  seat {seat} ({dict(zip(others, specs))[seat]}): {act}")
        if last_round[0] is not None and obs.get("round") != last_round[0] or obs.get("phase") == "finished":
            report = render_combat(obs, last_round[0])
            if report:
                print(report)
        last_round[0] = obs.get("round")

    obs, finished = None, False
    try:
        st, first = c.game(a.seed, moves, "manual")
        if st != 200:
            raise ApiError(st, first)
        last_round[0] = first.get("round")
        _, obs = play(c, a.seed, pols, mode="manual", moves=moves, on_move=on_move)
        finished = True
        print(summary(obs))
    except KeyboardInterrupt:
        print("\nStopped. Resume here with: --seed %d --moves %s" % (a.seed, ",".join(moves) or "''"))
    finally:
        print("Open this position in the web UI: %s/?seed=%d&mode=manual&moves=%s"
              % (c.base, a.seed, ",".join(moves)))
        if a.save:
            st, obs = c.game(a.seed, moves, "manual")
            rep = {"seed": a.seed, "mode": "manual", "protocolVersion": protocol_of(obs),
                   "moves": moves, "humanSeat": a.seat,
                   "policies": dict(zip(map(str, others), specs)), "finished": finished,
                   "final": {"winner": obs.get("winner"), "rank": obs.get("rank"),
                             "round": obs.get("round"), "hash": state_hash(obs)}}
            with open(a.save, "w") as f:
                json.dump(rep, f, indent=2)
            print("saved", a.save)
    return 0


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--backend", choices=bg_engine.BACKENDS, default=None,
                    help="engine transport: fast (default; build/runner), http (server at --url) or "
                         "cli (build/cli replay oracle); env BG_BACKEND")
    ap.add_argument("--url", default=None,
                    help="server base URL; giving it selects --backend http (default %s, env BG_URL)" % DEFAULT_URL)
    ap.add_argument("--cli", default=os.environ.get("BG_CLI"),
                    help="replay binary (e.g. build/cli); selects --backend cli (env BG_CLI)")
    ap.add_argument("--runner", default=None, help="fast runner binary (default build/runner, env BG_RUNNER)")
    ap.add_argument("--engine-dir", default="engine",
                    help="engine sources the --runner binary was built from (isolated candidate builds)")
    sub = ap.add_subparsers(dest="cmd", required=True)

    sub.add_parser("health", help="GET /api/health")
    sub.add_parser("rules", help="GET /api/rules (machine-readable rules + cards)")

    s = sub.add_parser("state", help="replay seed+moves and print the observation")
    s.add_argument("--seed", type=int, default=42)
    s.add_argument("--moves", default="")
    s.add_argument("--mode", default=None, choices=["bots", "manual"],
                   help="bots (default): you are seat 0; manual: every seat is client-driven")
    s.add_argument("--legal", action="store_true", help="print only legalActions")

    s = sub.add_parser("play", help="client policy on seat 0 vs built-in Bend bots")
    s.add_argument("--seed", type=int, default=42)
    s.add_argument("--policy", default="tempo", help="built-in name or file.py:func")
    s.add_argument("--save", help="write replay JSON here")
    s.add_argument("-v", "--verbose", action="store_true")

    s = sub.add_parser("selfplay", help="mode=manual: client policies control every seat")
    s.add_argument("--seed", type=int, default=42)
    s.add_argument("--policies", default="tempo,econ,random,bot",
                   help="one policy repeated for all seats, or four comma-separated policies (bot uses auto)")
    s.add_argument("--save")
    s.add_argument("-v", "--verbose", action="store_true")

    s = sub.add_parser("human", help="you play one seat interactively vs client policies (mode=manual)")
    s.add_argument("--seed", type=int, default=42)
    s.add_argument("--seat", type=int, default=0, choices=range(4), help="your seat (0-3)")
    s.add_argument("--policies", default="tempo,econ,bot",
                   help="policies for the other seats in seat order: built-in names "
                        "(bot = built-in Bend bot via 'auto') or file.py:func")
    s.add_argument("--moves", default="", help="resume from this manual-mode transcript prefix")
    s.add_argument("--save", help="write replay JSON here (also on quit)")

    s = sub.add_parser("replay", help="re-run a saved replay and verify identical result")
    s.add_argument("file")

    s = sub.add_parser("bench", help="play N seeds and tabulate results")
    s.add_argument("--seeds", default="1-10")
    s.add_argument("--policy", default="tempo", help="built-in name or file.py:func")

    a = ap.parse_args(argv)
    backend = a.backend or ("cli" if a.cli else "http" if a.url else bg_engine.default_backend())
    url = a.url or DEFAULT_URL
    try:
        c = make_client(url, a.cli, backend=backend, runner=a.runner, engine_dir=a.engine_dir)
    except bg_engine.EngineUnavailable as e:
        print(f"backend {backend} unavailable: {e}", file=sys.stderr)
        return 3
    a.url = url

    try:
        if a.cmd in ("health", "rules"):
            st, body = getattr(c, a.cmd)()
            out(body)
            return 0 if st == 200 else 1
        if a.cmd in ("play", "selfplay", "human", "bench"):
            have = server_protocol(c)
            if have != PROTOCOL:
                print(f"server speaks protocol {have}, this client and its policies need protocol {PROTOCOL} "
                      "(board-only selling, golden triples). Rebuild the server or use a matching client.", file=sys.stderr)
                return 5
        if a.cmd == "state":
            st, body = c.game(a.seed, parse_moves(a.moves), a.mode)
            out(body.get("legalActions") if a.legal and isinstance(body, dict) else body)
            return 0 if st == 200 else 1
        if a.cmd == "play":
            t = time.time()
            moves, obs = play(c, a.seed, {0: load_policy(a.policy)}, verbose=a.verbose)
            rep = {"seed": a.seed, "mode": None, "protocolVersion": protocol_of(obs),
                   "moves": moves, "policy": a.policy,
                   "final": {"winner": obs.get("winner"), "rank": obs.get("rank"),
                             "round": obs.get("round"), "hash": state_hash(obs)}}
            print(summary(obs))
            print(f"{len(moves)} moves, {c.requests} requests, {time.time()-t:.1f}s")
            print("moves=" + ",".join(moves))
            if a.save:
                with open(a.save, "w") as f:
                    json.dump(rep, f, indent=2)
                print("saved", a.save)
            return 0
        if a.cmd == "selfplay":
            names = a.policies.split(",")
            if len(names) == 1:
                names *= 4
            if len(names) != 4 or any(not name for name in names):
                raise SystemExit("--policies needs 1 or 4 non-empty entries (one per seat)")
            pols = {i: load_policy(n) for i, n in enumerate(names)}
            moves, obs = play(c, a.seed, pols, mode="manual", verbose=a.verbose)
            rep = {"seed": a.seed, "mode": "manual", "protocolVersion": protocol_of(obs),
                   "moves": moves, "policies": names,
                   "final": {"winner": obs.get("winner"), "rank": obs.get("rank"),
                             "round": obs.get("round"), "hash": state_hash(obs)}}
            print(summary(obs))
            print("moves=" + ",".join(moves))
            if a.save:
                with open(a.save, "w") as f:
                    json.dump(rep, f, indent=2)
                print("saved", a.save)
            return 0
        if a.cmd == "human":
            return run_human(c, a)
        if a.cmd == "replay":
            with open(a.file) as f:
                rep = json.load(f)
            want, have = rep.get("protocolVersion", 1), server_protocol(c)
            if want != have:
                # e.g. a v1 'buy:0,end' put the unit on the board; a v2 hand sale no longer exists.
                print(f"NOT EQUIVALENT: transcript was recorded under protocol {want}, "
                      f"server speaks protocol {have}; its moves do not mean the same thing. Not replayed.")
                return 4
            st, obs = c.game(rep["seed"], rep["moves"], rep.get("mode"))
            h = state_hash(obs)
            ok = st == 200 and h == rep["final"]["hash"] and obs.get("winner") == rep["final"]["winner"]
            print(summary(obs))
            print(f"hash {h} expected {rep['final']['hash']}: {'REPRODUCED' if ok else 'MISMATCH'}")
            return 0 if ok else 2
        if a.cmd == "bench":
            lo, _, hi = a.seeds.partition("-")
            seeds = range(int(lo), int(hi or lo) + 1)
            wins, places = 0, []
            for sd in seeds:
                moves, obs = play(c, sd, {0: load_policy(a.policy)})
                w = obs.get("winner")
                wins += w == 0
                rank = obs.get("rank") or []
                if 0 in rank:
                    places.append(rank.index(0) + 1)
                p0 = next((p for p in obs.get("players", []) if p.get("id") == 0), {})
                print(f"seed {sd}: winner={w} rank={rank} moves={len(moves)} "
                      f"plays={sum(kind(m) == 'play' for m in moves)} upgrades={moves.count('upgrade')} "
                      f"tier={p0.get('tier')} hp={p0.get('hp')}")
            mean = sum(places) / len(places) if places else float("nan")
            print(f"{a.policy}: won {wins}/{len(seeds)}, mean place {mean:.2f} (diagnostic only)")
            return 0
    except ApiError as e:
        out({"status": e.status, "body": e.body})
        return 1
    except bg_engine.EngineUnavailable as e:
        print(f"backend {backend} failed: {e}", file=sys.stderr)
        return 3
    except urllib.error.URLError as e:
        print(f"cannot reach {a.url}: {e.reason}. Start it with ./Play.command or ./build/server", file=sys.stderr)
        return 3


if __name__ == "__main__":
    sys.exit(main())
