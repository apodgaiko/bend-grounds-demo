#!/usr/bin/env python3
"""Strategy smoke test for Bend Grounds (stdlib only; no rules in here).

Plays scripted seat-0 policies against the built-in Bend bots, choosing only
among the engine's `legalActions` (protocol 3: buy puts a unit in the hand,
play:i deploys it, only board units can be sold, triples turn golden). Transport (scripts/bg_engine.py): --backend fast
(default, build/runner, one engine step per action), http (--base URL) or
cli (build/cli replay oracle). The JSON is the same /api/game JSON on all
three; HTTP-specific behaviour is covered by tests/api_test.py,
tests/http_security_test.py and tests/protocol_v3_test.py.

  tempo   - never invests; deploys from hand, buys the strongest affordable
            unit; upgrades only when nothing else useful is legal.
  greedy  - invests while legal in rounds 1-4, upgrades early (rounds <= 6),
            then plays like tempo.
  climber - upgrades whenever legal (towards tier 5), otherwise plays like
            tempo. Measures whether leveling is reachable and what it costs.

Checks:
  S1 determinism: replaying the same (seed, moves) from scratch returns the
     identical observation (bytes on http/cli, parsed JSON on fast).
  S2 liveness: every game reaches phase "finished" within maxRounds (/api/rules).
  S3 dominance (DIAGNOSTIC ONLY, never fails the run): win rate, mean rank,
     mean final HP, max tier and the round tier 5 was reached, per policy.
     There is no balance threshold; this is not a balance claim.
  S4 move cap: an absurdly long transcript gets a structured error, not a hang.
  S5 redaction: opponents' shops, gold and hands are not serialized for the
     viewer; handCount is public.
  S6 latency: per-request latency of the final state is reported (p50/p95):
     a full-game replay on http/cli, one engine step on fast.
  S7 deployment: every policy game deploys at least one unit (play:i);
     a bought unit that is never played cannot fight.

Usage: python3 tests/strategy_test.py [--backend fast|http|cli] [--base URL]
                                      [--seeds 1-20] [--json out]
  S8 manual cap: 4-seat manual self-play (tempo, greedy, climber, tempo; at
     most 25 actions per turn) must finish inside costs.maxMoves. Buy and
     play are now separate actions, so this re-measures the 1024 cap.

Exit 0 when S1, S2, S4, S5, S7, S8 pass (S3/S6 are informational).
"""
import argparse
import json
import statistics
import subprocess
import sys
import time
import urllib.error
import urllib.parse
import urllib.request
import os

sys.path.insert(0, os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), "scripts"))
import bg_engine  # noqa: E402

BASE = "http://127.0.0.1:8765"
CLI = None  # path to the native build/cli; when set, replays go through it instead of HTTP
ENG = None  # bg_engine engine for --backend fast


def _timed(fn, *args):
    t0 = time.perf_counter()
    st, obs = fn(*args)
    dt = time.perf_counter() - t0
    body = json.dumps(obs, separators=(",", ":")).encode() if isinstance(obs, dict) else str(obs).encode()
    return st, body, (obs if isinstance(obs, dict) else None), dt


class Game:
    """One sequential game: an engine session on fast (one step per action),
    a transcript replayed per request on http/cli."""

    def __init__(self, seed, extra=None):
        self.seed, self.extra = seed, extra
        self.mode = (extra or {}).get("mode", "bots")
        self.moves = []
        if ENG is not None:
            t0 = time.perf_counter()
            self.sess = ENG.session(seed, self.mode)
            self.last = (200, b"", self.sess.obs, time.perf_counter() - t0)
        else:
            self.sess = None
            self.last = fetch(seed, [], extra)

    def step(self, a):
        if self.sess is not None:
            self.last = _timed(self.sess.step, a)
            if self.last[0] == 200:
                self.moves.append(a)
        else:
            self.moves.append(a)
            self.last = fetch(self.seed, self.moves, self.extra)
        return self.last

    def close(self):
        if self.sess is not None:
            self.sess.close()


def fresh(seed, moves, extra=None):
    """Replay (seed, moves) from scratch: a new session on fast, a request on http/cli."""
    if ENG is not None:
        mode = (extra or {}).get("mode", "bots")
        t0 = time.perf_counter()
        try:
            with ENG.session(seed, mode, moves) as s:
                obs = s.obs
        except bg_engine.EngineLost:
            raise
        except bg_engine.EngineUnavailable:
            return fetch(seed, moves, extra)
        return 200, json.dumps(obs, separators=(",", ":")).encode(), obs, time.perf_counter() - t0
    return fetch(seed, moves, extra)


def fetch(seed, moves, extra=None):
    if ENG is not None:
        return _timed(ENG.game, seed, (extra or {}).get("mode", "bots"), list(moves))
    if CLI:
        t0 = time.perf_counter()
        mode = (extra or {}).get("mode", "bots")
        r = subprocess.run([CLI, str(seed), mode, ",".join(moves)], capture_output=True, timeout=30)
        dt = time.perf_counter() - t0
        body = r.stdout.strip()
        try:
            obs = json.loads(body)
        except ValueError:
            obs = None
        status = 400 if (obs is None or obs.get("error")) else 200
        return status, body, obs, dt
    q = {"seed": str(seed), "v": "3", "moves": ",".join(moves)}   # V4 cause (d): protocol 3
    if extra:
        q.update(extra)
    url = BASE + "/api/game?" + urllib.parse.urlencode(q, safe=":,")
    t0 = time.perf_counter()
    try:
        with urllib.request.urlopen(url, timeout=15) as r:
            body, status = r.read(), r.status
    except urllib.error.HTTPError as e:
        with e:   # close the error response (ResourceWarning hygiene)
            body, status = e.read(), e.code
    dt = time.perf_counter() - t0
    try:
        obs = json.loads(body)
    except ValueError:
        obs = None
    return status, body, obs, dt


def me(obs):
    return obs["players"][obs.get("player", 0)]


def unit_power(u):
    if not isinstance(u, dict):
        return -1
    return int(u.get("attack", 0)) + int(u.get("health", 0))


def idx(a):
    return int(a.split(":")[1])


def at(xs, i):
    return xs[i] if 0 <= i < len(xs) else None


def pick(policy, obs):
    legal = obs.get("legalActions") or []
    if not legal:
        return None
    rnd = int(obs.get("round", 1))
    p = me(obs)
    shop = p.get("shop") or []
    hand = p.get("hand") or []
    board = p.get("board") or []
    if policy == "greedy":
        if rnd <= 4 and "invest" in legal:
            return "invest"
        if rnd <= 6 and "upgrade" in legal:
            return "upgrade"
    if policy == "climber" and "upgrade" in legal:
        return "upgrade"
    plays = [a for a in legal if a.startswith("play:")]
    if plays:
        return max(plays, key=lambda a: unit_power(at(hand, idx(a))))
    buys = [a for a in legal if a.startswith("buy:")]
    if buys:
        return max(buys, key=lambda a: unit_power(at(shop, idx(a))))
    # board full: replace the weakest unit if the hand holds something stronger
    sells = [a for a in legal if a.startswith("sell:")]
    if sells and board and hand and len(board) >= 5:
        weakest = min(range(len(board)), key=lambda i: unit_power(board[i]))
        best_hand = max((unit_power(u) for u in hand if u), default=-1)
        if best_hand > unit_power(board[weakest]) + 1 and f"sell:{weakest}" in legal:
            return f"sell:{weakest}"
    if "upgrade" in legal:
        return "upgrade"
    if "end" in legal:
        return "end"
    return legal[0]


def play(seed, policy, max_actions_per_round=25):
    g = Game(seed)
    moves, lat = g.moves, []
    status, body, obs, dt = g.last
    lat.append(dt)
    per_round = 0
    last_round = None
    max_tier, tier5_round = 1, None
    for _ in range(1000):
        if obs is None or status >= 400 or obs.get("error"):
            return {"seed": seed, "policy": policy, "ok": False,
                    "why": f"status {status}: {body[:200]!r}", "moves": moves}
        if obs.get("phase") == "finished":
            break
        rnd = obs.get("round")
        t = me(obs).get("tier") or 1
        if t > max_tier:
            max_tier = t
        if t >= 5 and tier5_round is None:
            tier5_round = rnd
        per_round = per_round + 1 if rnd == last_round else 0
        last_round = rnd
        a = pick(policy, obs)
        if a is None:
            return {"seed": seed, "policy": policy, "ok": False, "why": "no legal actions", "moves": moves}
        if per_round >= max_actions_per_round and "end" in obs.get("legalActions", []):
            a = "end"
        status, body, obs, dt = g.step(a)
        lat.append(dt)
    g.close()
    if obs is not None and obs.get("phase") == "finished":
        body = fresh(seed, moves)[1]   # canonical final body for S1
    finished = obs is not None and obs.get("phase") == "finished"
    pl = obs.get("player", 0) if obs else 0
    rank = obs.get("rank") if obs else None
    if isinstance(rank, list):  # tolerate rank as a list of seats in finishing order
        rank = rank.index(pl) + 1 if pl in rank else None
    winner = obs.get("winner") if obs else None
    return {"seed": seed, "policy": policy, "ok": finished, "why": "" if finished else "not finished",
            "rank": rank, "won": winner == pl, "round": obs.get("round") if obs else None,
            "hp": me(obs).get("hp") if obs else None, "moves": moves,
            "maxTier": max_tier, "tier5Round": tier5_round,
            "plays": sum(m.startswith("play:") for m in moves),
            "final_latency": lat[-1], "body": body}


def play_manual(seed, seat_policies, max_actions_per_turn=25):
    """Realistic 4-seat manual self-play: every seat is a client policy, so the
    whole game (all buys, plays, sells and ends of all seats) is one transcript.
    Measures transcript length against the protocol cap."""
    extra = {"mode": "manual"}
    g = Game(seed, extra)
    moves = g.moves
    status, body, obs, _ = g.last
    per_turn, turn = 0, None
    while True:
        if obs is None or status >= 400 or obs.get("error"):
            code = ((obs or {}).get("error") or {}).get("code") if isinstance(obs, dict) else None
            return {"seed": seed, "ok": False, "code": code, "why": f"status {status}: {body[:160]!r}",
                    "moves": len(moves)}
        if obs.get("phase") == "finished":
            return {"seed": seed, "ok": True, "moves": len(moves), "round": obs.get("round"),
                    "plays": sum(m.startswith("play:") for m in moves)}
        key = (obs.get("round"), obs.get("player"))
        per_turn = per_turn + 1 if key == turn else 0
        turn = key
        a = pick(seat_policies[obs.get("player", 0) % len(seat_policies)], obs)
        if a is None:
            return {"seed": seed, "ok": False, "code": None, "why": "no legal actions", "moves": len(moves)}
        if per_turn >= max_actions_per_turn and "end" in obs.get("legalActions", []):
            a = "end"
        status, body, obs, _ = g.step(a)


def main():
    global BASE
    ap = argparse.ArgumentParser()
    ap.add_argument("--base", default=BASE)
    ap.add_argument("--seeds", default="1-20")
    ap.add_argument("--json")
    ap.add_argument("--cli", help="use the native CLI (e.g. build/cli) instead of HTTP; same as --backend cli")
    ap.add_argument("--backend", choices=bg_engine.BACKENDS, default=None,
                    help="fast (default; build/runner), http (--base) or cli (build/cli); env BG_BACKEND")
    ap.add_argument("--runner", help="fast runner binary (default build/runner, env BG_RUNNER)")
    ap.add_argument("--engine-dir", default="engine", help="engine sources of --runner")
    args = ap.parse_args()
    global CLI, ENG
    backend = args.backend or ("cli" if args.cli else bg_engine.default_backend())
    if backend == "cli":
        CLI = os.path.abspath(args.cli or bg_engine.DEFAULT_CLI)
        bg_engine.CliEngine(CLI)          # provenance check: refuse a missing/stale build/cli
    elif backend == "fast":
        try:
            ENG = bg_engine.open_engine("fast", binary=args.runner, engine_dir=args.engine_dir)
        except bg_engine.EngineUnavailable as e:
            print(f"FAIL: fast backend unavailable: {e}")
            return 1
    BASE = args.base.rstrip("/")
    print(f"transport: {backend}" + (f" {BASE}" if backend == "http" else ""))
    lo, _, hi = args.seeds.partition("-")
    seeds = list(range(int(lo), int(hi or lo) + 1))

    if backend == "http":
        try:
            urllib.request.urlopen(BASE + "/api/health", timeout=5).read()
        except Exception as e:  # noqa: BLE001
            print(f"SKIP: server not reachable at {BASE}: {e}")
            return 2

    max_rounds = 14
    try:
        if ENG is not None:
            rules = ENG.rules()
        elif CLI:
            rules = json.loads(subprocess.run([CLI, "rules"], capture_output=True, timeout=30).stdout)
        else:
            rules = json.loads(urllib.request.urlopen(BASE + "/api/rules", timeout=5).read())
        max_rounds = int(rules.get("maxRounds", max_rounds))
        proto = rules.get("protocolVersion", 1)
    except Exception as e:  # noqa: BLE001
        print(f"FAIL: cannot read rules: {e}")
        return 1
    if proto != 3:
        print(f"FAIL: server speaks protocol {proto}; this test needs protocol 3 (V4 rules)")
        return 1

    checks, results = {}, {"tempo": [], "greedy": [], "climber": []}
    for pol in results:
        for s in seeds:
            results[pol].append(play(s, pol))

    allg = [g for r in results.values() for g in r]
    bad = [g for g in allg if not g["ok"] or (g.get("round") or 0) > max_rounds]
    checks["S2_liveness"] = (not bad, f"{len(allg) - len(bad)}/{len(allg)} finished"
                             + (f"; first failure seed {bad[0]['seed']} {bad[0]['policy']}: {bad[0]['why']}" if bad else ""))

    # S1 determinism on a few finished transcripts
    det_ok, det_n = True, 0
    for g in [g for g in allg if g["ok"]][:4]:
        _, b2, _, _ = fresh(g["seed"], g["moves"])
        det_n += 1
        det_ok &= (b2 == g["body"])
    checks["S1_determinism"] = (det_ok and det_n > 0, f"{det_n} full transcripts replayed byte-identical={det_ok}")

    wr = {p: sum(g.get("won", False) for g in r) / len(r) for p, r in results.items()}
    mr = {p: statistics.mean([g["rank"] for g in r if isinstance(g.get("rank"), int)] or [float("nan")])
          for p, r in results.items()}
    hp = {p: statistics.mean([g["hp"] for g in r if isinstance(g.get("hp"), int)] or [float("nan")])
          for p, r in results.items()}
    tiers = {p: statistics.mean([g["maxTier"] for g in r if g.get("ok")] or [float("nan")]) for p, r in results.items()}
    t5 = {p: [g["tier5Round"] for g in r if g.get("tier5Round")] for p, r in results.items()}
    t5s = {p: (f"{len(v)}/{len(results[p])} reached, median round {statistics.median(v)}" if v else "never")
           for p, v in t5.items()}
    differ = sum(1 for a, b in zip(results["tempo"], results["greedy"]) if (a.get("rank"), a.get("hp")) != (b.get("rank"), b.get("hp")))
    s3 = all(0 < w < 1 for w in wr.values()) and differ > 0
    fmt = lambda d: {k: round(v, 2) if isinstance(v, float) else v for k, v in d.items()}
    checks["S3_dominance_diag"] = (s3, f"winrate {fmt(wr)}, mean rank {fmt(mr)}, mean final hp {fmt(hp)}, "
                                       f"mean max tier {fmt(tiers)}, tier 5: {t5s}, "
                                       f"tempo/greedy differ on {differ}/{len(seeds)} seeds")

    st, body, obs, dt = fetch(seeds[0], ["freeze"] * 2000)
    s4 = st >= 400 and obs is not None and bool(obs.get("error"))
    checks["S4_move_cap"] = (s4, f"2000 moves -> status {st} in {dt:.2f}s, error={(obs or {}).get('error')!r}")

    st, body, obs, _ = fetch(seeds[0], [])
    leaks = []
    if obs:
        for k, p in enumerate(obs.get("players", [])):
            if k != obs.get("player", 0) and p.get("shop") not in (None, [], "hidden"):
                leaks.append(k)
    gold_public = bool(obs) and any("gold" in p and p["gold"] is not None
                                    for k, p in enumerate(obs.get("players", [])) if k != obs.get("player", 0))
    # hands: check a mid-game state of a finished game, where bots hold cards
    hand_leaks, counted = [], True
    for g in [g for g in allg if g["ok"]][:6]:
        _, _, mid, _ = fresh(g["seed"], g["moves"][: len(g["moves"]) // 2])
        for k, p in enumerate((mid or {}).get("players", [])):
            counted &= isinstance(p.get("handCount"), int)
            if k != mid.get("player", 0) and p.get("hand") is not None:
                hand_leaks.append((g["seed"], k))
    checks["S5_redaction"] = (bool(obs) and not leaks and not gold_public and not hand_leaks and counted,
                              f"opponent shops leaked for seats {leaks}; opponent gold visible={gold_public}; "
                              f"opponent hands leaked {hand_leaks}; handCount public={counted}")

    undeployed = [(g["seed"], g["policy"]) for g in allg if g["ok"] and not g["plays"]]
    checks["S7_deployment"] = (not undeployed, f"games without any play:i {undeployed}; "
                               f"plays/game {min(g['plays'] for g in allg)}-{max(g['plays'] for g in allg)}")

    # S8: realistic 4-seat manual transcripts must fit the protocol cap
    cap = int((rules.get("costs") or {}).get("maxMoves", 1024))
    man = [play_manual(sd, ["tempo", "greedy", "climber", "tempo"]) for sd in seeds[:8]]
    over = [m for m in man if not m["ok"]]
    lens = [m["moves"] for m in man if m["ok"]]
    checks["S8_manual_cap"] = (not over, f"{len(lens)}/{len(man)} four-seat manual games finished; "
                               f"transcript length {min(lens or [0])}-{max(lens or [0])} "
                               f"(mean {statistics.mean(lens or [0]):.0f}) vs cap {cap}"
                               + (f"; failures {[(m['seed'], m['code'] or m['why']) for m in over]}" if over else ""))

    lats = sorted(g["final_latency"] for g in allg if g["ok"])
    if lats:
        p95 = lats[min(len(lats) - 1, int(0.95 * len(lats)))]
        lens = [len(g["moves"]) for g in allg if g["ok"]]
        checks["S6_latency"] = (True, f"{'final engine step' if ENG else 'full-game replay'} p50={statistics.median(lats)*1000:.0f}ms p95={p95*1000:.0f}ms, moves/game {min(lens)}-{max(lens)}")

    ok = True
    for k, (passed, msg) in checks.items():
        tag = ("INFO" if passed else "WARN") if k.startswith(("S3", "S6")) else ("PASS" if passed else "FAIL")
        print(f"{tag} {k}: {msg}")
        if not k.startswith(("S3", "S6")):
            ok &= passed
    if args.json:
        out = {"transport": ("fast" if ENG else ("cli:" + CLI) if CLI else ("http:" + BASE)),
               "provenance": ENG.provenance() if ENG else None, "protocolVersion": proto, "seeds": seeds, "checks": {k: {"pass": v[0], "detail": v[1]} for k, v in checks.items()},
               "games": [{k: v for k, v in g.items() if k != "body"} for g in allg], "manual": man}
        with open(args.json, "w") as f:
            json.dump(out, f, indent=1)
    print("STRATEGY SMOKE:", "PASS" if ok else "FAIL")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
