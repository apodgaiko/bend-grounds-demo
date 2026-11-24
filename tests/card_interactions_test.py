#!/usr/bin/env python3
"""EMBER v2 card-interaction runner.

Authoritative assertions live in tests/card_interactions.bend (real engine,
hand-calculated expectations). This script only drives them and adds a thin
real-HTTP consistency lane:

1. Bend fixtures: `bun vendor/bend/bend2/main.ts tests/card_interactions.bend`
   checks the file (every `law k_*` fixture must hold for bend2), runs `main`,
   and compares stdout with the `#|` lines at the end of the file.
2. Optional `--verdict`: rechecks the same file with the Lean-proven kernel.
3. HTTP lane, only when BG_URL is set (or --url): /api/rules card table
   against the SAME expected rows written in the Bend file, plus buy/play/
   board-sell zone flows, the removed hand sale (protocol 3: `sellhand:i` is
   a bad_move), rejection atomicity and hand privacy on /api/game.

Python is a client here, never a rules oracle: HTTP expectations come from
the Bend file's hand-written rows or from the observed pre-state.

Usage:
  python3 tests/card_interactions_test.py            # Bend fixtures (+HTTP if BG_URL)
  python3 tests/card_interactions_test.py --verdict  # also the kernel recheck
  BG_URL=http://127.0.0.1:8765 python3 tests/card_interactions_test.py
Exit status 0 only if every executed lane passes.
"""
import argparse
import json
import os
import re
import shutil
import subprocess
import sys
import urllib.error
import urllib.parse
import urllib.request

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
BEND_FILE = os.path.join(ROOT, "tests", "card_interactions.bend")
COMPILER = os.path.join(ROOT, "vendor", "bend", "bend2", "main.ts")


def env_path():
    home = os.path.expanduser("~")
    extra = [os.path.join(home, ".bun", "bin"), os.path.join(home, ".elan", "bin"),
             "/opt/homebrew/bin", "/usr/local/bin"]
    env = dict(os.environ)
    env["PATH"] = os.pathsep.join(extra + [env.get("PATH", "")])
    return env


def tidy(text):
    return "\n".join(l.rstrip() for l in text.strip().splitlines())


def expected_lines(src):
    return tidy("\n".join(l[2:] for l in src.splitlines() if l.startswith("#|")))


def run_bend(args, timeout):
    env = env_path()
    bun = shutil.which("bun", path=env["PATH"])
    if not bun:
        return None, "", "bun not found (run scripts/setup.sh)"
    p = subprocess.run([bun, COMPILER, BEND_FILE] + args, cwd=ROOT, env=env,
                       capture_output=True, text=True, timeout=timeout)
    return p.returncode, p.stdout, p.stderr


# -- lane 1/2: Bend ---------------------------------------------------------

def lane_fixtures():
    with open(BEND_FILE, encoding="utf-8") as fh:
        src = fh.read()
    want = expected_lines(src)
    rc, out, diagnostics = run_bend([], 600)
    if diagnostics:
        print(diagnostics, file=sys.stderr, end="" if diagnostics.endswith("\n") else "\n")
    if rc is None:
        print("FAIL fixtures:", diagnostics)
        return False
    got = tidy(out)
    total = len(want.splitlines())
    if got == want and rc == 0:
        print(f"PASS fixtures: {total}/{total} cases (bend2 check of every law + native run)")
        return True
    print(f"FAIL fixtures (exit {rc}). Output differs from the #| block:")
    wl, gl = want.splitlines(), got.splitlines()
    shown = 0
    for g in gl:
        if g not in wl and shown < 40:
            print("  " + g)
            shown += 1
    missing = [w for w in wl if w not in gl]
    if missing:
        print(f"  ({len(missing)} expected lines missing, e.g. {missing[:5]})")
    return False


def lane_verdict():
    rc, out, diagnostics = run_bend(["--verdict"], 900)
    if diagnostics:
        print(diagnostics, file=sys.stderr, end="" if diagnostics.endswith("\n") else "\n")
    if rc == 0 and "ALL PROOFS CHECK" in out:
        print("PASS verdict: every law k_* fixture rechecked by the BendTT kernel")
        return True
    print(f"FAIL verdict (exit {rc}):\n" + out[-3000:])
    return False


# -- lane 3: HTTP -----------------------------------------------------------

ROW = re.compile(r'"(\d+) (.+?) (Ember|Tide|Stone|Neutral) t(\d) \d+:(\d+)/(\d+)(s?) g([TF]) a(\d+) r(\d+) i(\d+) \| (.*?)"$')


def roster_rows(src):
    rows = {}
    for line in src.splitlines():
        m = ROW.search(line.strip().lstrip("[,").strip())
        if m:
            cid = int(m.group(1))
            rows[cid] = dict(name=m.group(2), tribe=m.group(3), tier=int(m.group(4)),
                             attack=int(m.group(5)), health=int(m.group(6)),
                             shield=m.group(7) == "s", guard=m.group(8) == "T",
                             armor=int(m.group(9)), rally=int(m.group(10)),
                             income=int(m.group(11)), text=m.group(12))
    return rows


# cards whose Play does nothing and which observe nothing (from the table:
# keyword-only, End of turn or Sell cards). Ordinary V3 ids 0..35 only; the
# Neutral cards 36..43 are covered by tests/card_interactions.bend.
QUIET_PLAY = {0, 3, 4, 6, 7, 8, 11, 15, 16, 17, 19, 21, 22, 23, 26, 27, 28, 29, 31, 32, 33, 34, 35}


class Http:
    def __init__(self, base):
        self.base = base.rstrip("/")

    def get(self, path, **q):
        url = self.base + path + ("?" + urllib.parse.urlencode(q, safe=":,") if q else "")
        try:
            with urllib.request.urlopen(url, timeout=20) as r:
                return r.status, json.loads(r.read().decode())
        except urllib.error.HTTPError as e:
            with e:
                return e.code, json.loads(e.read().decode() or "null")

    def game(self, seed, moves, mode="manual"):
        return self.get("/api/game", seed=str(seed), mode=mode, moves=",".join(moves))


class Checks:
    def __init__(self):
        self.ok = 0
        self.bad = []

    def eq(self, name, got, want):
        if got == want:
            self.ok += 1
        else:
            self.bad.append(f"{name}: got {got!r} want {want!r}")


def unit_key(u):
    return (u.get("id"), u.get("attack"), u.get("health"), bool(u.get("shield")))


def lane_http(base):
    with open(BEND_FILE, encoding="utf-8") as fh:
        src = fh.read()
    rows = roster_rows(src)
    h = Http(base)
    c = Checks()
    st, rules = h.get("/api/rules")
    if st != 200 or rules.get("schemaVersion") != 3:
        print(f"FAIL http: {base}/api/rules is not schema 3 (status {st}); stale pre-V4 server?")
        return False
    cards = {k["id"]: k for k in rules.get("cards", [])}
    # V4 (cause e): 36 ordinary cards + 8 Neutral ids 36..43 (the printed Neutral roster)
    c.eq("rules card count", len(cards), 44)
    c.eq("expected rows parsed from the Bend file", len(rows), 44)
    c.eq("no hand-sale refund field (V4 cause a)", "sellHandRefund" in rules.get("costs", {}), False)
    for cid, r in rows.items():
        k = cards.get(cid, {})
        for f in ("name", "tribe", "tier", "attack", "health", "text"):
            c.eq(f"card {cid} {f}", k.get(f), r[f])
        c.eq(f"card {cid} shield", bool(k.get("shield")), r["shield"])
        c.eq(f"card {cid} guard", bool(k.get("guard")), r["guard"])

    # find a seed whose seat-0 opening shop starts with a quiet card
    seed = None
    for s in range(1, 400):
        st, g = h.game(s, [])
        if st == 200 and g["players"][0]["shop"] and g["players"][0]["shop"][0]["id"] in QUIET_PLAY:
            seed = s
            break
    if seed is None:
        c.bad.append("no seed in 1..399 opens with a quiet card")
    else:
        st, g0 = h.game(seed, [])
        p0 = g0["players"][0]
        card0 = p0["shop"][0]
        r0 = rows[card0["id"]]
        base0 = (card0["id"], r0["attack"], r0["health"], r0["shield"])
        c.eq("shop unit = base unit from the table", unit_key(card0), base0)

        # buy: hand +1 base unit, gold -3, board unchanged, shop entry removed
        st, g1 = h.game(seed, ["buy:0"])
        p1 = g1["players"][0]
        c.eq("buy accepted", (st, g1.get("error")), (200, None))
        c.eq("buy gold", p1["gold"], p0["gold"] - 3)
        c.eq("buy hand", [unit_key(u) for u in p1["hand"]], [base0])
        c.eq("buy handCount", p1["handCount"], 1)
        c.eq("buy board", p1["board"], p0["board"])
        c.eq("buy shop", [u["id"] for u in p1["shop"]], [u["id"] for u in p0["shop"][1:]])
        c.eq("buy plays", p1["plays"], 0)

        # play: quiet card moves hand -> board unchanged, free, plays 1
        st, g2 = h.game(seed, ["buy:0", "play:0"])
        p2 = g2["players"][0]
        c.eq("play accepted", (st, g2.get("error")), (200, None))
        c.eq("play board", [unit_key(u) for u in p2["board"]], [base0])
        c.eq("play hand", p2["hand"], [])
        c.eq("play gold", p2["gold"], p1["gold"])
        c.eq("play plays", p2["plays"], 1)

        # V4 (cause a): no hand sale. `sellhand:0` no longer parses: bad_move,
        # nothing applied after the prefix, state = the accepted prefix
        st, g3 = h.game(seed, ["buy:0", "sellhand:0"])
        err3 = g3.get("error") or {}
        c.eq("sellhand rejected", (st, err3.get("code"), err3.get("index"), g3.get("movesApplied")),
             (400, "bad_move", 1, 1))
        c.eq("sellhand state unchanged", g3.get("players"), g1.get("players"))
        c.eq("sellhand not legal", [a for a in g1["legalActions"] if a.startswith("sellhand")], [])

        # board sale of the quiet card: base refund 1 plus the table's "Sell: gain N gold"
        # (hand-written row text in the Bend file), board empty, hand untouched
        m = re.search(r"Sell: gain (\d+) gold", r0["text"])
        want_sell = 1 + (int(m.group(1)) if m else 0)
        c.eq("board sellGold of the quiet card", p2["board"][0].get("sellGold"), want_sell)
        st, g4 = h.game(seed, ["buy:0", "play:0", "sell:0"])
        p4 = g4["players"][0]
        c.eq("sell accepted", (st, g4.get("error")), (200, None))
        c.eq("sell gold", p4["gold"], p2["gold"] + want_sell)
        c.eq("sell board", p4["board"], [])
        c.eq("sell hand", p4["hand"], p2["hand"])

        # rejections are atomic: state equals the accepted prefix
        for moves, idx in ((["play:0"], 0), (["buy:0", "play:1"], 1), (["buy:0", "sell:3"], 1),
                           (["buy:0", "sell:0"], 1)):
            st, ge = h.game(seed, moves)
            _, gp = h.game(seed, moves[:idx])
            err = ge.get("error") or {}
            c.eq(f"reject {moves} code", (st, err.get("code"), err.get("index"), ge.get("movesApplied")),
                 (400, "illegal_move", idx, idx))
            c.eq(f"reject {moves} state", ge.get("players"), gp.get("players"))

        # privacy: after seat 0 ends with a held card, seat 1 sees only handCount
        st, gq = h.game(seed, ["buy:0", "end"])
        if st == 200 and gq.get("player") == 1:
            q0 = gq["players"][0]
            c.eq("other seat hand hidden", q0["hand"], None)
            c.eq("other seat handCount public", q0["handCount"], 1)
            c.eq("other seat gold hidden", q0["gold"], None)
        else:
            c.bad.append(f"privacy setup: end did not pass to seat 1 (status {st})")

    if c.bad:
        print(f"FAIL http ({len(c.bad)} of {c.ok + len(c.bad)} checks), seed {seed}:")
        for b in c.bad[:40]:
            print("  " + b)
        return False
    print(f"PASS http: {c.ok} checks against {base} (44 card rows, zone flows seed {seed}, atomicity, privacy)")
    return True


def main():
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--verdict", action="store_true", help="also recheck the laws with the Lean-proven kernel")
    ap.add_argument("--url", default=os.environ.get("BG_URL"), help="server base URL (default: $BG_URL)")
    ap.add_argument("--no-fixtures", action="store_true", help="skip the Bend run (HTTP lane only)")
    a = ap.parse_args()
    ok = True
    if not a.no_fixtures:
        ok = lane_fixtures() and ok
    if a.verdict:
        ok = lane_verdict() and ok
    if a.url:
        ok = lane_http(a.url) and ok
    else:
        print("SKIP http: set BG_URL (or --url) to a fresh protocol-3 server")
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
