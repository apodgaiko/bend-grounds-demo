#!/usr/bin/env python3
"""Real-surface API tests for the Bend Grounds server.

Every assertion here goes through actual HTTP requests to the native Bend
server (build/server). Nothing is mocked; Python never computes rules.

  python3 tests/api_test.py            # uses BG_URL or http://127.0.0.1:8765
                                       # and starts build/server if not up

Protocol 3 (V4): bought units go to a private hand (max 7), `play:i`
deploys them to the board (max 5); only board units can be sold (`sell:i`,
the engine reports the total refund as `sellGold`); three regular copies of a
card merge into a golden one. Protocol-3 regression categories:
(a) no hand sale, (b) golden Mon field, (c) 40 HP, (d) protocol 3,
(e) neutral roster / filtered shop pool, (f) golden behaviour. Expected
values changed only for one of these; each edit names its cause. Card-effect specifics (each ability's
exact numbers) are tested by the effects lane; this suite asserts zone
conservation, capacity, atomic rejection, privacy, legalActions exactness,
replay, versioning, termination and the client CLI. Where an ability could
change a number (MAKE refills the hand on play, GOLD adds to a sell refund),
the exact value is asserted only for units whose `abilities` list is empty.
"""
import json
import os
import subprocess
import sys
import time
import unittest
import urllib.error
import urllib.request

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.join(ROOT, "scripts"))
import agent  # noqa: E402  (HTTP client only)

# Leak markers ("Exception ignored ...", "Exception in thread ...", default-format
# ResourceWarning) in a Python child's captured stderr fail the test whatever the
# child's exit code, checked before the existing rc/content assertions. Helper:
# the gate's scripts/child_stderr.py (existing scripts/ import convention).
if os.path.join(ROOT, 'scripts') not in sys.path:
    sys.path.insert(0, os.path.join(ROOT, 'scripts'))
from child_stderr import problems as child_stderr_problems  # noqa: E402


def assert_child_stderr_clean(stderr, what):
    """AssertionError naming the marker lines if a Python child's stderr shows a leak."""
    lines = child_stderr_problems(stderr or '')
    if lines:
        raise AssertionError(f'{what}: leak marker(s) in child stderr:\n' + '\n'.join(lines))


URL = os.environ.get("BG_URL", "http://127.0.0.1:8765")
CLI = os.environ.get("BG_CLI")  # offline mode: native Bend replay binary instead of HTTP
C = agent.make_client(URL, CLI)
http_only = unittest.skipIf(CLI, "HTTP-only (routing/static/URL decoding); BG_CLI transport")
_proc = None


def up():
    try:
        st, _ = C.health()
        return st == 200
    except (urllib.error.URLError, ConnectionError, OSError):
        return False


def setUpModule():
    global _proc
    if CLI or up():
        return
    binary = os.path.join(ROOT, "build", "server")
    if not os.path.exists(binary):
        raise unittest.SkipTest("server not running and build/server missing; run scripts/build.sh")
    log = open(os.path.join(ROOT, "evidence", "api_test_server.log"), "w")
    _proc = subprocess.Popen([binary], cwd=ROOT, stdout=log, stderr=subprocess.STDOUT)
    for _ in range(100):
        if up():
            return
        time.sleep(0.1)
    raise RuntimeError("server did not come up")


def tearDownModule():
    if _proc:
        _proc.terminate()
        _proc.wait(5)


def game(seed=42, moves=(), mode=None):
    st, body = C.game(seed, list(moves), mode)
    return st, body


def ok(tc, seed=42, moves=(), mode=None):
    st, body = game(seed, moves, mode)
    tc.assertEqual(st, 200, body)
    tc.assertIsInstance(body, dict, body)
    tc.assertIn(body.get("error"), (None, "", False), body)
    return body


def hero(obs):
    return agent.me(obs)


def find(obs, k):
    return [a for a in obs["legalActions"] if agent.kind(a) == k]


ERROR_CODES = {"bad_move", "illegal_move", "bad_request", "too_many_moves", "game_over",
               "unsupported_version"}
_RULES = []


def rules():
    if not _RULES:
        st, r = C.rules()
        assert st == 200, r
        _RULES.append(r)
    return _RULES[0]


def hand(obs):
    return hero(obs).get("hand")


def abilities(u):
    """Ability list of a unit: from the unit JSON, else from /api/rules by name."""
    if isinstance(u.get("abilities"), list):
        return u["abilities"]
    for c in rules()["cards"]:
        if c["name"] == u["name"]:
            return c.get("abilities") or []
    raise AssertionError(f"unknown card {u}")


# Tier economy (protocol 2, final): upgrading TO tier t has base cost BASE[t];
# the cost drops by 1 each round you wait but never below FLOOR[t].
MAX_ROUNDS, MAX_TIER = 14, 5
UPGRADE_BASE = {2: 5, 3: 8, 4: 11, 5: 13}
UPGRADE_FLOOR = {2: 3, 3: 5, 4: 8, 5: 10}


def expected_upcost(target, rounds_waited):
    return max(UPGRADE_FLOOR[target], UPGRADE_BASE[target] - rounds_waited)


def vanilla(u):
    return not abilities(u)


def stats(u):
    return (u["name"], u["attack"], u["health"])


def same_state(tc, b, o):
    for k in ("players", "round", "player", "phase", "legalActions"):
        tc.assertEqual(b.get(k), o.get(k), k)


def rejected(tc, seed, prefix, bad, mode=None, codes=("illegal_move",)):
    """bad appended to an accepted prefix: 400, error at that index, and the
    returned state is exactly the prefix state (no partial charge/effect)."""
    o = ok(tc, seed, prefix, mode)
    st, b = game(seed, list(prefix) + [bad, "end"], mode)
    e = err(tc, st, b, set(codes))
    tc.assertEqual(e.get("index"), len(prefix), e)
    tc.assertEqual(e.get("move"), bad, e)
    tc.assertEqual(b.get("movesApplied"), len(prefix))
    same_state(tc, b, o)
    return o


def drive(tc, seed, choose, done, mode="manual", limit=600):
    """Manual-mode scenario driver: seat 0 follows choose(obs) (a legal action),
    every other seat sends 'end'. Stops at the first state where done(obs) holds
    with seat 0 to act. Only server-provided legal actions are sent."""
    moves, o = [], ok(tc, seed, [], mode)
    while len(moves) < limit:
        tc.assertNotEqual(o["phase"], "finished", "scenario game ended before its goal")
        if o["player"] == 0 and done(o):
            return moves, o
        a = choose(o) if o["player"] == 0 else "end"
        tc.assertIn(a, o["legalActions"])
        moves.append(a)
        o = ok(tc, seed, moves, mode)
    tc.fail("scenario not reached")


def first_of(o, *kinds):
    for k in kinds:
        acts = find(o, k)
        if acts:
            return acts[0]
    return "end"


def check_zones(tc, o):
    """Capacity and visibility invariants of one observation."""
    viewer = o["player"]
    for p in o["players"]:
        tc.assertLessEqual(len(p["board"]), 5, p)
        tc.assertIsInstance(p.get("handCount"), int, p)
        tc.assertTrue(0 <= p["handCount"] <= 7, p)
        if p["id"] == viewer and o["phase"] != "finished":
            tc.assertIsInstance(p.get("hand"), list, p)
            tc.assertEqual(len(p["hand"]), p["handCount"], p)
        elif p["id"] != viewer:
            tc.assertIsNone(p.get("hand"), f"hand of seat {p['id']} leaked to seat {viewer}")


def err(tc, st, b, codes=ERROR_CODES):
    """Assert a structured error: HTTP 400 + error{code,message,...}."""
    tc.assertEqual(st, 400, b)
    tc.assertIsInstance(b, dict, b)
    e = b.get("error")
    tc.assertIsInstance(e, dict, b)
    tc.assertIn(e.get("code"), codes, e)
    tc.assertTrue(e.get("message"), e)
    return e


def request_err(tc, st, b, codes):
    """Request-level errors (bad seed/mode, over-cap transcript) are
    error-only: no game state is replayed or returned."""
    e = err(tc, st, b, codes)
    tc.assertIsNone(b.get("players"), "request-level error must not carry a game state")
    tc.assertIsNone(b.get("legalActions"), "request-level error must not carry a game state")
    return e


def max_moves():
    st, r = C.rules()
    return r["costs"]["maxMoves"]


def end_moves(tc, seed, n, mode=None):
    """Transcript of n 'end' moves and the resulting observation."""
    moves, o = [], ok(tc, seed, [], mode)
    for _ in range(n):
        moves.append("end")
        o = ok(tc, seed, moves, mode)
    return moves, o


def names(shop):
    return [u and u.get("name") for u in (shop or [])]


def versioned(tc, body, what):
    tc.assertEqual(body.get("schemaVersion"), 3, what)    # cause (d)
    tc.assertEqual(body.get("protocolVersion"), 3, what)


class Surface(unittest.TestCase):
    def test_health(self):
        st, body = C.health()
        self.assertEqual(st, 200, body)

    @http_only
    def test_health_versioned(self):
        versioned(self, C.health()[1], "/api/health")

    def test_protocol_version_everywhere(self):
        versioned(self, rules(), "/api/rules")
        versioned(self, ok(self), "initial game")
        versioned(self, ok(self, 42, ["buy:0", "play:0", "end"]), "mid game")
        st, b = game(42, ["buy:0", "buy:9"])
        err(self, st, b, {"illegal_move"})
        versioned(self, b, "move-level error state")
        self.assertEqual(agent.server_protocol(C), agent.PROTOCOL)

    @http_only
    def test_unsupported_version_rejected(self):
        # Transport details are tested in tests/protocol_v3_test.py.
        # cause (d): only v=3; the V3 release protocol 2 is refused like any other
        st, b = C.get("/api/game", {"seed": "42", "v": "3", "moves": "buy:0"})
        self.assertEqual(st, 200, b)
        st2, b2 = C.get("/api/game", {"seed": "42", "moves": "buy:0"})
        self.assertEqual((st2, b2), (st, b), "omitting v must equal v=3")
        for v in ("1", "2", "4", "0", "03", "three"):
            st, b = C.get("/api/game", {"seed": "42", "v": v, "moves": "buy:0"})
            request_err(self, st, b, {"unsupported_version"})
        # the version check comes first: a v1 client learns that before a bad seed
        st, b = C.get("/api/game", {"seed": "abc", "v": "1", "moves": ""})
        request_err(self, st, b, {"unsupported_version"})

    def test_rules_machine_readable(self):
        r = rules()
        self.assertIsInstance(r, dict)
        text = json.dumps(r).lower()
        for word in ("buy", "play", "sell", "swap", "roll", "freeze", "upgrade", "invest",
                     "end", "auto", "hand", "golden"):
            self.assertIn(word, text)
        costs = r["costs"]
        self.assertEqual((costs["buy"], costs["boardMax"], costs["handMax"], costs["sellRefund"],
                          costs["play"], costs["shopSize"]), (3, 5, 7, 1, 0, 3))
        self.assertEqual(costs["startHp"], 40)                       # cause (c)
        self.assertNotIn("sellHandRefund", costs)                     # cause (a)
        self.assertNotIn("sellhand", json.dumps(r["actions"]).lower())  # cause (a)
        for a in ("play:i", "sell:i"):
            self.assertTrue(any(a in line for line in r["actions"]), r["actions"])

    # Named card fixtures cover ids 0..23; ids 24..35 add tiers 4 and 5.
    V2_FIRST_24 = ["Spark Imp", "Cinder Whelp", "Kindler", "Purse Moth", "Tide Pup", "Shell Scout",
                   "Pebble Guard", "Moss Turtle", "Root Sprout", "Ember Herald", "Flame Dancer",
                   "Blaze Charger", "Reef Warden", "Tidecaller", "Coin Eel", "Boulder Ox", "Cairn Mason",
                   "Rootwarden", "Inferno Drake", "Ash Phoenix", "Storm Siren", "Tide Oracle",
                   "Granite Titan", "Mountain Heart"]

    NEUTRAL_IDS = list(range(36, 44))   # Neutral card ids, category (e)

    def test_roster_three_tribes_five_tiers(self):
        r = rules()
        cards = r["cards"]
        self.assertEqual(r["costs"]["maxTier"], MAX_TIER)
        self.assertEqual(r["maxRounds"], MAX_ROUNDS)
        # upgradeCosts / upgradeFloors: keyed by the CURRENT tier 1..4, values for
        # the upgrade to the next tier (no entry for tier 5)
        self.assertEqual(r["upgradeCosts"], {str(t - 1): c for t, c in UPGRADE_BASE.items()})
        self.assertEqual(r["upgradeFloors"], {str(t - 1): c for t, c in UPGRADE_FLOOR.items()})
        self.assertEqual(len(cards), 44)                                # cause (e)
        self.assertEqual(sorted(c["id"] for c in cards), list(range(len(cards))))
        self.assertEqual(r["tribes"], ["Ember", "Tide", "Stone", "Neutral"])
        self.assertEqual(len({c["name"] for c in cards}), len(cards), "card names must be unique")
        by_id = {c["id"]: c for c in cards}
        self.assertEqual([by_id[i]["name"] for i in range(24)], self.V2_FIRST_24, "ids 0..23 must keep their cards")
        self.assertEqual(sorted({c["tier"] for c in cards}), list(range(1, MAX_TIER + 1)))
        for tribe in ("Ember", "Tide", "Stone"):
            mine = [c for c in cards if c["tribe"] == tribe]
            self.assertEqual(sorted(c["tier"] for c in mine), [1, 1, 1, 2, 2, 2, 3, 3, 4, 4, 5, 5], tribe)
        neutral = [c for c in cards if c["tribe"] == "Neutral"]
        self.assertEqual(sorted(c["id"] for c in neutral), self.NEUTRAL_IDS)
        self.assertEqual(sorted(c["tier"] for c in neutral), [1, 1, 2, 2, 3, 3, 4, 5])
        for c in cards:
            for k in ("name", "attack", "health", "tier", "tribe", "text", "keywords", "abilities",
                      "armor", "rally", "income"):
                self.assertIn(k, c, c)
            self.assertIsInstance(c["keywords"], list, c)
            self.assertIsInstance(c["abilities"], list, c)
            self.assertLessEqual(len(c["abilities"]), 2, c)
            self.assertTrue(c["text"].strip() or not (c["keywords"] or c["abilities"]), c)
        # cause (e): ids 0..35 keep their tier-sorted order; the appended neutrals
        # span tiers 1..5, so a tier-t shop pool is no longer an id prefix
        # The engine provides authoritative shop eligibility.
        self.assertEqual([by_id[i]["tier"] for i in range(36)], sorted(by_id[i]["tier"] for i in range(36)))
        self.assertNotEqual([by_id[i]["tier"] for i in range(44)], sorted(c["tier"] for c in cards))

    @http_only
    def test_web_root_served(self):
        with urllib.request.urlopen(URL + "/", timeout=10) as r:
            self.assertEqual(r.status, 200)
            self.assertIn("<html", r.read().decode("utf-8", "replace").lower())

    @http_only
    def test_unknown_route_404(self):
        for path in ("/api/nope", "/api/game/extra"):
            st, _ = C.get(path)
            self.assertEqual(st, 404, path)

    @http_only
    def test_url_encoded_moves(self):
        a = ok(self, 42, ["buy:0", "play:0", "end"])
        st, b = C.get("/api/game?seed=42&v=3&moves=buy%3A0%2Cplay%3A0%2Cend")  # cause (d)
        self.assertEqual(st, 200, b)
        self.assertEqual(a, b)


class Observation(unittest.TestCase):
    def test_initial_state_shape(self):
        o = ok(self)
        self.assertEqual(o["phase"], "recruit")
        self.assertEqual(o["round"], 1)
        self.assertEqual(o.get("maxRounds"), MAX_ROUNDS)
        self.assertEqual(o.get("maxRounds"), rules()["maxRounds"])
        self.assertEqual(o["player"], 0)
        self.assertEqual(o.get("movesApplied"), 0)
        self.assertEqual(len(o["players"]), 4)
        self.assertTrue(all(p["hp"] == 40 for p in o["players"]))   # cause (c)
        self.assertIn("end", o["legalActions"])
        self.assertIsNone(o.get("winner"))
        self.assertIsNone(o.get("rank"))
        self.assertEqual(len(hero(o)["shop"]), 3)
        self.assertEqual(hand(o), [])
        self.assertEqual(hero(o)["board"], [])
        for p in o["players"]:
            self.assertEqual(p["handCount"], 0)
            self.assertEqual(p.get("plays"), 0)
        check_zones(self, o)

    def test_scouting_privacy(self):
        # check at several points, including mid-game with populated boards
        for moves in ([], ["auto"], ["auto", "auto", "auto"]):
            o = ok(self, 9, moves)
            if o["phase"] == "finished":
                continue
            me_id = o["player"]
            opp = o.get("nextOpponent")
            self.assertIsInstance(opp, int)
            self.assertNotEqual(opp, me_id)
            for p in o["players"]:
                for k in ("hp", "tier", "board", "investment", "handCount"):
                    self.assertIn(k, p)  # public scouting info
                if p["id"] != me_id:
                    self.assertIsNone(p.get("shop"), f"opponent shop leaked: {p}")
                    self.assertIsNone(p.get("gold"), f"opponent gold leaked: {p}")
                    self.assertIsNone(p.get("hand"), f"opponent hand leaked: {p}")
            check_zones(self, o)
            self.assertIsNotNone(hero(o).get("shop"))
            self.assertIsInstance(hero(o).get("gold"), int)
            blob = json.dumps(o).lower()
            for k in ('"rng"', '"rngstate"', '"deck"', '"pool"'):
                self.assertNotIn(k, blob, "private RNG/pool state exposed")

    def test_manual_privacy_follows_seat(self):
        o = ok(self, 9, ["end"], "manual")
        self.assertEqual(o["player"], 1)
        self.assertIsNotNone(o["players"][1].get("shop"))
        self.assertIsNone(o["players"][0].get("shop"))

    def test_held_hand_is_private_but_counted(self):
        # seat 0 buys and holds a unit; seat 1 then sees only its count
        mine = ok(self, 9, ["buy:0"], "manual")
        held = hand(mine)
        self.assertEqual(len(held), 1)
        o = ok(self, 9, ["buy:0", "end"], "manual")
        self.assertEqual(o["player"], 1)
        p0 = o["players"][0]
        self.assertIsNone(p0.get("hand"))
        self.assertEqual(p0["handCount"], 1)
        self.assertEqual(p0["board"], [], "a held unit must not appear on the public board")
        self.assertEqual(hand(o), [])
        check_zones(self, o)
        # combat reports show boards only; a unit that never left the hand never fights
        fin = ok(self, 9, ["buy:0"] + ["end"] * 4, "manual")
        for c in fin.get("combat") or []:
            if 0 in (c["a"], c["b"]):
                self.assertEqual(c["aBoard" if c["a"] == 0 else "bBoard"], [])

    def test_bot_hands_hidden_in_bots_mode(self):
        for moves in (["auto"], ["auto"] * 3, ["auto"] * 5):
            o = ok(self, 14, moves)
            if o["phase"] != "finished":
                check_zones(self, o)


class Determinism(unittest.TestCase):
    def test_same_transcript_same_state(self):
        moves, o = [], ok(self, 7)
        for _ in range(4):
            moves.append(o["legalActions"][0])
            o = ok(self, 7, moves)
        self.assertEqual(o, ok(self, 7, moves))
        self.assertEqual(o["movesApplied"], len(moves))

    def test_full_game_replay_identical(self):
        moves, fin = agent.play(C, 11, {0: agent.policy_tempo})
        st, again = game(11, moves)
        self.assertEqual(st, 200)
        self.assertEqual(agent.state_hash(fin), agent.state_hash(again))

    def test_seed_changes_shop(self):
        shops = {json.dumps(names(hero(ok(self, s))["shop"])) for s in range(1, 9)}
        self.assertGreater(len(shops), 1, "seed has no effect on shops")

    def test_prefix_consistency(self):
        # observation after a prefix never depends on later moves (replay is causal)
        moves, fin = agent.play(C, 13, {0: agent.policy_econ})
        k = len(moves) // 2
        st, pre = game(13, moves[:k])
        self.assertEqual(st, 200)
        self.assertEqual(pre["movesApplied"], k)


class Errors(unittest.TestCase):
    def test_unknown_action(self):
        e = err(self, *game(42, ["fly"]))
        self.assertEqual(e.get("index"), 0)
        self.assertEqual(e.get("move"), "fly")

    def test_out_of_range_buy(self):
        err(self, *game(42, ["buy:9"]))

    def test_sell_empty_board(self):
        err(self, *game(42, ["sell:0"]))

    def test_malformed_seed(self):
        for seed in ("abc", "-1", "", "4294967296"):
            st, b = C.get("/api/game", {"seed": seed, "moves": ""})
            request_err(self, st, b, {"bad_request"})

    def test_bad_mode(self):
        st, b = C.get("/api/game", {"seed": "1", "mode": "chaos", "moves": ""})
        request_err(self, st, b, {"bad_request"})

    def test_malformed_move_syntax(self):
        for bad in ["buy:", "buy:x", "swap:0", ":::", "BUY:0", "buy:0:1"]:
            err(self, *game(42, [bad]))

    def test_error_returns_prior_state_unmutated(self):
        o = ok(self, 42, ["buy:0"])
        st, b = game(42, ["buy:0", "buy:9", "end"])
        e = err(self, st, b)
        self.assertEqual(e.get("index"), 1)
        self.assertEqual(b.get("movesApplied"), 1)
        for k in ("players", "round", "legalActions"):
            self.assertEqual(b.get(k), o.get(k), k)

    def test_moves_after_finish_rejected(self):
        moves, o = end_moves(self, 3, 0)
        while o["phase"] != "finished":
            moves.append("end")
            o = ok(self, 3, moves)
        self.assertEqual(o["legalActions"], [])
        err(self, *game(3, moves + ["end"]), {"game_over"})

    def test_overspend_rejected(self):
        # round 1 gold is 3 = one unit; a second buy must be illegal
        o = ok(self, 42, ["buy:0"])
        self.assertLess(hero(o)["gold"], 3)
        self.assertFalse(find(o, "buy"), o["legalActions"])
        err(self, *game(42, ["buy:0", "buy:0"]), {"illegal_move"})

    def test_replay_cap_boundary(self):
        # The cap is protocol-level: free actions (freeze/swap) are always legal,
        # so only the transcript bound keeps replay finite. Read it from /api/rules.
        cap = max_moves()
        self.assertEqual(cap, 1024)
        base = ["roll", "roll", "roll"]           # spend round-1 gold; freeze stays legal
        at = base + ["freeze"] * (cap - len(base))
        o = ok(self, 42, at)                       # exactly cap moves: accepted
        self.assertEqual(o["movesApplied"], cap)
        st, b = game(42, at + ["freeze"])          # cap + 1: error-only
        e = request_err(self, st, b, {"too_many_moves"})
        st, b = game(42, base + ["freeze"] * 2000)  # far over the cap
        request_err(self, st, b, {"too_many_moves"})
        self.assertTrue(up(), "server died on oversized transcript")

    def test_bots_mode_cannot_act_as_other_seats(self):
        o = ok(self, 42, ["end"])
        self.assertEqual(o["player"], 0)


class Zones(unittest.TestCase):
    """Hand (private, max 7) vs board (public, max 5)."""

    def test_play_moves_hand_unit_to_board(self):
        exact = 0
        for seed in range(1, 13):
            for i in range(3):
                o = ok(self, seed, [f"buy:{i}"])
                u = hand(o)[0]
                self.assertIn("play:0", o["legalActions"])
                o2 = ok(self, seed, [f"buy:{i}", "play:0"])
                h, b = hero(o), hero(o2)
                self.assertEqual([x["name"] for x in b["board"]], [u["name"]])
                self.assertEqual(b["plays"], h["plays"] + 1)
                self.assertEqual(names(b["shop"]), names(h["shop"]), "play must not touch the shop")
                self.assertGreaterEqual(b["gold"], h["gold"], "play is free")
                self.assertIn(len(hand(o2)), (0, 1), "play removes the unit; a Make ability adds at most one")
                if vanilla(u):
                    self.assertEqual(hand(o2), [])
                    self.assertEqual(b["gold"], h["gold"])
                    self.assertEqual(stats(b["board"][0]), stats(u))
                    exact += 1
        self.assertGreater(exact, 0)

    def test_play_selects_index_and_keeps_order(self):
        pre = ["end", "end", "end", "buy:0", "buy:0"]   # round 4: 6 gold, two units in hand
        o = ok(self, 4, pre)
        held = hand(o)
        self.assertEqual(len(held), 2)
        o2 = ok(self, 4, pre + ["play:1"])
        self.assertEqual(hero(o2)["board"][-1]["name"], held[1]["name"])
        self.assertEqual(hand(o2)[0]["name"], held[0]["name"], "unplayed hand units keep their order")
        o3 = ok(self, 4, pre + ["play:1", "play:0"])
        self.assertEqual([x["name"] for x in hero(o3)["board"]], [held[1]["name"], held[0]["name"]])

    def test_hand_units_cannot_be_sold(self):
        # cause (a): selling is board-only; the hand-sale command no longer parses
        o = rejected(self, 42, ["buy:0"], "sell:0")       # the unit is in hand, board is empty
        self.assertNotIn("sell:0", o["legalActions"])
        self.assertFalse([a for a in o["legalActions"] if a.startswith("sellhand")])
        for i in (0, 1, 6):
            rejected(self, 42, ["buy:0"], f"sellhand:{i}", codes=("bad_move",))
        on_board = ok(self, 42, ["buy:0", "play:0"])
        self.assertIn("sell:0", on_board["legalActions"])

    def test_board_sell_gold_equals_reported_sellGold(self):
        # V3 had a flat +1 hand sale here (cause a). V4: a board sale pays the
        # base refund 1 plus its Sell gold; the engine reports the total as
        # `sellGold` on each board unit, and the gold change must equal it.
        seen, exact = set(), 0
        for seed in range(1, 25):
            for i in range(3):
                pre = [f"buy:{i}", "play:0"]
                o = ok(self, seed, pre)
                u = hero(o)["board"][0]
                self.assertIsInstance(u.get("sellGold"), int, u)
                self.assertGreaterEqual(u["sellGold"], 1, u)
                self.assertIs(u.get("golden"), False, u)
                o2 = ok(self, seed, pre + ["sell:0"])
                self.assertEqual(hero(o2)["gold"], hero(o)["gold"] + u["sellGold"], u)
                self.assertEqual(hero(o2)["board"], [])
                if vanilla(u):
                    self.assertEqual(u["sellGold"], 1, u)
                    self.assertEqual(hand(o2), hand(o))
                    exact += 1
                seen.add((u["name"], u["sellGold"]))
        self.assertGreater(exact, 0)
        self.assertTrue(any(g > 1 for _, g in seen), f"no Sell-gold card sampled: {sorted(seen)}")

    def test_hand_cap_7_blocks_buy_atomically(self):
        # seat 0 buys but never plays; everyone else ends (empty boards draw)
        def full(o):
            return len(hand(o)) == 7 and hero(o)["gold"] >= 3 and hero(o)["shop"]
        moves, o = drive(self, 12, lambda o: first_of(o, "buy"), full)
        self.assertEqual(hero(o)["handCount"], 7)
        self.assertFalse(find(o, "buy"), "buy listed with a full hand")
        self.assertIn("roll", o["legalActions"])
        rejected(self, 12, moves, "buy:0", "manual")
        # cause (a): the slot is freed by deploying an ability-free unit (V3 sold it from the hand)
        k = next((j for j, u in enumerate(hand(o)) if vanilla(u)), None)
        self.assertIsNotNone(k, "no ability-free unit in the full hand")
        self.assertIn(f"play:{k}", o["legalActions"])
        o2 = ok(self, 12, moves + [f"play:{k}"], "manual")
        self.assertEqual(len(hand(o2)), 6)
        self.assertTrue(find(o2, "buy"))
        o3 = ok(self, 12, moves + [f"play:{k}", "buy:0"], "manual")
        # cause (f): a third regular copy merges (3 -> 1 golden in the hand)
        cid = hero(o2)["shop"][0]["id"]
        copies = sum(1 for u in hand(o2) + hero(o2)["board"] if u["id"] == cid and not u["golden"])
        self.assertEqual(len(hand(o3)), 7 if copies < 2 else 7 - 2, (cid, copies))

    def _full_board(self, seed=12):
        # seat 0 plays whenever it can, else buys; stops with a full board and a unit in hand
        def done(o):
            return len(hero(o)["board"]) == 5 and len(hand(o)) >= 1
        return drive(self, seed, lambda o: first_of(o, "play", "buy"), done)

    def test_play_full_board_rejected_atomically(self):
        moves, o = self._full_board()
        self.assertFalse(find(o, "play"), "play listed with a full board")
        rejected(self, 12, moves, "play:0", "manual")
        o2 = ok(self, 12, moves + ["sell:0"], "manual")
        self.assertEqual(len(hero(o2)["board"]), 4)
        self.assertIn("play:0", o2["legalActions"])
        o3 = ok(self, 12, moves + ["sell:0", "play:0"], "manual")
        self.assertEqual(len(hero(o3)["board"]), 5)
        self.assertEqual(hero(o3)["board"][-1]["name"], hand(o2)[0]["name"])

    def test_buy_with_full_board_succeeds(self):
        def done(o):
            return len(hero(o)["board"]) == 5 and hero(o)["gold"] >= 3 and hero(o)["shop"] and len(hand(o)) < 7
        moves, o = drive(self, 12, lambda o: first_of(o, "play", "buy"), done)
        self.assertTrue(find(o, "buy"))
        o2 = ok(self, 12, moves + ["buy:0"], "manual")
        self.assertEqual(hero(o2)["board"], hero(o)["board"])
        self.assertEqual(len(hand(o2)), len(hand(o)) + 1)
        self.assertEqual(hero(o2)["gold"], hero(o)["gold"] - 3)

    def test_hand_persists_across_rounds(self):
        o = ok(self, 42, ["buy:0", "end"])
        self.assertEqual(o["round"], 2)
        self.assertEqual([stats(u) for u in hand(o)], [stats(u) for u in hand(ok(self, 42, ["buy:0"]))])
        self.assertEqual(hero(o)["plays"], 0, "plays resets each round")

    def test_rejections_are_atomic(self):
        cases = [
            ([], "play:0"), (["buy:0"], "play:1"), (["buy:0"], "sell:0"),
            (["buy:0"], "sell:5"), (["buy:0"], "buy:0"), (["buy:0"], "buy:2"), ([], "buy:3"),
            (["end", "buy:0", "play:0"], "sell:1"), (["end", "buy:0", "play:0"], "swap:0:1"),
        ]
        for prefix, bad in cases:
            with self.subTest(prefix=prefix, bad=bad):
                rejected(self, 42, prefix, bad)
        # cause (a): former hand-sale moves are now unparseable (bad_move), still atomic
        for prefix, bad in (([], "sellhand:0"), (["buy:0"], "sellhand:0"), (["buy:0"], "sellhand:7")):
            with self.subTest(prefix=prefix, bad=bad):
                rejected(self, 42, prefix, bad, codes=("bad_move",))

    def test_malformed_zone_moves(self):
        for bad in ["play", "play:", "play:x", "play:-1", "play:0:1", "sellhand", "sellhand:",
                    "sellhand:0", "sellhand:0:0", "PLAY:0", "hand:0", "sell_hand:0", "discard:0"]:
            with self.subTest(bad=bad):
                rejected(self, 42, ["buy:0"], bad, codes=("bad_move",))


def candidates():
    acts = [f"buy:{i}" for i in range(4)] + [f"play:{i}" for i in range(8)]
    acts += [f"sell:{i}" for i in range(6)]   # cause (a): sellhand:i is not a move form any more
    acts += [f"swap:{i}:{j}" for i in range(6) for j in range(6)]
    return acts + ["roll", "freeze", "upgrade", "invest", "end", "auto"]


class LegalActions(unittest.TestCase):
    """legalActions is exact: every listed action is accepted, and every
    well-formed unlisted action is rejected as illegal_move. Swaps are listed
    canonically (i < j); swap:j:i is the same move and is accepted iff
    swap:i:j is listed."""

    def check_state(self, seed, prefix, mode=None):
        o = ok(self, seed, prefix, mode)
        legal = o["legalActions"]
        universe = set(candidates())
        self.assertEqual(len(legal), len(set(legal)), "duplicate legal actions")
        for a in legal:
            self.assertIn(a, universe, f"unexpected action form {a!r}")
            st, b = game(seed, list(prefix) + [a], mode)
            self.assertEqual(st, 200, (a, b))
        for a in universe - set(legal):
            st, b = game(seed, list(prefix) + [a], mode)
            if a.startswith("swap:"):
                _, i, j = a.split(":")
                if f"swap:{j}:{i}" in legal:
                    self.assertEqual(st, 200, (a, b))
                    continue
            err(self, st, b, {"illegal_move"})
        return o

    def test_exact_at_varied_states(self):
        self.check_state(42, [])
        self.check_state(42, ["buy:0"])
        self.check_state(42, ["end", "buy:0", "play:0"])
        self.check_state(4, ["end", "end", "end", "buy:0", "buy:0", "play:0", "play:0"])
        self.check_state(9, ["buy:0", "end"], "manual")
        moves, _ = agent.play(C, 17, {0: agent.policy_tempo})
        for k in (len(moves) // 3, (2 * len(moves)) // 3):
            o = ok(self, 17, moves[:k])
            if o["phase"] != "finished":
                self.check_state(17, moves[:k])

    def test_full_hand_and_full_board_listings(self):
        moves, o = drive(self, 12, lambda o: first_of(o, "play", "buy"),
                         lambda o: len(hero(o)["board"]) == 5 and len(hand(o)) >= 1)
        self.check_state(12, moves, "manual")


class Economy(unittest.TestCase):
    def test_buy_costs_3_and_fills_hand_not_board(self):
        # v1 put the unit on the board; v2 moves exactly that shop slot into the hand.
        o = ok(self)
        g = hero(o)["gold"]
        shop = hero(o)["shop"]
        for i in range(3):
            o2 = ok(self, 42, [f"buy:{i}"])
            self.assertEqual(hero(o2)["gold"], g - 3)
            self.assertEqual(hero(o2)["board"], hero(o)["board"], "buy must not touch the board")
            self.assertEqual([stats(u) for u in hand(o2)], [stats(shop[i])])
            self.assertEqual(names(hero(o2)["shop"]), names(shop[:i] + shop[i + 1:]))
            self.assertEqual(hero(o2)["handCount"], 1)
            self.assertEqual(hero(o2)["plays"], 0)

    def test_roll_costs_1(self):
        o = ok(self)
        o2 = ok(self, 42, ["roll"])
        self.assertEqual(hero(o2)["gold"], hero(o)["gold"] - 1)

    def test_sell_refunds_1(self):
        # round 2 (4 gold): buy (->1), play (free), sell (->2, more only via a Sell ability)
        exact = 0
        for seed in range(40, 52):
            pre = ["end", "buy:0", "play:0"]
            o = ok(self, seed, pre)
            u = hero(o)["board"][-1]
            o2 = ok(self, seed, pre + ["sell:0"])
            gain = hero(o2)["gold"] - hero(o)["gold"]
            self.assertGreaterEqual(gain, 1)
            if vanilla(u):
                self.assertEqual(gain, 1, u)
                exact += 1
            self.assertEqual(len(hero(o2)["board"]), len(hero(o)["board"]) - 1)
            if vanilla(u):  # a Sell ability may add a card (Pearl Broker); a plain unit may not
                self.assertEqual(hand(o2), hand(o), "sell:i must not touch the hand")
        self.assertGreater(exact, 0, "no ability-free unit sampled; exact refund untested")

    def test_income_schedule_without_investment(self):
        for r in range(1, 9):
            _, o = end_moves(self, 4, r - 1)
            if o["phase"] == "finished":
                break
            self.assertEqual(o["round"], r)
            # empty board -> no Purse Moth bonus; gold does not carry over
            self.assertEqual(hero(o)["gold"], min(2 + r, 10), f"round {r}")

    def test_invest_trades_now_for_later(self):
        base = ok(self, 4, ["end"])
        o = ok(self, 4, ["invest"])
        self.assertEqual(hero(o)["gold"], 3 - 2)
        self.assertEqual(hero(o)["investment"], 1)
        later = ok(self, 4, ["invest", "end"])
        self.assertEqual(hero(later)["gold"], hero(base)["gold"] + 1)
        # payback continues: by round 4 investment has returned its cost
        a = ok(self, 4, ["invest", "end", "end", "end"])
        b = ok(self, 4, ["end", "end", "end"])
        self.assertEqual(hero(a)["gold"], hero(b)["gold"] + 1)

    def test_investment_capped_at_3(self):
        moves, o = [], ok(self, 4)
        for _ in range(12):
            if o["phase"] == "finished":
                break
            if "invest" in o["legalActions"]:
                moves.append("invest")
            else:
                moves.append("end")
            o = ok(self, 4, moves)
            self.assertLessEqual(hero(o)["investment"], 3)
        self.assertEqual(moves.count("invest"), 3)
        if o["phase"] != "finished":
            self.assertNotIn("invest", o["legalActions"])
            err(self, *game(4, moves + ["invest"]))

    def test_upgrade_spends_upgrade_cost_and_raises_tier(self):
        moves, o = [], ok(self, 6)
        while "upgrade" not in o["legalActions"]:
            moves.append("end")
            o = ok(self, 6, moves)
            self.assertNotEqual(o["phase"], "finished", "upgrade never affordable")
        cost = hero(o)["upgradeCost"]
        o2 = ok(self, 6, moves + ["upgrade"])
        self.assertEqual(hero(o2)["gold"], hero(o)["gold"] - cost)
        self.assertEqual(hero(o2)["tier"], hero(o)["tier"] + 1)
        self.assertEqual(hero(o2)["upgradeCost"], UPGRADE_BASE[3], "next tier starts at its full base cost")

    def test_upgrade_cost_decays_to_floor_never_zero(self):
        # a tier-1 seat that only ends: 5, 4, 3, 3, ... (floor 3 for tier 2)
        moves, o = [], ok(self, 6, [], "manual")
        seen = []
        while o["phase"] != "finished" and o["round"] <= MAX_ROUNDS:
            if o["player"] == 0:
                seen.append((o["round"], hero(o)["upgradeCost"]))
            moves.append("end")
            o = ok(self, 6, moves, "manual")
        self.assertEqual(len(seen), MAX_ROUNDS, "end-only manual game must last all rounds")
        for rnd, cost in seen:
            self.assertEqual(cost, expected_upcost(2, rnd - 1), rnd)

    def test_unaffordable_upgrade_rejected_atomically(self):
        o = ok(self, 42)
        self.assertEqual((hero(o)["gold"], hero(o)["upgradeCost"]), (3, 5))
        self.assertNotIn("upgrade", o["legalActions"])
        rejected(self, 42, [], "upgrade")

    def test_upgrade_punishes_tempo_now(self):
        # round 2: 4 gold, cost 4. Upgrading spends the turn's whole budget,
        # so the buy (and roll) that were affordable are no longer legal.
        pre = ["end"]
        o = ok(self, 42, pre)
        self.assertEqual((o["round"], hero(o)["gold"], hero(o)["upgradeCost"]), (2, 4, 4))
        self.assertTrue(find(o, "buy"))
        self.assertIn("upgrade", o["legalActions"])
        o2 = ok(self, 42, pre + ["upgrade"])
        self.assertEqual((hero(o2)["tier"], hero(o2)["gold"]), (2, 0))
        self.assertFalse(find(o2, "buy"))
        self.assertNotIn("roll", o2["legalActions"])
        rejected(self, 42, pre + ["upgrade"], "buy:0")
        # and the alternative line keeps the gold for a unit instead
        o3 = ok(self, 42, pre + ["buy:0"])
        self.assertEqual((hero(o3)["tier"], hero(o3)["gold"], len(hand(o3))), (1, 1, 1))

    def _climb(self, seed, stop_tier):
        """manual: seat 0 upgrades whenever legal while tier < stop_tier, else ends;
        other seats end (empty boards draw). Returns per-round (round, tier, cost) for seat 0."""
        moves, o, log = [], ok(self, seed, [], "manual"), []
        reached = {1: 1}
        while o["phase"] != "finished":
            if o["player"] == 0:
                p = hero(o)
                t = p["tier"]
                if not log or log[-1][0] != o["round"]:
                    log.append((o["round"], t, p["upgradeCost"]))
                for x in [x for x in hero(o)["shop"] or [] if x]:
                    self.assertLessEqual(x["tier"], t, "shop offers a tier above the seat's tier")
                if t < stop_tier and "upgrade" in o["legalActions"]:
                    self.assertGreaterEqual(p["gold"], p["upgradeCost"])
                    moves.append("upgrade")
                    o2 = ok(self, seed, moves, "manual")
                    self.assertEqual(hero(o2)["tier"], t + 1)
                    self.assertEqual(hero(o2)["gold"], p["gold"] - p["upgradeCost"])
                    if t + 1 < MAX_TIER:
                        self.assertEqual(hero(o2)["upgradeCost"], UPGRADE_BASE[t + 2])
                    reached[t + 1] = o["round"]
                    o = o2
                    continue
                if t < MAX_TIER:
                    self.assertEqual("upgrade" in o["legalActions"], p["gold"] >= p["upgradeCost"], p)
            moves.append("end")
            o = ok(self, seed, moves, "manual")
        return moves, log, reached

    def test_reach_tier_5_and_costs_follow_schedule(self):
        moves, log, reached = self._climb(12, MAX_TIER)
        self.assertIn(MAX_TIER, reached, f"tier 5 never reached: {log}")
        for rnd, tier, cost in log:
            if tier >= MAX_TIER:
                self.assertIsNone(cost, "no upgrade cost at the top tier")
                continue
            # rounds_waited counts round starts since the current tier was reached
            self.assertEqual(cost, expected_upcost(tier + 1, rnd - reached[tier]), (rnd, tier, log))
        # at the top tier upgrade is never listed and is rejected atomically
        pre = moves[:max(i for i, m in enumerate(moves) if m == "upgrade") + 1]
        o = ok(self, 12, pre, "manual")
        self.assertEqual(hero(o)["tier"], MAX_TIER)
        self.assertNotIn("upgrade", o["legalActions"])
        rejected(self, 12, pre, "upgrade", "manual")

    def test_waiting_never_erases_high_tier_cost(self):
        moves, log, reached = self._climb(12, 4)
        self.assertIn(4, reached, log)
        tail = [c for rnd, t, c in log if t == 4]
        self.assertTrue(tail and min(tail) == UPGRADE_FLOOR[5], (tail, log))
        self.assertTrue(all(c >= UPGRADE_FLOOR[5] for c in tail), tail)

    def test_freeze_keeps_shop_and_toggles(self):
        o = ok(self)
        self.assertIn("freeze", o["legalActions"])
        o2 = ok(self, 42, ["freeze"])
        self.assertTrue(hero(o2)["frozen"])
        self.assertFalse(hero(ok(self, 42, ["freeze", "freeze"]))["frozen"])
        o3 = ok(self, 42, ["freeze", "end"])
        self.assertEqual(names(hero(o3)["shop"]), names(hero(o)["shop"]))
        # control: without freeze the shop refreshes for some seed
        changed = any(names(hero(ok(self, s))["shop"]) != names(hero(ok(self, s, ["end"]))["shop"])
                      for s in range(1, 10))
        self.assertTrue(changed, "shop never refreshes; freeze test vacuous")

    def test_freeze_clears_after_refresh(self):
        o = ok(self, 42, ["freeze", "end"])
        if o["phase"] != "finished":
            self.assertFalse(hero(o)["frozen"], "freeze must be consumed by the next refresh")
            self.assertEqual(len(hero(o)["shop"]), 3)

    def test_frozen_partial_shop_refills_to_3(self):
        # round 2 has 4 gold: buy one unit, freeze the remaining two slots
        pre = ok(self, 42, ["end"])
        kept = names(hero(pre)["shop"])[1:]
        o = ok(self, 42, ["end", "buy:0", "freeze"])
        self.assertEqual(names(hero(o)["shop"]), kept)
        self.assertEqual(len(hand(o)), 1, "freeze must not touch the hand")
        self.assertTrue(hero(o)["frozen"])
        nxt = ok(self, 42, ["end", "buy:0", "freeze", "end"])
        self.assertNotEqual(nxt["phase"], "finished")
        shop = hero(nxt)["shop"]
        self.assertEqual(len(shop), 3, shop)
        self.assertEqual(names(shop)[:2], kept, "unsold frozen prefix must be preserved in order")
        self.assertTrue(all(shop), "refilled slots must be real cards")
        self.assertFalse(hero(nxt)["frozen"])

    def test_frozen_empty_shop_refills_to_3(self):
        # manual mode with every seat ending: empty boards draw, nobody dies.
        # Round 7 gives 9 gold = three buys, emptying the shop.
        prefix = ["end"] * (4 * 6)
        o = ok(self, 12, prefix, "manual")
        self.assertEqual((o["round"], o["player"]), (7, 0))
        self.assertEqual(hero(o)["gold"], 9)
        moves = prefix + ["buy:0", "buy:0", "buy:0"]
        o = ok(self, 12, moves, "manual")
        self.assertEqual([u for u in hero(o)["shop"] if u], [])
        if "freeze" in o["legalActions"]:
            moves.append("freeze")
            self.assertTrue(hero(ok(self, 12, moves, "manual"))["frozen"])
        nxt = ok(self, 12, moves + ["end"] * 4, "manual")
        self.assertEqual((nxt["round"], nxt["player"]), (8, 0))
        shop = hero(nxt)["shop"]
        self.assertEqual(len(shop), 3, shop)
        self.assertTrue(all(shop))
        self.assertFalse(hero(nxt)["frozen"])

    def test_board_max_5_hand_max_7(self):
        moves, fin = agent.play(C, 17, {0: agent.policy_tempo})
        for k in range(0, len(moves) + 1, max(1, len(moves) // 15)):
            check_zones(self, ok(self, 17, moves[:k]))


class Completion(unittest.TestCase):
    def check_finished(self, o):
        self.assertEqual(o["phase"], "finished")
        self.assertLessEqual(o["round"], MAX_ROUNDS)
        self.assertEqual(o["legalActions"], [])
        self.assertEqual(sorted(o["rank"]), [0, 1, 2, 3])
        self.assertEqual(o["winner"], o["rank"][0])

    def test_end_only_finishes_within_max_rounds(self):
        moves, o = [], ok(self, 3)
        while o["phase"] != "finished":
            moves.append("end")
            o = ok(self, 3, moves)
            self.assertLessEqual(len(moves), MAX_ROUNDS)
        self.check_finished(o)

    def test_combat_report(self):
        o = ok(self, 5, ["auto"])
        self.assertTrue(o.get("combat"), "no combat report after first end")
        for c in o["combat"]:
            for k in ("round", "a", "b", "winner", "damage", "aBoard", "bBoard", "log", "events"):
                self.assertIn(k, c, c)
            self.assertIn(c["winner"], (c["a"], c["b"], -1))
        hp = {p["id"]: p["hp"] for p in o["players"]}
        for c in o["combat"]:
            if c["winner"] == -1:
                self.assertEqual(c["damage"], 0)
        self.assertTrue(all(0 <= v <= 40 for v in hp.values()))   # cause (c)

    def test_policy_agents_vs_bots(self):
        for pol in ("tempo", "econ", "random", "bot"):
            moves, fin = agent.play(C, 21, {0: agent.POLICIES[pol]}, rng_seed=1)
            self.check_finished(fin)
            if pol in ("tempo", "econ"):
                self.assertTrue(any(agent.kind(m) == "play" for m in moves), f"{pol} never deployed")

    def test_bots_deploy_and_finish(self):
        for seed in range(1, 7):
            moves, o, bot_board = [], ok(self, seed), 0
            while o["phase"] != "finished":
                moves.append("auto")
                o = ok(self, seed, moves)
                self.assertLessEqual(len(moves), MAX_ROUNDS)
                bot_board = max([bot_board] + [len(p["board"]) for p in o["players"] if p["id"] != 0])
                if o["phase"] != "finished":
                    check_zones(self, o)
                    self.assertGreater(len(hero(o)["board"]) + hero(o)["handCount"], 0,
                                       "seat 0 on auto bought nothing")
            self.check_finished(o)
            self.assertGreater(bot_board, 0, f"seed {seed}: bots never deployed a unit")

    def test_hp_monotone_nonincreasing(self):
        moves, fin = agent.play(C, 23, {0: agent.policy_bot})
        prev = None
        for k in range(len(moves) + 1):
            hp = [p["hp"] for p in ok(self, 23, moves[:k])["players"]]
            if prev:
                self.assertTrue(all(a <= b for a, b in zip(hp, prev)), (prev, hp))
            prev = hp


def _ids(units):
    return [u["id"] for u in units or []]


class Battle(unittest.TestCase):
    """Structured combat events agree with the fight result. Attack events are
    atomic snapshots: side "a"/"b" (fight seat a/b), indexes into the before
    boards, after boards, and each event's before boards equal the previous
    event's after boards. A final "end" event carries winner, damage and
    finishReason."""

    def fights(self):
        out = []
        for seed in (5, 21, 33):
            moves, fin = agent.play(C, seed, {0: agent.policy_tempo})
            for k in sorted({len(moves) // 2, len(moves)}):
                out += ok(self, seed, moves[:k]).get("combat") or []
        return out

    def test_events_chain_and_match_result(self):
        fs = self.fights()
        self.assertTrue(fs)
        attacks_seen, rallies, reasons = 0, 0, set()
        for c in fs:
            ev = c["events"]
            self.assertIsInstance(ev, list, c)
            self.assertTrue(ev, "every fight ends with an end event")
            end = ev[-1]
            self.assertEqual(end.get("kind"), "end", end)
            self.assertEqual([e for e in ev if e.get("kind") == "end"], [end], "exactly one end event, last")
            self.assertEqual((end["winner"], end["damage"]), (c["winner"], c["damage"]))
            reasons.add(end.get("finishReason"))
            atk = [e for e in ev if e.get("kind") == "attack"]
            self.assertEqual(len(atk) + 1, len(ev), f"unknown event kinds {[e.get('kind') for e in ev]}")
            if atk:
                self.assertEqual(_ids(atk[0]["beforeA"]), _ids(c["aBoard"]))
                self.assertEqual(_ids(atk[0]["beforeB"]), _ids(c["bBoard"]))
            prev = None
            for e in atk:
                for f in ("step", "side", "attackerIndex", "targetIndex", "beforeA", "beforeB", "afterA", "afterB"):
                    self.assertIn(f, e, e)
                self.assertIn(e["side"], ("a", "b"))
                mine, theirs = (e["beforeA"], e["beforeB"]) if e["side"] == "a" else (e["beforeB"], e["beforeA"])
                amine = e["afterA"] if e["side"] == "a" else e["afterB"]
                atheirs = e["afterB"] if e["side"] == "a" else e["afterA"]
                self.assertLess(e["attackerIndex"], len(mine), e)
                self.assertLess(e["targetIndex"], len(theirs), e)
                if "attackerAfterIndex" in e and e["attackerAfterIndex"] >= 0:
                    self.assertLess(e["attackerAfterIndex"], len(amine), e)
                if "targetAfterIndex" in e and e["targetAfterIndex"] >= 0:
                    self.assertLess(e["targetAfterIndex"], len(atheirs), e)
                if "rally" in e and "attackerAttack" in e:
                    self.assertEqual(e["attackerAttack"], mine[e["attackerIndex"]]["attack"] + e["rally"], e)
                    rallies += e["rally"] > 0
                if prev:
                    self.assertEqual(e["beforeA"], prev["afterA"], "snapshots must chain")
                    self.assertEqual(e["beforeB"], prev["afterB"], "snapshots must chain")
                    self.assertGreater(e["step"], prev["step"])
                self.assertLessEqual(len(e["afterA"]), len(e["beforeA"]), "no summons in combat")
                self.assertLessEqual(len(e["afterB"]), len(e["beforeB"]), "no summons in combat")
                prev = e
            fa = end.get("afterA", prev["afterA"] if prev else c["aBoard"])
            fb = end.get("afterB", prev["afterB"] if prev else c["bBoard"])
            if prev:
                self.assertEqual((fa, fb), (prev["afterA"], prev["afterB"]), "end event repeats the last boards")
            if c["winner"] == c["a"]:
                self.assertTrue(fa and not fb, c)
            elif c["winner"] == c["b"]:
                self.assertTrue(fb and not fa, c)
            else:
                self.assertEqual(c["winner"], -1)
                self.assertEqual(c["damage"], 0)
                self.assertEqual(bool(fa), bool(fb), "a draw leaves both or neither side standing")
                if fa:
                    self.assertEqual(end.get("finishReason"), "fuel", end)
            attacks_seen += len(atk)
        self.assertGreater(attacks_seen, 0, "no attack events in any sampled fight")
        print(f"\n  [battle] fights={len(fs)} attacks={attacks_seen} rally events={rallies} "
              f"finishReasons={sorted(map(str, reasons))}", file=sys.stderr)


class SelfPlay(unittest.TestCase):
    def test_human_cli_vs_custom_agents(self):
        save = os.path.join(ROOT, "evidence", "api_test_human.json")
        # round 1: buy, try a (removed) hand sale; round 2: buy, deploy the held unit
        feed = ("help\nnot-a-move\nbuy:0\nsellhand:0\nend\nbuy:0\nplay:0\nend\n"
                + "end\n" * 13 + "quit\n")
        transport = ["--cli", CLI] if CLI else ["--url", URL]
        r = subprocess.run([sys.executable, os.path.join(ROOT, "scripts", "agent.py"), *transport,
                            "human", "--seed", "31", "--seat", "2",
                            "--policies", "tempo,scripts/example_policy.py:policy,bot", "--save", save],
                           input=feed, capture_output=True, text=True, cwd=ROOT, timeout=300)
        assert_child_stderr_clean(r.stderr, 'agent.py human')
        self.assertEqual(r.returncode, 0, r.stdout[-2000:] + r.stderr[-2000:])
        self.assertIn("Not legal now", r.stdout)
        self.assertIn("Scout", r.stdout)
        self.assertIn("hand :", r.stdout)
        self.assertNotIn("sellhand", r.stdout.split("Not legal now: 'sellhand:0'")[0])  # help text, cause (a)
        self.assertIn("Not legal now: 'sellhand:0'", r.stdout)
        with open(save) as f:
            rep = json.load(f)
        self.assertTrue(rep["finished"], r.stdout[-1500:])
        self.assertEqual(rep.get("protocolVersion"), 3)   # cause (d)
        mv = rep["moves"]
        # the human's own moves (seat 2): who acted is the `player` before each move
        mine = [m for k, m in enumerate(mv) if ok(self, 31, mv[:k], "manual")["player"] == 2]
        self.assertEqual(mine[:5], ["buy:0", "end", "buy:0", "play:0", "end"], mine)   # cause (a)
        st, again = game(31, rep["moves"], "manual")
        self.assertEqual(st, 200)
        self.assertEqual(agent.state_hash(again), rep["final"]["hash"])
        self.assertIn("auto", rep["moves"])  # seat 3 = built-in Bend bot

    def test_custom_policy_file(self):
        pol = agent.load_policy(os.path.join(ROOT, "scripts", "example_policy.py") + ":policy")
        moves, fin = agent.play(C, 33, {0: pol})
        Completion.check_finished(self, fin)
        self.assertTrue(any(m.startswith("play:") for m in moves), "example policy never deployed")

    def _agent(self, *args):
        transport = ["--cli", CLI] if CLI else ["--url", URL]
        r = subprocess.run([sys.executable, os.path.join(ROOT, "scripts", "agent.py"), *transport, *args],
                           capture_output=True, text=True, cwd=ROOT, timeout=300)
        assert_child_stderr_clean(r.stderr, 'agent.py ' + ' '.join(args))   # before callers' rc checks
        return r

    def test_saved_replay_reproduces_and_v1_is_refused(self):
        import tempfile
        d = tempfile.mkdtemp(prefix="bg-v4-")
        f = os.path.join(d, "v3.json")
        r = self._agent("play", "--seed", "42", "--policy", "econ", "--save", f)
        self.assertEqual(r.returncode, 0, r.stdout + r.stderr)
        with open(f) as fh:
            rep = json.load(fh)
        self.assertEqual(rep["protocolVersion"], 3)   # cause (d)
        r = self._agent("replay", f)
        self.assertEqual(r.returncode, 0, r.stdout + r.stderr)
        self.assertIn("REPRODUCED", r.stdout)
        # a v1 file (no protocolVersion) must not be replayed as if it meant the same thing
        old = dict(rep)
        old.pop("protocolVersion")
        f1 = os.path.join(d, "v1.json")
        with open(f1, "w") as fh:
            json.dump(old, fh)
        r = self._agent("replay", f1)
        self.assertEqual(r.returncode, 4, r.stdout + r.stderr)
        self.assertIn("NOT EQUIVALENT", r.stdout)
        # cause (d): a V3-release (protocol 2) file is refused the same way, never re-run
        f2 = os.path.join(d, "v2.json")
        with open(f2, "w") as fh:
            json.dump(dict(rep, protocolVersion=2), fh)
        r = self._agent("replay", f2)
        self.assertEqual(r.returncode, 4, r.stdout + r.stderr)
        self.assertIn("NOT EQUIVALENT", r.stdout)

    def test_manual_end_passes_seat(self):
        o = ok(self, 42, [], "manual")
        self.assertEqual(o["player"], 0)
        o = ok(self, 42, ["end"], "manual")
        self.assertEqual((o["round"], o["player"]), (1, 1))
        o = ok(self, 42, ["end"] * 4, "manual")
        self.assertEqual((o["round"], o["player"]), (2, 0))

    def test_manual_selfplay_client_policies(self):
        seats = []
        pols = {0: agent.policy_tempo, 1: agent.policy_econ, 2: agent.policy_random, 3: agent.policy_bot}
        moves, fin = agent.play(C, 42, pols, mode="manual", seats=seats)
        Completion.check_finished(self, fin)
        self.assertEqual(set(seats), {0, 1, 2, 3})
        st, again = game(42, moves, "manual")
        self.assertEqual(agent.state_hash(again), agent.state_hash(fin))

    def test_manual_all_auto_is_bot_selfplay(self):
        moves, o = [], ok(self, 8, [], "manual")
        while o["phase"] != "finished":
            moves.append("auto")
            o = ok(self, 8, moves, "manual")
            self.assertLess(len(moves), 4 * MAX_ROUNDS + 1)
        Completion.check_finished(self, o)

if __name__ == "__main__":
    unittest.main(verbosity=2)
