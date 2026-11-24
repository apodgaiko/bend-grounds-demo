#!/usr/bin/env python3
"""V4 protocol plumbing checks (engine/main.bend, scripts/bg_engine.py,
scripts/agent.py). Stdlib only.

Static lane (always): the game protocol is 3 everywhere in the plumbing, the
HTTP version gate takes its value from the game (no stale literal), the fast
runner WIRE protocol is unchanged ("fast-runner/1"), and no plumbing file or
client policy knows a hand sale (`sellhand`).

HTTP lane (only with BG_PROTO_URL=http://127.0.0.1:PORT, an isolated V4
server; never the live one): missing `v` serves protocol 3, explicit `v=3` is
the same body, `v=2` and every other value is an error-only 400
unsupported_version naming protocol 3, and `sellhand:0` is a bad move.

    python3 tests/v4_protocol_plumbing_test.py
    BG_PROTO_URL=http://127.0.0.1:18961 python3 tests/v4_protocol_plumbing_test.py
"""
import json
import os
import random
import re
import sys
import unittest
import urllib.error
import urllib.request

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.join(ROOT, 'scripts'))
import agent  # noqa: E402
import bg_engine  # noqa: E402

GAME_PROTOCOL = 3
WIRE_PROTOCOL = 'fast-runner/1'
URL = os.environ.get('BG_PROTO_URL', '').rstrip('/')


def read(rel):
    with open(os.path.join(ROOT, rel), encoding='utf-8') as f:
        return f.read()


def code_lines(text, comment='#'):
    return [ln for ln in text.splitlines() if not ln.lstrip().startswith(comment)]


class Static(unittest.TestCase):
    def test_client_protocols_are_3(self):
        self.assertEqual(bg_engine.PROTOCOL, GAME_PROTOCOL)
        self.assertEqual(agent.PROTOCOL, GAME_PROTOCOL)

    def test_game_announces_3(self):
        m = re.search(r'def protocol_version\(\) -> Nat:\s*\n\s*(\d+)n', read('engine/game.bend'))
        self.assertIsNotNone(m, 'protocol_version() not found in engine/game.bend')
        self.assertEqual(int(m.group(1)), GAME_PROTOCOL)

    def test_http_gate_derives_from_game(self):
        src = read('engine/main.bend')
        m = re.search(r'def api_version\(\) -> String:\s*\n\s*(.+)', src)
        self.assertIsNotNone(m)
        self.assertEqual(m.group(1).strip(), 'Nat.show(G.protocol_version())')
        # the unsupported_version message is built from api_version(), not a literal
        msg = [ln for ln in src.splitlines() if '"unsupported_version"' in ln]
        self.assertEqual(len(msg), 1, msg)
        self.assertIn('api_version()', msg[0])
        self.assertNotRegex(msg[0], r'version \d')

    def test_runner_wire_unchanged(self):
        import fast_runner
        self.assertEqual(fast_runner.PROTOCOL, WIRE_PROTOCOL)
        m = re.search(r'def runner_protocol\(\) -> String:\s*\n\s*"([^"]*)"', read('engine/runner.bend'))
        self.assertIsNotNone(m)
        self.assertEqual(m.group(1), WIRE_PROTOCOL)

    def test_no_hand_sale_in_plumbing(self):
        for rel in ('engine/main.bend', 'scripts/bg_engine.py'):
            self.assertNotIn('sellhand', read(rel).lower(), rel)
        # agent.py may only mention sellhand when describing why protocol-2
        # transcripts are refused; no code line may use it
        src = read('scripts/agent.py')
        for ln in code_lines(src):
            if 'sellhand' in ln.lower():
                self.assertNotIn('"sellhand"', ln, ln)
        self.assertNotIn('sellhand', agent.HUMAN_HELP)
        body = src.split('"""', 2)[2]          # past the module docstring
        self.assertNotIn('"sellhand"', body)
        self.assertNotIn("'sellhand", body)


def unit(name, atk, hp, tier=1, golden=False):
    return {'name': name, 'attack': atk, 'health': hp, 'tier': tier, 'tribe': 'Neutral',
            'golden': golden, 'keywords': []}


def obs_full_hand(legal):
    hand = [unit(f'H{i}', 1, 1) for i in range(7)]
    board = [unit(f'B{i}', 9, 9, 3) for i in range(5)]
    shop = [unit('S0', 9, 9, 3)]
    return {'player': 0, 'round': 6, 'legalActions': legal,
            'players': [{'id': 0, 'hand': hand, 'board': board, 'shop': shop, 'gold': 9}]}


class Policies(unittest.TestCase):
    """Client policies choose verbatim from legalActions and have no hand-sale
    branch any more (the V3 tempo policy recycled a full hand via sellhand)."""

    LEGAL = ['sell:0', 'sell:1', 'sell:2', 'sell:3', 'sell:4', 'roll', 'freeze', 'upgrade', 'end']

    def test_full_hand_never_sells_from_hand(self):
        for name, pol in agent.POLICIES.items():
            for seed in range(20):
                a = pol(obs_full_hand(self.LEGAL), random.Random(seed), {})
                self.assertIn(a, self.LEGAL, name)
                self.assertNotEqual(agent.kind(a), 'sellhand', name)

    def test_even_a_stray_sellhand_token_is_not_chosen_by_rule_policies(self):
        legal = self.LEGAL + ['sellhand:0']
        for name in ('tempo', 'econ', 'climber'):
            a = agent.POLICIES[name](obs_full_hand(legal), random.Random(0), {})
            self.assertNotEqual(agent.kind(a), 'sellhand', name)

    def test_golden_marker_rendered(self):
        self.assertTrue(agent.fmt_unit(unit('Imp', 4, 2, golden=True)).startswith('Golden Imp'))
        self.assertTrue(agent.fmt_unit(unit('Imp', 2, 1)).startswith('Imp'))


def get(path):
    try:
        with urllib.request.urlopen(URL + path, timeout=30) as r:
            return r.status, r.read()
    except urllib.error.HTTPError as e:
        with e:
            return e.code, e.read()


@unittest.skipUnless(URL, 'set BG_PROTO_URL to an isolated V4 server for the HTTP lane')
class Http(unittest.TestCase):
    def game(self, query):
        st, raw = get('/api/game?' + query)
        return st, json.loads(raw), raw

    def assertUnsupported(self, query):
        st, data, raw = self.game(query)
        self.assertEqual(st, 400, (query, raw[:200]))
        self.assertEqual(set(data), {'error'}, (query, raw[:200]))
        self.assertEqual(data['error']['code'], 'unsupported_version', query)
        self.assertIn(f'protocol version {GAME_PROTOCOL} only', data['error']['message'])
        self.assertIn(f'v={GAME_PROTOCOL}', data['error']['message'])

    def test_missing_v_is_3_and_explicit_3_same(self):
        st, a, raw_a = self.game('seed=42&moves=')
        self.assertEqual(st, 200, raw_a[:200])
        self.assertEqual((a['protocolVersion'], a['schemaVersion']), (GAME_PROTOCOL, GAME_PROTOCOL))
        st, _, raw_b = self.game('seed=42&moves=&v=3')
        self.assertEqual(st, 200)
        self.assertEqual(raw_a, raw_b)
        st, _, raw_c = self.game('v=3&seed=42&moves=')
        self.assertEqual(raw_a, raw_c)

    def test_old_and_other_versions_rejected(self):
        for v in ('2', '1', '4', '03', '3.0', '%203', '3%20', '', 'x', '%33x'):
            self.assertUnsupported(f'seed=42&moves=&v={v}')
        self.assertUnsupported('seed=42&moves=&v')
        self.assertUnsupported('seed=42&moves=&v=3&v=3')
        self.assertUnsupported('seed=42&moves=&v=2&v=3')

    def test_version_checked_first(self):
        self.assertUnsupported('seed=&moves=&v=2')

    def test_bodies_announce_3(self):
        for path in ('/api/rules', '/api/health'):
            st, raw = get(path)
            self.assertEqual(st, 200, path)
            d = json.loads(raw)
            self.assertEqual((d['protocolVersion'], d['schemaVersion']), (GAME_PROTOCOL, GAME_PROTOCOL), path)
        st, raw = get('/api/rules')
        rules = json.loads(raw)
        self.assertNotIn('sellhand:i', rules['actions'])
        self.assertNotIn('sellHandRefund', rules['costs'])

    def test_sellhand_is_a_bad_move(self):
        st, d, raw = self.game('seed=42&moves=buy:0,sellhand:0&v=3')
        self.assertEqual(st, 400, raw[:200])
        self.assertEqual(d.get('movesApplied'), 1, raw[:300])
        self.assertIn(d['error']['code'], ('bad_move', 'illegal_move'))
        self.assertFalse(any(a.startswith('sellhand') for a in d.get('legalActions') or []))

    def test_http_engine_and_agent_client_pin_3(self):
        eng = bg_engine.HttpEngine(URL)
        st, obs = eng.game(42, 'bots', [])
        self.assertEqual((st, obs['protocolVersion']), (200, GAME_PROTOCOL))
        c = agent.Client(URL)
        self.assertEqual(agent.server_protocol(c), GAME_PROTOCOL)
        st, obs = c.game(42, [])
        self.assertEqual((st, obs['protocolVersion']), (200, GAME_PROTOCOL))


if __name__ == '__main__':
    unittest.main(verbosity=2)
