#!/usr/bin/env python3
"""Protocol version (`v` query parameter) checks against a real HTTP server.

Usage:
    python3 tests/protocol_v3_test.py                 # all checks
    python3 tests/protocol_v3_test.py Transport       # transport only
    BG_URL=http://127.0.0.1:18765 python3 tests/protocol_v3_test.py

V4 migration of tests/protocol_v2_test.py (docs/V4-MISSION.md, main freeze):
the served protocol is 3; a missing `v` means 3; only the exact value `3` is
accepted; the former version `2` is now `unsupported_version` like any other
value. `Transport` checks engine/main.bend routing; `EngineV3` needs the V4
engine (schemaVersion/protocolVersion 3, no hand sale).
"""
import json
import os
import unittest
import urllib.error
import urllib.request

BASE = os.environ.get('BG_URL', 'http://127.0.0.1:8765').rstrip('/')


def get(path):
    try:
        with urllib.request.urlopen(BASE + path, timeout=10) as r:
            return r.status, r.read()
    except urllib.error.HTTPError as e:
        with e:
            return e.code, e.read()


def get_json(path):
    status, body = get(path)
    return status, json.loads(body), body


class Transport(unittest.TestCase):
    def assertUnsupported(self, query):
        status, data, body = get_json('/api/game?' + query)
        self.assertEqual(status, 400, (query, body[:300]))
        # error-only envelope: no observation fields
        self.assertEqual(set(data), {'error'}, (query, body[:300]))
        self.assertEqual(data['error']['code'], 'unsupported_version', query)
        self.assertIsInstance(data['error']['message'], str)

    def test_missing_v_defaults_to_3(self):
        s1, b1 = get('/api/game?seed=42')
        s2, b2 = get('/api/game?seed=42&v=3')
        self.assertEqual(s1, 200, b1[:300])
        self.assertEqual(s2, 200, b2[:300])
        self.assertEqual(b1, b2)

    def test_v3_any_position_same_body(self):
        base_status, base = get('/api/game?seed=7&mode=manual&moves=end')
        for q in ('v=3&seed=7&mode=manual&moves=end',
                  'seed=7&v=3&mode=manual&moves=end',
                  'seed=7&mode=manual&moves=end&v=3'):
            status, body = get('/api/game?' + q)
            self.assertEqual(status, base_status, q)
            self.assertEqual(body, base, q)

    def test_v_is_percent_decoded_like_other_params(self):
        s1, b1 = get('/api/game?seed=3&v=%33')
        s2, b2 = get('/api/game?seed=3')
        self.assertEqual(s1, 200, b1[:300])
        self.assertEqual(b1, b2)

    def test_other_versions_rejected(self):
        # '2' is the previous protocol (V3 release): refused, never reinterpreted
        for v in ('2', '1', '4', '0', '03', '3.0', '3%20', '%203', '+3',
                  'v3', 'three', '-3', '33', '4294967299', 'x' * 64):
            with self.subTest(v=v):
                self.assertUnsupported('seed=42&v=' + v)

    def test_empty_or_bare_v_rejected(self):
        self.assertUnsupported('seed=42&v=')
        self.assertUnsupported('seed=42&v')

    def test_undecodable_v_rejected(self):
        for v in ('%ZZ', '%2', '%', '%C3%A9', '%0A'):
            with self.subTest(v=v):
                self.assertUnsupported('seed=42&v=' + v)

    def test_repeated_v_rejected(self):
        self.assertUnsupported('seed=42&v=3&v=3')
        self.assertUnsupported('seed=42&v=2&v=3')
        self.assertUnsupported('v=3&seed=42&v=')

    def test_version_checked_before_other_params(self):
        # a wrong version wins over every other query problem
        self.assertUnsupported('seed=abc&v=1')
        self.assertUnsupported('seed=42&seed=43&v=2')
        self.assertUnsupported('seed=42&mode=nope&v=2')
        self.assertUnsupported('seed=42&moves=buy%3A9999999999&v=2')
        self.assertUnsupported('seed=42&moves=' + ',end' * 1100 + '&v=2')
        # a V3-era transcript with a hand sale is refused on version first
        self.assertUnsupported('seed=42&moves=buy%3A0%2Csellhand%3A0&v=2')

    def test_strict_params_still_enforced_with_v3(self):
        for q, code in (('v=3', 'bad_request'),
                        ('seed=abc&v=3', 'bad_request'),
                        ('seed=42&seed=42&v=3', 'bad_request'),
                        ('seed=42&mode=nope&v=3', 'bad_request'),
                        ('seed=42&moves=buy%3A9999999999&v=3', 'bad_move'),
                        ('seed=42&moves=buy%3A0%2Csellhand%3A0&v=3', 'bad_move'),
                        ('seed=42&moves=' + ',end' * 1100 + '&v=3',
                         'too_many_moves')):
            with self.subTest(q=q[:60]):
                status, data, body = get_json('/api/game?' + q)
                self.assertEqual(status, 400, body[:300])
                self.assertEqual(data['error']['code'], code)

    def test_key_is_case_sensitive_and_unknown_keys_ignored(self):
        # only the exact key `v` is the version; `V` or `version` are
        # ignored like any other unknown key (cache-busters etc.)
        _, b0 = get('/api/game?seed=42')
        for q in ('seed=42&V=1', 'seed=42&version=1', 'seed=42&vv=1', 'seed=42&_=1'):
            with self.subTest(q=q):
                status, body = get('/api/game?' + q)
                self.assertEqual(status, 200, body[:300])
                self.assertEqual(body, b0)

    def test_other_endpoints_ignore_v(self):
        for path in ('/api/rules', '/api/health'):
            s0, b0 = get(path)
            s1, b1 = get(path + '?v=1')
            self.assertEqual(s0, 200)
            self.assertEqual((s1, b1), (s0, b0), path)
        status, body = get('/?v=1')
        self.assertEqual(status, 200)
        self.assertIn(b'<html', body)


class EngineV3(unittest.TestCase):
    """Needs the V4 engine (game.bend owns these fields)."""

    def test_versions_reported(self):
        for path in ('/api/game?seed=42&v=3', '/api/game?seed=42', '/api/rules', '/api/health'):
            with self.subTest(path=path):
                status, data, body = get_json(path)
                self.assertEqual(status, 200, body[:300])
                self.assertEqual(data.get('schemaVersion'), 3)
                self.assertEqual(data.get('protocolVersion'), 3)

    def test_cli_example_transcript(self):
        # the example in engine/main.bend: buy into the hand, play it
        status, data, body = get_json('/api/game?seed=42&mode=bots&moves=buy:0,play:0,end&v=3')
        self.assertEqual(status, 200, body[:300])
        self.assertEqual(data.get('movesApplied'), 3)
        self.assertIsNone(data.get('error'))

    def test_hand_sale_removed(self):
        # V4 cause (a): the command is gone from the grammar, the action list
        # and the cost table; it is a bad_move at its index, prefix kept
        status, ok, _ = get_json('/api/game?seed=42&moves=buy:0&v=3')
        self.assertEqual(status, 200)
        self.assertFalse([a for a in ok['legalActions'] if a.startswith('sellhand')])
        for i in ('0', '1', '7'):
            status, data, body = get_json('/api/game?seed=42&moves=buy:0,sellhand:' + i + '&v=3')
            self.assertEqual(status, 400, body[:300])
            self.assertEqual(data['error']['code'], 'bad_move')
            self.assertEqual(data['error'].get('index'), 1)
            self.assertEqual(data.get('movesApplied'), 1)
            self.assertEqual(data.get('players'), ok['players'])
        _, rules, _ = get_json('/api/rules')
        self.assertNotIn('sellHandRefund', rules['costs'])
        self.assertFalse([a for a in rules['actions'] if 'sellhand' in a.lower()])


if __name__ == '__main__':
    unittest.main(verbosity=2)
