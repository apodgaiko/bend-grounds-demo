#!/usr/bin/env python3
"""Independent real HTTP boundary regression checks. Requires running server."""
import json
import os
import socket
import unittest
import urllib.error
import urllib.request
import urllib.parse

BASE = os.environ.get('BG_URL', 'http://127.0.0.1:8765').rstrip('/')


def request(path):
    try:
        with urllib.request.urlopen(BASE + path, timeout=4) as r:
            return r.status, r.read(), dict(r.headers)
    except urllib.error.HTTPError as e:
        # An HTTPError owns the response body; close it on every path.
        with e:
            return e.code, e.read(), dict(e.headers)


class HTTPBoundary(unittest.TestCase):
    def assertHealthy(self):
        status, body, _ = request('/api/health')
        self.assertEqual(status, 200, body)
        json.loads(body)

    def test_static_whitelist(self):
        for path in ('/../README.md', '/engine/game.bend', '/.git/config',
                     '/vendor/bend/base.bend', '/api/game/extra', '/app.js/extra'):
            status, body, _ = request(path)
            self.assertEqual(status, 404, (path, body[:200]))
        self.assertHealthy()

    def test_numeric_tokens_bounded(self):
        for token in ('4294967295', '99999999999999999999999999999', '-1'):
            status, body, _ = request('/api/game?seed=42&moves=buy%3A' + token)
            self.assertEqual(status, 400, (token, body[:200]))
            self.assertIsInstance(json.loads(body).get('error'), dict)
        self.assertHealthy()

    def test_seed_boundaries(self):
        for seed in ('0', '4294967295'):
            status, body, _ = request('/api/game?seed=' + seed)
            self.assertEqual(status, 200, body[:300])
            self.assertEqual(json.loads(body)['seed'], int(seed))
        for seed in ('4294967296', '999999999999999999999', 'abc', '-1'):
            status, body, _ = request('/api/game?seed=' + seed)
            self.assertEqual(status, 400, body[:300])
        self.assertHealthy()

    def test_json_and_static_content_types(self):
        for path in ('/api/game?seed=1', '/api/rules', '/api/health'):
            status, body, headers = request(path)
            self.assertEqual(status, 200, body[:200])
            self.assertIn('application/json', headers.get('Content-Type', ''))
            json.loads(body)
        status, body, headers = request('/')
        self.assertEqual(status, 200)
        self.assertIn(b'<html lang="en">', body)
        self.assertIn('text/html', headers.get('Content-Type', ''))

    def test_request_overflow_rejected(self):
        # A complete oversized request must never be accepted as a valid prefix.
        req = ('GET /api/game?seed=1&moves=' + 'freeze,' * 12000 +
               'end HTTP/1.1\r\nHost: localhost\r\n\r\n').encode('ascii')
        url = urllib.parse.urlsplit(BASE)
        with socket.create_connection((url.hostname, url.port or 80), timeout=4) as s:
            s.settimeout(4)
            try:
                s.sendall(req)
                response = s.recv(4096)
            except (ConnectionResetError, BrokenPipeError):
                response = b''
        if response:
            self.assertRegex(response.split(b'\r\n', 1)[0], br'HTTP/1\.[01] (400|413|414|431)\b')
        self.assertHealthy()


if __name__ == '__main__':
    unittest.main(verbosity=2)
