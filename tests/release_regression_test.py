#!/usr/bin/env python3
"""Focused resource-lifecycle, CLI, compiler-stream and launcher regressions (no engine required)."""
import contextlib
import importlib.util
import io
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from types import SimpleNamespace
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'scripts'))
import agent
spec = importlib.util.spec_from_file_location('card_checks', ROOT / 'tests/card_interactions_test.py')
card_checks = importlib.util.module_from_spec(spec)
spec.loader.exec_module(card_checks)


class Client:
    def __init__(self):
        self.owned = set()
        self.close_count = 0

    def session(self, *args):
        owner = self
        class Session:
            obs = {'phase': 'recruit', 'legalActions': ['end'], 'player': 0}
            def step(self, move):
                return 200, {'phase': 'finished'}
            def close(self):
                owner.owned.remove(self)
                owner.close_count += 1
        session = Session()
        self.owned.add(session)
        return session

    def close(self):
        pass


class Regressions(unittest.TestCase):
    def test_repeated_games_release_sessions(self):
        client = Client()
        for seed in range(4100):
            moves, obs = agent.play(client, seed, {'*': lambda *_: 'end'})
            self.assertEqual(moves, ['end'])
            self.assertFalse(client.owned)
        self.assertEqual(client.close_count, 4100)

    def test_failures_release_sessions(self):
        for kwargs, policy, error in [
            ({}, lambda *_: 'illegal', ValueError),
            ({'max_steps': 0}, lambda *_: 'end', RuntimeError),
            ({'on_move': lambda *_: (_ for _ in ()).throw(LookupError('callback'))}, lambda *_: 'end', LookupError),
            ({}, lambda *_: (_ for _ in ()).throw(LookupError('policy')), LookupError),
        ]:
            client = Client()
            with self.assertRaises(error):
                agent.play(client, 1, {'*': policy}, **kwargs)
            self.assertFalse(client.owned)
            self.assertEqual(client.close_count, 1)

    def test_selfplay_policy_counts(self):
        for names in ['tempo,econ', 'tempo,econ,random', 'tempo,econ,random,bot,tempo', '']:
            with patch.object(agent, 'make_client', return_value=Client()), patch.object(agent, 'server_protocol', return_value=3):
                with self.assertRaisesRegex(SystemExit, '1 or 4'):
                    agent.main(['selfplay', '--policies', names])
        for names in ['tempo', 'tempo,econ,random,bot']:
            with patch.object(agent, 'make_client', return_value=Client()), patch.object(agent, 'server_protocol', return_value=3), patch.object(agent, 'play', return_value=([], {'phase': 'finished'})) as play, contextlib.redirect_stdout(io.StringIO()):
                self.assertEqual(agent.main(['selfplay', '--policies', names]), 0)
                self.assertEqual(set(play.call_args.args[2]), {0, 1, 2, 3})

    def test_compiler_stderr_is_not_fixture_stdout(self):
        expected = card_checks.expected_lines(Path(card_checks.BEND_FILE).read_text())
        diagnostic = 'Compiler update notice\n'
        with patch.object(card_checks.shutil, 'which', return_value='/stub/bun'), patch.object(card_checks.subprocess, 'run', return_value=SimpleNamespace(returncode=0, stdout=expected+'\n', stderr=diagnostic)), contextlib.redirect_stderr(io.StringIO()) as err, contextlib.redirect_stdout(io.StringIO()):
            self.assertTrue(card_checks.lane_fixtures())
            self.assertEqual(err.getvalue(), diagnostic)
        with patch.object(card_checks.shutil, 'which', return_value='/stub/bun'), patch.object(card_checks.subprocess, 'run', return_value=SimpleNamespace(returncode=0, stdout=expected+'\nUNEXPECTED SEMANTIC OUTPUT\n', stderr=diagnostic)), contextlib.redirect_stderr(io.StringIO()), contextlib.redirect_stdout(io.StringIO()):
            self.assertFalse(card_checks.lane_fixtures())

    def test_launcher_refusal_explains_safe_recovery(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root/'scripts').mkdir()
            (root/'Play.command').write_bytes((ROOT/'Play.command').read_bytes())
            (root/'scripts/setup.sh').write_text('exit 0\n')
            (root/'scripts/build_manifest.py').write_text('raise SystemExit(0)\n')
            (root/'scripts/start.sh').write_text('echo "port occupied" >&2; exit 1\n')
            result = subprocess.run(['bash', str(root/'Play.command')], input='\n', text=True, capture_output=True, timeout=10)
            self.assertEqual(result.returncode, 1)
            self.assertIn('No existing server was adopted or stopped', result.stderr)
            self.assertIn('BG_PORT=8766 bash scripts/start.sh --fg', result.stderr)


if __name__ == '__main__':
    unittest.main()
