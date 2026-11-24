#!/usr/bin/env python3
"""Build provenance for the native binaries (stdlib only).

The HTTP server and the replay CLI (build/server, build/cli, or an isolated
candidate build of them) each have a manifest B.manifest.json:

  {"binary": "build/cli", "binarySha256": "...", "engineDir": "engine",
   "sources": {"engine/game.bend": "...", ...}, "compilerPin": "<vendor/bend HEAD>",
   "builtAt": "..."}

Paths are repo-relative (absolute outside the repo).

  python3 scripts/build_manifest.py snapshot --out build/cli.sources.json SRC...
  (compile)
  python3 scripts/build_manifest.py write --binary build/cli --snapshot build/cli.sources.json
  python3 scripts/build_manifest.py check [build/server build/cli]

build/runner is NOT covered here: scripts/build_runner.sh writes its own
manifest (kind bend-grounds-runner) and scripts/fast_runner.py validates it
before every spawn (scripts/fast_runner.py).

scripts/build.sh hashes the sources a binary is compiled from BEFORE the
compile (`snapshot`) and `write` re-hashes them afterwards: if any source
changed during the build, no manifest is written and the build fails, so a
manifest never attests sources the binary was not built from. verify_binary() refuses a binary
that is missing, has no manifest, whose sha256 differs, whose recorded sources
changed on disk, or whose compiler pin differs from vendor/bend HEAD, or
when vendor/bend is dirty (at build time or now). A
protocol or rules check cannot catch a stale build of the same schema; this
can.
"""
import argparse
import hashlib
import json
import os
import subprocess
import sys
import time

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
SUFFIX = '.manifest.json'
DEFAULT_BINARIES = ('build/server', 'build/cli')


class StaleBuild(RuntimeError):
    pass


def sha256_file(path):
    h = hashlib.sha256()
    with open(path, 'rb') as f:
        for block in iter(lambda: f.read(1 << 20), b''):
            h.update(block)
    return h.hexdigest()


def rel(p):
    p = os.path.abspath(os.fspath(p))
    return os.path.relpath(p, ROOT) if p.startswith(ROOT + os.sep) else p


def absolute(p):
    p = os.fspath(p)
    return p if os.path.isabs(p) else os.path.join(ROOT, p)


def compiler_clean():
    """True when vendor/bend has no staged, unstaged or untracked changes."""
    try:
        r = subprocess.run(['git', '-C', os.path.join(ROOT, 'vendor/bend'), 'status', '--porcelain',
                            '--untracked-files=all'], capture_output=True, text=True, timeout=30)
        return r.returncode == 0 and r.stdout.strip() == ''
    except OSError:
        return False


def compiler_head():
    try:
        out = subprocess.run(['git', '-C', os.path.join(ROOT, 'vendor/bend'), 'rev-parse', 'HEAD'],
                             capture_output=True, text=True, timeout=10).stdout.strip()
        return out or None
    except OSError:
        return None


def snapshot(sources, out):
    snap = {rel(absolute(p)): sha256_file(absolute(p)) for p in sources}
    with open(absolute(out), 'w') as f:
        json.dump({'sources': snap, 'compilerPin': compiler_head(), 'compilerClean': compiler_clean(),
                   'takenAt': time.strftime('%Y-%m-%dT%H:%M:%S%z')}, f, indent=1, sort_keys=True)
    return snap


def write(binary, snapshot_file):
    b = absolute(binary)
    with open(absolute(snapshot_file)) as f:
        snap = json.load(f)
    now = {p: sha256_file(absolute(p)) if os.path.isfile(absolute(p)) else None for p in snap['sources']}
    changed = [p for p, h in snap['sources'].items() if now[p] != h]
    if not snap.get('compilerClean') or not compiler_clean():
        raise StaleBuild(f'vendor/bend is not clean; refusing to attest {rel(b)}')
    if changed or compiler_head() != snap.get('compilerPin'):
        raise StaleBuild(f'sources changed during the build of {rel(b)}: {", ".join(changed) or "compiler pin"}; '
                         'no manifest written, rebuild')
    m = {'binary': rel(b), 'binarySha256': sha256_file(b),
         'engineDir': rel(os.path.dirname(absolute(next(iter(snap['sources']))))),
         'sources': snap['sources'], 'compilerPin': snap.get('compilerPin'), 'compilerClean': True,
         'builtAt': time.strftime('%Y-%m-%dT%H:%M:%S%z')}
    with open(b + SUFFIX, 'w') as f:
        json.dump(m, f, indent=1, sort_keys=True)
    os.remove(absolute(snapshot_file))
    return m


def verify_binary(binary):
    """Return provenance for `binary` (dict) or raise StaleBuild."""
    b = absolute(binary)
    fix = 'rebuild with: bash scripts/build.sh'
    if not os.path.isfile(b) or not os.access(b, os.X_OK):
        raise StaleBuild(f'{rel(b)} missing; {fix}')
    mpath = b + SUFFIX
    if not os.path.isfile(mpath):
        raise StaleBuild(f'{rel(b)} has no provenance manifest {rel(mpath)}; {fix}')
    with open(mpath) as f:
        m = json.load(f)
    have = sha256_file(b)
    if m.get('binarySha256') != have:
        raise StaleBuild(f'{rel(b)} sha256 {have[:12]} != manifest {str(m.get("binarySha256"))[:12]}; {fix}')
    sources = m.get('sources') or {}
    if not sources:
        raise StaleBuild(f'{rel(mpath)} lists no sources; {fix}')
    changed = [p for p, h in sources.items()
               if not os.path.isfile(absolute(p)) or sha256_file(absolute(p)) != h]
    if changed:
        raise StaleBuild(f'{rel(b)} was built {m.get("builtAt")} from older sources '
                         f'({", ".join(changed)} changed since); {fix}')
    pin = compiler_head()
    if m.get('compilerClean') is not True or not compiler_clean():
        raise StaleBuild(f'{rel(b)}: compiler tree vendor/bend not clean (at build or now); {fix}')
    if m.get('compilerPin') != pin:
        raise StaleBuild(f'{rel(b)} built with compiler {m.get("compilerPin")}, vendor/bend is {pin}; {fix}')
    return {'binary': rel(b), 'binarySha256': have, 'manifest': rel(mpath),
            'engineDir': m.get('engineDir'), 'sources': sources,
            'compilerPin': m.get('compilerPin'), 'builtAt': m.get('builtAt')}


def main():
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    sub = ap.add_subparsers(dest='cmd', required=True)
    sn = sub.add_parser('snapshot', help='hash the sources before compiling')
    sn.add_argument('--out', required=True)
    sn.add_argument('sources', nargs='+')
    w = sub.add_parser('write', help='write BINARY.manifest.json from a pre-build snapshot')
    w.add_argument('--binary', required=True)
    w.add_argument('--snapshot', required=True)
    c = sub.add_parser('check', help='verify binaries against their manifests')
    c.add_argument('binaries', nargs='*', default=list(DEFAULT_BINARIES))
    a = ap.parse_args()
    if a.cmd == 'snapshot':
        snapshot(a.sources, a.out)
        return 0
    if a.cmd == 'write':
        try:
            m = write(a.binary, a.snapshot)
        except StaleBuild as e:
            print(f'REFUSED {e}', file=sys.stderr)
            return 1
        print(f'provenance: {m["binary"]} {m["binarySha256"][:12]} ({len(m["sources"])} sources)')
        return 0
    bad = 0
    for b in a.binaries:
        try:
            v = verify_binary(b)
            print(f'OK {v["binary"]} {v["binarySha256"][:12]} built {v["builtAt"]}')
        except StaleBuild as e:
            print(f'STALE {e}')
            bad += 1
    return 1 if bad else 0


if __name__ == '__main__':
    sys.exit(main())
