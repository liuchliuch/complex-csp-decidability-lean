#!/usr/bin/env python3
"""Build and check the frozen paper goals with the pinned official Comparator."""
import argparse
import os
from pathlib import Path
import shutil
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]

def run(args, env=None):
    print('+ ' + ' '.join(map(str, args)), flush=True)
    subprocess.run(list(map(str, args)), cwd=ROOT, env=env, check=True)

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--no-sandbox', action='store_true',
                        help='explicit local-author mode without Linux Landrun isolation')
    args = parser.parse_args()
    run([sys.executable, ROOT / 'scripts/audit.py'])
    if not args.no_sandbox and not shutil.which('landrun'):
        parser.error('install Landrun on Linux, or explicitly select --no-sandbox for a local author check')
    run(['lake', 'build', 'ComplexCSP', '@Comparator/comparator', '@lean4export/lean4export'])
    # Run source audits and executable assertions once, independently of cached check objects.
    for module in ['verification/Axioms', 'tests/Instances', 'tests/AlgebraicInput',
                   'tests/Degrees', 'tests/Identity', 'tests/Detector', 'tests/Recognition']:
        run(['lake', 'env', 'lean', '-s', '65536', '-j', '1', ROOT / (module + '.lean')])
    env = os.environ.copy()
    bins = [ROOT / '.lake/packages/Comparator/.lake/build/bin',
            ROOT / '.lake/packages/lean4export/.lake/build/bin']
    if args.no_sandbox:
        adapter = ROOT / '.lake/verification/author-bin'
        adapter.mkdir(parents=True, exist_ok=True)
        shim = adapter / 'landrun'
        shim.write_text('''#!/usr/bin/env python3
import os, sys
args = sys.argv[1:]
no_value = {'--best-effort', '-ldd', '-add-exec'}
with_value = {'--ro', '--rw', '--rwx', '--rox', '--env'}
while args and args[0].startswith('-'):
    flag = args.pop(0)
    if flag in with_value:
        if not args: raise SystemExit('missing Landrun argument')
        args.pop(0)
    elif flag not in no_value:
        raise SystemExit('unsupported author adapter flag: ' + flag)
if not args: raise SystemExit('missing command')
os.execvpe(args[0], args, os.environ)
''')
        shim.chmod(0o755)
        bins.insert(0, adapter)
        print('Mode: explicit local author check; process sandbox disabled.', flush=True)
    env['PATH'] = os.pathsep.join(map(str, bins)) + os.pathsep + env.get('PATH', '')
    run(['lake', 'env', 'comparator', 'verification/comparator.json'], env=env)
    print('Production axiom audit, executable regressions, and frozen-goal Comparator replay passed.')

if __name__ == '__main__':
    try:
        main()
    except subprocess.CalledProcessError as error:
        raise SystemExit(error.returncode)
