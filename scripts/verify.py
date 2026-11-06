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
    parser.add_argument('--reuse-dependencies', action='store_true',
                        help='local author mode: direct Lean builds using read-only dependency caches; never run Lake')
    args = parser.parse_args()
    if args.reuse_dependencies and not args.no_sandbox:
        parser.error('--reuse-dependencies is an explicit --no-sandbox local-author mode')
    run([sys.executable, ROOT / 'scripts/audit.py'])
    if not args.no_sandbox and not shutil.which('landrun'):
        parser.error('install Landrun on Linux, or explicitly select --no-sandbox for a local author check')
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
    else:
        adapter = ROOT / '.lake/verification/sandbox-bin'
        adapter.mkdir(parents=True, exist_ok=True)
        shim = adapter / 'landrun'
        if shim.is_symlink() or shim.exists():
            shim.unlink()
        shim.symlink_to(ROOT / 'scripts/landrun-runner.sh')
        env['LANDRUN_EXECUTABLE'] = str(Path(shutil.which('landrun')).resolve())
        bins.insert(0, adapter)
    env['PATH'] = os.pathsep.join(map(str, bins)) + os.pathsep + env.get('PATH', '')
    if args.reuse_dependencies:
        from cached_build import environment
        env.update(environment())
        # Keep the official binary and export tool; replace only its internal
        # build launcher. Loading a Lake workspace may otherwise replace a
        # shared checkout before any build target is considered.
        for package, executable in [('Comparator', 'comparator'), ('lean4export', 'lean4export')]:
            binary = ROOT / '.lake/packages' / package / '.lake/build/bin' / executable
            if not os.access(binary, os.X_OK):
                parser.error('missing cached executable: ' + str(binary))
        lake_adapter = ROOT / '.lake/verification/direct-bin'
        lake_adapter.mkdir(parents=True, exist_ok=True)
        lake = lake_adapter / 'lake'
        lake.write_text('#!/usr/bin/env python3\nimport sys\n' +
                        f'sys.path.insert(0, {str(ROOT / "scripts")!r})\n' +
                        'from cached_build import build\n'
                        'if len(sys.argv) != 3 or sys.argv[1] != "build":\n'
                        '    raise SystemExit("direct adapter accepts one module build only")\n'
                        'build([sys.argv[2]])\n')
        lake.chmod(0o755)
        env['PATH'] = os.pathsep.join(map(str, [lake_adapter] + bins)) + os.pathsep + os.environ.get('PATH', '')
        run([sys.executable, ROOT / 'scripts/cached_build.py', 'ComplexCSP'], env=env)
        lean = ['lean']
        comparator = ['comparator']
    else:
        run(['lake', 'build', 'ComplexCSP', '@Comparator/comparator', '@lean4export/lean4export'])
        lean = ['lake', 'env', 'lean']
        comparator = ['lake', 'env', 'comparator']
    # Run source audits and executable assertions once, independently of cached check objects.
    for module in ['verification/Axioms', 'tests/Instances', 'tests/AlgebraicInput',
                   'tests/Degrees', 'tests/Identity', 'tests/Detector', 'tests/Recognition']:
        run(lean + ['-s', '65536', '-j', '1', ROOT / (module + '.lean')], env=env)
    run(comparator + ['verification/comparator.json'], env=env)
    run([sys.executable, ROOT / 'scripts/comparator_negative.py'], env=env)
    print('Production axiom audit, executable regressions, frozen-goal Comparator replay, '
          'and negative controls passed.')

if __name__ == '__main__':
    try:
        main()
    except subprocess.CalledProcessError as error:
        raise SystemExit(error.returncode)
