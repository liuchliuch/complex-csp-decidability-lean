#!/usr/bin/env python3
"""Build project modules with direct Lean, reading pinned dependency caches only.

This local-author mode never invokes Lake: even loading a Lake workspace can
replace a dependency checkout when its recorded URL differs. It reuses existing
project objects only when their source hashes match the saved build traces, and recompiles changed
sources and their local import dependants. Official Comparator still exports
and replays the resulting proof closure independently.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
OBJECTS = ROOT / '.lake/build/lib/lean'
STATE = ROOT / '.lake/verification/direct-build.json'


def environment():
    env = os.environ.copy()
    packages = json.loads((ROOT / 'lake-manifest.json').read_text())['packages']
    paths = [OBJECTS]
    for package in packages:
        directory = ROOT / '.lake/packages' / package['name']
        if not (directory / package['configFile']).is_file():
            raise RuntimeError('Missing pinned dependency: ' + package['name'])
        library = directory / '.lake/build/lib/lean'
        if library.is_dir():
            paths.append(library.resolve())
    env['LEAN_PATH'] = os.pathsep.join(map(str, paths))
    env.setdefault('LEAN_NUM_THREADS', '1')
    return env


def build(targets):
    # Use the same comment-aware import parser as the release audit.
    from audit import lean_code
    modules = {}
    for base, prefix in [(ROOT / 'ComplexCSP', ROOT),
                         (ROOT / 'vendor/plgh/PlanarHom', ROOT / 'vendor/plgh'),
                         (ROOT / 'verification', ROOT), (ROOT / 'tests', ROOT)]:
        for source in base.rglob('*.lean'):
            name = source.relative_to(prefix).with_suffix('').as_posix().replace('/', '.')
            modules[name] = (source, prefix)
    modules['ComplexCSP'] = (ROOT / 'ComplexCSP.lean', ROOT)
    state = json.loads(STATE.read_text()) if STATE.exists() else {}
    env = environment()
    # A packaged checkout can have newer source mtimes than its verified cache.
    # Compare contents with the pinned toolchain's exact source-hashing routine.
    uncached = [name for name in modules if name not in state]
    hashes = subprocess.run(['lean', '--run', str(ROOT / 'scripts/cache_hashes.lean')],
                            input=''.join(str(modules[name][0]) + '\n' for name in uncached),
                            cwd=ROOT, env=env, text=True, stdout=subprocess.PIPE, check=True)
    values = hashes.stdout.splitlines()
    if len(values) != len(uncached) or any(not value.isdecimal() for value in values):
        raise RuntimeError('Unexpected output from the pinned source-hash helper')
    source_hashes = dict(zip(uncached, values))
    visiting, completed, rebuilt = set(), {}, []

    def visit(name):
        if name in completed:
            return completed[name]
        if name not in modules:
            return None
        if name in visiting:
            raise RuntimeError('Cyclic local import: ' + name)
        visiting.add(name)
        source, prefix = modules[name]
        content = source.read_bytes()
        imports = re.findall(r'(?m)^\s*import\s+([\w.]+)', lean_code(content.decode()))
        deps = {dep: visit(dep) for dep in imports if dep in modules}
        source_hash = hashlib.sha256(content).hexdigest()
        signature = hashlib.sha256(json.dumps([source_hash, deps], sort_keys=True).encode()).hexdigest()
        output = OBJECTS / (name.replace('.', '/') + '.olean')
        prior = state.get(name)
        if prior is not None:
            stale = prior['signature'] != signature or not output.is_file()
        else:
            trace_path = output.with_suffix('.trace')
            trace = json.loads(trace_path.read_text()) if trace_path.is_file() else {}
            suffix = '/' + name.replace('.', '/') + '.lean'
            recorded = [value for caption, value in trace.get('inputs', [])
                        if caption.endswith(suffix) and isinstance(value, str)]
            stale = (not output.is_file() or
                     recorded != [source_hashes[name]] or
                     any(dep in rebuilt for dep in deps))
        if stale:
            output.parent.mkdir(parents=True, exist_ok=True)
            print('Direct Lean build: ' + name, flush=True)
            subprocess.run(['lean', '-s', '65536', '-j', '1', '--root=' + str(prefix),
                            '-o', str(output), '-i', str(output.with_suffix('.ilean')),
                            str(source)], cwd=ROOT, env=env, check=True)
            rebuilt.append(name)
        state[name] = {'signature': signature, 'source_sha256': source_hash}
        visiting.remove(name)
        completed[name] = signature
        return signature

    try:
        for target in targets:
            if target not in modules:
                raise RuntimeError('Only local Lean module targets are supported: ' + target)
            visit(target)
    finally:
        STATE.parent.mkdir(parents=True, exist_ok=True)
        STATE.write_text(json.dumps(state, indent=2, sort_keys=True) + '\n')
    print(f'Direct cached build passed: {len(completed)} local modules; '
          f'{len(rebuilt)} recompiled; dependency directories read only.', flush=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('targets', nargs='+')
    args = parser.parse_args()
    build(args.targets)


if __name__ == '__main__':
    try:
        main()
    except (RuntimeError, subprocess.CalledProcessError) as error:
        print(str(error), file=sys.stderr)
        raise SystemExit(1)
