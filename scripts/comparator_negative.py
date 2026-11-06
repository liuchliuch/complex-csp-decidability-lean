#!/usr/bin/env python3
"""Require official Comparator rejection of two mutations of a current goal.

All synthetic sources and logs stay under .lake. The temporary build adapter
compiles these small modules with Lean directly; it never edits dependencies or
the trusted specification. Matching a diagnostic as well as a nonzero exit code
prevents a missing executable or failed compilation from counting as rejection.
"""
import json
import os
from pathlib import Path
import subprocess
import sys

from cached_build import ROOT, environment


def build_adapter(directory, env):
    """Compile a native launcher accepted by Landrun's existing execute policy.

The sandbox permits the Lean toolchain and the project's .lake directory.
A Python shebang would require additional interpreter permissions and is not
an ELF executable for Landrun's dependency inspection on Linux.
"""
    adapter = directory / 'bin'
    adapter.mkdir(exist_ok=True)
    output = directory / '.lake/build/lib/lean'
    output.mkdir(parents=True, exist_ok=True)
    prefix = Path(subprocess.check_output(['lean', '--print-prefix'], cwd=ROOT, text=True).strip())
    lean = prefix / 'bin/lean'
    if not os.access(lean, os.X_OK):
        raise RuntimeError('Missing toolchain Lean executable: ' + str(lean))
    lean_path = str(output) + os.pathsep + env['LEAN_PATH']
    literal = lambda value: json.dumps(str(value))
    source = adapter / 'lake.c'
    source.write_text(f'''#define _POSIX_C_SOURCE 200809L
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

int main(int argc, char **argv) {{
    if (argc != 3 || strcmp(argv[1], "build") != 0 ||
        (strcmp(argv[2], "Challenge") != 0 && strcmp(argv[2], "Solution") != 0)) {{
        fputs("probe adapter accepts Challenge or Solution build only\\n", stderr);
        return 2;
    }}
    int challenge = strcmp(argv[2], "Challenge") == 0;
    char *source = challenge ? {literal(directory / 'Challenge.lean')} : {literal(directory / 'Solution.lean')};
    char *object = challenge ? {literal(output / 'Challenge.olean')} : {literal(output / 'Solution.olean')};
    if (setenv("LEAN_PATH", {literal(lean_path)}, 1) != 0) {{ perror("setenv"); return 2; }}
    char *args[] = {{{literal(lean)}, "-s", "65536", "-j", "1",
                    {literal('--root=' + str(directory))}, "-o", object, source, NULL}};
    execv(args[0], args);
    perror("execv Lean");
    return 2;
}}
''')
    subprocess.run(['cc', '-std=c11', '-O2', str(source), '-o', str(adapter / 'lake')],
                   cwd=ROOT, check=True)
    return adapter


def main():
    config = json.loads((ROOT / 'verification/comparator.json').read_text())
    # Exercise a concrete claim in the current paper, not an unrelated toy goal.
    name = next(n for n in config['theorem_names'] if n.endswith('_doubledUnary_first_value'))
    namespace, short = name.rsplit('.', 1)
    proposition = 'ComplexCSP.PaperStatements.' + short
    challenge = (f'import verification.Statements\nnamespace {namespace}\n'
                 f'theorem {short} : {proposition} := by sorry\nend {namespace}\n')
    cases = {
        'statement-mismatch': (
            f'import verification.Statements\nnamespace {namespace}\n'
            f'theorem {short} : True := True.intro\nend {namespace}\n',
            'Challenge and solution theorem statement do not match'),
        'forbidden-axiom': (
            f'import verification.Statements\nnamespace {namespace}\n'
            f'axiom injectedProof : {proposition}\n'
            f'theorem {short} : {proposition} := injectedProof\nend {namespace}\n',
            'Illegal axiom detected'),
    }
    results = {}
    for case, (solution, diagnostic) in cases.items():
        directory = ROOT / '.lake/verification/negative-controls' / case
        directory.mkdir(parents=True, exist_ok=True)
        (directory / 'Challenge.lean').write_text(challenge)
        (directory / 'Solution.lean').write_text(solution)
        probe_config = dict(config, challenge_module='Challenge', solution_module='Solution',
                            theorem_names=[name])
        (directory / 'comparator.json').write_text(json.dumps(probe_config, indent=2) + '\n')
        # Comparator asks `lake build <module>`. For generated probes this
        # deliberately narrow adapter performs precisely that Lean compilation.
        env = environment()
        adapter = build_adapter(directory, env)
        env['PATH'] = str(adapter) + os.pathsep + os.environ['PATH']
        env['LEAN_PATH'] = str(directory / '.lake/build/lib/lean') + os.pathsep + env['LEAN_PATH']
        print('Official Comparator negative control: ' + case, flush=True)
        # Keep the trusted project as Comparator's sandbox root. Probe sources
        # and objects are still isolated below its .lake directory.
        result = subprocess.run(['comparator', str(directory / 'comparator.json')], cwd=ROOT,
                                env=env, text=True, stdout=subprocess.PIPE,
                                stderr=subprocess.STDOUT)
        (directory / 'result.log').write_text(result.stdout)
        if result.returncode == 0 or diagnostic not in result.stdout:
            print(result.stdout, file=sys.stderr)
            raise RuntimeError('Negative control did not reject for the expected reason: ' + case)
        results[case] = {'result': 'rejected', 'exit_code': result.returncode,
                         'diagnostic': diagnostic, 'goal': name}
        print(case + ': rejected for the expected reason.', flush=True)
    (ROOT / '.lake/verification/negative-controls/results.json').write_text(
        json.dumps(results, indent=2) + '\n')
    print('Official Comparator negative controls passed.', flush=True)


if __name__ == '__main__':
    try:
        main()
    except (RuntimeError, subprocess.CalledProcessError) as error:
        print(str(error), file=sys.stderr)
        raise SystemExit(1)
