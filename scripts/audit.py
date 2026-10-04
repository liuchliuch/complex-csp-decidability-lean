#!/usr/bin/env python3
"""Audit release hygiene, proof imports, and the fixed paper correspondence."""
import argparse
import hashlib
import json
from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parents[1]
IGNORED = {'.lake', '.git', '__pycache__'}
ALLOWED_AXIOMS = {'propext', 'Classical.choice', 'Quot.sound'}

def files():
    return sorted(p for p in ROOT.rglob('*') if p.is_file()
                  and not any(x in IGNORED for x in p.relative_to(ROOT).parts))

def sha(data):
    return hashlib.sha256(data).hexdigest()

def source_digest():
    h = hashlib.sha256()
    for p in files():
        name = p.relative_to(ROOT).as_posix()
        if name == 'verification/release.json':
            continue
        h.update(name.encode() + b'\0' + p.read_bytes() + b'\0')
    return h.hexdigest()

def lean_code(text):
    """Erase nested comments and strings while preserving line boundaries."""
    out = list(text)
    i, depth, string = 0, 0, False
    while i < len(text):
        if depth:
            if text.startswith('/-', i):
                out[i:i+2] = '  '; depth += 1; i += 2
            elif text.startswith('-/', i):
                out[i:i+2] = '  '; depth -= 1; i += 2
            else:
                if text[i] != '\n': out[i] = ' '
                i += 1
        elif string:
            if text[i] == '\\':
                out[i:i+2] = '  '; i += 2
            else:
                if text[i] == '"': string = False
                if text[i] != '\n': out[i] = ' '
                i += 1
        elif text.startswith('/-', i):
            out[i:i+2] = '  '; depth = 1; i += 2
        elif text.startswith('--', i):
            end = text.find('\n', i)
            if end < 0: end = len(text)
            out[i:end] = ' ' * (end-i); i = end
        elif text[i] == '"':
            out[i] = ' '; string = True; i += 1
        else:
            i += 1
    if depth or string:
        raise ValueError('unterminated Lean comment or string')
    return ''.join(out)

def require(condition, message):
    if not condition: raise ValueError(message)

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--release', action='store_true', help='require the exact verified release source digest')
    args = parser.parse_args()
    all_files = files()
    modules = {}
    graph = {}
    for p in all_files:
        rel = p.relative_to(ROOT).as_posix()
        require(not p.is_symlink(), 'release contains a symlink: ' + rel)
        require(p.suffix not in {'.log', '.olean', '.ilean', '.pyc', '.zip', '.gz', '.tar'},
                'generated or redundant artifact: ' + rel)
        require(p.name != '.DS_Store', 'OS metadata: ' + rel)
        text = p.read_text()
        require(not re.search(r'[\u3400-\u9fff]', text), 'non-English release text: ' + rel)
        require(not re.search(r'/(Users|workspace|home)/[\w.-]+', text), 'machine-specific path: ' + rel)
        if p.suffix != '.lean': continue
        code = lean_code(text)
        require('⋯' not in code, 'elided Lean term: ' + rel)
        require(not re.search(r'\b(admit|axiom|unsafe|native_decide|sorryAx)\b', code),
                'forbidden proof construct: ' + rel)
        require(not re.search(r'\bsorry\b', code) or rel == 'verification/Challenge.lean',
                'proof hole outside Challenge: ' + rel)
        require(not re.search(r'@\[\s*extern\b', code), 'external proof implementation: ' + rel)
        if rel.startswith('ComplexCSP'):
            name = rel[:-5].replace('/', '.')
        elif rel.startswith('vendor/plgh/PlanarHom/'):
            name = rel[len('vendor/plgh/'):-5].replace('/', '.')
        else:
            name = rel[:-5].replace('/', '.')
        modules[name] = rel
        graph[name] = re.findall(r'(?m)^\s*import\s+([\w.]+)', code)
        if rel != 'verification/Challenge.lean':
            require('verification.Challenge' not in graph[name], 'Challenge imported by proof code: ' + rel)
    needed = set()
    def visit(name):
        if name in needed or name not in modules: return
        needed.add(name)
        for dep in graph[name]:
            if dep.startswith(('ComplexCSP', 'PlanarHom')):
                require(dep in modules, 'missing local import: ' + dep)
            visit(dep)
    visit('ComplexCSP')
    production = {m for m in modules if m.startswith(('ComplexCSP', 'PlanarHom'))}
    require(production == needed, 'unused production modules: ' + ', '.join(sorted(production-needed)))
    mapping = json.loads((ROOT/'verification/paper.json').read_text())
    paper = ROOT/mapping['paper']['tex_file']
    require(sha(paper.read_bytes()) == mapping['paper']['tex_sha256'], 'original paper source changed')
    bib = ROOT/mapping['paper']['bib_file']
    require(sha(bib.read_bytes()) == mapping['paper']['bib_sha256'], 'original bibliography changed')
    lines = paper.read_text().splitlines()
    items = mapping['statements']
    require(len(items) == 36 and sum(x['kind'] in {'theorem','lemma','corollary'} for x in items) == 31,
            'paper inventory is incomplete')
    config = json.loads((ROOT/'verification/comparator.json').read_text())
    require(set(config['permitted_axioms']) == ALLOWED_AXIOMS, 'unexpected comparator axiom policy')
    require(config['enable_nanoda'] is False, 'checker mode differs from the documented mode')
    names = config['theorem_names']
    require(len(names) == len(set(names)), 'duplicate comparator target')
    solution = lean_code((ROOT/'verification/Solution.lean').read_text())
    challenge = lean_code((ROOT/'verification/Challenge.lean').read_text())
    spec = lean_code((ROOT/'verification/Statements.lean').read_text())
    for name in names:
        short = name.rsplit('.', 1)[1]
        require(re.search(r'\btheorem\s+'+re.escape(short)+r'\b', challenge), 'missing challenge: ' + name)
        require(re.search(r'\btheorem\s+'+re.escape(short)+r'\b', solution), 'missing solution: ' + name)
        require(re.search(r'\bdef\s+'+re.escape(short)+r'\b', spec), 'missing proposition: ' + name)
    for item in items:
        a,b = item['source_range']['start_line'],item['source_range']['end_line']
        statement = '\n'.join(lines[a-1:b])
        require(statement == item['statement_tex'] and sha(statement.encode()) == item['statement_sha256'],
                'paper statement mismatch: ' + item['number'])
        if item['kind'] in {'theorem','lemma','corollary'}:
            require(bool(item['goals']), 'unmapped proof statement: ' + item['number'])
        for goal in item['goals']:
            require(goal in names, 'paper goal missing from Comparator: ' + goal)
        for decl in item['declarations']:
            require((ROOT/decl['file']).is_file(), 'missing declaration source: ' + decl['file'])
    receipt = ROOT/'verification/release.json'
    digest = source_digest()
    if args.release:
        require(receipt.exists(), 'missing verified release receipt')
        require(json.loads(receipt.read_text())['source_tree_sha256'] == digest, 'source differs from verified release')
    print(json.dumps({'production_modules':len(production), 'paper_items':len(items),
                      'comparator_goals':len(names), 'source_tree_sha256':digest}, indent=2))
    print('Release source audit passed.')

if __name__ == '__main__':
    try:
        main()
    except (ValueError, OSError, KeyError) as error:
        print('Audit failed: ' + str(error), file=sys.stderr)
        raise SystemExit(1)
