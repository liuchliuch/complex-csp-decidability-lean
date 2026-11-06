#!/usr/bin/env python3
"""Audit release hygiene, proof imports, and the fixed paper correspondence."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parents[1]
IGNORED = {'.lake', '.git', '__pycache__'}
ALLOWED_AXIOMS = {'propext', 'Classical.choice', 'Quot.sound'}

def files():
    result = []
    for directory, subdirectories, names in os.walk(ROOT):
        subdirectories[:] = [name for name in subdirectories if name not in IGNORED]
        result.extend(Path(directory) / name for name in names)
    return sorted(result)

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

PROOF_KINDS = {'theorem', 'lemma', 'corollary', 'proposition', 'claim'}
NUMBERED_KINDS = PROOF_KINDS | {'definition', 'remark', 'procedure'}

def paper_inventory(text):
    """Read this manuscript's shared theorem counter independently of its map.

    This intentionally supports the explicit section, full-paper and appendix
    counter setup in the archived self-contained source. No generated .aux file
    or TeX installation is required for the release audit.
    """
    lines = text.splitlines()
    section = counter = 0
    full = appendix = False
    found = []
    i = 0
    while i < len(lines):
        line = re.split(r'(?<!\\)%', lines[i], maxsplit=1)[0]
        if r'\setcounter{section}{0}' in line:
            section = counter = 0
        if r'\renewcommand{\thesection}{F.\arabic{section}}' in line:
            full = True
        if re.match(r'\s*\\appendix\b', line):
            appendix = True
            section = counter = 0
        if re.match(r'\s*\\section\{', line):
            section += 1
            counter = 0
        match = re.match(r'\s*\\begin\{(' + '|'.join(sorted(NUMBERED_KINDS)) + r')\}', line)
        if match:
            kind = match[1]
            counter += 1
            start = i
            while i < len(lines) and ('\\end{' + kind + '}') not in lines[i]:
                i += 1
            require(i < len(lines), 'unterminated paper statement at line ' + str(start + 1))
            statement = '\n'.join(lines[start:i+1])
            title = re.match(r'\s*\\begin\{[^}]+\}(?:\[(.*)\])?', lines[start])
            title_tex = title.group(1) or ''
            labels = re.findall(r'\\label\{([^}]+)\}', statement)
            require(bool(labels), 'unlabelled numbered statement at line ' + str(start + 1))
            section_name = chr(ord('A') + section - 1) if appendix else str(section)
            number = ('F.' if full else '') + section_name + '.' + str(counter)
            found.append({'number': number, 'kind': kind, 'label': labels[0],
                          'source_range': {'start_line': start + 1, 'end_line': i + 1},
                          'statement_tex': statement, 'title_tex': title_tex,
                          'part': 'appendix' if appendix else 'full' if full else 'short'})
        i += 1
    return found

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--release', action='store_true', help='require the exact verified release source digest')
    args = parser.parse_args()
    mapping = json.loads((ROOT/'verification/paper.json').read_text())
    require(mapping['schema_version'] == 2, 'unexpected paper-map schema')
    pdf_name = mapping['paper']['pdf_file']
    all_files = files()
    modules = {}
    graph = {}
    for p in all_files:
        rel = p.relative_to(ROOT).as_posix()
        require(not p.is_symlink(), 'release contains a symlink: ' + rel)
        require(p.suffix not in {'.log', '.olean', '.ilean', '.pyc', '.zip', '.gz', '.tar'},
                'generated or redundant artifact: ' + rel)
        require(p.name != '.DS_Store', 'OS metadata: ' + rel)
        if p.suffix == '.pdf':
            require(rel == pdf_name, 'unexpected binary artifact: ' + rel)
            require(p.read_bytes().startswith(b'%PDF-'), 'invalid paper PDF header')
            continue
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
    paper = ROOT/mapping['paper']['tex_file']
    require(sha(paper.read_bytes()) == mapping['paper']['tex_sha256'], 'current paper source changed')
    pdf = ROOT/pdf_name
    require(pdf.is_file(), 'missing current paper PDF')
    require(sha(pdf.read_bytes()) == mapping['paper']['pdf_sha256'], 'current paper PDF changed')
    require(mapping['paper']['bibliography'] == 'embedded in the self-contained TeX source',
            'unexpected bibliography provenance')
    historical = mapping['historical_arxiv_v1']
    old_map = ROOT/historical['map_file']
    require(sha(old_map.read_bytes()) == historical['map_sha256'], 'historical paper map changed')
    old_paper = historical['paper']
    for kind in ['tex', 'bib']:
        require(sha((ROOT/old_paper[kind + '_file']).read_bytes()) == old_paper[kind + '_sha256'],
                'historical arXiv v1 ' + kind + ' changed')
    items = mapping['statements']
    parsed = paper_inventory(paper.read_text())
    require(len(items) == len(parsed), 'paper inventory is incomplete')
    require(len({x['label'] for x in items}) == len(items), 'duplicate paper label')
    for item, source in zip(items, parsed):
        for key in ['number', 'kind', 'label', 'source_range', 'statement_tex', 'title_tex', 'part']:
            require(item[key] == source[key], 'paper inventory mismatch for ' + key + ': ' + source['label'])
        require(sha(source['statement_tex'].encode()) == item['statement_sha256'],
                'paper statement hash mismatch: ' + item['label'])
    counts = {'total': len(parsed), 'proof_statements': sum(x['kind'] in PROOF_KINDS for x in parsed)}
    counts.update({part: sum(x['part'] == part for x in parsed) for part in ['short', 'full', 'appendix']})
    require(all(mapping['inventory'][key] == value for key, value in counts.items()),
            'paper inventory summary differs from source')
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
    mapped_goals = set()
    labels = {x['label']: x for x in items}
    for item in items:
        if item['kind'] in PROOF_KINDS or item['label'] == 'rem:simple-instance-counterexample':
            require(bool(item['goals']), 'unmapped proof statement: ' + item['number'])
        if item['part'] == 'short':
            target = labels[item['full_paper_label']]
            require(item['goals'] == target['goals'], 'short/full goal mismatch: ' + item['label'])
        for goal in item['goals']:
            require(goal in names, 'paper goal missing from Comparator: ' + goal)
            mapped_goals.add(goal)
        for decl in item['declarations']:
            require((ROOT/decl['file']).is_file(), 'missing declaration source: ' + decl['file'])
    require(mapped_goals == set(names), 'Comparator goals missing from current paper map')
    require(labels['thm:young-pinned']['status'] == 'proved', 'current pinned theorem mislabeled')
    require(labels['rem:simple-instance-counterexample']['status'] == 'proved_counterexample',
            'current appendix counterexample mislabeled')
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
