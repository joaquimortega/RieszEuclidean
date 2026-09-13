#!/usr/bin/env python3
"""Check source fidelity and development inventory, not mathematical truth.

Lean compilation and axiom reports are separate gates. --require-complete refuses
unfinished full-paper obligations even if the implemented files contain no holes.
"""
from pathlib import Path
import argparse
import hashlib
import json
import re

ROOT = Path(__file__).resolve().parents[1]


def uncomment(text):
    result, i, depth = [], 0, 0
    while i < len(text):
        if text.startswith('/-', i):
            depth += 1
            i += 2
        elif depth and text.startswith('-/', i):
            depth -= 1
            i += 2
        elif depth:
            result.append('\n' if text[i] == '\n' else ' ')
            i += 1
        elif text.startswith('--', i):
            end = text.find('\n', i)
            i = len(text) if end < 0 else end
        else:
            result.append(text[i])
            i += 1
    assert depth == 0, 'Unterminated block comment'
    return ''.join(result)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--require-complete', action='store_true')
    args = parser.parse_args()
    data = json.loads((ROOT / 'blueprint/manifest.json').read_text())
    source = ROOT / data['manuscript']['file']
    assert hashlib.sha256(source.read_bytes()).hexdigest() == data['manuscript']['sha256'], 'Stale paper hash'
    tex = source.read_text()
    assert data['repository'] in tex, 'Wrong manuscript repository link'
    labels = set(re.findall(r'\\label\{([^}]+)\}', tex))
    theorem_labels = set(re.findall(r'\\begin\{(?:theorem|lemma|proposition|corollary)\}'
        r'(?:\[[^\]]*\])?\s*\\label\{([^}]+)\}', tex))
    graph = {n['id']: n for n in data['nodes']}
    assert len(graph) == len(data['nodes']), 'Duplicate node ID'
    covered, visited, active = set(), set(), set()
    audit = (ROOT / 'RieszEuclidean/ProofAudit.lean').read_text()

    def visit(key):
        assert key in graph, f'Unknown node {key}'
        assert key not in active, f'Cycle at {key}'
        if key in visited:
            return
        active.add(key)
        for dep in graph[key]['dependencies']:
            visit(dep)
        active.remove(key)
        visited.add(key)

    for node in data['nodes']:
        visit(node['id'])
        assert set(node['source_labels']) <= labels, f"Missing source label: {node['id']}"
        covered.update(node['source_labels'])
        assert node['status'] in {'proved', 'pending'}
        if node['status'] == 'proved':
            assert node['file'] and (ROOT / node['file']).is_file()
            assert all(graph[d]['status'] == 'proved' for d in node['dependencies'])
            for name in node['declarations']:
                assert f'#print axioms {name}\n' in audit, f'Missing axiom audit {name}'
    assert theorem_labels <= covered, f'Untracked manuscript results: {theorem_labels-covered}'
    for filename, digest in data['proof_source_sha256'].items():
        assert hashlib.sha256((ROOT / filename).read_bytes()).hexdigest() == digest, f'Stale Lean hash: {filename}'
    umbrella = (ROOT / 'RieszEuclidean.lean').read_text()
    for path in sorted((ROOT / 'RieszEuclidean').glob('*.lean')):
        text = uncomment(path.read_text())
        assert not re.search(r'\b(?:sorry|admit|axiom|unsafe)\b', text), f'Untrusted source token: {path}'
        for imp in re.findall(r'^import\s+(\S+)', text, re.M):
            assert imp == 'RieszEuclidean' or imp.startswith(('RieszEuclidean.', 'Mathlib.')), f'External project import: {imp}'
        if path.stem != 'ProofAudit':
            assert f'import RieszEuclidean.{path.stem}\n' in umbrella, f'Unbuilt source module: {path}'
            assert str(path.relative_to(ROOT)) in data['proof_source_sha256']
    pending = [n['id'] for n in data['nodes'] if n['status'] != 'proved']
    assert data['complete'] == (not pending), 'False completion flag'
    print(f'Inventory checked: {len(graph)-len(pending)} proved-scope nodes; {len(pending)} pending full-paper obligations.')
    if args.require_complete:
        assert not pending, 'Full formalization incomplete: ' + ', '.join(pending)


if __name__ == '__main__':
    main()
