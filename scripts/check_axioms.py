#!/usr/bin/env python3
"""Elaborate the public audit file and reject nonstandard transitive axioms."""
from pathlib import Path
import json
import re
import subprocess

ROOT = Path(__file__).resolve().parents[1]
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}
manifest = json.loads((ROOT / 'blueprint/manifest.json').read_text())
expected = {name for node in manifest['nodes']
            for name in node['declarations']}
result = subprocess.run(['lake', 'env', 'lean', 'RieszEuclidean/ProofAudit.lean'],
                        cwd=ROOT, capture_output=True, text=True)
print(result.stdout, end='')
if result.stderr:
    print(result.stderr, end='')
assert result.returncode == 0, 'Lean axiom-report elaboration failed'
reports = dict(re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", result.stdout, re.S))
for name in re.findall(r"'([^']+)' does not depend on any axioms", result.stdout):
    reports[name] = ''
assert set(reports) == expected, f'Axiom inventory mismatch: {set(reports)^expected}'
for name, value in reports.items():
    axioms = {x.strip() for x in value.split(',') if x.strip()}
    assert axioms <= ALLOWED, f'Unexpected axioms for {name}: {axioms-ALLOWED}'
print(f'Checked {len(reports)} transitive axiom reports; standard Lean axioms only.')
