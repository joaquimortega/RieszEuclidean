#!/usr/bin/env python3
"""Audit every manifest target with Lean's builtin transitive-axiom collector.

Share the builtin visitor's state across roots to compute their exact axiom
union without traversing common dependencies thousands of times. A union
contained in ALLOWED certifies every root. ProofAudit.lean retains the slower
individual #print axioms interface when per-declaration reports are wanted.
"""
from pathlib import Path
import json
import re
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}
manifest = json.loads((ROOT / 'blueprint/manifest.json').read_text())
expected = {name for node in manifest['nodes']
            for name in node['declarations']}
assert expected, 'Empty axiom inventory'
assert all(re.fullmatch(r"[\w.']+", name) for name in expected), 'Unsupported declaration name'
individual = re.findall(r'^#print axioms (\S+)\s*$',
                        (ROOT / 'RieszEuclidean/ProofAudit.lean').read_text(), re.M)
assert len(individual) == len(set(individual)), 'Duplicate individual audit target'
assert set(individual) == expected, 'Individual audit file and manifest disagree'
names = ',\n    '.join('``' + name for name in sorted(expected))
source = '''import RieszEuclidean
import Lean.Util.CollectAxioms
import Lean.Elab.Command
open Lean Elab Command

run_cmd do
  let env ← getEnv
  let roots : Array Name := #[
    ''' + names + ''']
  for root in roots do
    unless (env.checked.get.find? root).isSome do
      throwError "Missing checked target: {root}"
  -- Use the pinned builtin recursive visitor unchanged. Sharing state is
  -- correct for the union; no per-root axiom sets are inferred from this state.
  let (_, state) := ((roots.forM CollectAxioms.collect).run env).run {}
  let axioms := state.axioms.qsort Name.lt
  for root in roots do
    logInfo m!"TARGET '{root}'"
  logInfo m!"UNION {axioms.toList}"
  for axiomName in axioms do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unexpected transitive axiom: {axiomName}"
'''
with tempfile.TemporaryDirectory(prefix='riesz-axiom-audit-') as directory:
    path = Path(directory) / 'Audit.lean'
    path.write_text(source)
    result = subprocess.run(['lake', 'env', 'lean', '-DwarningAsError=true', str(path)],
                            cwd=ROOT, capture_output=True, text=True)
print(result.stdout, end='')
if result.stderr:
    print(result.stderr, end='')
assert result.returncode == 0, 'Lean transitive axiom audit failed'
targets = re.findall(r"^TARGET '(.+)'$", result.stdout, re.M)
assert len(targets) == len(set(targets)), 'Duplicate reported target'
assert set(targets) == expected, f'Axiom inventory mismatch: {set(targets)^expected}'
unions = re.findall(r'^UNION \[([^\]]*)\]$', result.stdout, re.M)
assert len(unions) == 1, 'Missing or duplicate axiom union'
axioms = {name.strip() for name in unions[0].split(',') if name.strip()}
assert axioms <= ALLOWED, f'Unexpected transitive axioms: {axioms-ALLOWED}'
print(f'Checked transitive axiom union of {len(targets)} declarations; standard Lean axioms only.')
