#!/usr/bin/env python3
"""Validate metadata against the vendored official v0.4 schema and project state."""
from pathlib import Path
import json
import yaml
import jsonschema

root = Path(__file__).resolve().parents[1]
data = yaml.safe_load((root / 'formalization.yaml').read_text())
schema = json.loads((root / 'schema/formalization-v0.4.schema.json').read_text())
jsonschema.Draft7Validator(schema).validate(data)
manifest = json.loads((root / 'blueprint/manifest.json').read_text())
assert data['alignment']['namespace'] == 'RieszEuclidean'
assert data['alignment']['complete_mapping'] == 'blueprint/manifest.json'
assert data['sources'][0]['id'] == manifest['repository'] + '/blob/main/paper/RieszEuclidean.tex'
for result in data['status']['main_results']:
    assert any(result['declaration'] in n['declarations'] and n['status'] == 'proved'
               for n in manifest['nodes']), 'Claimed result absent from proved inventory'
assert data['status']['sorry_count'] == 0
print('formalization.yaml: official v0.4 schema and project-state checks passed.')
