#!/usr/bin/env python3
"""Historical C2A checker probes; synthetic data, never candidate Lean output.

Run against PR #6 commit ce92b80. Refuses changed test/reference sources.
Writes only to a temporary input path and the requested evidence directory.
This is a review reproducer, not an ongoing production gate.
"""
from __future__ import annotations
import argparse
import copy
import hashlib
import importlib.util
import io
import json
from pathlib import Path
import tempfile
import unittest

EXPECTED = {
    'tests/test_ll_c2a.py': '21f98a0d84c9f38971eae2077c1c62dceb51a411',
    'll/ring_reference.py': '641d536ad219738af480c7bae159721aef49e5bd',
}


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root', type=Path, required=True)
    parser.add_argument('--out', type=Path, required=True)
    args = parser.parse_args()
    root = args.root.resolve()
    hashes = {}
    for name, expected in EXPECTED.items():
        data = (root / name).read_bytes()
        actual = hashlib.sha1(f'blob {len(data)}\0'.encode() + data).hexdigest()
        hashes[name] = actual
        if actual != expected:
            raise SystemExit(f'Refusing changed historical source {name}: {actual}')
    spec = importlib.util.spec_from_file_location('review_c2a_tests', root / 'tests/test_ll_c2a.py')
    if spec is None or spec.loader is None:
        raise SystemExit('Could not load historical tests')
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    control = {'source': 'SYNTHETIC REVIEWER DATA; NOT LEAN OUTPUT',
               'orders': [0, 1, 2, 3, 4], 'values': []}
    for name, fx in module.FIXTURES.items():
        row = {'name': name, 'N': len(fx['G']), 'i': fx['i'], 'j': fx['j']}
        for k in control['orders']:
            row[f'k{k}'] = str(module.ref.ring_contribution_matrix(
                fx['G'], fx['v'], fx['i'], fx['j'], k))
        control['values'].append(row)
    cases = {'synthetic_valid_control': copy.deepcopy(control)}
    bad = copy.deepcopy(control)
    bad['values'][0]['k3'] = '999999'
    cases['ordinary_wrong_value_control'] = bad
    bad = copy.deepcopy(control)
    duplicate = dict(bad['values'][0]); duplicate['k3'] = '999999'
    bad['values'].insert(0, duplicate)
    cases['wrong_duplicate_before_correct_row'] = bad
    bad = copy.deepcopy(control)
    bad['values'][0]['i'] = bad['values'][0]['j'] = 999
    cases['out_of_bounds_external_indices'] = bad
    bad = copy.deepcopy(control); bad['values'][0]['N'] = 999
    cases['false_dimension'] = bad
    bad = copy.deepcopy(control); bad['orders'] = [0, 3]
    bad['values'][0]['k4'] = '999999'
    cases['candidate_hides_wrong_k4_by_selecting_orders'] = bad
    args.out.mkdir(parents=True, exist_ok=True)
    evidence = {'reviewed_commit': 'ce92b809897bbe3fa4268870eaef72e7741755b1',
                'input_origin': 'synthetic Python reference values, not Lean output',
                'git_blob_hashes': hashes, 'cases': {}}
    with tempfile.TemporaryDirectory(prefix='ll-c2a-probe-') as temp:
        module.VALUES = Path(temp) / 'synthetic.json'
        for name, data in cases.items():
            module.VALUES.write_text(json.dumps(data))
            stream = io.StringIO()
            suite = unittest.defaultTestLoader.loadTestsFromModule(module)
            result = unittest.TextTestRunner(stream=stream, verbosity=2).run(suite)
            (args.out / f'{name}.log').write_text(stream.getvalue())
            outcome = {'tests': result.testsRun, 'failures': len(result.failures),
                       'errors': len(result.errors), 'successful': result.wasSuccessful()}
            evidence['cases'][name] = outcome
            print(name, outcome, flush=True)
    (args.out / 'checker_probe.json').write_text(json.dumps(evidence, indent=2) + '\n')
    expected_fail = evidence['cases']['ordinary_wrong_value_control']
    okay = expected_fail['failures'] == 1 and expected_fail['errors'] == 0
    okay = okay and all(v['successful'] and v['tests'] == 13
                        for k, v in evidence['cases'].items()
                        if k != 'ordinary_wrong_value_control')
    return 0 if okay else 1


if __name__ == '__main__':
    raise SystemExit(main())
