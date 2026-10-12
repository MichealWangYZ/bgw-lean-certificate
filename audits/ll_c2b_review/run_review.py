#!/usr/bin/env python3
"""C2B reviewer checks. All input tables are SYNTHETIC, not Lean output.

Checks the submitted Python surface and independent finite mathematics.
Does NOT execute Lean, certify the kernel, or reproduce the full repository gate.
Requires SymPy only for this standalone review reproducer, not for the project.
"""
from pathlib import Path
from fractions import Fraction as F
import argparse, copy, hashlib, importlib.util, io, json, subprocess, sys, tempfile, unittest
import sympy as sp

HERE = Path(__file__).resolve().parent
EXPECTED = {
    'll/screening_reference.py': '56a312e2e0d7cfa559b25c030f82e12811bb58a0',
    'll/evidence.py': 'c4824ae1c1963248d08d1271780d1a08994ad7f0',
    'tests/test_ll_c2b.py': 'efae546564bd53c46538e73b3916b8ecb5e25087',
    'll/ring_reference.py': '641d536ad219738af480c7bae159721aef49e5bd',
    'audits/ll_c2a_review/checker_probe.py': '0cd0532410dbea20cdf66406ae2b4c77558ed5a1',
}


def load(path, name):
    spec = importlib.util.spec_from_file_location(name, path)
    if spec is None or spec.loader is None:
        raise RuntimeError(f'Cannot load {path}')
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


def frac(x):
    return F(int(sp.numer(x)), int(sp.denom(x)))


def matrix_json(M):
    return [[str(frac(M[i, j])) for j in range(M.cols)] for i in range(M.rows)]


def s_matrix(A):
    return sp.Matrix([[sp.Rational(x.numerator, x.denominator) for x in row] for row in A])


def run(repo, out):
    out.mkdir(parents=True, exist_ok=True)
    hashes = {}
    for rel, expected in EXPECTED.items():
        b = (repo / rel).read_bytes()
        h = hashlib.sha1(f'blob {len(b)}\0'.encode() + b).hexdigest()
        if h != expected:
            raise RuntimeError(f'Historical source changed: {rel}; refusing to run as if unchanged')
        hashes[rel] = h
    m = load(repo / 'tests/test_ll_c2b.py', 'candidate_c2b_tests')
    rr = load(repo / 'll/ring_reference.py', 'ring_reference')
    sr = m.sr
    ev = m.evidence
    table = {
        'reviewer_input': 'SYNTHETIC: SymPy W coefficients plus direct Python graph contractions; NOT Lean output',
        'orders': list(range(5)),
        'bridges': ['GW.LL.coeff_W', 'GW.LL.coeff_T_eq_Tcoeff'],
        'values': [],
    }
    graph_entries = 0
    for name, fx in m.FIXTURES.items():
        G, v = s_matrix(fx['G']), s_matrix(fx['v'])
        B = G.multiply_elementwise(G)
        row = {'name': name, 'N': G.rows, 'i': fx['i'], 'j': fx['j'], 'W': {}, 'T': {}}
        for k in range(5):
            W = (-sp.Rational(1, 2)) ** k * v * (B * v) ** k
            T = [[rr.ring_contribution_contraction(fx['G'], fx['v'], i, j, k)
                  for j in range(G.cols)] for i in range(G.rows)]
            assert T == [[frac(-G[i, j] * W[i, j]) for j in range(G.cols)] for i in range(G.rows)]
            assert sr.w_closed(fx['G'], fx['v'], k) == [[frac(W[i, j]) for j in range(G.cols)] for i in range(G.rows)]
            graph_entries += G.rows * G.cols
            row['W'][str(k)] = matrix_json(W)
            row['T'][str(k)] = [[str(x) for x in r] for r in T]
        table['values'].append(row)
    cases = {}

    def evaluate(label, data):
        with tempfile.TemporaryDirectory(prefix='c2b_review_') as td:
            p = Path(td) / 'synthetic.json'
            p.write_text(json.dumps(data))
            m.VALUES = p
            log = io.StringIO()
            res = unittest.TextTestRunner(stream=log, verbosity=2).run(
                unittest.defaultTestLoader.loadTestsFromModule(m))
        (out / f'{label}.log').write_text(log.getvalue())
        cases[label] = {'tests_run': res.testsRun, 'failures': len(res.failures),
                        'errors': len(res.errors), 'accepted': res.wasSuccessful()}

    evaluate('synthetic_control', table)
    d = copy.deepcopy(table); d['values'][0]['W']['3'][0][0] = '999/1'
    evaluate('ordinary_wrong_W', d)
    d = copy.deepcopy(table); d['values'][0]['T']['4'][0][1] = '999/1'
    evaluate('ordinary_wrong_T', d)
    d = copy.deepcopy(table); bad = copy.deepcopy(d['values'][0])
    bad['W']['3'][0][0] = '999/1'; d['values'].insert(0, bad)
    evaluate('wrong_duplicate', d)
    d = copy.deepcopy(table); d['values'][0]['i'] = d['values'][0]['j'] = 999
    evaluate('invalid_indices', d)
    d = copy.deepcopy(table); d['values'][0]['N'] = 999
    evaluate('false_dimension', d)
    d = copy.deepcopy(table); d['orders'] = [0, 3]; d['values'][0]['W']['4'][0][0] = '999/1'
    evaluate('self_selected_orders', d)
    d = copy.deepcopy(table); d['orders'] = [0, 1, 2, 3, 3, 4]
    evaluate('duplicate_order', d)
    d = copy.deepcopy(table); del d['values'][0]['W']['4']
    evaluate('missing_degree', d)
    d = copy.deepcopy(table); d['values'][0]['W']['5'] = d['values'][0]['W']['4']
    evaluate('extra_degree', d)
    d = copy.deepcopy(table); del d['values'][0]['T']
    evaluate('missing_series', d)
    assert cases['synthetic_control']['accepted']
    assert all(not r['accepted'] for k, r in cases.items() if k != 'synthetic_control')

    # Independent generic inverse: noncommuting higher P coefficients.
    P = [sp.eye(2), sp.Matrix([[0, 1], [0, 0]]), sp.Matrix([[0, 0], [1, 0]])]
    P_py = [[[frac(A[i, j]) for j in range(2)] for i in range(2)] for A in P]
    S = [s_matrix(A) for A in sr.invert_series(P_py, 6)]
    for k in range(7):
        L = sum((P[j] * S[k-j] for j in range(min(k, len(P)-1)+1)), sp.zeros(2))
        R = sum((S[k-j] * P[j] for j in range(min(k, len(P)-1)+1)), sp.zeros(2))
        assert L == R == (sp.eye(2) if k == 0 else sp.zeros(2))

    # Extra cases outside the symmetric/invertible fixtures.
    extra_cases = [(sp.Matrix([[1, 2], [0, -1]]), sp.Matrix([[0, 1], [0, 0]])),
                   (sp.Matrix([[2, 1], [1, 2]]), sp.Matrix([[1, 2], [2, 4]])),
                   (sp.zeros(2), sp.Matrix([[1, 3], [4, 5]]))]
    for G, v in extra_cases:
        B = G.multiply_elementwise(G)
        Gp = [[frac(G[i, j]) for j in range(2)] for i in range(2)]
        vp = [[frac(v[i, j]) for j in range(2)] for i in range(2)]
        actual = sr.all_routes_agree(Gp, vp, 6)
        for k, A in enumerate(actual):
            assert s_matrix(A) == (-sp.Rational(1, 2)) ** k * v * (B * v) ** k

    # Scalar readers also reject the previously demonstrated coverage attacks.
    scalar = {'orders': list(range(5)), 'values': []}
    for row in table['values']:
        scalar['values'].append(
            {key: row[key] for key in ('name', 'N', 'i', 'j')} |
            {f'k{k}': row['T'][str(k)][row['i']][row['j']] for k in range(5)})
    ev.validate_c2a(scalar, m.FIXTURES)
    scalar_probes = {}
    for kind in ('duplicate', 'index', 'dimension', 'coverage', 'missing_column', 'extra_column'):
        d = copy.deepcopy(scalar)
        if kind == 'duplicate': d['values'].insert(0, dict(d['values'][0]))
        elif kind == 'index': d['values'][0]['i'] = 999
        elif kind == 'dimension': d['values'][0]['N'] = 999
        elif kind == 'coverage': d['orders'] = [0, 3]; d['values'][0]['k4'] = '999/1'
        elif kind == 'missing_column': del d['values'][0]['k4']
        else: d['values'][0]['k5'] = '999/1'
        try:
            ev.validate_c2a(d, m.FIXTURES)
            scalar_probes[kind] = 'ACCEPTED'
        except ev.EvidenceError as e:
            scalar_probes[kind] = str(e)
        assert scalar_probes[kind] != 'ACCEPTED'

    # Nonblocking serializer observation, not a wrong-value bypass.
    d = copy.deepcopy(table); d['values'][0]['W']['0'][0][0] = True
    ev.validate_c2b(d, m.FIXTURES)
    d = copy.deepcopy(table); d['values'][0]['W']['0'][0][0] = 1.0
    ev.validate_c2b(d, m.FIXTURES)

    # Check the worker's reported exit-zero refusal on the actual archived script.
    with tempfile.TemporaryDirectory(prefix='c2b_archive_refusal_') as td:
        r = Path(td); (r / 'tests').mkdir()
        (r / 'tests/test_ll_c2a.py').write_text('# deliberate source mismatch for refusal test\n')
        c = subprocess.run([sys.executable, str(repo / 'audits/ll_c2a_review/checker_probe.py'),
                            '--root', td, '--out', str(r / 'out')], capture_output=True, text=True)
        archive_refusal = {'exit_code': c.returncode, 'stdout': c.stdout, 'stderr': c.stderr}
        assert c.returncode == 1
    fx = m.FIXTURES['N2-pd']; W = sr.all_routes_agree(fx['G'], fx['v'], 4)
    truncation_degree5 = sr.convolve(sr.pl_series(fx['G'], fx['v'], 4), W, 5)[5]
    assert any(x for row in truncation_degree5 for x in row)
    report = {
        'reviewed_commit': '63363c79ce73598810174f241e6907211b0c23d3',
        'input_kind': 'synthetic reference tables, NOT Lean execution',
        'git_blobs': hashes,
        'original_test_suite_probes': cases,
        'c2a_shared_validator_probes': scalar_probes,
        'independent_sympy_vs_direct_graph_entry_comparisons': graph_entries,
        'independent_sympy_vs_W_entry_comparisons': graph_entries,
        'generic_noncommuting_series_inverse': 'both products verified through degree 6',
        'extra_matrix_cases': 'nonsymmetric/nilpotent v, singular symmetric v, zero G; degrees 0..6',
        'archived_probe_refusal': archive_refusal,
        'first_omitted_truncated_product_coefficient': [[str(x) for x in row] for row in truncation_degree5],
        'serializer_note': 'bool and float numeric entries accepted by Fraction conversion; no wrong-value bypass demonstrated',
        'not_run': ['Lean/Lake build or axiom audit', 'candidate Lean executable',
                    'full repository gate', 'BerkeleyGW'],
    }
    (out / 'review_results.json').write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps(report, indent=2))


if __name__ == '__main__':
    if not __debug__:
        raise SystemExit('Run without -O: this historical review uses assertions.')
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--source', type=Path, required=True)
    ap.add_argument('--out', type=Path, required=True)
    a = ap.parse_args()
    run(a.source.resolve(), a.out.resolve())
