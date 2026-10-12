#!/usr/bin/env python3
"""Exact finite reviewer checks for PRs 10/11; never candidate Lean output.

Requires SymPy as a reviewer-only dependency. Source references must match the
reviewed blobs. No repository input, source, or generated candidate output is
modified; only the requested evidence directory is written.
"""
from __future__ import annotations
import argparse
from collections import Counter
from fractions import Fraction as F
import hashlib
import importlib.util
from itertools import permutations, product
import json
from pathlib import Path
import sys
import sympy as s

EXPECTED = {
    'll/wick_reference.py': 'c3a16b495c02bf86f71ed5738fbb77a4dcc5d623',
    'll/electronic_reference.py': '7506e8aadcde818a2b9e9a2a9a7d6a5d22de9e41',
}


def require(condition, message):
    if not condition:
        raise AssertionError(message)


def load(root, relative, name):
    spec = importlib.util.spec_from_file_location(name, root / relative)
    if spec is None or spec.loader is None:
        raise RuntimeError(f'Cannot load {relative}')
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


def sm(M):
    return s.Matrix([[s.Rational(x) for x in row] for row in M])


def serial(M):
    return [[str(x) for x in row] for row in M.tolist()]


def check_wick(w):
    explicit = set()
    for p in permutations(range(6)):
        if all(p[p[x]] == x and p[x] != x for x in range(6)):
            explicit.add(p)
    recursive = []
    for matching in w.matchings(list(range(6))):
        p = [-1] * 6
        for a, b in matching:
            p[a], p[b] = b, a
        recursive.append(tuple(p))
    require(len(explicit) == len(recursive) == 15, 'arity-six count')
    require(set(recursive) == explicit, 'arity-six completeness')
    fixtures = [
        ('N2-sym', w.mat([[2,1],[1,3]]), w.mat([[1,2],[2,3]])),
        ('N2-rational', w.mat([[F(1,2),F(-1,3)],[F(-1,3),F(3,2)]]),
         w.mat([[F(2,5),F(1,7)],[F(1,7),F(-4,3)]])),
        ('N3-sym', w.mat([[3,1,0],[1,3,1],[0,1,3]]),
         w.mat([[1,2,3],[2,0,1],[3,1,2]])),
    ]
    six_count = 0
    correction_entries = 0
    results = []
    for name, G, v in fixtures:
        N = len(G)
        t = s.symbols(f't0:{N}')
        tv = s.Matrix(t)
        Q = (tv.T * sm(G) * tv)[0] / 2
        # To extract any moment of degree <=6, only these four terms matter.
        generating = s.Poly(sum(Q**r / s.factorial(r) for r in range(4)), *t)
        def moment(labels):
            powers = Counter(labels)
            monomial = s.prod(t[i]**powers[i] for i in range(N))
            multiplicity = s.prod(s.factorial(powers[i]) for i in range(N))
            return generating.coeff_monomial(monomial) * multiplicity
        delta = s.zeros(N)
        for a,b,i,j in product(range(N), repeat=4):
            labels = [a,b,i,i,j,j]
            m6 = moment(labels)
            require(m6 == s.Rational(w.moment(G,labels)), f'{name} moment {labels}')
            six_count += 1
            delta[a,b] -= s.Rational(v[i][j])/8 * (m6-moment([a,b])*moment([i,i,j,j]))
        require(delta == sm(w.first_order_matrix(G,v)), f'{name} normalized result')
        require(delta == sm(w.both_agree(G,v)), f'{name} Hartree/Fock split')
        correction_entries += N*N
        detected = {}
        for kind in ('unnormalized','weight_quarter','weight_half','hartree_fock_swapped','fock_only'):
            detected[kind] = delta != sm(w.mutant(G,v,kind))
            require(detected[kind], f'{name} mutant {kind}')
        results.append({'fixture':name, 'delta':serial(delta), 'mutants_detected':detected})
    require(six_count == 113 and correction_entries == 17, 'review inventory')
    return {'algorithm':'finite coefficients of exp(t^T G t/2), NOT Gaussian integrals',
            'pairings_checked_against_720_permutations':len(explicit),
            'six_point_moments_compared':six_count,
            'normalized_correction_entries_compared':correction_entries,
            'fixtures':results}


def check_electronic(e):
    fixtures = [
        ('N2-two-channel', e.mat([[2,1],[1,3]]),
         [e.Transition(0,2,4,[1,0]), e.Transition(F(-1,2),F(3,2),4,[1,1])]),
        ('N2-rational', e.mat([[F(1,2),F(-1,3)],[F(-1,3),F(3,2)]]),
         [e.Transition(F(-1,5),F(7,5),F(2,3),[F(1,2),F(-2,3)])]),
        ('N3-three-channel', e.mat([[3,1,0],[1,3,1],[0,1,3]]),
         [e.Transition(0,1,2,[1,0,0]),e.Transition(F(-1,2),2,2,[0,1,0]),
          e.Transition(-1,3,2,[1,1,1])]),
    ]
    entries = 0
    results = []
    for name, v, ts in fixtures:
        N=len(v); V=sm(v)
        X=s.zeros(N)
        for t in ts:
            m=s.Matrix([s.Rational(x) for x in t.m])
            X += s.Rational(t.weight)/s.Rational(t.occ-t.emp) * m*m.T
        require(X == sm(e.chi0(ts,N)), f'{name} chi0')
        eps=s.eye(N)-V*X
        require(eps == sm(e.epsilon(v,e.chi0(ts,N))), f'{name} epsilon')
        require(eps.det()!=0, f'{name} invertibility')
        W=eps.adjugate()*V/eps.det()
        require(W == sm(e.screened(v,ts)), f'{name} exact solve')
        partial=s.zeros(N)
        for k in range(4):
            C=(V*X)**k * V
            partial += C
            require(C == sm(e.neumann_coeff(v,ts,k)), f'{name} coefficient{k}')
            require(partial == sm(e.partial_sum(v,ts,k)), f'{name} partial{k}')
            require(V-eps*partial == (V*X)**(k+1)*V, f'{name} residual{k}')
            entries += 2*N*N
        results.append({'fixture':name,'chi0':serial(X),'epsilon':serial(eps),
                        'exact_W':serial(W),'partial3':serial(partial)})
    require(entries==136,'electronic inventory')
    v, ts=fixtures[0][1:]
    exact=sm(e.screened(v,ts)); early=sm(e.mutant(v,ts,'truncated_early',3))
    intended=sm(e.partial_sum(v,ts,3))
    # These are exactly the inequality assertions used in the submitted test.
    require(early != exact, 'submitted early-truncation assertion')
    require(intended != exact, 'unmutated correct truncation also passes assertion')
    X=sm(e.chi0(ts,2)); V=sm(v)
    spectral=[str(x) for x in (V*X).eigenvals()]
    require(all(abs(x)>1 for x in (V*X).eigenvals()),'divergent unit-coupling witness')
    G=s.diag(2,3); V=s.Matrix([[2,1],[1,3]]); B=G.multiply_elementwise(G)
    ts2=[e.Transition(0,2,4,[1,0]),e.Transition(0,2,9,[0,1])]
    X=sm(e.chi0(ts2,2))
    require(X == -B/2 and V*B != B*V,'signed-scaled noncommuting witness')
    for k in range(6):
        classical=(-s.Rational(1,2))**k * V * (B*V)**k
        electronic=(V*X)**k*V
        require(classical==electronic, f'signed correspondence order{k}')
    gpp_count=0
    for inv0 in (F(1,3),F(1),F(-2,7),F(0)):
        for wt in (F(5),F(1,2),F(-3)):
            require(e.gpp_inv_eps(e.gpp_omega2_from_static(inv0,wt),wt,0)==inv0,
                    'scalar static GPP identification')
            gpp_count+=1
    return {'coefficient_and_partial_entries_compared':entries,'fixtures':results,
            'early_truncation_test':{'mutated_early_passes':early!=exact,
                                    'unmutated_intended_passes':intended!=exact,
                                    'early_partial2':serial(early),
                                    'correct_partial3':serial(intended),
                                    'exact_W':serial(exact),
                                    'eigenvalues_v_chi0':spectral},
            'signed_scaled_counterexample':{'G':serial(G),'v':serial(V),'B':serial(B),
                                            'chi0':serial(X),'noncommuting':True,
                                            'kernels_identical':True,
                                            'coefficient_orders_checked':list(range(6))},
            'gpp_static_scalar_checks':gpp_count}


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--source',type=Path,required=True)
    parser.add_argument('--out',type=Path,required=True)
    args=parser.parse_args()
    root=args.source.resolve(); hashes={}
    for path,expected in EXPECTED.items():
        b=(root/path).read_bytes()
        actual=hashlib.sha1(f'blob {len(b)}\0'.encode()+b).hexdigest()
        require(actual==expected,f'Source mismatch for {path}: {actual} != {expected}')
        hashes[path]=actual
    w=load(root,'ll/wick_reference.py','review_wick')
    e=load(root,'ll/electronic_reference.py','review_electronic')
    results={'reviewed_pr10':'2abd10d8b5b4f52ebc38808de8be7ba3440ee297',
             'reviewed_pr11':'7a2f4601eaaa676e6e215d05034f1399e79ff93a',
             'python':sys.version,'sympy':s.__version__,'reference_blob_hashes':hashes,
             'evidence_origin':'independent finite Python/SymPy calculations; NOT Lean output',
             'not_executed':['Lean/Lake','candidate Lean executables','full original Python test suites',
                             'repository verification gate','BerkeleyGW'],
             'C3':check_wick(w),'C4':check_electronic(e)}
    args.out.mkdir(parents=True,exist_ok=True)
    (args.out/'review_results.json').write_text(json.dumps(results,indent=2)+'\n')
    print('PASS: C3 15 matching permutations, 113 moments, 17 delta entries; C4 136 entries.')
    print('Finding reproduced: both early and intended truncation pass the early-truncation assertion.')
    print('Finding reproduced: chi0=-B/2 matches the screening kernels despite opposite diagonal signs.')
    print(args.out/'review_results.json')


if __name__=='__main__':
    main()
