#!/usr/bin/env python3
"""Archival LL-C1 reviewer probes for cf498531; no Lean execution.

Run from the unchanged submission or this review-only branch:
  python3 audits/ll_c1_review/review_checks.py --repo . --output /tmp/ll-c1-review

Uses standard-library Python. Reads four actual repository files and requires
their reviewed Git blob hashes. After repairs, run the migrated regressions in
the normal suite instead: this reproducer deliberately asserts OLD false passes.

The half-edge model retains four flags per interaction, the two-side partition,
propagator pairings and individually fixed external flags. It does not assume
2**k. The compressed model separately transcribes IsAut; neither executes Lean.
The checker probes use synthetic values, NOT saved Lean output. This script is
review evidence, not a new production gate or a claim of formal model equivalence.
"""
from __future__ import annotations
from collections import Counter
from contextlib import redirect_stdout, redirect_stderr
from copy import deepcopy
from dataclasses import dataclass
from fractions import Fraction
from importlib.util import spec_from_file_location, module_from_spec
from itertools import permutations, product
from pathlib import Path
from unittest.mock import patch
import argparse
import hashlib
import io
import json
import math
import platform
import shutil
import subprocess
import tempfile
import unittest



def load(name: str, path: Path):
    spec = spec_from_file_location(name, path)
    if spec is None or spec.loader is None:
        raise RuntimeError(f'Cannot import {path}')
    module = module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def check_sources(source: Path) -> dict:
    expected = {
        'll/ring_reference.py': '641d536ad219738af480c7bae159721aef49e5bd',
        'tests/test_ll_c1.py': 'd3f83857170fd514086167495d69f0e81349a760',
        'scripts/bootstrap.sh': '4a9f8a51cc05344fd22771d98e932449e1aab230',
        'scripts/env.sh': '23c5ee1b65e2064b99e8db1718ca6f39cd65a93b',
    }
    out = {}
    for path, sha in expected.items():
        data = (source/path).read_bytes()
        actual = hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()
        if actual != sha:
            raise AssertionError(f'Source mismatch {path}: {actual} != {sha}')
        out[path] = {'git_blob_sha1': actual, 'sha256': hashlib.sha256(data).hexdigest()}
    return out


@dataclass(frozen=True)
class Diagram:
    # Interaction endpoints are the two sides of each four-half-edge vertex.
    interactions: tuple[tuple[str, str], ...]
    propagators: tuple[tuple[str, str], ...]
    external: tuple[str, str] = ('i', 'j')

    @property
    def sites(self):
        return tuple(s for edge in self.interactions for s in edge)


def ring(k: int) -> Diagram:
    if k < 0:
        raise ValueError('Negative ring order')
    pairs = tuple((f'a{m}', f'b{m}') for m in range(k))
    props = (('i', 'j'),) + tuple(e for pair in pairs for e in (pair, pair))
    if k == 0:
        ints = (('i', 'j'),)
    else:
        ints = (('i', 'a0'),) + tuple((f'b{m}', f'a{m+1}') for m in range(k-1))
        ints += ((f'b{k-1}', 'j'),)
    return Diagram(ints, props)


def key(edge):
    return tuple(sorted(edge))


def compatible_edge_perms(edges, sigma):
    # This is the literal finite predicate used by samePair/IsAut, without
    # exploiting a ring-specific 2**k formula or a precomputed cardinality.
    ans = []
    for p in permutations(range(len(edges))):
        if all(key((sigma[u], sigma[v])) == key(edges[p[e]])
               for e, (u, v) in enumerate(edges)):
            ans.append(p)
    return ans


def compressed_auts(D: Diagram):
    i, j = D.external
    sites = D.sites
    assert len(set(sites)) == len(sites), 'Interactions must be a site matching'
    internal = tuple(s for s in sites if s not in D.external)
    ans = set()
    for perm in permutations(internal):
        sigma = dict(zip(internal, perm)) | {i: i, j: j}
        rhos = compatible_edge_perms(D.interactions, sigma)
        if not rhos:
            continue
        pis = compatible_edge_perms(D.propagators, sigma)
        for pi, rho in product(pis, rhos):
            ans.add((tuple(sigma[s] for s in sites), pi, rho))
    return ans


def halfedge_auts(D: Diagram):
    """Return genuine half-edge automorphisms and their compressed projections."""
    sites = D.sites
    assert len(sites) == len(set(sites))
    at = {s: [] for s in sites}
    # A propagator has two distinct incidences even when it is a site self-loop.
    for e, (u, v) in enumerate(D.propagators):
        at[u].append((e, 0)); at[v].append((e, 1))
    extflags = (('external', 0), ('external', 1))
    for s, f in zip(D.external, extflags):
        at[s].append(f)
    assert all(len(v) == 2 for v in at.values()), 'Each interaction side has two half-edges'
    H = tuple(h for s in sites for h in at[s])
    position = {h: (r, side, slot)
                for r, edge in enumerate(D.interactions)
                for side, s in enumerate(edge) for slot, h in enumerate(at[s])}
    pair = {}
    for e in range(len(D.propagators)):
        pair[(e, 0)] = (e, 1); pair[(e, 1)] = (e, 0)
    local = tuple(product((0, 1), repeat=3))  # side swap + a swap within EACH source side
    results = []
    for vp in permutations(range(len(D.interactions))):
        choices = []
        for r, edge in enumerate(D.interactions):
            opts = []
            for side_swap, flip0, flip1 in local:
                mapping = {}
                for side, s in enumerate(edge):
                    target_site = D.interactions[vp[r]][side ^ side_swap]
                    for slot, h in enumerate(at[s]):
                        mapping[h] = at[target_site][slot ^ (flip0 if side == 0 else flip1)]
                if all(mapping.get(f, f) == f for f in extflags):
                    opts.append(mapping)
            choices.append(opts)
        for maps in product(*choices):
            psi = {h: image for mapping in maps for h, image in mapping.items()}
            assert len(set(psi.values())) == len(H)
            if not all(psi[pair[h]] == pair.get(psi[h]) for h in pair):
                continue
            sigma = {}
            for s in sites:
                r, side, _ = position[psi[at[s][0]]]
                sigma[s] = D.interactions[r][side]
                assert all(position[psi[h]][:2] == (r, side) for h in at[s])
            pi = tuple(psi[(e, 0)][0] for e in range(len(D.propagators)))
            projection = (tuple(sigma[s] for s in sites), pi, vp)
            results.append((tuple(psi[h] for h in H), projection))
    assert len(set(x[0] for x in results)) == len(results)
    return results


def is_1pi(D: Diagram) -> bool:
    # Test connectedness of the whole interaction/propagator incidence graph
    # after deleting each single PROPAGATOR, as in the paper's definition.
    for remove in [None, *range(len(D.propagators))]:
        edges = D.interactions + tuple(e for idx, e in enumerate(D.propagators) if idx != remove)
        reached = {D.sites[0]}
        while True:
            previous = len(reached)
            for u, v in edges:
                if u in reached or v in reached:
                    reached.update((u, v))
            if len(reached) == previous:
                break
        if len(reached) != len(D.sites):
            return False
    return True


def suite_result(tests, data=None):
    with tempfile.TemporaryDirectory() as td:
        path = Path(td)/'synthetic_values.json'
        if data is not None:
            path.write_text(json.dumps(data))
        stream = io.StringIO()
        with patch.object(tests, 'LEAN_VALUES', path), redirect_stdout(stream), redirect_stderr(stream):
            result = unittest.TextTestRunner(stream=stream, verbosity=2).run(
                unittest.defaultTestLoader.loadTestsFromModule(tests))
        return {'run': result.testsRun, 'failures': len(result.failures),
                'errors': len(result.errors), 'ok': result.wasSuccessful(),
                'log': stream.getvalue()}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--repo', type=Path, default=Path(__file__).resolve().parents[2])
    parser.add_argument('--output', type=Path, default=Path('/tmp/ll-c1-review'))
    args = parser.parse_args()
    source = args.repo.resolve()
    evidence = args.output.resolve()
    evidence.mkdir(parents=True, exist_ok=True)
    hashes = check_sources(source)
    ref = load('review_reference', source/'ll/ring_reference.py')
    tests = load('review_original_tests', source/'tests/test_ll_c1.py')
    findings = {'reviewed_commit': 'cf498531d1e0776daa69a22c891a853b2275cfff',
                'python': platform.python_version(), 'source_hashes': hashes,
                'reproducer_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                'scope': 'Independent Python review, not Lean/full-gate execution',
                'rings': []}
    derived_counts = {}
    for k in range(3):
        D = ring(k)
        raw = halfedge_auts(D)
        compressed = compressed_auts(D)
        projections = Counter(p for _, p in raw)
        assert set(projections) == compressed
        assert set(projections.values()) == {1}
        derived_counts[k] = len(raw)
        findings['rings'].append({'k': k, 'halfedge_count': len(raw),
                                 'compressed_count': len(compressed),
                                 'projection_is_bijection': True,
                                 'one_particle_irreducible': is_1pi(D),
                                 'raw_interaction_relabeling_space': math.factorial(k+1)*8**(k+1)})
    assert [derived_counts[k] for k in range(3)] == [1, 2, 4]

    # Valid 1PI self-energy diagram: insert a Hartree tadpole into one of
    # ring1's two parallel bubble propagators. This is OUTSIDE C1's ring family.
    tad = Diagram((('i', 'a'), ('b', 'j'), ('c', 'd')),
                  (('i', 'j'), ('a', 'b'), ('a', 'c'), ('c', 'b'), ('d', 'd')))
    raw = halfedge_auts(tad)
    comp = compressed_auts(tad)
    fibers = Counter(p for _, p in raw)
    assert len(raw) == 2 and len(comp) == 1 and is_1pi(tad)
    assert set(fibers) == comp and set(fibers.values()) == {2}
    findings['outside_ring_counterexample'] = {
        'interactions': tad.interactions, 'propagators': tad.propagators,
        'external_labels': tad.external, 'one_particle_irreducible': is_1pi(tad),
        'halfedge_count': len(raw), 'compressed_count': len(comp),
        'projection_fiber_sizes': list(fibers.values()),
        'cause': 'The two incidences of the propagator self-loop d-d may be swapped while its edge ID and site remain fixed.',
        'scope': 'Refutes an unrestricted model-correspondence claim, NOT the C1 ring counts.'}

    # Compare amplitudes with an independently generated half-edge count.
    # This uses source Python calculations, not output from an executed Lean binary.
    table = []
    synthetic = {'symmetry_factors': {f'ring{k}': derived_counts[k] for k in range(3)}, 'values': []}
    for name, fx in ref.FIXTURES.items():
        row = {'name': name, 'N': len(fx['G']), 'i': fx['i'], 'j': fx['j']}
        for k in range(3):
            a = ref.both_agree(fx['G'], fx['v'], fx['i'], fx['j'], k)
            # Remove the source's literal normalization; divide by the half-edge count.
            raw_amplitude = ref.ring_contribution_contraction(
                fx['G'], fx['v'], fx['i'], fx['j'], k)*ref.symmetry_factor(k)
            independent_normalization = raw_amplitude/derived_counts[k]
            assert a == independent_normalization
            row[f'ring{k}'] = str(a)
            table.append({'fixture': name, 'k': k, 'value': str(a),
                          'normalization_from_halfedges': derived_counts[k]})
        synthetic['values'].append(row)
    findings['recomputed_reference_values_NOT_Lean_execution'] = table

    probes = {'no_output_file': None, 'synthetic_valid_control': deepcopy(synthetic)}
    single = deepcopy(synthetic)
    single['values'][2]['ring1'] = str(Fraction(single['values'][2]['ring1'])*2)
    probes['ordinary_wrong_value_control'] = single
    duplicate = deepcopy(synthetic)
    wrong = deepcopy(duplicate['values'][2]); wrong['ring1'] = '999999'
    duplicate['values'].insert(0, wrong)
    probes['wrong_duplicate_before_correct_row'] = duplicate
    invalid_metadata = deepcopy(synthetic)
    invalid_metadata['values'][0]['i'] = 999
    invalid_metadata['values'][0]['j'] = 999
    probes['out_of_bounds_external_indices'] = invalid_metadata
    results = {}
    for name, data in probes.items():
        result = suite_result(tests, data)
        (evidence/f'{name}.log').write_text(result.pop('log'))
        result['input_kind'] = 'synthetic reviewer input; NOT original Lean output'
        result['rows'] = None if data is None else len(data['values'])
        results[name] = result
    assert results['synthetic_valid_control']['ok']
    assert not results['ordinary_wrong_value_control']['ok']
    assert results['wrong_duplicate_before_correct_row']['ok']
    assert results['out_of_bounds_external_indices']['ok']
    assert not results['no_output_file']['ok']
    findings['checker_probes'] = results
    # Exercise the actual bootstrap scripts in an otherwise empty checkout.
    # On the original author's host the absolute target may exist. Do not follow
    # it or alter that installation: record a skip and use a separate host.
    target = Path('<repo>/.tools')
    if target.exists():
        findings['bootstrap_reproduction'] = {
            'status': 'skipped', 'reason': 'Original absolute target exists on this host',
            'tracked_symlink_target': str(target)}
    else:
        with tempfile.TemporaryDirectory() as td:
            checkout = Path(td)
            (checkout/'scripts').mkdir()
            for script in ('bootstrap.sh', 'env.sh'):
                shutil.copy2(source/'scripts'/script, checkout/'scripts'/script)
            (checkout/'.tools').symlink_to(target)
            done = subprocess.run(['bash', 'scripts/bootstrap.sh'], cwd=checkout,
                                  text=True, capture_output=True, timeout=5)
            assert done.returncode != 0 and 'File exists' in done.stderr
            (evidence/'bootstrap_symlink.log').write_text(done.stdout+done.stderr)
            findings['bootstrap_reproduction'] = {
                'status': 'reproduced',
                'kind': 'minimal reconstructed checkout; actual scripts, not full build',
                'tracked_symlink_target': str(target), 'exit_code': done.returncode,
                'stderr': done.stderr, 'failed_before_network_or_Lean': True}

    # The smaller loop witness used in the community-alignment review is also
    # valid. Keep both concrete examples; they establish the same lost flag swap.
    small = Diagram((('i','j'), ('a','b')), (('i','a'), ('a','j'), ('b','b')))
    raw_small, comp_small = halfedge_auts(small), compressed_auts(small)
    fibers_small = Counter(p for _, p in raw_small)
    assert len(raw_small) == 2 and len(comp_small) == 1 and is_1pi(small)
    assert set(fibers_small) == comp_small and set(fibers_small.values()) == {2}
    findings['smaller_loop_counterexample'] = {
        'interactions': small.interactions, 'propagators': small.propagators,
        'external_labels': small.external, 'one_particle_irreducible': True,
        'halfedge_count': len(raw_small), 'compressed_count': len(comp_small),
        'projection_fiber_sizes': list(fibers_small.values())}

    out = evidence/'evidence.json'
    out.write_text(json.dumps(findings, indent=2, allow_nan=False)+'\n')
    print(json.dumps({'rings': findings['rings'],
                      'counterexample': findings['outside_ring_counterexample'],
                      'checker_probes': results}, indent=2))
    print('Evidence:', out)

if __name__ == '__main__':
    main()
