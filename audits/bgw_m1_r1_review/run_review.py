#!/usr/bin/env python3
"""Recheck the pinned BGW-M1-R1 snapshot. Reviewer-only SymPy dependency.
Uses the committed dump; does not run Lean or BerkeleyGW. No candidate files changed.
The submitted test suite writes scratch files into this checkout's artifacts directory;
use an isolated checkout. Refuses different source hashes.
"""
import argparse, hashlib, importlib.util, io, json, tempfile, unittest
from pathlib import Path
import sympy as sp
EXPECTED = {
 'bgw/m1_screening/extract.py':'6074ec0c246ac2556422e898e4ae038bd4542165',
 'bgw/m1_screening/reference.py':'92f49da565f8d5dfdc5108c948e3cc090d524ff8',
 'tests/test_bgw_m1.py':'548a7eaad0066b547e93391ac33c8435e73702ef',
 'GW/BGW/M1Screening.lean':'58c13ea250265394e5be0d7f7707f85cf1d287e3',
 'bgw/m1_screening/data/m1_eps_dump_q2.txt':'5b422d62f82665420a2850aeb3879ecf1f3b8c76',
 'bgw/m1_screening/data/m1_gvec_q2.txt':'d51a609c1e9f3e0b003a6b8192b28a1a6d572e51'}
def require(c,m):
 if not c: raise AssertionError(m)
def main():
 ap=argparse.ArgumentParser(description=__doc__); ap.add_argument('--source',type=Path,required=True); ap.add_argument('--out',type=Path,required=True);args=ap.parse_args()
 root=args.source.resolve();args.out.mkdir(parents=True,exist_ok=True);hashes={}
 for f,want in EXPECTED.items():
  b=(root/f).read_bytes();h=hashlib.sha1(f'blob {len(b)}\0'.encode()+b).hexdigest();require(h==want,f'Source mismatch: {f}: {h}'); hashes[f]=h
 spec=importlib.util.spec_from_file_location('original_m1_r1_tests',root/'tests/test_bgw_m1.py');m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
 stream=io.StringIO();res=unittest.TextTestRunner(stream=stream,verbosity=2).run(unittest.defaultTestLoader.loadTestsFromModule(m));(args.out/'original_34_tests.log').write_text(stream.getvalue());require(res.wasSuccessful() and res.testsRun==34,'Submitted suite failed')
 block,E,X,v=m.load();ref=m.ref;R=ref.exact_inverse(E);n=len(E)
 sym=sp.Matrix([[sp.Rational(x) for x in row] for row in E]).inv(method='DM');require(sym==sp.Matrix(R),'Independent inverse mismatch')
 measure=ref.metrics(E,X,R);rho=ref.inf_norm(ref.matsub(ref.matmul(E,X),ref.eye(n)));p=ref.inf_norm(E)*ref.inf_norm(X)
 variants={'without_rhs_norm':str(rho/p),'with_rhs_norm':str(rho/(p+1)),'without_rhs_float':float(rho/p),'with_rhs_float':float(rho/(p+1))}
 good=m.DUMP.read_text().splitlines();bad=[('EPSPRE 1 1   4.00000000000000000E+00 4616189618054758400' if l.startswith('EPSPRE 1 1 ') else l) for l in good]
 q99=['QSTART 99 0 0 0 1','VCOUL 1 1.0 4607182418800017408','EPSPRE 1 1 1.0 4607182418800017408','EPSINV 1 1 1.0 4607182418800017408','QEND 99']
 cases={'repeated_q':bad+good,'nested_q':[l for l in bad if not l.startswith('QEND')]+good,'extra_q':good+q99,'duplicate_inside':good[:10]+[good[9]]+good[10:],'mismatched_end':[('QEND 7' if l.startswith('QEND') else l) for l in good],'outside_entry':['EPSPRE 1 1 1.0 4607182418800017408']+good,'missing_entry':[l for l in good if not l.startswith('EPSPRE 3 3 ')],'empty':[],'inconsistent_n':[l[:-1]+'9' if l.startswith('QSTART') else l for l in good]}
 probes={}
 with tempfile.TemporaryDirectory(prefix='m1-r1-review-') as temp:
  f=Path(temp)/'input.txt'
  for name,lines in cases.items():
   f.write_text('\n'.join(lines)+'\n')
   try: m.extract.load_single(f,2,expected_n=8,expected_q=(0,0,.5))
   except m.extract.ExtractionError as err: probes[name]={'rejected':True,'error':str(err)}
   else: raise AssertionError('Accepted malformed '+name)
  f.write_text('\n'.join(good+q99)+'\n'); parsed=m.extract.parse(f);require(set(parsed)=={2,99},'Legitimate multi-q parse was lost');probes['explicit_multi_q_parser']={'accepted':True,'q_ids':sorted(parsed)}
 results={'reviewed_commit':'353f9803ec4e51c572dcaa4e3fc785e4a21f49fa','source_hashes':hashes,'evidence':'Original submitted suite on committed data; corrupted copies only for probes. Not Lean output generated here.','original_tests':res.testsRun,'failures':len(res.failures),'errors':len(res.errors),'independent_inverse_matches':True,'metrics':{k:float(x) for k,x in measure.items()},'thresholds':{k:float(x) for k,x in ref.thresholds(n,ref.kappa_inf(E,R)).items()},'residual_conventions':variants,'probes':probes,'not_executed':['Lean/Lake and axiom audit','full repository gate','BerkeleyGW rebuild/run','pristine/instrumented A/B','external input/source hash verification']}
 (args.out/'review_results.json').write_text(json.dumps(results,indent=2)+'\n');print('PASS: original 34 tests; exact independent inverse; nine malformed inputs rejected; explicit multi-q retained.');print(variants);print(args.out/'review_results.json')
if __name__=='__main__': main()
