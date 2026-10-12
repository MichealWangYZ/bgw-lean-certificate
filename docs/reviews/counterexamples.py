"""Independent exact-arithmetic checks for the PR28 source review.
These are small mathematical witnesses, NOT a checkout/test of the repository
and NOT Lean kernel replays. All arithmetic used in assertions is rational.
"""
from fractions import Fraction as Q
import json

# The actual rationals in S3Check.o1_enclosure, in eV.
lo = Q(8880811588953599, 2**59)
hi = Q(8880812351936001, 2**59)
# Recorded printed production O1, 15.400547 meV.
prod = Q('0.015400547')
# Conservatively allow 1 neV for a difference of two printed energies,
# each printed to 1 neV and rounded to nearest.
print_error = Q(1, 10**9)
max_error = max(abs(lo-prod), abs(hi-prod)) + print_error
assert max_error < Q('0.00000521')

# CompleteK is exact scaled closure, not approximate orthogonality.
# One computed row in a two-dimensional basis, one physical omitted row.
r = [Q(1), Q(0)]
kappa = Q(1) + Q(1, 2**40)
defect = [[kappa-r[i]*r[j] if i == j else -r[i]*r[j]
           for j in range(2)] for i in range(2)]
det = defect[0][0]*defect[1][1] - defect[0][1]*defect[1][0]
assert det > 0  # rank 2; cannot equal the outer product of one missing row.

# Even when exact scaled closure is available, the static remainder need not
# vanish. One unit-weight channel: CS=-I/4, sum AC=kappa*I/4.
I = Q(1)
cor_scaled = -I/Q(4) + kappa*I/Q(4)
assert cor_scaled == (kappa-1)/4 and cor_scaled != 0

# A separate finite-sphere closure counterexample, even with kappa=1:
# WFN sphere {0}, complete orbital c(0)=1; epsilon sphere {0,1};
# pair densities M(0)=1, M(1)=0; density rho_aa(0)=1;
# choose I diagonal (0,1/2), v_1=1, include 0 in Gch.
# CS=-1/8 while sum AC=0, so full finite-basis summation leaves COR=-1/8.
M = [Q(1), Q(0)]
Idiag = [Q(0), Q(1,2)]
v = [Q(1), Q(1)]
cs = -sum(vj*ij for vj,ij in zip(v, Idiag))/4
ac = sum(m*m*vj*ij for m,vj,ij in zip(M,v,Idiag))/4
assert cs + ac == -Q(1,8)

out = {
    'numerical_bound': {
        'spec_lo_eV_exact': str(lo), 'spec_hi_eV_exact': str(hi),
        'spec_lo_meV': float(lo*1000), 'spec_hi_meV': float(hi*1000),
        'max_error_microeV_including_print_allowance': float(max_error*10**6),
        'less_than_5_21_microeV': True,
        'production_value_provenance': 'Recorded value; not independently rerun',
    },
    'CompleteK_rank_witness': {
        'computed_row': ['1','0'], 'physical_missing_rows': 1,
        'kappa': str(kappa), 'defect': [[str(x) for x in row] for row in defect],
        'determinant': str(det), 'defect_rank': 2,
        'requires_at_least_two_completion_rows': True,
    },
    'COR_witnesses': {
        'scaled_closure_nonzero_COR': str(cor_scaled),
        'complete_finite_WFN_sphere_nonzero_COR': str(cs+ac),
    },
    'scope': 'Mathematical witnesses reconstructed from reviewed definitions. Not a repository or Lean replay.',
}
print(json.dumps(out, indent=2))
