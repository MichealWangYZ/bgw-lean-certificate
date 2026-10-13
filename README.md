# A kernel-checked certificate for a BerkeleyGW G₀W₀–GPP calculation

For one production BerkeleyGW 4.0 run (the shipped `testsuite/Si-EPM`, GPP, 18 bands,
7 Ry), we proved in Lean what the specified calculation gives. The production output
matches the proof to **5.21 µeV**.

![O1 at three scales](docs/figures/fig1_three_scales.png)

| | |
| --- | --- |
| **Observable** | $O_1 = E^{\rm QP}_X - E^{\rm QP}_L$, the X–L conduction-band ordering; 15 meV out of self-energies of ~9 eV |
| **Theorem** (Lean, no hypotheses) | $O_1 \in [15.405752349,\ 15.405753673]$ meV for the specification evaluated exactly on the run's own mean-field data ([`Headline.lean`](GW/Endpoint/Kernel/Headline.lean)) |
| **Production** (`sigma_hp.log`) | 15.400547 meV, within 5.21 µeV of the enclosure; almost all of the difference is BerkeleyGW's Monte Carlo Coulomb averages |
| **Audit** | 34,553 theorems checked; only `propext`, `Classical.choice`, `Quot.sound`; no `sorry`, no `native_decide` |

## What is proved, and what is trusted

![proof chain](docs/figures/pipeline.png)

Kernel-checked from the irreducible wavefunctions:
- the symmetry unfolding;
- static RPA ε and the existence of ε⁻¹, with a box containing it;
- the exact mini-BZ Coulomb averages, as Lebesgue integrals;
- the GPP self-energy with BerkeleyGW's branch rules;
- the linearised QP equation.

**Trusted, not proved:**
- the export of the run files into Lean literals;
- that the Fortran evaluates this specification. This was checked by reading the source line
  by line, and the [reviewer's guide](docs/review/index.html) shows each definition next to
  the Fortran it transcribes;
- the production execution.

**Not claimed:**
- that BerkeleyGW is correct on other inputs;
- that 18 bands are converged;
- that GW, the GPP or the EPM describe silicon;
- formal verification of BerkeleyGW's physics.

## What else we learned about this deck

| | |
| --- | --- |
| ![conventions](docs/figures/fig2_conventions.png) | ![convergence](docs/figures/fig3_convergence.png) |
| Documented conventions decide the sign. Without the static remainder, $O_1 = -101$ meV. | The positive production value comes from cancelling truncations in bands and cutoff (measured). |

Beyond the deck itself:
- **Full QP equation.** It moves $O_1$ to 69.0 meV, a kernel-checked result. In [−10⁴, 10⁴] eV
  each state has exactly two roots.
- **Other treatments.** Full-frequency contour deformation gives 58–67 meV and evGW about
  134 meV (both measured).
- **q → 0.** Σ uses one direction of the anisotropic ε⁻¹ (the last matching symmetry
  operation). That choice moves $O_1$ by up to 1.06 meV.

## For BerkeleyGW developers

- [**Slides**](docs/talk/slides.pdf) and [**notes**](docs/talk/NOTES.md): the
  result, the conventions, and what we would like your input on.
- [**Reviewer's guide**](docs/review/index.html) (open it locally in a browser): each Lean
  definition next to the BerkeleyGW source lines it transcribes.
- [**Details**](docs/DETAILS.md): every claim with its evidence, hypotheses and caveats.
- Further documents:
  - [`docs/ENDPOINT.md`](docs/ENDPOINT.md): the calculation and its three error layers;
  - [`docs/BRIDGE.md`](docs/BRIDGE.md): conditional theory-to-specification identities and the
    departure table.

## Reproduce

```bash
bash scripts/bootstrap.sh   # user-space Lean 4.19.0 + Mathlib caches
bash scripts/verify.sh      # build, exhaustive axiom audit, 699 scientific + 16 workflow tests (~5 h cold)
```

The pinned BerkeleyGW 4.0 archive and its builds live outside git
([`bgw/README.md`](bgw/README.md)). The figures are regenerated with
`python3 docs/figures/make_figures.py`.

## Credits and licence

**Jinyuan Wu** ([@jywu20](https://github.com/jywu20)) proposed the idea. The formalization,
certificates and analysis code were written by Claude (Anthropic) under the authors'
direction. The project went through adversarial and independent AI reviews (Codex), recorded
in [`docs/reviews/`](docs/reviews/README.md). No human maintainer has audited it. The
development record (tasks, handoffs, corrections) is kept in [`.agent/`](.agent/).

This repository is a snapshot of private development commit `0eeae74` (2026-10-13). The
development history is not included. Local paths, scratch directories, host names and
agent-session links are replaced by placeholders (`<repo>`, `<scratch>`, `~/`, `<node>`,
`<agent-session>`). A few historical audit scripts that hard-coded a local path, such as
`audits/ll_c1_review/review_checks.py`, cannot run as committed; the gate does not run them.
Links to the private repository's pull requests are not publicly accessible.

The project's own work is BSD 3-Clause ([`LICENSE`](LICENSE)). BerkeleyGW-derived material
stays under BerkeleyGW's licence ([`THIRD_PARTY_NOTICES.md`](THIRD_PARTY_NOTICES.md)).
Copyright is held jointly by Yizhou Wang and Jinyuan Wu. `LICENSE` also states what AI
authorship means for the rights asserted.
