# Frequency separation

The actual exponential Riesz basis synthesis map on a bounded measurable
Euclidean domain now implies uniform separation of its frequencies.
The proof combines a uniform lower bound for distinct synthesis columns with
a quantitative pointwise phase estimate and the finite-measure L² bound.

This is partial progress on `separation-and-bumps`; the normalized bump family
and initial projection gap remain required. The blueprint remains 6 proved
obligations and 19 pending obligations.

The modular and regenerated standalone builds pass. The modular library passes
all 15 default linters. The eight-result Comparator log from commit 06ab223 is
historical evidence for the Fourier checkpoint; no new Comparator acceptance
is claimed for the expanded source until it is rerun.

All 15 linters also pass for the standalone (153 declarations plus 235 generated)
and MainResults (11 plus 5). The audit checks 68 declarations and finds only
standard Lean axioms. Blueprint and standalone extraction checks pass.
