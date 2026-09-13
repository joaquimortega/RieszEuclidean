# Development status

The full formalization remains in progress. The scaffold, independent dependency
manifest, source manuscript and blueprint are in place.

Implemented and compiled:

- Actual Euclidean synthesis and Beurling weak-convergence definitions.
- Projection-gap equivalence and strict-inclusion obstruction (ported proofs).
- Simultaneous strong-limit gap transfer and the moving-comparison obstruction.
- Determinant-correct L² pullback and arbitrary affine invariance of the actual
  exponential Riesz basis predicate, with 2π phases and transpose frequencies.
- Fixed-translation invariance of weak convergence and preservation of separation.

The actual Fourier/bump construction, compact hull and stationary measure,
Euclidean Bochner measures, continuous filters, covariant projection kernels,
averaged scalar forms, boundary geometry and unconditional main theorems remain
open obligations. See `blueprint/manifest.json` for the complete dependency plan.

No proof-development `sorry` is used in the implemented files. This does **not**
mean that the manuscript is formalized: unfinished work is recorded as pending
blueprint nodes, not hidden behind axioms or assumed analytic-data structures.

The CI build verifies implemented sources. The full-paper completion command
`python3 scripts/check_blueprint.py --require-complete` must currently fail.
