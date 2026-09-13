# Development status

The full formalization remains in progress: **13 of 25 blueprint obligations
(52%) are proved**. This counts completed nodes, not estimated remaining effort.

The Euclidean Fourier and initial bump constructions, compact configuration hull,
invariant probability measure, stationary Koopman system and continuous Fejér
construction are proved. The continuous filters use real radii tending to infinity.

Given representing spectral measures, the common control measure, integrated
spectral calculus and simultaneous stationary cutoff family are proved, including
strong convergence, projection properties and spectral norm/difference identities.
Bochner existence is postponed at the user's request; these downstream results
retain explicit measure hypotheses and their blueprint nodes remain pending.

The actual comparison kernel now also has configuration continuity, and the
stationary comparison operator family is self-adjoint, idempotent and
operator-norm Lipschitz. Literal finite-positive Hausdorff sphere surface
measure and translated-overlap nullity are proved. Boundary-cutoff limits and
the sphere obstruction are assembled conditionally on explicit spectral data
and the averaged gap; their dependency node remains pending. Continuous
averaging, planar geometry and the unconditional main theorems still require
work. Bochner existence remains postponed.

The current 13/25 checkpoint exposes twenty-three public supporting results.
Official Comparator and Lean's default kernel accepted the standalone solution.
All builds and all 15 linters pass; the final axiom audit covers 597 declarations
with standard axioms only. See `reviews/comparison-sphere-progress.md` and
`reviews/comparator-comparison-sphere-hashes.json` for exact verification scope
and inputs. The earlier nineteen-result audit is retained separately.

No unfinished theorem is replaced by `sorry` or a new axiom. See
`blueprint/manifest.json` for precise scopes and dependencies. The full-paper
check `python3 scripts/check_blueprint.py --require-complete` must still fail.
