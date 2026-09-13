# Development status

The full formalization remains in progress: **10 of 25 blueprint obligations
(40%) are proved**. This counts completed nodes, not estimated remaining effort.

The Euclidean Fourier and initial bump constructions, compact configuration hull,
invariant probability measure, stationary Koopman system and continuous Fejér
construction are proved. The continuous filters use real radii tending to infinity.

Given representing spectral measures, the common control measure, integrated
spectral calculus and simultaneous stationary cutoff family are proved, including
strong convergence, projection properties and spectral norm/difference identities.
Bochner existence is postponed at the user's request; these downstream results
retain explicit measure hypotheses and their blueprint nodes remain pending.

The bump comparison kernel has proved bounds, covariance, Hermitian symmetry,
product integrability, its projection integral identity and joint spatial continuity. Continuity in the configuration variable,
the stationary comparison operators, averaging, boundary geometry and the
unconditional main theorems still require work.

The nineteen-result reference and standalone solution pass official Comparator and
Lean kernel verification. All 15 linters pass for modular, public and standalone
sources. All 434 transitive axiom reports use standard axioms only. Exact verified
inputs and logs are recorded in `reviews/comparator-fejer-cutoffs-hashes.json` and
`reviews/fejer-cutoffs-progress.md`.

No unfinished theorem is replaced by `sorry` or a new axiom. See
`blueprint/manifest.json` for precise scopes and dependencies. The full-paper
check `python3 scripts/check_blueprint.py --require-complete` must still fail.
