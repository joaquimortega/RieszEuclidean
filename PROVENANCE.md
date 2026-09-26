# Code provenance

The manuscript is by Joaquim Ortega-Cerdà. Formalization and tooling are
AI-assisted work directed by the author.

Joaquim Ortega-Cerdà authorized reuse of author-owned helper code from the
[`Disc` repository](https://github.com/joaquimortega/Disc), commit
`fc3817f638b0a5f94a58ab9943a1c8b1c3a8eec9`. The reused material consists of the
projection-gap argument in `RieszEuclidean/ProjectionGap.lean`, general
pullback/equivalence/sequence components in `RieszEuclidean/L2Transport.lean`,
and affine transport components in `RieszEuclidean/Affine.lean`. These files are
adapted to the `RieszEuclidean` namespace, the project types, and local Mathlib
imports.

The L²-to-tempered-distribution construction in
`RieszEuclidean/CompleteMinimalDistributions.lean` adapts Moritz Doll's
Apache-2.0 Mathlib implementation from
[`TemperedDistribution.lean` at `9658bdd6`](https://github.com/leanprover-community/mathlib4/blob/9658bdd6ca3a5c557ef9a46698d9e7aedc6bcffd/Mathlib/Analysis/Distribution/TemperedDistribution.lean).
The adaptation uses the pinned Schwartz-space API and retains the source's
copyright and license notice. The remaining new distribution operations use
the project's existing Mathlib dependency.

The Poisson-kernel argument in `RieszEuclidean/CompleteMinimalPoisson.lean`
adapts the Apache-2.0 Mathlib proof by Mihai Iancu, Stefan Kebekus, and
Sebastian Schleissinger from
[`Poisson.lean` at `9658bdd6`](https://github.com/leanprover-community/mathlib4/blob/9658bdd6ca3a5c557ef9a46698d9e7aedc6bcffd/Mathlib/Analysis/Complex/Poisson.lean).
Its copyright, license notice, and author attribution are retained in the file.
The upstream Apache-2.0 license is included at
[`third_party/mathlib/LICENSE`](third_party/mathlib/LICENSE); it applies to
the adapted Mathlib material and does not assign a license to the manuscript
or the rest of this project.

On 2026-09-26 the author authorized the Titchmarsh–Lions convolution support
theorem as an explicit external hypothesis for Section 9. This mathematical
dependency does not authorize additional unproved analytic inputs.

Automated kernel and Comparator checks and AI-assisted source reviews are
recorded in `reviews/`; no independent human review is claimed. No new
redistribution license has been assigned by the assistant.
