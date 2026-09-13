# Provenance

`RieszEuclidean/ProjectionGap.lean` was ported from
`DiskRiesz/ProjectionGap.lean` in Joaquim Ortega-Cerdà's
[Disc repository](https://github.com/joaquimortega/Disc), commit
`fc3817f638b0a5f94a58ab9943a1c8b1c3a8eec9`.
The namespace was changed and the unnecessary import of the old lattice-based
`Basic` module was replaced by the Mathlib inner-product-space import.
The user explicitly authorized reuse of that code for this project.

`Basic.lean`, `WeakLimits.lean`, and `MovingComparison.lean` are new development
for the Euclidean manuscript. The library has no import from `DiskRiesz` and
requires no access to the original repository.

The manuscript is by Joaquim Ortega-Cerdà. Formalization and tooling are
AI-assisted work directed by the author. Automated kernel/Comparator checks and
AI-assisted source reviews are recorded in `reviews/`; no independent human
review is claimed.
No new redistribution license has been assigned by the assistant.

`L2Transport.lean` extracts the general Pullback, Equiv and Sequences sections
of `DiskRiesz/BallRounding.lean` at the same commit. It performs no frequency
rounding. `Affine.lean` ports `DiskRiesz/BallAffine.lean`, quantifies over all
finite dimensions directly, and uses the Euclidean manuscript's 2π convention.
The imports and declarations are local to this repository.
