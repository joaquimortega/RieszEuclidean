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
AI-assisted work directed by the author. No independent review is claimed.
No new redistribution license has been assigned by the assistant.
