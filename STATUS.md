# Development status

The formalization has **25 of 25 blueprint obligations proved**. This counts
completed nodes, not estimated effort.

The Euclidean Fourier and initial bump constructions, compact configuration hull,
invariant probability measure, stationary Koopman system and continuous Fejér
construction are proved. The continuous filters use real radii tending to infinity.

Scalar spectral measures are constructed for every vector of a strongly
continuous unitary representation on a separable complex Hilbert space, and in
particular for the stationary hull Koopman representation. Hilbert-basis
coordinates of windows in the original space, explicit physical Fourier-density
measures and a bounded vague limit give the construction. The common control
measure, spectral calculus and stationary cutoffs now have all inputs discharged.

The actual comparison kernel has configuration continuity, and the stationary
comparison family is self-adjoint, idempotent and operator-norm Lipschitz. The
formalization implements the actual scalar averaging identities and gap,
then assembles nonexistence results for positive-radius balls, all
noncollinear triangles, affine ellipsoids, the general boundary-measure
criterion, and finite irredundant supporting-halfspace polygons with nonzero
normals, nonempty faces and an unpaired maximal side. The polygon presentation
identifies maximal boundary segments geometrically and includes the odd-side
consequence. Physical translation spectra and the interval/rectangle
boundary-overlap remarks are also formalized.

The unconditional wrappers instantiate their formerly explicit representation
hypotheses with the proved stationary spectral family. This is the exact Bochner
scope needed by the paper; no theorem for every abstract positive-definite
function is claimed.

The published `0fb31ee` checkpoint has 13 of 25 nodes and twenty-three public
supporting results. Official Comparator and Lean's default kernel accepted its
standalone solution; all builds and all 15 linters passed, and its axiom audit
covers 597 declarations with standard axioms only. See
`reviews/comparison-sphere-progress.md` and
`reviews/comparator-comparison-sphere-hashes.json` for the exact archived scope
and inputs. Official Comparator and Lean's default kernel accept the expanded
37-target reference, and its integrated module and standalone builds pass. The
931-declaration transitive axiom audit uses only standard Lean axioms.
The earlier nineteen-result audit is retained separately.

No theorem is replaced by `sorry` or a new axiom. See `blueprint/manifest.json`
for precise scopes and dependencies. The full-paper check
`python3 scripts/check_blueprint.py --require-complete` passes and is enforced by CI.
