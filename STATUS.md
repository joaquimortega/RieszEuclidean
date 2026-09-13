# Formalization status

The formalization has **25 of 25 blueprint obligations proved**. No theorem is
implemented by `sorry` or a new axiom.

The completed construction includes Euclidean Fourier analysis, normalized bump
projections and the initial gap, the compact configuration hull, an invariant
probability measure, the strongly continuous stationary Koopman representation,
continuous Fejér approximation, simultaneous spectral cutoffs, the covariant
comparison kernel, and the averaged scalar gap.

For every vector of a strongly continuous unitary representation on a separable
complex Hilbert space, the Bochner modules construct a finite positive Euclidean
measure representing its scalar correlation. Hilbert-basis coordinates of
windows, explicit Fourier-density measures, and a bounded vague limit give the
construction. These measures supply the stationary spectral family and its common
control measure.

The unconditional results cover positive-radius balls, all noncollinear
triangles, affine ellipsoids, the general boundary-measure criterion, and finite
irredundant supporting-halfspace polygons with nonzero normals, nonempty faces,
and an unpaired maximal side. The polygon presentation identifies maximal
boundary segments geometrically and includes the odd-maximal-side consequence.
Physical translation spectra and the interval/rectangle boundary-overlap remarks
are formalized as well.

Official Comparator and Lean's default kernel accept all 37 public targets.
Modular, public, and standalone builds and all 15 linters pass. A transitive audit
of 931 project declarations reports only the standard Lean axioms `propext`,
`Classical.choice`, and `Quot.sound`. The verification commands, inputs, hashes,
and logs are recorded in [`reviews/bochner-progress.md`](reviews/bochner-progress.md).

See [`blueprint/manifest.json`](blueprint/manifest.json) for the precise scopes,
dependencies, declarations, and proof hashes. The full-project check
`python3 scripts/check_blueprint.py --require-complete` passes and is enforced by
CI.
