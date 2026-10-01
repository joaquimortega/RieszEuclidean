# Formalization status

**Sections 2–9: 53 proved milestones and no external mathematical hypotheses.**
Section 9 proves locally finite complete and ordinary minimal exponential systems
on every nonempty bounded open convex domain in positive dimension, with duals
supported in a John ellipsoid of its closure. It also proves the intermediate-domain
scope and incompleteness of the dual family outside a proper support region.

The Titchmarsh–Lions convolution support theorem is proved in
[`TitchmarshLions.lean`](RieszEuclidean/TitchmarshLions.lean). It gives the exact
convex-support equality for actual nonzero compactly supported tempered
distributions. The public Section 9 results use this proof directly.
Paley–Wiener–Schwartz,
Bessel zero geometry and estimates, the physical resolvents, interpolation-space
dimensions and nesting, and the exact tail characterization are proved.

The proof derives Bessel zero geometry directly from the radial ODE. The literal
infinite-product identity is not formalized. John translation rigidity follows
from maximal volume without a general uniqueness theorem. These alternatives
are documented in the blueprint and [Section 9 review](reviews/complete-minimal-progress.md).

The modular, public and standalone builds, all 15 linters in each environment,
and the full 2,448-declaration axiom audit have passed. Official Comparator
accepts all 47 public targets, and Lean's kernel accepts the standalone solution.
Logs and exact source fingerprints are in the
[Titchmarsh–Lions review](reviews/titchmarsh-progress.md). The earlier 46-target
record remains in the [Section 9 review](reviews/complete-minimal-progress.md).

The previously completed formalization includes the revised Section 2 and
Section 8 on convex C² domains.

Section 2 includes both directions of the bump characterization, with the
Fourier lower bound on the closure of the domain. The projection proof identifies
the adjoint restriction, proves lower bounds and closed range, and uses the exact
maximum-norm identity for the converse. The nested-range proof follows the
manuscript's surjectivity/injectivity contradiction.

Section 8 derives its geometry from local regular C² defining functions:

- A containing-ball contact point yields a negative radial chart Hessian.
- Continuity and strict concavity give a relatively open patch with singleton
  supporting faces.
- Regular codimension-two levels handle transverse translated intersections;
  proportional supporting functionals give the equal/opposite normal cases.
- A chart and its affine inverse give positive finite Hausdorff measure on a
  smaller patch, completing the general boundary-measure obstruction.

The public theorem is `RieszEuclidean.Results.convex_C2_no_exponentialRieszBasis`.
It applies to every bounded nonempty open convex domain with C² boundary in
real dimension at least two, and every frequency set. No curvature or boundary
measure assumption is added to this statement.

The earlier ball, triangle, ellipsoid, general-boundary and polygon results are
retained. The former ellipsoid corollary remains a legacy result.

There are no placeholder proofs, added axioms, or linter suppressions.
Build, linter, axiom, source-correspondence and Comparator results are recorded
in [the current verification review](reviews/titchmarsh-progress.md);
the [Sections 2–8 record](reviews/convex-progress.md) is retained as history.
