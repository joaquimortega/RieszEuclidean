# Formalization status

**All 32 blueprint obligations are proved.** The formalization includes the
revised Section 2 and the new Section 8 on convex C² domains.

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
in [the verification review](reviews/convex-progress.md).
