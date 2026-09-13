# Blueprint for the Euclidean proof

This blueprint follows `paper/RieszEuclidean.tex`, not the earlier proof overview
or the lattice proof. `manifest.json` records each obligation, dependencies,
source labels, implementation status and relevant Lean declarations. A proved
conditional lemma is distinguished from the construction of its hypotheses.

## Concrete statements and conventions

Use `Euclidean d = EuclideanSpace ℝ (Fin d)`, actual restricted Lebesgue
`L²(Ω)`, and `lp (fun _ : Λ => ℂ) 2`. The basis predicate requires a continuous
complex linear equivalence whose standard coordinate vectors are sent almost
everywhere to `exp(2 π i ⟪ξ,x⟫)`. It is not an abstract spectral-data hypothesis.
There is no discreteness assumption on the original frequency set beyond what
is proved from the basis property. Mathlib conjugates the first inner-product
argument; correlation formulas must therefore use `inner f (U z f)`.

The final statements cover every dimension `d ≥ 2`, arbitrary positive-radius
balls and arbitrary frequency sets, noncollinear triangles, finite irredundant
supporting-halfspace polygons with nonzero normals and nonempty faces whose
maximal sides include an unpaired one (in particular an odd number of sides),
and arbitrary invertible affine ellipsoids. The generic boundary-measure
criterion is also a proof obligation.

## Projection gap

**Implemented:** `ProjectionGap.lean` proves Lemmas 2.1 and 2.2, including
bounded invertibility of the range restriction, the converse gap estimate,
and the impossibility of two strictly included projection ranges both lying
at distance less than one from a third projection. These are copied proofs
with independent Mathlib imports, not an import of a lattice main theorem.

**Implemented:** `MovingComparison.lean` proves preservation of a common gap
under simultaneous strong limits, specializes to norm convergence of the
comparison operators, and obtains the final conditional contradiction.
This does not assert that the paper's analytic construction already exists.

## Section 2: Fourier projection and bumps

**Implemented:** Construct the unitary Fourier transform on Euclidean `L²` with the positive
exponent convention, then its conjugate of multiplication by `1_Ω`.
Prove the compact-support kernel formula `p(v-w)` by integrability and Fubini.
A Riesz lower bound gives a positive separation constant. Scale a real
nonnegative smooth compactly supported bump so its Fourier transform is bounded
away from zero on the bounded domain. Its separated translates form an
orthonormal family. The exact identity between projected bump synthesis and
exponential synthesis gives the projection gap. Completeness/surjectivity of
synthesis is essential here; a Riesz sequence alone is insufficient.

Implemented across the Fourier, bump, synthesis and initial-gap modules. The pinned Mathlib has Fourier inversion
and Schwartz Fourier transforms but no ready-to-use continuum Bochner spectral
construction was found in the initial inventory. Reusing names from the older
project must not hide this additional analytic work.

## Section 3: Beurling weak limits

`WeaklyConverges` is the two-sided local matching definition for subsets of ℝⁿ.
The elementary module proves constant convergence, translation invariance, and
preservation of the common separation bound. The full compactness theorem is proved. The implementation supplies a compact
metrizable space of separated configurations and
identifies its topology with local matching and proves joint continuity of real
translations. The empty set is permitted in the ambient space and excluded
from the actual hull by the projection gap, not by an unsupported assumption.

Strong convergence of the configuration bump projections by matching finitely many centers
for compactly supported inputs, then use density, is proved. Continuous box averaging, the invariant probability measure and the strongly
continuous Koopman action on separable `L²(X,μ)` with invariant unit constant are
proved.

The configuration, translation-hull, invariant-measure, Koopman and bump-limit
modules are implemented. The hull-gap result uses the actual basis hypothesis
to obtain a uniform hull gap.

## Section 4: Bochner measures and cutoffs

Scalar correlations of strongly continuous unitary representations on separable
complex Hilbert spaces now have finite positive representing measures on ℝⁿ.
This is the exact Bochner existence used in the manuscript; it does not assert
the theorem for every abstract continuous positive-definite scalar function. Uniqueness,
finiteness, total mass, the parallelogram law and the invariant constant's Dirac
spectrum are proved. A countable dense sequence of normalized vectors constructs
one probability control measure and proves domination of every spectral measure.

Existence uses normalized vector windows in the original Hilbert space. Scalar
coordinates in a countable Hilbert basis have explicit physical Fourier-density
measures; a bounded vague cluster limit represents the original correlation. No
amplified Hilbert space or lattice is introduced.

Integrated L¹ operators have proved adjoint and convolution formulas, spectral
norm identities and the uniform symbol bound. Actual continuous box overlaps give
the Fejér weights. Plancherel proves positivity and unit mass of their Fourier
kernels; dilation and integrable tails prove concentration. The smoothed indicator
is the exact finite-filter symbol and converges off the frontier.

Boundary-nullity gives a measurable conull good-parameter set. Scalar dominated
convergence, pointwise Cauchy limits of bounded operators and composition limits
construct the simultaneous cutoff family for real radii tending to infinity.
Self-adjointness, idempotence, spectral mass and two-parameter difference identities
are proved. The unitary spectral-measure construction supplies their formerly
explicit representing family, completing the scalar-calculus and cutoff nodes.

## Section 5: comparison and averaged scalar forms

The actual covariant bump kernel has proved uniform bounds, support where
`‖v-w‖ ≤ 2r`, Hermitian symmetry, covariance, product integrability, the kernel
projection identity and joint spatial continuity, including configuration
continuity. The stationary comparison family `M_t` is self-adjoint,
idempotent and operator-norm Lipschitz. The working batch implements the actual
averaged scalar construction and its gap estimate.

For each configuration use the actual compactly supported test function
`|C_R|⁻¹ᐟ² 1_C_R(v) exp(-2πit·v) f(Γ-v)`. Tonelli proves the averaged energy
identity and independence from measurable representatives. Expanding scalar
inner products yields exactly `Π_(t,R)` and `M_(t,R)`. Apply the original gap
pointwise in the configuration, then Cauchy–Schwarz. Pass strongly on the cutoff
side and in norm on the bump-kernel side. No amplified Hilbert space `𝒦` is
introduced. No finite averaged operator is assumed to be a projection.

Implemented across the comparison-kernel and `Averaged*` modules, with
`BumpBoxKernel.lean` and `StationaryAssemblyHelpers.lean`. The conclusion still
can be stated with an explicit representing family, while the proved stationary
spectral family discharges that hypothesis in the final result.

## Section 6: sphere and crossing

`SphereGeometry` proves the literal sphere-overlap statement for Hausdorff
surface measure, including finiteness, positivity and Lebesgue-nullity.

Fubini discards every shifted boundary component except zero. Choose good
parameters in the two ambient open sides; do not assume that a conull set
meets a prescribed ray. Dominated convergence gives strictly ordered cutoff
limits. The invariant constant witnesses strictness. Apply the already proved
moving-comparison obstruction after proving that `M_t` has the common limit.

Boundary jump limits and the sphere obstruction are assembled with the actual
averaged gap. `SphereAnalyticAssembly.lean` isolates the representation hypothesis;
`BallEllipsoidTheorems.lean` supplies it from Bochner existence and proves the
unconditional ball theorem.

## Sections 7 and 8: remaining domains

For triangles and an unpaired maximal polygon edge, remove the other edges
using their zero-length translated overlaps. Prove that all surviving edge
components cross in the same normal direction. The jump may have nonzero
tangential frequencies. For an odd polygon, prove that at most two maximal
edges have a given unoriented direction and extract an unpaired edge. The working
modules implement these steps. `PolygonPresentation.lean` identifies supporting
faces with maximal boundary segments and derives both the unpaired-maximal-side
and odd-maximal-side formulations.

**Implemented:** `L2Transport.lean` and `Affine.lean` prove the determinant factor,
transpose frequency map and unit phases with the paper's `2π` convention.
This transport carries the ball result to affine ellipsoids and the
standard-triangle result to all noncollinear triples.

The triangle, polygon, ellipsoid and general-boundary assembly modules first
isolate the supplied hull-representation hypothesis. The unconditional wrapper
modules discharge it using the proved stationary spectral family.
`PhysicalTranslationSpectrum.lean` constructs the concrete physical
translation spectral measure and proves its boundary-symbol consequences;
`IntervalRectangleRemarks.lean` formalizes why interval endpoints and opposite
rectangle edges have positive translated boundary overlap.

## Completion criteria

1. Every full-paper obligation in the manifest has a proved concrete declaration.
2. All project code builds from a fresh standalone clone with the pinned dependencies.
3. No proof holes or additional axioms occur in the transitive dependencies of
   the public results; inspect Lean's axiom reports, not only text searches.
4. Public theorem types preserve arbitrary frequency sets and the full geometric scope.
5. Source labels, hashes, bibliography, repository links and proof status agree.
6. The final public theorems are separately checked against independent statement
   specifications, as in the original project's Comparator workflow.
7. GitHub contains the verified sources, blueprint, scaffold and current manuscript.

The development CI builds and lints the modular, public and standalone sources,
checks extraction and metadata, audits axioms, and requires the full manifest to
be discharged with `check_blueprint.py --require-complete`.

## Published supporting checkpoint and working batch

The published `0fb31ee` 13/25 inventory has twenty-three public supporting results
accepted by official Comparator and Lean's default kernel. Modular, public and
standalone builds and all 15 linters passed; all 597 axiom reports use standard
axioms only. See [the archived audit](../reviews/comparison-sphere-progress.md).
The current tree has all 25 nodes proved. Official Comparator and Lean's default
kernel accept its 37-target reference, and the 931-declaration transitive axiom
audit uses only standard Lean axioms.
