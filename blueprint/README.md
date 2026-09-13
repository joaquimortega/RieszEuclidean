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
balls and arbitrary frequency sets, noncollinear triangles, unpaired maximal
polygon edges including odd side counts, and arbitrary invertible affine
ellipsoids. The generic boundary-measure criterion is also a proof obligation.

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

Prove strong convergence of bump projections by matching finitely many centers
for compactly supported inputs, then use density. Continuous box averaging, the invariant probability measure and the strongly
continuous Koopman action on separable `L²(X,μ)` with invariant unit constant are
proved. Strong convergence of the configuration bump projections remains pending.

The configuration, translation-hull, invariant-measure and Koopman modules are
implemented. `BumpLimits` remains pending.

## Section 4: Bochner measures and cutoffs

General Euclidean Bochner existence for continuous positive-definite correlations
is postponed at the user's request. Spectral measures stay on ℝⁿ. Uniqueness,
finiteness, total mass, the parallelogram law and the invariant constant's Dirac
spectrum are proved. A countable dense sequence of normalized vectors constructs
one probability control measure and proves domination of every spectral measure,
provided the representing family is supplied.

Integrated L¹ operators have proved adjoint and convolution formulas, spectral
norm identities and the uniform symbol bound. Actual continuous box overlaps give
the Fejér weights. Plancherel proves positivity and unit mass of their Fourier
kernels; dilation and integrable tails prove concentration. The smoothed indicator
is the exact finite-filter symbol and converges off the frontier.

Boundary-nullity gives a measurable conull good-parameter set. Scalar dominated
convergence, pointwise Cauchy limits of bounded operators and composition limits
construct the simultaneous cutoff family for real radii tending to infinity.
Self-adjointness, idempotence, spectral mass and two-parameter difference identities
are proved. These statements retain the representing-measure hypotheses. Thus the
continuous-Fejér node is proved, while scalar calculus and cutoffs remain pending
on the postponed Bochner dependency.

## Section 5: comparison and averaged scalar forms

The actual covariant bump kernel has proved uniform bounds, support where
`‖v-w‖ ≤ 2r`, Hermitian symmetry, covariance, product integrability, the kernel
projection identity and joint spatial continuity for fixed configuration. Joint
configuration continuity remains under development. The next construction defines `M_t` by an L²-valued integral of multiplication by `k_z`
after `U_z`. Invariance and the kernel identities prove that it is an
orthogonal projection. Compact support gives operator-norm Lipschitz continuity.

For each configuration use the actual compactly supported test function
`|C_R|⁻¹ᐟ² 1_C_R(v) exp(-2πit·v) f(Γ-v)`. Tonelli proves the averaged energy
identity and independence from measurable representatives. Expanding scalar
inner products yields exactly `Π_(t,R)` and `M_(t,R)`. Apply the original gap
pointwise in the configuration, then Cauchy–Schwarz. Pass strongly on the cutoff
side and in norm on the bump-kernel side. No amplified Hilbert space `𝒦` is
introduced. No finite averaged operator is assumed to be a projection.

Planned modules: `ComparisonKernel`, `ContinuousAveraging`.

## Section 6: sphere and crossing

Prove the literal sphere-overlap statement for Hausdorff surface measure,
including its finiteness, positivity and Lebesgue-nullity. If an alternative
boundary measure is temporarily used, record that divergence explicitly and
do not mark the literal surface-measure lemma proved.

Fubini discards every shifted boundary component except zero. Choose good
parameters in the two ambient open sides; do not assume that a conull set
meets a prescribed ray. Dominated convergence gives strictly ordered cutoff
limits. The invariant constant witnesses strictness. Apply the already proved
moving-comparison obstruction after proving that `M_t` has the common limit.

Planned modules: `SphereGeometry`, `BoundaryLimits`, `BallMain`.

## Sections 7 and 8: remaining domains

For triangles and an unpaired maximal polygon edge, remove the other edges
using their zero-length translated overlaps. Prove that all surviving edge
components cross in the same normal direction. The jump may have nonzero
tangential frequencies. For an odd polygon, prove that at most two maximal
edges have a given unoriented direction and extract an unpaired edge.
Specify the concrete polygon presentation and any fidelity limitation.

**Implemented:** `L2Transport.lean` and `Affine.lean` prove the determinant factor,
transpose frequency map and unit phases with the paper's `2π` convention.
This transport can carry a future ball result
to ellipsoids and standard triangles to all noncollinear triples.

Planned modules: `EdgeGeometry`, `PolygonGeometry`, `Affine`, `Main`.

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

The development CI checks implemented sources. It does not certify completion.
`check_blueprint.py --require-complete` must remain unsuccessful until the full
manifest is discharged.
