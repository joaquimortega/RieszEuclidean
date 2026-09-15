# Revised Section 2 and convex C² domains

The updated manuscript has 32 proved blueprint obligations. The public reference
contains 41 targets, including the unconditional convex-domain corollary.
The manuscript and proof fingerprints are recorded in `convex-progress-hashes.json`.
Historical Bochner/37-target verification records describe the earlier revision.

## Mathematical scope

Lemma 2.1 is formalized in both directions, including a Fourier lower bound on
the closure of the domain. The converse reconstructs exponential synthesis from
the bump range isomorphism and the inverse Fourier multiplier. Lemma 2.2 follows
the revised adjoint, lower-bound and closed-range proof, with the exact maximum
identity for the projection gap. Lemma 2.3 uses surjectivity on the smaller range
and injectivity on the larger range, as in the manuscript.

`HasC2Boundary` means that every boundary point has a local real C² defining
function with nonzero derivative, negative on the domain and zero on its
frontier. It includes no curvature, measure or spectral conclusion.

The new convex proof constructs a contact point with a containing ball, obtains
a regular implicit chart and derives a negative radial second-derivative bound.
The operator-norm perturbation argument makes that bound uniform nearby.
Strict concavity of the radial height rules out boundary segments; convexity
then gives singleton supporting faces on a relatively open patch. Curvature is
encoded by a quantitative chart-Hessian inequality and an affine chart inverse.

For translated intersections, two nonproportional defining derivatives yield a
regular codimension-two level and hence a surface-null set. Positive
proportionality is impossible on the patch; negative proportionality forces
the whole intersection of the closed domains to be a singleton. Lipschitz
estimates for a small chart and its affine inverse give positive finite
Hausdorff measure on a smaller patch. The existing general boundary criterion
then proves `RieszEuclidean.convex_C2_no_exponentialRieszBasis` for every bounded
nonempty open convex C² domain in dimension at least two and every frequency set.

The earlier ellipsoid theorem is retained as a legacy result. It is not used as
a substitute for the convex theorem.

## Verification

All final verification checks pass:

- `lake build` and `lake build MainResults` pass.
- All 15 modular linters pass on 1,087 declarations and 663 generated declarations.
- All 15 public-reference linters pass on 44 declarations and 5 generated declarations.
- The blueprint completion gate reports 32 proved obligations, none pending.
- Standalone extraction matches every source module and the public reference.
- The official v0.4 metadata schema and project-state checks pass.
- `git diff --check` passes.

The standalone source builds and all 15 of its linters pass on 1,131 declarations
and 666 generated declarations. Official Comparator
accepts all 41 reference/solution targets and Lean's default kernel accepts the
solution. The complete 987-declaration transitive axiom audit reports only
`propext`, `Classical.choice` and `Quot.sound`. No placeholder proofs, added
axioms, unsafe declarations or linter suppressions occur in project sources.

The standalone concatenation needed explicit root-qualified references and
classical instance scope in several new proofs. Those corrections preserve the
statements and are included in the final verified sources.

Logs: `convex-build.txt`, `convex-standalone-build.txt`, `convex-lint.txt`,
`convex-lint-main.txt`, `convex-lint-standalone.txt`, `convex-axioms.txt`, and
`comparator-convex.txt`.

The tools are Lean 4.19.0, the pinned Mathlib revision in `lake-manifest.json`,
and the pinned Comparator/exporter/checker/Landrun setup described in
`standalone/TOOLS.md`. No independent external human review is claimed.
