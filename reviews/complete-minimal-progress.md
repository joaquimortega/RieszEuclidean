# Complete and minimal exponential systems

The named results of Section 9 are proved with the explicit Titchmarsh–Lions
hypothesis. The source audit includes the interpolation spaces' explicit
dimension and nesting clauses and their exact tail-annihilator characterization.
All 46 public targets passed official Comparator and Lean kernel replay.
Exact inputs, validation logs and tool revisions are fingerprinted in
`complete-minimal-progress-hashes.json`. Historical validation records for
Sections 2–8 remain separate from this revision.

## Mathematical scope and assumptions

The target is a locally finite set of real frequencies whose actual
exponentials form a complete and ordinary minimal family in the domain's L²
space, with individual biorthogonal functions supported in a maximal-volume
inscribed ellipsoid of the closure. Neither uniform bounds on those functions
nor a Riesz or Schauder basis conclusion are asserted.

On 2026-09-26 the author explicitly authorized assuming the Titchmarsh–Lions
convolution support theorem. `CompleteMinimal.TitchmarshLions` states its
convex-support equality for actual nonzero compactly supported distributions
and their iterated-action convolution. It is an explicit theorem hypothesis,
not an added Lean axiom. No other analytic theorem is authorized as an
unproved premise of the final result.

The construction uses the negative Fourier convention of the manuscript's new
section. Pairings with positive exponentials account for Mathlib's convention
that the complex inner product is conjugate-linear in its first argument.
The formal spherical denominator is the manuscript's denominator divided by
the nonzero constant `(4π²)^N`; polynomial spaces and their degree bounds are
unchanged.

## Alternative proofs and source correspondence

The ball transform is obtained from its actual integral. Gaussian moments,
polar integration and Gamma identities yield its even series and radial ODE.
Energy and asymptotic arguments then prove its complete complex zero locus,
simple local quadric factors, ordered positive zero sequence, decay and the
required lower bounds. This proves the consequences for which the manuscript
uses its infinite product. **The literal infinite-product identity
`cm:eq:product` is not formalized or claimed to have been checked.**

John ellipsoid existence and actual affine normalization are proved. Translation
rigidity follows directly from maximal volume by enlarging a capsule. General
uniqueness of the John ellipsoid is not proved or needed for this argument.

The quotient growth argument proves Jensen and Poisson estimates with zeros
handled explicitly. Paley–Wiener–Schwartz constructs the inverse distribution
using Gaussian regularization, multidimensional contour shifting and a
compact-test limit. Point-support classification, polynomial differential
operators and the sharp radial L² degree obstruction are genuine proofs.

The finite interpolation and selection construction retains prescribed
frequencies, gives global individual biorthogonals, and proves local finiteness.
The one-dimensional interval case is already established directly by its
Fourier basis. Affine transport and restriction to intermediate measurable
domains preserve the actual functions and support statements.

## Validation status

The actual analytic package discharges all intermediate analytic premises.
The following checks have passed for the complete modular implementation:

- `lake build RieszEuclidean MainResults`, with warnings treated as errors
  (`complete-minimal-build.txt`). The public reference exposes 46 targets.
- `lake build RieszEuclideanStandalone`, also with warnings treated as errors
  (`complete-minimal-standalone-build.txt`).
- All 15 default linters: 2,230 project declarations and 1,495 generated
  declarations (`complete-minimal-lint.txt`); 49 public-reference declarations
  and five generated declarations (`complete-minimal-lint-main.txt`).
- All 15 standalone linters: 2,279 declarations and 1,491 generated declarations
  (`complete-minimal-lint-standalone.txt`).
- Blueprint completeness and source fingerprints: 52 proved milestones,
  one authorized external hypothesis, and no pending named results.
- `formalization.yaml` against the official v0.4 schema and project state.
- All 2,267 declarations have transitive axioms contained in `propext`,
  `Classical.choice` and `Quot.sound` (`complete-minimal-axioms-batch.txt`).
  The checker uses Lean's unchanged builtin collector with shared traversal
  state to compute the exact union over every manifest target. It also checks
  agreement with the individual `ProofAudit.lean` inventory. Equivalence with
  twelve individual reports and rejection of an extra axiom and a missing
  target are recorded in `complete-minimal-axiom-checker-validation.txt`.
- Exact standalone extraction from all source modules and the public reference.
- The merged manuscript compiles to a 34-page PDF. Upstream commit `cff0701`
  adds references and attributions; these are preserved alongside the new
  section, whose mathematical text is unchanged by the merge.

The standalone generator closes each file's anonymous sections and uses an outer
anonymous section to restore namespace openings, notation and local settings.
It resets Lean's nonpersistent auxiliary-proof and matcher name caches at file
boundaries. The interpolation space is defined directly by its polynomial
Fourier multiplier, definitionally equal to the analytic-package construction.
The elementary arithmetic proofs and one measure instance are explicit so the modular
and standalone environments generate identical relevant constants.
The final sources include a local elaboration-budget increase for
`pointBumpSchwartz` and an explicit `_root_.zero_sub` in the interval proof.
These settings and name qualifications preserve the mathematical statements.
Official Comparator accepted all 46 public targets with only `propext`,
`Classical.choice` and `Quot.sound` permitted. Its pinned Lean kernel replay
accepted the standalone solution and the process exited successfully. The run
used the real Landrun sandbox and the documented outer AF_UNIX restriction;
see `comparator-complete-minimal.txt` and `standalone/TOOLS.md`.

Independent AI-assisted source review found no discrepancy in the Fourier
signs, support definitions, convolution hypothesis, degree exponents or
biorthogonality conventions. This is not an independent human review.
