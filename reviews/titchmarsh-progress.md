# Titchmarsh–Lions convolution support theorem

The former external Titchmarsh–Lions hypothesis is now proved. All 53 named
milestones in Sections 2–9 are proved, and the public complete-minimal and
interpolation results no longer take that hypothesis. The public reference
contains 47 targets.

## Statement and scope

`CompleteMinimal.titchmarshLions d` proves, for nonzero compactly supported
tempered distributions `u` and `v` and their convolution `w`,

```text
convexHull ℝ (distributionSupport w) =
  convexHull ℝ (distributionSupport u) +
  convexHull ℝ (distributionSupport v).
```

Tempered distributions are continuous complex-linear functionals on actual
Schwartz functions. Their support is defined by local compact Schwartz tests;
compact support means a compact physical supporting set. The convolution
relation is the actual iterated action on `φ(x+y)` and contains no support
assertion. This proves the existing manuscript target for every witness of
`IsDistributionConvolution u v w`. A total convolution operator for arbitrary
compact factors, with a general existence theorem, is a separate API extension.
The applications already supply concrete convolution witnesses.

## Proof

1. The self-convolution halfspace argument uses the square of a Fourier-twisted
   Laplace transform, Liouville and Fourier uniqueness.
2. A nonunital convolution algebra and its coordinate derivations implement the
   algebraic bootstrap. Polynomial moment detection follows from complex
   Stone–Weierstrass. Translation normalization gives directional endpoints and
   the convex-support equality for compact continuous functions.
3. Arbitrarily small compact Schwartz kernels detect each distribution support
   point. Schwartz translation continuity makes the regularizations continuous;
   physical support bounds make them compactly supported.
4. Hahn–Banach factors a tempered distribution through finitely many weighted
   derivative jets in a Banach space. Exact derivatives of the kernel integral
   and Bochner integration give the distribution/kernel integral interchange
   and the regularized convolution identity.
5. Forward support inclusion, compactness of finite-dimensional convex hulls
   and strict separation assemble the distribution theorem.

The implementation is in the 26 `RieszEuclidean/Titchmarsh*.lean` modules,
ending in `TitchmarshLions.lean`. `CompleteMinimalTheorem.lean` and
`MainResults.lean` use the proof directly. Reusable intermediate lemmas that
accept analytic premises remain available; those premises are discharged in
the public results.

## Validation

Passed:

- The complete modular, public and standalone builds with warnings treated as
  errors: `lake build` and `lake build MainResults RieszEuclideanStandalone`
  (`titchmarsh-default-build.txt`, `titchmarsh-build.txt`).
- All 15 modular linters: 2,394 declarations and 1,795 generated declarations
  (`titchmarsh-lint.txt`).
- All 15 public-reference linters: 50 declarations and five generated
  declarations (`titchmarsh-lint-main.txt`).
- The transitive axiom audit over all 2,448 manifest declarations: exactly
  `propext`, `Classical.choice` and `Quot.sound` (`titchmarsh-axioms.txt`).
  `ProofAudit.lean` and the manifest inventories agree.
- All 15 standalone linters: 2,444 declarations and 1,772 generated
  declarations (`titchmarsh-lint-standalone.txt`).
- Blueprint completeness: 53 proved nodes, no authorized external hypotheses
  and no pending obligations.
- The official v0.4 metadata schema and project-state checks.
- Exact standalone generation and source correspondence.
- The revised LaTeX manuscript builds with `latexmk`. The final TeX pass has
  no warnings; the changed formalization note, its following page and the
  final references page were checked visually in the rebuilt PDF
  (`titchmarsh-manuscript-build.txt`).
- Official Comparator: all 47 public targets match the modular reference,
  with only the three standard Lean axioms permitted. Lean's default kernel
  accepts the exported standalone solution (`comparator-titchmarsh.txt`).
  The documented systemd/Landrun sandbox was used; the process exited
  successfully after 6 minutes 45 seconds.

Exact input, source and validation fingerprints are recorded in
`titchmarsh-progress-hashes.json`.

Private helper names are distinct across input modules so they also work in
the single compilation unit. The generator preserves per-file section scope
and clears only Lean's nonpersistent auxiliary-proof and matcher name caches.
The Bessel file's ordered Mathlib imports align its arithmetic elaboration with
the standalone import context; the proof statements and source bodies are
preserved. Comparator also checks all declaration dependencies of the public
statements, including those arithmetic proofs.

The Comparator tools and sandbox configuration are pinned in
`standalone/TOOLS.md`. Historical 37-, 41- and 46-target records remain separate.
No placeholder proof, added mathematical axiom or linter suppression is used.

The delegated subtasks used `gpt-6-luna` with high reasoning effort.
AI-assisted statement review found no discrepancy in support definitions,
convolution signs, nonzero or compact-support prerequisites, or the public
Section 9 statements. This is not an independent human review.

The manuscript's formalization note now records the proved Titchmarsh–Lions
theorem, and its PDF is rebuilt from the revised LaTeX. Existing manuscript
edits were preserved. The manuscript fingerprint in the blueprint matches
the revised source.
