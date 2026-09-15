# Riesz bases in Euclidean space

Lean formalization project for Joaquim Ortega-Cerdà's
[`RieszEuclidean.tex`](paper/RieszEuclidean.tex).

All **32 blueprint obligations are proved**, including the revised Section 2
and the new Section 8 on bounded convex domains with C² boundary. The bump
characterization is an equivalence, and the projection proof uses adjoints,
closed range, and the exact maximum-norm identity.

The convex extension constructs a curved boundary patch from a containing-ball
contact point, proves translated surface-null intersections, and derives the
positive finite boundary measure needed by the analytic obstruction.
See [the verification review](reviews/convex-progress.md).

Scalar correlations of strongly continuous unitary representations on separable
complex Hilbert spaces have finite positive Euclidean representing measures. This
is the Bochner statement used for the stationary hull. The geometric conclusions
cover bounded nonempty convex C² domains in dimension at least two,
positive-radius balls, all noncollinear triangles, affine ellipsoids, a
general boundary-measure criterion, and polygons given by finite irredundant
supporting-halfspace presentations with nonzero normals, nonempty faces, and an
unpaired maximal side, including the odd-maximal-side consequence. Physical
translation spectra and the interval/rectangle boundary-overlap remarks are also
formalized.

## Build from a standalone clone

Install [elan](https://github.com/leanprover/elan), then run:

```sh
git clone https://github.com/joaquimortega/RieszEuclidean.git
cd RieszEuclidean
lake exe cache get
lake build
lake env lean -DwarningAsError=true scripts/Lint.lean
python3 scripts/check_blueprint.py --require-complete
python3 scripts/check_axioms.py
```

`lean-toolchain` and `lake-manifest.json` pin Lean and every Lake dependency.
All project-specific Lean sources are contained in this repository. No sibling
checkout, absolute path, generated proof file, or private package is required.
Mathlib and its transitive dependencies are fetched by Lake.

The public theorems use the concrete `HasExponentialRieszBasis` predicate,
arbitrary frequency sets, and the manuscript's dimensional and geometric
hypotheses. CI builds and lints the modular, public, and standalone sources,
checks extraction and metadata, audits transitive axioms, and requires all
blueprint obligations to be proved.

## Verification

`MainResults.lean` exposes 41 public targets, including the unconditional convex
`C²` corollary and the Section 2 bump equivalence.
`RieszEuclideanStandalone.lean` is generated from the same checked source modules.
Current verification results are recorded in
[`reviews/convex-progress.md`](reviews/convex-progress.md).

The earlier 37-target Comparator run is a historical verification of the previous
manuscript scope, recorded in [`reviews/bochner-progress.md`](reviews/bochner-progress.md).
It must not be read as verification of the new Section 8. Pinned Comparator
instructions are in [`standalone/TOOLS.md`](standalone/TOOLS.md).

Regenerate and verify the standalone source after proof edits with:

```sh
python3 scripts/build_standalone.py
lake build MainResults RieszEuclideanStandalone
lake env lean -DwarningAsError=true scripts/LintMainResults.lean
lake env lean -DwarningAsError=true scripts/LintStandalone.lean
python3 scripts/build_standalone.py --check
python3 -m pip install -r requirements-validation.txt
python3 scripts/check_metadata.py
```

Use a virtual environment for the Python validation dependencies if required by
your system. The official metadata schema is vendored under `schema/`.

## Documents

- [Blueprint and proof structure](blueprint/README.md)
- [Machine-readable obligations](blueprint/manifest.json)
- [Formalization status](STATUS.md)
- [Code provenance](PROVENANCE.md)
- [Formalization metadata](formalization.yaml)
- [Dependency caches and cloud sync](CACHE-SYNC.md)

## Manuscript

The canonical manuscript is `paper/RieszEuclidean.tex`; edit this file directly.
In the author's parent workspace, `RieszEuclidean.tex` is a relative symlink to
this file, so edits through either path affect the same manuscript. The repository
contains the real file and remains self-contained when cloned.

With a TeX Live installation containing AMS packages, microtype, hyperref, and
latexmk:

```sh
mkdir -p paper/build
latexmk -pdf -interaction=nonstopmode -halt-on-error \
  -outdir=paper/build paper/RieszEuclidean.tex
```

The paper credits weak limits to Beurling and cites Rudin, *Fourier Analysis on
Groups*, §1.4.3, for Bochner's theorem. The required mathematical conclusions are
proved in Lean or obtained from Mathlib.

## Contribution checks

Run the build, all default environment linters, the blueprint checker, extraction
check, metadata checker, and transitive axiom checker. Compiler warnings are
errors. Fix linter findings in the code; do not add `nolint` annotations or
disable linters. The blueprint checker rejects such suppressions in project proof
sources.
