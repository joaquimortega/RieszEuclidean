# Riesz bases in Euclidean space

Lean formalization project for Joaquim Ortega-Cerdà's
[`RieszEuclidean.tex`](paper/RieszEuclidean.tex).

All **25 of 25 blueprint obligations** are proved. The formalization covers the
Euclidean Fourier and bump constructions, the compact configuration hull and its
invariant probability measure, the stationary Koopman representation, continuous
box averaging and spectral cutoffs, the comparison projection, and the geometric
boundary arguments.

Scalar correlations of strongly continuous unitary representations on separable
complex Hilbert spaces have finite positive Euclidean representing measures. This
is the Bochner statement used for the stationary hull. The geometric conclusions
cover positive-radius balls, all noncollinear triangles, affine ellipsoids, a
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
checks extraction and metadata, audits transitive axioms, and requires the full
blueprint manifest to be discharged.

## Verification

`MainResults.lean` exposes 37 audited targets covering the supporting interfaces,
averaging, Bochner existence, conditional geometric interfaces, and unconditional
geometric conclusions. `RieszEuclideanStandalone.lean` contains their extracted
Mathlib-only proofs. Official Comparator and Lean's default kernel accept all 37
targets. The transitive audit of 931 project declarations reports only `propext`,
`Classical.choice`, and `Quot.sound`.

The exact inputs, commands, hashes, and results are recorded in the
[current verification record](reviews/bochner-progress.md). Pinned Comparator
build and run instructions are in [`standalone/TOOLS.md`](standalone/TOOLS.md).

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
