# Riesz bases directly in Euclidean space

Lean formalization project for Joaquim Ortega-Cerdà's
[`RieszEuclidean.tex`](paper/RieszEuclidean.tex).

**Work in progress. The Euclidean nonexistence theorems are not yet formally
proved in this repository.** The blueprint records the remaining analytic and
geometric constructions; a successful build checks the implemented modules only.

The intended proof keeps frequencies, translations, and scalar spectral measures
in ℝⁿ. It uses Beurling weak limits, smooth orthonormal bumps, continuous box
averaging of scalar inner products, and a norm-continuous comparison projection.
It does not replace this route with the earlier lattice proof.

Frequency separation and normalized nonnegative smooth compact bumps are now proved.
The Fourier lower bound for these bumps, the translated orthonormal family and
the initial projection gap remain pending.

## Build from a standalone clone

Install [elan](https://github.com/leanprover/elan), then run:

```sh
git clone https://github.com/joaquimortega/RieszEuclidean.git
cd RieszEuclidean
lake exe cache get
lake build
lake env lean -DwarningAsError=true scripts/Lint.lean
python3 scripts/check_blueprint.py
python3 scripts/check_axioms.py
```

`lean-toolchain` and `lake-manifest.json` pin Lean and every Lake dependency.
All project-specific Lean sources are contained in this repository. No sibling
checkout, absolute path, generated proof file, or private package is required.
Mathlib and its transitive dependencies are fetched by Lake, not vendored into Git.

The stronger completion gate is deliberately separate:

```sh
python3 scripts/check_blueprint.py --require-complete
```

It must fail while any full-paper obligation remains open. The final theorem
statements will use the concrete `HasExponentialRieszBasis` predicate, arbitrary
frequency sets, and the manuscript's dimensional and geometric hypotheses.
Conditional projection lemmas do not discharge those theorems.

## Documents

- [Blueprint and proof plan](blueprint/README.md)
- [Machine-readable obligations](blueprint/manifest.json)
- [Current status](STATUS.md)
- [Code provenance](PROVENANCE.md)
- [Formalization metadata](formalization.yaml)
- [Dependency caches and cloud sync](CACHE-SYNC.md)

## Manuscript

The canonical repository copy is `paper/RieszEuclidean.tex`. With a TeX Live
installation containing AMS packages, microtype, hyperref, and latexmk:

```sh
mkdir -p paper/build
latexmk -pdf -interaction=nonstopmode -halt-on-error \
  -outdir=paper/build paper/RieszEuclidean.tex
```

The paper credits weak limits to Beurling and cites Rudin, *Fourier Analysis on
Groups*, §1.4.3, for Bochner's theorem. Mathematical references are not extra
Lean axioms; their needed conclusions must be proved or obtained from Mathlib.

## Before each commit

Run the build, all default environment linters (including slow tests), the
blueprint checker and the transitive axiom checker. Compiler warnings are errors.
Fix the code when linting fails; do not add `nolint` annotations or disable a
linter. The blueprint checker rejects such suppressions in project proof sources.

## Compact statements and standalone verification

`MainResults.lean` currently states eight proved supporting results with concrete
basis definitions. `RieszEuclideanStandalone.lean` contains their full proofs,
assembled from the modular source with Mathlib imports only. The analytic results include Schwartz Parseval, Schwartz density, and existence
of the unitary Fourier transform with its measurable-domain cutoffs. Neither file yet
contains the pending geometric nonexistence theorems.

Regenerate after source edits with `python3 scripts/build_standalone.py`.
The generator resets Lean's auxiliary-proof naming cache at each file boundary,
matching separate compilation; it does not change declarations or kernel checks.
Before committing, also run:

```sh
lake build MainResults RieszEuclideanStandalone
lake env lean -DwarningAsError=true scripts/LintMainResults.lean
lake env lean -DwarningAsError=true scripts/LintStandalone.lean
python3 scripts/build_standalone.py --check
python3 -m pip install -r requirements-validation.txt
python3 scripts/check_metadata.py
```

Use a virtual environment for the Python validation dependencies if required by
your system. The official metadata schema is vendored under `schema/`.
Pinned Comparator build/run instructions are in `standalone/TOOLS.md`; actual
verification scope and results are recorded in `reviews/standalone-validation.md`.
Comparator checks source correspondence and kernel acceptance, not mathematical
fidelity to the paper. The final main-theorem check remains a completion gate.
