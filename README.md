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
Radius selection, the positive uniform Fourier lower bound and the translated
orthonormal family are also proved, together with isometric synthesis and the
projection onto its range. The initial projection gap and the
compact metrizable configuration space with its jointly continuous translation action
are proved. This completes 8 of 25 blueprint obligations; the stationary-measure,
spectral and geometric arguments remain pending.

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

`MainResults.lean` currently states thirteen proved supporting results with concrete
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

The hull lemma is proved: configurations with a common positive separation bound,
including the empty configuration, form a compact metrizable space. Sequential
convergence is precisely Beurling local matching, and translations act jointly
continuously. Compatible Hausdorff limits on compact Euclidean windows and
countable distance probes give a direct Euclidean proof of this lemma.

`VagueConvergence` proves that this topology is also the vague counting-measure
topology. Finite point matchings control compactly supported test integrals;
distinguishing bumps and compactness make the counting-test map an embedding.

Continuous Euclidean box averages produce an invariant probability measure on
the translation hull. Relative shell-volume estimates make their translation
errors vanish. Banach–Alaoglu gives an invariant cluster functional, and
Riesz–Markov–Kakutani represents it by the required measure.

`Koopman` constructs the strongly continuous unitary action on the separable
stationary L² space, with the group law and invariant unit constant. It follows
the manuscript convention U_z f(Γ)=f(Γ+z), hence pullback by T_{-z}.

The stationary-system node is complete: 9 of 25 blueprint nodes are proved and
16 remain pending. All builds, all 15 linters, and the 245-declaration axiom audit
pass. The official Comparator accepted thirteen supporting results, and the
Lean kernel accepted the standalone solution. The verified inputs are recorded
in `reviews/comparator-stationary-system-hashes.json`; the successful log is
`reviews/comparator-stationary-system.txt`.
