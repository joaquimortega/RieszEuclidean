# Uniform hull gap, stationary comparison and sphere checkpoint

The blueprint has 13 proved nodes and 12 pending obligations. The public reference
contains 23 supporting results. Four additions cover the uniform hull gap, actual
stationary comparison projections, Hausdorff sphere measure and the conditional
sphere cutoff obstruction.

An exponential Riesz basis supplies a uniform strict Fourier/bump projection gap
on the full configuration hull. The stationary comparison operators are constructed
on the stationary L² space and are self-adjoint, idempotent and norm-Lipschitz.
Literal Hausdorff sphere surface measure is finite and positive; nontrivial
translated sphere intersections are null. Boundary limits use conull sequences
approaching through ambient open sets, without imposing a ray condition.

The sphere obstruction still assumes representing spectral data and the averaged
operator gap. It is not the unconditional ball nonexistence theorem. Bochner
existence remains postponed. New averaging and planar scratch proofs are not
included in this checkpoint or its declaration counts.

The modular, public and standalone builds pass with warnings as errors. All 15
linters pass: 680 modular declarations plus 506 generated, 26 public declarations
plus 5 generated, and 706 standalone declarations plus 511 generated. Blueprint,
source extraction and official v0.4 metadata checks pass. All 597 transitive axiom
reports use only standard Lean axioms; see `comparison-sphere-axioms.txt`.

Explicit counting-measure and Koopman regularity instances ensure that the
modular and standalone declaration bodies agree where required by Comparator.
Every compared declaration type matches, and the traversal of 48,694 statement
dependencies found no project declaration mismatch.

Official Comparator accepted all 23 results, and Lean's default kernel accepted
the standalone solution with exit 0. The real Landrun sandbox and systemd
restriction were used. Runtime: 4min 53.577s; CPU: 4min 58.989s; peak memory: 3.3G.
Exact inputs are recorded in `comparator-comparison-sphere-hashes.json` and
`comparison-sphere-progress-hashes.json`. The earlier nineteen-result checkpoint
remains separately recorded in `fejer-cutoffs-progress.md`.
