# Continuous Fejér and conditional cutoff checkpoint

The blueprint has 10 proved nodes and 15 pending obligations. Continuous Fejér
approximation is proved. Bochner existence remains postponed; the complete paper,
scalar calculus and cutoff nodes are not certified as finished.

The new proofs establish the actual box-overlap weights, Plancherel probability
kernels, dilation and concentration, smoothed-indicator convergence, and the exact
Fourier symbol of the finite filters. All radius limits are real `R → ∞`.

Given representing spectral measures, a dense sequence of normalized vectors
yields a probability control measure. The integrated kernel algebra and spectral
norm identity give the uniform symbol bound. Dominated convergence and bounded
strong operator limits give a simultaneous family of self-adjoint idempotent
contractions on a measurable conull parameter set. Spectral mass and difference
identities use the actual raw finite filters.

The bump kernel has proved covariance, Hermitian symmetry, finite propagation,
uniform bounds, product integrability, the normalized projection integral identity,
and joint spatial continuity for fixed configuration. The stationary comparison
operator itself remains under development.

The public reference contains nineteen supporting results. The five additions
cover continuous Fejér approximation, the exact finite-filter symbol, the control
measure, stationary cutoffs and the bump-kernel projection identity. None asserts
general Bochner existence or a geometric nonexistence theorem.

The modular, public-reference and standalone builds pass with compiler warnings
as errors. All 15 linters pass: 517 modular declarations plus 433 generated,
22 public declarations plus 5 generated, and 539 standalone declarations plus
438 generated. Blueprint, source-extraction and official v0.4 metadata checks pass.
All 434 final transitive axiom reports use only standard Lean axioms; see
`fejer-cutoffs-axioms.txt`. Official Comparator accepted all nineteen results, and Lean's default kernel
accepted the standalone solution with exit 0. The real Landrun sandbox and
systemd restriction were used. Runtime: 4min 47.356s; CPU: 4min 52.873s;
peak memory: 3.1G. See `comparator-fejer-cutoffs.txt` and
`comparator-fejer-cutoffs-hashes.json` for the exact verified inputs.
The earlier fourteen-result checkpoint remains recorded separately in
`comparator-spectral-norm-hashes.json`.
