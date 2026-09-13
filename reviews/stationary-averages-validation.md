# Invariant probability from continuous Euclidean box averages

`EuclideanBoxes` and `BoxAverages` construct coordinate cubes of volume `(2R)^d`
and normalized positive averaging functionals with operator norm at most one.
`BoxBoundary` bounds the symmetric difference with a fixed translate by a shell
whose relative volume tends to zero. `IntegralSymmDiff` and
`BoxTranslationIntegral` turn this into vanishing translation error for bounded
continuous observables.

`CompactMeans` uses Banach–Alaoglu to obtain a common invariant weak-star cluster
functional. `MeanRepresentation` and `PositiveFunctionalMeasure` use
Riesz–Markov–Kakutani to represent it by an invariant probability measure.
`InvariantProbability` proves the construction for continuous Euclidean actions;
`HullInvariantMeasure` specializes it to the compact translation hull.
The averages are actual Lebesgue integrals in real Euclidean space.

The stationary-measure blueprint node remains pending: equivalence with vague
counting-measure convergence and the strongly continuous Koopman action still
require proofs. The main geometric nonexistence theorems remain pending.

Validation of the current source:

- Modular and public-result builds passed.
- All 15 modular linters passed for 296 declarations and 362 generated declarations.
- All 15 public-result linters passed for 14 declarations and 5 generated declarations.
- Blueprint and official metadata schema checks passed: 8 nodes proved, 17 pending.
- All 15 standalone linters passed for 310 declarations and 367 generated declarations.
- Expanded standalone build passed. All 213 transitive axiom reports use only
  `propext`, `Classical.choice`, and `Quot.sound`; see
  `stationary-invariant-measure-axioms.txt`.
- The first eleven-result Comparator run exposed import-dependent instance
  inference. The source imports were aligned; see `comparator-import-alignment.md`.
- The aligned official Comparator accepted all eleven results, and the Lean
  default kernel accepted the standalone solution, with exit code 0.
  The real Landrun and systemd sandbox remained enabled. Runtime: 8min 35.237s;
  CPU: 10min 59.673s; peak memory: 3.2G.
- Successful log: `comparator-invariant-measure-aligned.txt`.
- Verified source/configuration/log hashes: `comparator-invariant-measure-hashes.json`.
- Independent GitHub CI for this new checkpoint has not yet been observed.
