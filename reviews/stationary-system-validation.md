# Stationary system and vague convergence

The stationary-system scope now has Lean proofs of every mathematical component:

- Actual continuous Euclidean box averages produce an invariant hull probability.
- Pullback by T_{-z} implements U_z f(Γ)=f(Γ+z), as in the manuscript.
- The resulting unitaries obey the group law and are strongly continuous.
- The stationary Hilbert space is separable; the constant one is invariant and has norm one.
- Beurling matching and vague counting-measure convergence are equivalent.

For the final item, injective finite point matchings express both test integrals
as finite sums and bound their difference by a uniform oscillation. Compact
support and uniform continuity give forward convergence. A smooth compact bump
distinguishes different configurations. The resulting continuous injective map
from the compact configuration space into all real test integrals is an
embedding, yielding the converse without an unproved measure-uniqueness premise.

Current checks:

- Modular and public-result builds pass.
- All 15 modular linters pass for 328 declarations and 371 generated declarations.
- All 15 public-result linters pass for 16 declarations and 5 generated declarations.
- Expanded standalone build passed, as did all 245 transitive axiom reports.
- All 15 standalone linters passed for 344 declarations and 376 generated declarations.
- Official Comparator and Lean-kernel verification accepted all thirteen results
  with exit code 0. The real Landrun and systemd sandbox remained enabled.
- The stationary blueprint node is proved: 9 nodes proved, 16 pending.
- Standard-Borel, paracompactness, and real scalar imports are aligned for exact
  proof exports. Direct comparison agrees for all newly added declarations.
- Successful log: `comparator-stationary-system.txt`.
- Exact verified inputs: `comparator-stationary-system-hashes.json`.
- Runtime: 8min 37.728s; CPU: 11min 10.385s; peak memory: 3.2G.
- All refreshed validation passed after the import alignment.

Independent GitHub run 34764953503 for the published 3d1e7a0 checkpoint passed.
