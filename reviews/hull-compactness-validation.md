# Compact metrizable configuration space

The hull lemma (`lem:hull`) is implemented by
`SeparatedConfiguration.compactSpace`, the metrizable-space instance,
`tendsto_iff_weaklyConverges`, and `continuous_translate`.
`RieszEuclidean.Results.compact_configuration_space` bundles the four conclusions for the
expanded ten-result Comparator configuration.

The configuration type consists of closed Euclidean sets with the specified
separation bound. For every positive bound all separated sets are closed, so this
adds no restriction to the manuscript's space. The empty set is included.
The translation definition uses the paper's convention `x + z ∈ Γ`.
Zero and composition laws are proved.

## Proof and fidelity

1. Restrict a sequence to integer-radius compact Euclidean windows and extract
   one subsequence in the countable product of their compact Hausdorff spaces.
2. Prove inclusion of nested window limits and compatibility at interior points.
   Their union is a Beurling weak limit with the original separation bound.
3. Probe each closed configuration by its extended distances from a countable
   dense set. These probes determine the configuration, including the empty set,
   and induce a metrizable topology.
4. Prove weak convergence implies convergence of every extended-distance probe.
   The extraction theorem gives sequential compactness and hence compactness.
5. Conversely, a sequence failing local matching has a bad subsequence. Extracting
   a weakly convergent further subsequence and uniqueness of topological limits
   contradict the failure. Thus the topology has exactly the paper's convergence.
6. Combine this equivalence with moving-translation convergence to prove joint
   continuity of the real action.

This is a direct Euclidean proof of the same lemma, replacing the manuscript's
counting-measure extraction. It does not replace the main Euclidean proof route
with a lattice argument. Equivalence with vague counting-measure convergence is
explicitly retained as a pending obligation under stationary measures.

## Validation

- Modular project build: passed.
- All 15 default environment linters: passed for 243 declarations and 320
  generated declarations; the missing carrier-field documentation was fixed.
- Blueprint inventory: 8 proved nodes and 17 pending full-paper obligations.
- Standalone source correspondence, official metadata schema and whitespace
  checks: passed.
- MainResults: all 15 linters passed for 13 declarations and 5 generated declarations.
- Expanded axiom audit: 160 transitive reports passed, standard Lean axioms only.
- Standalone build: passed; all 15 linters passed for 256 declarations and 325
  generated declarations.
- Official ten-result Comparator: exit 0, `Lean default kernel accepts the solution`
  and `Your solution is okay!`. Runtime 4min 18.774s; peak memory 3G.
  Log: `comparator-hull-compactness.txt`; verified input and log hashes:
  `comparator-hull-compactness-hashes.json`.

This checkpoint does not prove the stationary measure, spectral constructions,
or geometric nonexistence theorems.
