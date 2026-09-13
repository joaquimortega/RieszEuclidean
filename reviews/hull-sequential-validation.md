# Hull subsequence extraction checkpoint

The modular project now proves `separated_weak_subsequence`: every sequence of
configurations in Euclidean space with a common positive separation constant
has a strictly increasing subsequence converging in the paper's two-sided
Beurling local matching sense, with the same separation constant in the limit.

The proof takes a subsequence in the countable product of compact Hausdorff
spaces of closed subsets of compact Euclidean windows. Nested-window inclusion
and reverse compatibility at interior points identify one ambient configuration.
Uniform Hausdorff matching on a larger window gives both local matching clauses.
The existing weak-limit separation theorem supplies separation of the limit.
This is a direct Euclidean extraction proof; it does not use a lattice reduction.

Validation at this checkpoint:

- `lake build RieszEuclidean`: passed.
- All 15 default environment linters: passed for 219 declarations and 297
  generated declarations.
- Blueprint inventory and official formalization.yaml schema: passed.
- Full updated axiom audit and standalone build validation remain in progress.
- The recorded nine-result Comparator acceptance belongs to the earlier
  initial-gap source hashes; it does not certify these new hull sources.

The hull node remains pending. A metrizable topology with exactly this sequential
convergence, topological compactness, and joint continuity of real translations
remain to be constructed. Stationary measures and subsequent analytic and
geometric arguments are not claimed here.

The later compactness and topology proof is documented in
`hull-compactness-validation.md`; the pending topology work above describes this
earlier sequential-extraction checkpoint.
