# Spectral construction in progress

The full-paper inventory remains 9 proved nodes and 16 pending nodes. Neither
Bochner existence nor the complete scalar-calculus node is certified here.

`Correlations` proves continuity, positive definiteness, the zero value, a uniform
bound, and the algebraic identities of actual hull correlations.
`SpectralMeasures` proves uniqueness and total mass of finite representing
measures, constructs the invariant constant's Dirac measure, and derives measure
identities when the relevant representing measures are supplied.
`IntegratedUnitary` constructs the orbit integral for an L¹ scalar kernel, its
continuous linear operator and L¹ norm bound. It proves almost-everywhere kernel
congruence and the squared-norm double-correlation formula. `SpectralNorm` proves absolute
integrability of the correlation kernel and the three-variable Fourier Gram
kernel. Fubini and character factorization then give the spectral norm identity
for every L¹ kernel with a supplied representing measure. Its symbol equals the
actual positive Euclidean Fourier transform; the squared symbol is integrable
against every finite measure.

Validation of the inputs in `spectral-progress-hashes.json`:

- Modular and public-result builds pass; the generated standalone builds.
- All 15 modular linters pass: 370 declarations and 386 generated declarations.
- All 15 public-result linters pass: 17 declarations and 5 generated declarations.
- All 15 standalone linters pass: 387 declarations and 391 generated declarations.
- 287 transitive axiom reports pass, with only `propext`, `Classical.choice`, and
  `Quot.sound`; see `spectral-progress-axioms.txt`.
- Blueprint, standalone extraction, and official v0.4 metadata checks pass.

The official Comparator accepted all fourteen exported supporting results and
Lean's default kernel accepted the standalone solution with exit code 0. The new
public result explicitly assumes a representing measure; it does not establish
Bochner existence. See `comparator-spectral-norm.txt` and
`comparator-spectral-norm-hashes.json`. The real Landrun sandbox was used.
Runtime: 8min 58.193s; CPU: 11min 44.854s; peak memory: 3.2G.

At the user's request, general Bochner existence is postponed while the remaining
scalar calculus, cutoffs, comparison and geometric arguments are developed.
Every downstream use must retain this outstanding dependency explicitly.
