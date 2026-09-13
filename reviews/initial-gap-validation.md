# Initial bump and gap construction verified

The complete initial-bump theorem starts from the actual exponential Riesz basis
on a bounded measurable Euclidean domain. It derives separation and constructs
a real nonnegative compact smooth bump, a uniform positive Fourier lower bound,
isometric synthesis of its translates, and the orthogonal synthesis projection.
The synthesis identity and exact Fourier range identification give a range
isomorphism; the projection-gap theorem yields norm distance strictly below one.

Modular and standalone builds pass. All 15 linters pass on the mathematical
library (195 declarations plus 291 generated), reference (12 plus 5), and
standalone (207 plus 296). The 121-declaration axiom audit finds only propext,
Classical.choice and Quot.sound. Blueprint, source hashes and metadata validate.

The official nine-result Comparator run passes, including Lean default kernel
acceptance (exit 0). See comparator-initial-gap-aligned.txt and
comparator-initial-gap-hashes.json. Runtime was 9min 47.289s; peak memory 3.1 GiB.
The earlier failed run and import-alignment analysis are preserved for audit.

The blueprint has 7 proved obligations and 18 pending obligations. No geometric
main nonexistence theorem is yet formally proved.
