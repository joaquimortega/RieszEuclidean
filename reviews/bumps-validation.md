# Normalized compact bumps

The project constructs nonnegative real-valued complex Schwartz functions
supported in any prescribed positive-radius ball. Their L² norm is exactly one,
and their value at zero is positive. Nonvanishing in L² follows from injectivity
of the Schwartz-to-L² map; normalization preserves smoothness and support.

Modular and standalone builds pass. All 15 default linters pass for the modular
library (145 declarations plus 231 generated), standalone (156 plus 236), and
MainResults (11 plus 5). The 71-declaration transitive axiom audit finds only
standard Lean axioms. Blueprint and extraction-hash checks pass.

The Fourier lower bound, translated orthonormal family and initial projection
gap remain pending. The blueprint remains 6 proved obligations and 19 pending.
The recorded eight-result Comparator acceptance concerns the earlier Fourier
checkpoint; no new acceptance is claimed for these additional source modules.
