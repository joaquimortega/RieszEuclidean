# Bochner completion and unconditional Euclidean conclusions

All 25 blueprint nodes are proved, including the independent public-statement
and transitive-axiom audit.

Six Bochner modules contain 46 public declarations. They prove finite positive
Euclidean representing measures for scalar correlations of strongly continuous
unitary representations on separable complex Hilbert spaces, choose such
measures for every vector, and specialize the construction to the stationary
hull Koopman representation. This is exactly the existence statement used in
the manuscript. It does not formalize the broader theorem for every abstract
continuous positive-definite scalar function.

The proof uses normalized vector windows in the original Hilbert space, scalar
coordinates in a countable Hilbert basis, their explicit physical
Fourier-density measures, and a bounded vague measure limit. Fourier convergence
identifies the limit with the original correlation.

The stationary spectral-measure construction supplies the hull representations. They cover every positive-radius ball in dimension at least two,
every noncollinear planar triangle, every invertible affine image of the unit
ball, the manuscript's general boundary-measure criterion, and finite
irredundant supporting-halfspace polygons with nonzero normals and nonempty faces
when a maximal side is unpaired, including the odd-maximal-side consequence.

The final public reference contains 37 targets: supporting and
conditional interfaces, Bochner existence, and the unconditional conclusions.
The modular project, 37-target public reference, and generated standalone
solution all build. All 15 linters pass on the modular project
(1,014 declarations and 647 generated declarations), public reference (40 and
5), and standalone solution (1,054 and 650). The reference/solution type audit
finds no mismatches, and a traversal of 48,710 reachable constants finds no
project declaration mismatch. The six Bochner
modules and ball/ellipsoid wrappers have a 50-declaration
transitive audit using only `propext`, `Classical.choice`, and `Quot.sound`.

Official Comparator and Lean's default kernel accept all 37 targets; the exact
run log is `comparator-bochner.txt`. The complete 931-declaration transitive
axiom audit uses only `propext`, `Classical.choice`, and `Quot.sound`.
