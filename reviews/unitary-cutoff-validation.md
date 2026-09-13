# Unitary Fourier and cutoff checkpoint

The new modules prove Schwartz density in actual Euclidean L², extend the
Schwartz Fourier isometry along the dense inclusion, and prove norm preservation
and surjectivity. The inverse extension realizes the paper's positive-sign
Fourier integral on Schwartz functions. Measurable indicator multiplication is
constructed on L² classes and proved to be a contracting orthogonal projection;
unitary conjugation constructs the actual Fourier cutoff.

The modular and standalone builds passed before expanding MainResults. All 15
modular environment linters passed (111 declarations plus 222 generated ones).
The expanded reference adds Schwartz density and a concrete existential theorem
stating unitary integral agreement on Schwartz functions and the cutoff formula
for every measurable domain. Both new statements compiled in isolation.
The updated reference and standalone builds pass. All 15 default linters pass
on the reference (10 declarations plus 5 generated ones) and standalone
(121 plus 227 generated ones). The seven-result Comparator run passed with
exit 0 and Lean default kernel acceptance. Runtime was 245.950 seconds,
with 2.8 GiB peak memory. See comparator-unitary-cutoff.txt and
comparator-unitary-cutoff-hashes.json. Earlier acceptance records are historical.

The new axiom inventory is recorded in cutoff-axioms.txt. No geometric main
nonexistence theorem is yet proved. Integral agreement on arbitrary L¹∩L²,
translation commutation, and the convolution-kernel formula remain explicit
requirements of the Fourier blueprint node; it is not marked complete.
