# Standalone verification status

The compact `MainResults.lean` reference states four implemented supporting
results: the projection gap equivalence, strict-inclusion obstruction,
preservation of separation under weak limits, and affine invariance of the
concrete exponential Riesz basis predicate. No geometric nonexistence theorem
is yet included or certified.

Both `MainResults` and `RieszEuclideanStandalone` compile with warnings treated
as errors. All 15 default environment linters pass: 7 declarations plus 5
generated declarations for the reference; 80 plus 184 for the standalone.
Source extraction and the official v0.4 metadata validation also pass.

The reference uses proved modular wrapper bodies, avoiding placeholders.
The standalone contains the corresponding definitions and full proofs with
only Mathlib imports. Comparator therefore checks extraction fidelity and
kernel acceptance against trusted modular source; this is not an independent
mathematical audit of the paper or a certification of its pending main results.

The first real Comparator run failed with `Const does not match between
challenge and target 'RieszEuclidean.Results.HasBasis'`. Both exports completed;
no kernel acceptance is claimed. The modular/standalone definition mismatch
must be resolved before a passing verification can be recorded.

The mismatch was traced to Lean's per-file auxiliary-proof cache
(`Lean.Meta.auxLemmasExt`), which is not serialized into `.olean` files.
The generator now resets this cache at each source-file boundary, matching
modular compilation without changing proofs or bypassing kernel checks.
The rebuilt file passes all default linters. The second real Comparator run passed (exit 0), reporting both
`Lean default kernel accepts the solution` and `Your solution is okay!`.
See `comparator-current.txt`. Runtime was 94.810 seconds with 1.6 GiB peak memory.
This verifies the four supporting results only; the full-paper gate remains open.

## Expanded Fourier checkpoint

The newer five-result run includes Schwartz Parseval and passed. See
`fourier-progress.md`, `comparator-fourier.txt`, and
`comparator-fourier-hashes.json`. Earlier logs and hashes above are historical.

The latest seven-result verification includes Schwartz density and unitary
Fourier/cutoff existence. See `unitary-cutoff-validation.md` for current scope
and `comparator-unitary-cutoff-hashes.json` for verified inputs.

The latest eight-result verification covers the full initial Fourier
construction, including L¹∩L² integral agreement, the kernel formula and
translation commutation. See `fourier-module-validation.md`.
