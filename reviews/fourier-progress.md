# Euclidean Fourier progress

`RieszEuclidean/FourierL2.lean` proves Fourier transposition for integrable
functions by Mathlib's bilinear Fubini theorem, conjugation exchanging the
Fourier signs, and the conjugated pairing identity. Schwartz inversion then
gives Parseval with the exact Euclidean 2π normalization.

The almost-everywhere representative identity for `SchwartzMap.toLp` identifies
this pairing with the actual L² inner product. Its real diagonal gives equality
of L² norms. The full modular, compact reference and standalone builds pass. All 15 default
environment linters pass on each library. All 19 audited declarations use only
propext, Classical.choice and Quot.sound.

This is partial progress on the existing `fourier-l2` obligation, not completion:
Schwartz density in L², extension to a surjective linear isometry, the positive
Fourier-sign convention used by the paper, and the cutoff projection still
need implementation. No extra hypotheses replace these requirements.

The five-result Comparator specification now includes the explicit Schwartz
Parseval pairing. The preceding four-result acceptance belongs to commit
938a476; the expanded acceptance is recorded below.

The expanded five-result Comparator run passed with exit 0, exact statement
and definition comparison, and Lean default kernel acceptance. Runtime was
216.584 seconds; peak memory was 2.8 GiB. See `comparator-fourier.txt` and
`comparator-fourier-hashes.json` for the log and verified input hashes.
