# Koopman representation on the stationary hull

`Koopman.lean` constructs complex L² pullback isometries and unitaries, proves
composition and inverse identities, and specializes them to hull translations.
The manuscript defines T_z Γ = Γ-z and U_z f(Γ)=f(Γ+z); the public
`hullKoopmanUnitary` therefore uses pullback by T_{-z}.

The module proves the additive group law, identity, strong continuity, separability
of the stationary Hilbert space, invariance of constants, and norm one for the
constant one. Strong continuity uses Mathlib's continuity theorem for Lp
composition with continuous measure-preserving maps. Separability follows from
countable generation of the Borel sigma algebra and separability of the measure.

The modular, MainResults, and standalone builds pass. All 15 integrated modular
linters pass for 316 declarations and 368 generated declarations; all 15
standalone linters pass for 330 declarations and 373 generated declarations.
All 233 transitive axiom reports use only propext, Classical.choice, and
Quot.sound; see `koopman-axioms.txt`.
The vague-convergence equivalence is now proved in `VagueConvergence`; the
stationary blueprint node is complete. Later spectral and geometric nodes remain pending.

Official Comparator verification now covers thirteen supporting results, including
the Koopman representation and vague equivalence; see `stationary-system-validation.md`.
GitHub run 34764953503 for that published checkpoint completed successfully.
