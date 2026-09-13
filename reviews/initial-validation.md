# Initial validation

All implemented modules build under Lean 4.19.0 with the pinned Mathlib revision.
The blueprint checker validates four proved-scope nodes and 21 pending full-paper
obligations. Its --require-complete mode was run and failed for the pending
obligations, as required.

initial-axioms.txt records eight declaration reports, using only propext,
Classical.choice and Quot.sound. This audit covers the implemented declarations;
no unconditional main theorem declaration is present yet.

The manuscript was rebuilt without LaTeX warnings. The repository-link paragraph
was visually checked. The repository source agrees with the workspace source.
Dependency checkouts are local and independent of the old project; Mathlib and
Batteries have clean Git worktrees.
