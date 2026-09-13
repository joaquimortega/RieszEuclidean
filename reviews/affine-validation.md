# Affine transport validation

The independent L2Transport and Affine modules compile in the new project.
They preserve the actual exponential synthesis predicate for every finite
Euclidean dimension, with the paper's 2π normalization. The determinant,
transpose frequency map, inverse unit phases and a.e. pullback formula are proved.

The blueprint now has five proved-scope nodes and twenty pending obligations.
All twelve audited declaration reports use only standard Lean axioms.
The axiom checker parses those reports and rejects missing reports and any
additional axiom, rather than merely printing a list.

The initial GitHub build (run 34752264532, commit 2507530) completed successfully
on a fresh runner. It predates the affine modules; their GitHub build is checked
separately after this commit.
