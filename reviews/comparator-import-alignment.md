# Aligning modular and standalone inference

The first nine-result Comparator run failed at
`RieszEuclidean.memLp_exists_schwartz_eLpNorm_lt`. Both files compiled and all
linters passed. Inspection of the imported Lean constants showed equal theorem
types and universe parameters but different proof values.

The standalone's combined imports supplied the paracompactness route to
`NormalSpace`, while the modular Schwartz-density proof used regularity and
second countability. Adding the explicit Mathlib EMetricSpace.Paracompact import
to SchwartzDensity aligns the available instances. After recompilation, direct
comparison reports equal types, levels, and proof values for the previously
mismatched theorem. No comparator logic, permitted axioms or theorem statement
was changed. Full Comparator verification must still be rerun.

Further inspection aligned order-closed topology and complete-metrizability imports.
The range completeness proof explicitly selects the metric T₀ instance. A separate
compilation under the full standalone import set passes all 15 linters and yields
exactly equal type, universe parameters and proof value for range_completeSpace.
The official rerun is logged in comparator-initial-gap-aligned.txt.
