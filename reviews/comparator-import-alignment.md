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

The first eleven-result run failed at the configuration-space metrizable instance.
Direct Lean environment inspection showed that the modular proof selected the
second-countable regular-space route, while the combined imports selected
complete metrizability through `PolishSpace.instENNReal`. Importing
`Mathlib.Topology.MetricSpace.Polish` in `ConfigurationTopology` makes that same
standard instance available to both compilations. The failed run is preserved
in `comparator-invariant-measure.txt`; the aligned rerun is separate.

A broader direct environment comparison also found that the new real-functional
helpers used the normed-field route to the real normed-space instance, whereas
the standalone imports supplied `RCLike.toInnerProductSpaceReal`.
`CompactMeans`, `PositiveFunctionalMeasure`, and `IntegralSymmDiff` explicitly
import the standard inner-product-space basics to align inference. This fixes
proof export identity without changing their mathematical statements.

For the stationary-system expansion, direct comparison found alternate routes to
measurable singleton and countably generated Borel instances in the new counting
integral and L² separability proofs. Explicit standard-Borel and paracompactness
imports align these routes. `VagueConvergence` also imports `RCLike.Basic` so its
positivity proof uses the same real characteristic-zero instance as the standalone.
The mathematical statements and permitted axioms are unchanged.
