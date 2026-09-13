# Initial continuum API inventory

Pinned Mathlib: c44e0c8ee63ca166450922a373c7409c5d26b00b (Lean 4.19.0).
These are implementation leads, not discharged proof obligations.

- `Analysis/Distribution/FourierSchwartz.lean` provides
  `SchwartzMap.fourierTransformCLM` and `fourierTransformCLE`, inverse formulas
  and the pointwise Fourier inversion bridge. Its forward transform uses the
  negative sign; the paper's positive transform corresponds to its inverse.
- `Analysis/Distribution/SchwartzSpace.lean` provides `memLp`, `toLp`,
  `coeFn_toLp`, `norm_toLp`, `toLpCLM` and `injective_toLp`.
  No ready-made dense-range Schwartz-to-L² lemma was found in the initial search.
- `Analysis/Fourier/FourierTransform.lean` provides
  `VectorFourier.integral_bilin_fourierIntegral_eq_flip` and
  `integral_fourierIntegral_smul_eq_flip`, useful for a Parseval proof.
  `Real.fourierIntegralInv_eq` is the positive-character integral formula.
- `MeasureTheory/Function/ContinuousMapDense.lean` provides
  `MemLp.exists_hasCompactSupport_eLpNorm_sub_le`.
  `Analysis/Calculus/BumpFunction/SmoothApprox.lean` provides smooth
  approximation of uniformly continuous functions. These can support a proof
  of Schwartz density with compactly supported smooth approximation.
- `Topology/MetricSpace/Closeds.lean` provides compactness of the closed-set
  hyperspace for a compact metric ambient space. Together with the one-point
  compactification this is a possible route to local configuration compactness;
  the equivalence with Beurling matching and continuous real translations still
  has to be proved.
- The old BallSpectral module constructs measures on a compact torus using
  lattice correlation means. It is not a continuum Bochner implementation.
  Its generic control-measure and dominated-limit arguments may be extracted.
- The old BallGeometry module uses an arc measure, not literal Hausdorff surface
  measure. Copying it alone does not discharge the source's sphere lemma.

The next central task is the Euclidean Fourier L²/bump construction. Affine
transport and projection limits are already proved and should not be reimplemented.

## Density construction verified in isolation

A direct `compactSchwartz` construction now elaborates in the working scratch
file `/tmp/CompactSchwartz.lean`. Given `ContDiff ℝ ∞ f` and
`HasCompactSupport f`, its decay estimate uses
`HasCompactSupport.iteratedFDeriv`, compact support of the norm and product,
`ContDiff.continuous_iteratedFDeriv`, and
`HasCompactSupport.exists_bound_of_continuous`. This supplies the embedding
needed after compactly supported smooth approximation. It has not yet been
integrated into the library or counted as completing density.

For the next approximation step,
`Continuous.exists_contDiff_dist_le_of_forall_mem_ball_dist_le` is stronger than
uniform approximation alone: its local bound with delta zero forces the smooth
approximant to vanish outside a thickening of the original compact support.
This should preserve compact support while controlling the L² error on a fixed
finite-measure thickening. This route remains to be implemented.
