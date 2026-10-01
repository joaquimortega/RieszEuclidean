import RieszEuclidean.TitchmarshFunctions
import RieszEuclidean.TitchmarshDistributionAssembly
import RieszEuclidean.TitchmarshRegularizedConvolution

/-!
# The Titchmarsh–Lions convolution support theorem

For nonzero compactly supported tempered distributions, the convex hull of
convolution support equals the sum of the convex hulls of the factor supports.
The function theorem, local regularization, and exact convolution identity
provide the three analytic ingredients of the proof.
-/

noncomputable section
open MeasureTheory Set
open scoped Convolution Pointwise SchwartzMap

namespace RieszEuclidean.CompleteMinimal

/-- The classical Titchmarsh–Lions theorem for actual compactly supported
tempered distributions on finite-dimensional Euclidean space. -/
theorem titchmarshLions (d : ℕ) : TitchmarshLions d := by
  apply titchmarshLions_of_regularized_support
  · intro f g _ _
    exact convexHull_tsupport_convolution
      f.continuous g.continuous f.hasCompactSupport g.hasCompactSupport
  · intro u v w hu hv hc ρ σ hρ hσ
    change tsupport (distributionRegularization u ρ ⋆[
      ContinuousLinearMap.mul ℂ ℂ, volume] distributionRegularization v σ) ⊆
        distributionSupport w + tsupport (ρ : Euclidean d → ℂ) +
          tsupport (σ : Euclidean d → ℂ)
    exact hc.regularizedConvolution_support_subset hu hv hρ hσ

end RieszEuclidean.CompleteMinimal
