import RieszEuclidean.TitchmarshFunctionEndpoints
import RieszEuclidean.TitchmarshConvexGeometry

/-! The convolution support theorem for continuous compactly supported functions. -/

noncomputable section
open MeasureTheory Set
open scoped Convolution Pointwise

namespace RieszEuclidean.CompleteMinimal

/-- The convex hull of convolution support is the Minkowski sum of the factor
support hulls, for actual continuous compactly supported complex functions. -/
theorem convexHull_tsupport_convolution {d : ℕ}
    {f g : Euclidean d → ℂ} (hf : Continuous f) (hg : Continuous g)
    (hfc : HasCompactSupport f) (hgc : HasCompactSupport g) :
    convexHull ℝ (tsupport (f ⋆[ContinuousLinearMap.mul ℂ ℂ, volume] g)) =
      convexHull ℝ (tsupport f) + convexHull ℝ (tsupport g) := by
  have hwc : HasCompactSupport (f ⋆[ContinuousLinearMap.mul ℂ ℂ, volume] g) :=
    hfc.convolution (L := ContinuousLinearMap.mul ℂ ℂ) hgc
  have hs : tsupport (f ⋆[ContinuousLinearMap.mul ℂ ℂ, volume] g) ⊆
      tsupport f + tsupport g := by
    apply closure_minimal
    · exact (MeasureTheory.support_convolution_subset
        (L := ContinuousLinearMap.mul ℂ ℂ) (μ := volume)).trans
        (Set.add_subset_add (subset_tsupport f) (subset_tsupport g))
    · exact (IsCompact.add hfc hgc).isClosed
  apply convexHull_tsupport_eq_add_of_all_direction_endpoint_of_compact hwc
  · rw [← convexHull_add]
    exact convexHull_mono hs
  · intro ℓ T hvan
    exact RieszEuclidean.TitchmarshFunctionAlgebra.convolution_halfspace_endpoint
      hf hg hfc hgc ℓ hvan

end RieszEuclidean.CompleteMinimal
