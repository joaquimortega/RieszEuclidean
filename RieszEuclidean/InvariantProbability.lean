import RieszEuclidean.BoxAverages
import RieszEuclidean.BoxTranslationIntegral
import RieszEuclidean.MeanRepresentation
open MeasureTheory Filter
namespace RieszEuclidean
/-- A jointly continuous additive Euclidean action on a nonempty compact metrizable
Borel space has an invariant probability measure, constructed from continuous box averages. -/
theorem exists_invariant_probability_euclidean_action {d : ℕ} {X : Type*}
    [TopologicalSpace X] [T2Space X] [CompactSpace X] [HasOuterApproxClosed X]
    [MeasurableSpace X] [BorelSpace X]
    (T : Euclidean d → C(X, X))
    (hT : Continuous (fun p : Euclidean d × X => T p.1 p.2))
    (hadd : ∀ z y x, T z (T y x) = T (y + z) x) (x₀ : X) :
    ∃ μ : Measure X, IsProbabilityMeasure μ ∧ ∀ z, MeasurePreserving (T z) μ μ := by
  let a : C(Euclidean d, X) :=
    ⟨fun y => T y x₀, hT.comp (continuous_id.prodMk continuous_const)⟩
  let A : ℕ → WeakDual ℝ C(X, ℝ) := fun n =>
    NormedSpace.Dual.toWeakDual (boxAverage (show 0 < (n : ℝ) + 1 by positivity) a)
  apply exists_invariant_probability_of_averages A
  · intro n
    exact boxAverage_mem_meanFunctionals (show 0 < (n : ℝ) + 1 by positivity) a
  · intro z f
    have hR : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
      tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
    have he := (box_translation_error_tendsto_zero (f.continuous.comp a.continuous)
      (fun y => f.norm_coe_le_norm (a y)) z).comp hR
    change Tendsto (fun n : ℕ =>
      (∫ y, f (T z (T y x₀)) ∂boxProbabilityMeasure d ((n : ℝ) + 1)) -
      ∫ y, f (T y x₀) ∂boxProbabilityMeasure d ((n : ℝ) + 1)) atTop (nhds 0)
    simpa only [a, ContinuousMap.coe_mk, hadd] using he
end RieszEuclidean
