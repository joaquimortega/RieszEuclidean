import RieszEuclidean.EuclideanBoxes
import RieszEuclidean.CompactMeans
import Mathlib.MeasureTheory.Integral.Bochner.Basic
open MeasureTheory
namespace RieszEuclidean
/-- Continuous observables along a continuous orbit are integrable over a normalized box. -/
theorem integrable_box_observable {d : ℕ} {X : Type*} [TopologicalSpace X] [CompactSpace X]
    {R : ℝ} (hR : 0 < R) (a : C(Euclidean d, X)) (f : C(X, ℝ)) :
    Integrable (fun y => f (a y)) (boxProbabilityMeasure d R) := by
  letI := boxProbabilityMeasure_isProbability d hR
  exact (integrable_const ‖f‖).mono' (f.continuous.comp a.continuous).aestronglyMeasurable
    (Filter.Eventually.of_forall fun y => f.norm_coe_le_norm (a y))
/-- Box averaging as a real linear functional. -/
noncomputable def boxAverageLinear {d : ℕ} {X : Type*} [TopologicalSpace X] [CompactSpace X]
    {R : ℝ} (hR : 0 < R) (a : C(Euclidean d, X)) : C(X, ℝ) →ₗ[ℝ] ℝ where
  toFun f := ∫ y, f (a y) ∂boxProbabilityMeasure d R
  map_add' f g := integral_add (integrable_box_observable hR a f) (integrable_box_observable hR a g)
  map_smul' r f := integral_smul r (fun y => f (a y))
/-- Averaging over a probability box is bounded by the supremum norm. -/
theorem norm_boxAverageLinear_le {d : ℕ} {X : Type*} [TopologicalSpace X] [CompactSpace X]
    {R : ℝ} (hR : 0 < R) (a : C(Euclidean d, X)) (f : C(X, ℝ)) :
    ‖boxAverageLinear hR a f‖ ≤ ‖f‖ := by
  letI := boxProbabilityMeasure_isProbability d hR
  have h := norm_integral_le_of_norm_le_const
    (μ := boxProbabilityMeasure d R) (Filter.Eventually.of_forall fun y => f.norm_coe_le_norm (a y))
  simpa [boxAverageLinear] using h
/-- The actual continuous box average, viewed as a bounded functional. -/
noncomputable def boxAverage {d : ℕ} {X : Type*} [TopologicalSpace X] [CompactSpace X]
    {R : ℝ} (hR : 0 < R) (a : C(Euclidean d, X)) : C(X, ℝ) →L[ℝ] ℝ :=
  (boxAverageLinear hR a).mkContinuous 1 (fun f => by simpa using norm_boxAverageLinear_le hR a f)
/-- The functional evaluates to the normalized Lebesgue box integral. -/
theorem boxAverage_apply {d : ℕ} {X : Type*} [TopologicalSpace X] [CompactSpace X]
    {R : ℝ} (hR : 0 < R) (a : C(Euclidean d, X)) (f : C(X, ℝ)) :
    boxAverage hR a f = ∫ y, f (a y) ∂boxProbabilityMeasure d R := rfl
/-- Actual box averages belong to the compact set of normalized positive functionals. -/
theorem boxAverage_mem_meanFunctionals {d : ℕ} {X : Type*}
    [TopologicalSpace X] [CompactSpace X] {R : ℝ} (hR : 0 < R) (a : C(Euclidean d, X)) :
    NormedSpace.Dual.toWeakDual (boxAverage hR a) ∈ meanFunctionals X := by
  letI := boxProbabilityMeasure_isProbability d hR
  refine ⟨?_, ?_, ?_⟩
  · apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num : (0 : ℝ) ≤ 1)
    intro f
    simpa [boxAverage] using norm_boxAverageLinear_le hR a f
  · change (∫ _ : Euclidean d, (1 : ℝ) ∂boxProbabilityMeasure d R) = 1
    simp
  · intro f hf
    exact integral_nonneg (fun y => hf (a y))
end RieszEuclidean
