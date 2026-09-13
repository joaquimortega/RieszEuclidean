import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed
open MeasureTheory Set CompactlySupportedContinuousMap
open scoped CompactlySupported
namespace RieszEuclidean
/-- A normalized positive functional on a compact space represents a probability measure. -/
theorem rieszMeasure_isProbability {X : Type*} [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
    {Λ : C_c(X, ℝ) →ₗ[ℝ] ℝ} (hΛ : ∀ f, 0 ≤ f → 0 ≤ Λ f) (h1 : Λ (ContinuousMap.liftCompactlySupported (ContinuousMap.const X 1)) = 1) :
    IsProbabilityMeasure (RealRMK.rieszMeasure hΛ) := by
  have hi := RealRMK.integral_rieszMeasure hΛ (ContinuousMap.liftCompactlySupported (ContinuousMap.const X 1))
  have hm : ((RealRMK.rieszMeasure hΛ) univ).toReal = 1 := by
    rw [h1] at hi
    change (∫ _ : X, (1 : ℝ) ∂RealRMK.rieszMeasure hΛ) = 1 at hi
    simpa using hi
  have hf : (RealRMK.rieszMeasure hΛ) univ ≠ ⊤ := by
    intro he
    simp [he] at hm
  exact ⟨(ENNReal.toReal_eq_toReal hf (by simp)).mp (by simpa using hm)⟩
/-- Invariance of a normalized positive functional implies invariance of its measure. -/
theorem rieszMeasure_measurePreserving {X : Type*} [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [HasOuterApproxClosed X] [MeasurableSpace X] [BorelSpace X]
    {Λ : C_c(X, ℝ) →ₗ[ℝ] ℝ} (hΛ : ∀ f, 0 ≤ f → 0 ≤ Λ f)
    (h1 : Λ (ContinuousMap.liftCompactlySupported (ContinuousMap.const X 1)) = 1)
    (T : C(X, X))
    (hInv : ∀ f : C_c(X, ℝ),
      Λ (ContinuousMap.liftCompactlySupported (f.toContinuousMap.comp T)) = Λ f) :
    MeasurePreserving T (RealRMK.rieszMeasure hΛ) (RealRMK.rieszMeasure hΛ) := by
  letI := rieszMeasure_isProbability hΛ h1
  refine ⟨T.continuous.measurable, ?_⟩
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro f
  rw [integral_map T.continuous.measurable.aemeasurable f.continuous.aestronglyMeasurable]
  let g : C_c(X, ℝ) := ContinuousMap.liftCompactlySupported f.toContinuousMap
  calc
    (∫ x, f (T x) ∂RealRMK.rieszMeasure hΛ) =
        Λ (ContinuousMap.liftCompactlySupported (g.toContinuousMap.comp T)) :=
      RealRMK.integral_rieszMeasure hΛ
        (ContinuousMap.liftCompactlySupported (g.toContinuousMap.comp T))
    _ = Λ g := hInv g
    _ = ∫ x, f x ∂RealRMK.rieszMeasure hΛ := (RealRMK.integral_rieszMeasure hΛ g).symm
end RieszEuclidean
