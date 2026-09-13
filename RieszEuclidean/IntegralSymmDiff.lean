import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
open MeasureTheory Set
open scoped symmDiff
namespace RieszEuclidean
/-- A bounded observable changes its set integral by at most its bound times the
symmetric-difference volume. -/
theorem norm_setIntegral_sub_le_symmDiff {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {s t : Set α} (hs : MeasurableSet s) (ht : MeasurableSet t)
    {f : α → ℝ} (hfs : IntegrableOn f s μ) (hft : IntegrableOn f t μ)
    {C : ℝ} (hC : ∀ x, ‖f x‖ ≤ C) (hfin : μ (s ∆ t) < ⊤) :
    ‖(∫ x in s, f x ∂μ) - ∫ x in t, f x ∂μ‖ ≤ C * μ.real (s ∆ t) := by
  have hm := hs.symmDiff ht
  have hi : Integrable ((s ∆ t).indicator (fun _ => C)) μ :=
    (integrableOn_const.mpr (Or.inr hfin)).integrable_indicator hm
  have hb : ∀ x, ‖s.indicator f x - t.indicator f x‖ ≤ (s ∆ t).indicator (fun _ => C) x := by
    intro x
    by_cases hxs : x ∈ s <;> by_cases hxt : x ∈ t
    · simp [Set.symmDiff_def, hxs, hxt]
    · simpa [Set.symmDiff_def, hxs, hxt] using hC x
    · simpa [Set.symmDiff_def, hxs, hxt] using hC x
    · simp [Set.symmDiff_def, hxs, hxt]
  rw [← integral_indicator hs, ← integral_indicator ht,
    ← integral_sub (hfs.integrable_indicator hs) (hft.integrable_indicator ht)]
  calc
    _ ≤ ∫ x, (s ∆ t).indicator (fun _ => C) x ∂μ :=
      norm_integral_le_of_norm_le hi (Filter.Eventually.of_forall hb)
    _ = _ := by rw [integral_indicator_const C hm, smul_eq_mul, mul_comm]
end RieszEuclidean
