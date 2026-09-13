import RieszEuclidean.BumpFourier
import RieszEuclidean.BumpSynthesis
open MeasureTheory
namespace RieszEuclidean
/-- Translation of a bump introduces exactly the paper's exponential phase. -/
theorem inverseFourier_translate {d : ℕ} (b : Euclidean d → ℂ) (t x : Euclidean d) :
    Real.fourierIntegralInv (fun ξ => b (ξ - t)) x =
      exponential t x * Real.fourierIntegralInv b x := by
  have h := congrFun (VectorFourier.fourierIntegral_comp_add_right Real.fourierChar volume
    (-innerₗ (Euclidean d)) b (-t)) x
  simpa [Real.fourierIntegralInv, Function.comp_def, sub_eq_add_neg, Circle.smul_def,
    Real.fourierChar_apply, exponential_eq_phase] using h
/-- The actual unitary transform of a translated L² bump has its phased integral representative. -/
theorem paperFourierL2_translated_bump {d : ℕ} (b : SchwartzMap (Euclidean d) ℂ)
    (t : Euclidean d) :
    (paperFourierL2 d (translationL2 (-t) (b.toLp 2 volume)) : Euclidean d → ℂ) =ᵐ[volume]
      fun x => exponential t x * Real.fourierIntegralInv b x := by
  have hb : Integrable (b.toLp 2 volume : Euclidean d → ℂ) :=
    b.integrable.congr (b.coeFn_toLp 2 volume).symm
  have h := paperFourierL2_eq_integral _ (translationL2_integrable (-t) _ hb)
  apply h.trans
  apply Filter.Eventually.of_forall
  intro x
  rw [show Real.fourierIntegralInv (translationL2 (-t) (b.toLp 2 volume) : Euclidean d → ℂ) x =
      Real.fourierIntegralInv (fun ξ => b (ξ - t)) x from ?_]
  · exact inverseFourier_translate b t x
  · rw [Real.fourierIntegralInv_eq, Real.fourierIntegralInv_eq]
    apply integral_congr_ae
    filter_upwards [translated_bump_coe b t] with ξ hξ
    rw [hξ]
end RieszEuclidean
