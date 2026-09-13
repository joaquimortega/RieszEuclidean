import RieszEuclidean.FejerFourier
import RieszEuclidean.FourierKernel
import RieszEuclidean.ApproximateCutoffs
open Set MeasureTheory
open scoped FourierTransform
namespace RieszEuclidean
/-- The domain kernel is precisely the negative-sign Fourier transform of its indicator. -/
theorem fourier_domain_indicator {d : ℕ} {Ω : Set (Euclidean d)} (hΩ : MeasurableSet Ω)
    (y : Euclidean d) :
    𝓕 (Ω.indicator (fun _ => (1 : ℂ))) y = domainKernel Ω y := by
  rw [Real.fourierIntegral_eq, domainKernel, ← integral_indicator hΩ]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by
    by_cases hx : x ∈ Ω <;> simp [hx, Circle.smul_def]
/-- Modulating the Fejér weight shifts its negative-sign transform to the actual box kernel. -/
theorem fourier_modulated_fejerWeight {d : ℕ} {R : ℝ} (hR : 0 < R)
    (x ξ : Euclidean d) :
    𝓕 (fun y => (fejerWeight R y : ℂ) *
      (Real.fourierChar (inner (𝕜 := ℝ) y x) : ℂ)) ξ = (fejerKernel d R (x - ξ) : ℂ) := by
  rw [← integratedKernelSymbol_fejerWeight hR, Real.fourierIntegral_eq, integratedKernelSymbol]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun y => by
    simp only [Circle.smul_def, smul_eq_mul]
    rw [mul_left_comm, ← Circle.coe_mul, ← Real.fourierChar.map_add_eq_mul]
    congr 2
    rw [inner_sub_right]
    ring_nf
/-- Reflecting the convolution variable identifies the integral of the translated kernel over Ω. -/
theorem smoothedIndicator_eq_domain_integral {d : ℕ} (k : Euclidean d → ℝ)
    {Ω : Set (Euclidean d)} (hΩ : MeasurableSet Ω) (x : Euclidean d) :
    smoothedIndicator k Ω x = ∫ ξ in Ω, k (x - ξ) := by
  rw [smoothedIndicator, ← integral_sub_left_eq_self _ volume x, ← integral_indicator hΩ]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun ξ => by
    simp only [sub_sub_cancel]
    by_cases hξ : ξ ∈ Ω <;> simp [hξ]
/-- The actual finite-filter coefficient is integrable. -/
theorem integrable_fejerWeight_domainKernel {d : ℕ} {R : ℝ} (hR : 0 < R)
    {Ω : Set (Euclidean d)} (hΩ : MeasurableSet Ω) (hfin : volume Ω ≠ ⊤) :
    Integrable (fun y => (fejerWeight R y : ℂ) * domainKernel Ω y) := by
  have hf : Integrable (Ω.indicator (fun _ => (1 : ℂ))) :=
    (integrable_indicator_iff hΩ).mpr (integrableOn_const.mpr (Or.inr hfin.lt_top))
  have hc : Continuous (domainKernel Ω) := by
    have h := VectorFourier.fourierIntegral_continuous (L := innerₗ (Euclidean d))
      Real.continuous_fourierChar (continuous_fst.inner continuous_snd) hf
    convert h using 1
    funext y
    exact (fourier_domain_indicator hΩ y).symm
  apply ((Complex.continuous_ofReal.comp (continuous_fejerWeight R)).mul hc).integrable_of_hasCompactSupport
  apply HasCompactSupport.intro (isCompact_euclideanBox d (2 * R))
  intro y hy
  simp [fejerWeight_eq_zero_outside hR y hy]
/-- The Fejér-weighted domain kernel has exactly the smoothed-indicator Fourier symbol. -/
theorem integratedKernelSymbol_fejerWeight_domainKernel {d : ℕ} {R : ℝ} (hR : 0 < R)
    {Ω : Set (Euclidean d)} (hΩ : MeasurableSet Ω) (hfin : volume Ω ≠ ⊤)
    (x : Euclidean d) :
    integratedKernelSymbol (fun y => (fejerWeight R y : ℂ) * domainKernel Ω y) x =
      (smoothedIndicator (fejerKernel d R) Ω x : ℂ) := by
  have hf : Integrable (Ω.indicator (fun _ => (1 : ℂ))) :=
    (integrable_indicator_iff hΩ).mpr (integrableOn_const.mpr (Or.inr hfin.lt_top))
  have hw : Integrable (fun y : Euclidean d => (fejerWeight R y : ℂ)) :=
    Complex.ofRealCLM.integrable_comp (integrable_fejerWeight hR)
  have ht := integral_fourier_mul hf (integrable_kernel_character hw x)
  simp only [fourier_domain_indicator hΩ, fourier_modulated_fejerWeight hR] at ht
  rw [smoothedIndicator_eq_domain_integral _ hΩ, ← integral_complex_ofReal]
  calc
    _ = ∫ y, domainKernel Ω y * ((fejerWeight R y : ℂ) *
        (Real.fourierChar (inner (𝕜 := ℝ) y x) : ℂ)) := by
      unfold integratedKernelSymbol
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun y => by ring
    _ = _ := ht
    _ = _ := by
      rw [← integral_indicator hΩ]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun ξ => by
        by_cases hξ : ξ ∈ Ω <;> simp [hξ]
end RieszEuclidean
