import RieszEuclidean.FourierAgreement
noncomputable section
open MeasureTheory Set
namespace RieszEuclidean
/-- Cutting an L² function to a finite-measure domain makes it integrable. -/
theorem domainCutoff_integrable {d : ℕ} (Ω : Set (Euclidean d)) (hΩ : MeasurableSet Ω)
    (hfin : volume Ω ≠ ⊤) (f : FullL2 d) :
    Integrable (domainCutoff Ω hΩ f : Euclidean d → ℂ) := by
  have h : Integrable (Ω.indicator (f : Euclidean d → ℂ)) volume :=
    (integrable_indicator_iff hΩ).mpr (integrableOn_Lp_of_measure_ne_top f (by norm_num) hfin)
  exact h.congr (domainCutoff_coe Ω hΩ f).symm
/-- The Fourier cutoff is the integral transform of its finite-domain frequency restriction. -/
theorem fourierProjection_integral_transform {d : ℕ} (Ω : Set (Euclidean d))
    (hΩ : MeasurableSet Ω) (hfin : volume Ω ≠ ⊤) (f : FullL2 d) :
    ((fourierProjection Ω hΩ).op f : Euclidean d → ℂ) =ᵐ[volume]
      Real.fourierIntegral (domainCutoff Ω hΩ (paperFourierL2 d f)) := by
  change (fourierL2Equiv d (domainCutoff Ω hΩ (paperFourierL2 d f)) : Euclidean d → ℂ) =ᵐ[volume] _
  exact fourierL2Equiv_eq_integral _ (domainCutoff_integrable Ω hΩ hfin _)
/-- The cutoff projection has an explicit finite-domain Fourier integral. -/
theorem fourierProjection_integral {d : ℕ} (Ω : Set (Euclidean d))
    (hΩ : MeasurableSet Ω) (hfin : volume Ω ≠ ⊤) (f : FullL2 d) :
    ((fourierProjection Ω hΩ).op f : Euclidean d → ℂ) =ᵐ[volume]
      fun v => ∫ x in Ω, Real.fourierChar (-inner (𝕜 := ℝ) x v) • paperFourierL2 d f x := by
  filter_upwards [fourierProjection_integral_transform Ω hΩ hfin f] with v hv
  rw [hv, Real.fourierIntegral_eq]
  calc
    _ = ∫ x, Ω.indicator
        (fun x => Real.fourierChar (-inner (𝕜 := ℝ) x v) • paperFourierL2 d f x) x := by
      apply integral_congr_ae
      filter_upwards [domainCutoff_coe Ω hΩ (paperFourierL2 d f)] with x hx
      rw [hx]
      by_cases hmem : x ∈ Ω <;> simp [hmem]
    _ = _ := integral_indicator hΩ
/-- The inverse transform of the domain indicator, with the paper's normalization. -/
def domainKernel {d : ℕ} (Ω : Set (Euclidean d)) (y : Euclidean d) : ℂ :=
  ∫ x in Ω, (Real.fourierChar (-inner (𝕜 := ℝ) x y) : ℂ)
/-- A domain indicator carrying a Fourier phase. -/
def phaseIndicator {d : ℕ} (Ω : Set (Euclidean d)) (v : Euclidean d) : Euclidean d → ℂ :=
  Ω.indicator (fun x => (Real.fourierChar (-inner (𝕜 := ℝ) x v) : ℂ))
/-- The phased indicator is integrable when the domain has finite measure. -/
theorem phaseIndicator_integrable {d : ℕ} (Ω : Set (Euclidean d))
    (hΩ : MeasurableSet Ω) (hfin : volume Ω ≠ ⊤) (v : Euclidean d) :
    Integrable (phaseIndicator Ω v) := by
  have h1 : Integrable (Ω.indicator (fun _ : Euclidean d => (1 : ℂ))) :=
    (integrable_indicator_iff hΩ).mpr (integrableOn_const.mpr (Or.inr hfin.lt_top))
  have h := (Real.fourierIntegral_convergent_iff v).mpr h1
  convert h using 1
  ext x
  by_cases hx : x ∈ Ω <;> simp [phaseIndicator, hx, Circle.smul_def]
/-- Transforming the phased indicator gives the translated domain kernel. -/
theorem inverseFourier_phaseIndicator {d : ℕ} (Ω : Set (Euclidean d))
    (hΩ : MeasurableSet Ω) (v w : Euclidean d) :
    Real.fourierIntegralInv (phaseIndicator Ω v) w = domainKernel Ω (v - w) := by
  rw [Real.fourierIntegralInv_eq, domainKernel, ← integral_indicator hΩ]
  apply integral_congr_ae
  filter_upwards with x
  by_cases hx : x ∈ Ω
  · simp only [phaseIndicator, Set.indicator_of_mem hx, Circle.smul_def, smul_eq_mul]
    rw [← Circle.coe_mul, ← Real.fourierChar.map_add_eq_mul]
    congr 2
    rw [inner_sub_right]
    ring
  · simp [phaseIndicator, hx]
/-- Fourier transposition gives the domain convolution kernel. -/
theorem integral_domain_inverseFourier {d : ℕ} (Ω : Set (Euclidean d))
    (hΩ : MeasurableSet Ω) (hfin : volume Ω ≠ ⊤) {f : Euclidean d → ℂ}
    (hf : Integrable f) (v : Euclidean d) :
    (∫ x in Ω, Real.fourierChar (-inner (𝕜 := ℝ) x v) • Real.fourierIntegralInv f x) =
      ∫ w, domainKernel Ω (v - w) * f w := by
  have h := integral_inverseFourier_mul hf (phaseIndicator_integrable Ω hΩ hfin v)
  calc
    _ = ∫ x, Real.fourierIntegralInv f x * phaseIndicator Ω v x := by
      rw [← integral_indicator hΩ]
      apply integral_congr_ae
      filter_upwards with x
      by_cases hx : x ∈ Ω <;> simp [phaseIndicator, hx, Circle.smul_def, mul_comm]
    _ = _ := by simpa only [inverseFourier_phaseIndicator Ω hΩ v, mul_comm] using h
/-- The paper's convolution-kernel formula, for all L¹∩L² inputs. -/
theorem fourierProjection_kernel {d : ℕ} (Ω : Set (Euclidean d))
    (hΩ : MeasurableSet Ω) (hfin : volume Ω ≠ ⊤) (f : FullL2 d)
    (hf : Integrable (f : Euclidean d → ℂ)) :
    ((fourierProjection Ω hΩ).op f : Euclidean d → ℂ) =ᵐ[volume]
      fun v => ∫ w, domainKernel Ω (v - w) * f w := by
  filter_upwards [fourierProjection_integral Ω hΩ hfin f] with v hv
  rw [hv]
  calc
    _ = ∫ x in Ω, Real.fourierChar (-inner (𝕜 := ℝ) x v) • Real.fourierIntegralInv f x := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_of_ae (paperFourierL2_eq_integral f hf)] with x hx
      rw [hx]
    _ = _ := integral_domain_inverseFourier Ω hΩ hfin hf v
end RieszEuclidean
