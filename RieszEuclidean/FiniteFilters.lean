import RieszEuclidean.FourierKernel
import RieszEuclidean.FejerWeights
import RieszEuclidean.IntegratedAlgebra
import RieszEuclidean.FejerCoefficients
import RieszEuclidean.SmoothedFejer
import RieszEuclidean.SymbolBound
open MeasureTheory
namespace RieszEuclidean
/-- The domain kernel is the negative-sign transform of its indicator. -/
theorem domainKernel_eq_fourier {d : ℕ} (Ω : Set (Euclidean d)) (hΩ : MeasurableSet Ω)
    (y : Euclidean d) :
    domainKernel Ω y = Real.fourierIntegral (Ω.indicator (fun _ => (1 : ℂ))) y := by
  rw [domainKernel, Real.fourierIntegral_eq, ← integral_indicator hΩ]
  apply integral_congr_ae
  filter_upwards [] with x
  by_cases hx : x ∈ Ω <;> simp [hx, Circle.smul_def]
/-- A finite domain has a continuous Fourier kernel. -/
theorem continuous_domainKernel {d : ℕ} (Ω : Set (Euclidean d)) (hΩ : MeasurableSet Ω)
    (hfin : volume Ω ≠ ⊤) : Continuous (domainKernel Ω) := by
  have hi : Integrable (Ω.indicator (fun _ : Euclidean d => (1 : ℂ))) :=
    (integrable_indicator_iff hΩ).mpr (integrableOn_const.mpr (Or.inr hfin.lt_top))
  rw [show domainKernel Ω = Real.fourierIntegral (Ω.indicator (fun _ => (1 : ℂ))) from
    funext (domainKernel_eq_fourier Ω hΩ)]
  exact VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
    (continuous_fst.inner continuous_snd) hi
/-- The domain volume uniformly bounds its Fourier kernel. -/
theorem norm_domainKernel_le {d : ℕ} (Ω : Set (Euclidean d)) (y : Euclidean d) :
    ‖domainKernel Ω y‖ ≤ volume.real Ω := by
  apply (norm_integral_le_integral_norm _).trans_eq
  simp
/-- Reflection conjugates the domain kernel. -/
theorem domainKernel_neg {d : ℕ} (Ω : Set (Euclidean d)) (y : Euclidean d) :
    domainKernel Ω (-y) = star (domainKernel Ω y) := by
  change (∫ x in Ω, (Real.fourierChar (-inner (𝕜 := ℝ) x (-y)) : ℂ)) =
    starRingEnd ℂ (∫ x in Ω, (Real.fourierChar (-inner (𝕜 := ℝ) x y) : ℂ))
  rw [← integral_conj]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [inner_neg_right]
  rw [Real.fourierChar.map_neg_eq_inv, Circle.coe_inv_eq_conj]
/-- The actual finite-radius stationary filter kernel in the manuscript. -/
noncomputable def finiteFilterKernel {d : ℕ} (Ω : Set (Euclidean d))
    (t : Euclidean d) (R : ℝ) (y : Euclidean d) : ℂ :=
  (fejerWeight R y : ℂ) * domainKernel Ω y *
    (Real.fourierChar (inner (𝕜 := ℝ) t y) : ℂ)
/-- Positive-radius finite filters have integrable kernels. -/
theorem integrable_finiteFilterKernel {d : ℕ} (Ω : Set (Euclidean d))
    (hΩ : MeasurableSet Ω) (hfin : volume Ω ≠ ⊤) (t : Euclidean d)
    {R : ℝ} (hR : 0 < R) : Integrable (finiteFilterKernel Ω t R) := by
  have hc : Continuous (finiteFilterKernel Ω t R) :=
    (((Complex.continuous_ofReal.comp (continuous_fejerWeight R)).mul (continuous_domainKernel Ω hΩ hfin)).mul
      ((continuous_subtype_val.comp Real.continuous_fourierChar).comp
        (continuous_const.inner continuous_id)))
  apply ((integrable_fejerWeight hR).mul_const (volume.real Ω)).mono' hc.aestronglyMeasurable
  filter_upwards [] with y
  change ‖(fejerWeight R y : ℂ) * domainKernel Ω y *
    (Real.fourierChar (inner (𝕜 := ℝ) t y) : ℂ)‖ ≤ fejerWeight R y * volume.real Ω
  simp only [norm_mul, Circle.norm_coe, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (fejerWeight_nonneg R y)]
  exact mul_le_mul_of_nonneg_left (norm_domainKernel_le Ω y) (fejerWeight_nonneg R y)
/-- The finite filter kernel is fixed by reflected conjugation. -/
theorem adjointKernel_finiteFilterKernel {d : ℕ} (Ω : Set (Euclidean d))
    (t : Euclidean d) (R : ℝ) :
    adjointKernel (finiteFilterKernel Ω t R) = finiteFilterKernel Ω t R := by
  funext y
  simp [adjointKernel, finiteFilterKernel, domainKernel_neg,
    inner_neg_right, Real.fourierChar.map_neg_eq_inv, Circle.coe_inv_eq_conj,
    mul_comm, mul_left_comm, mul_assoc]
/-- The manuscript's finite stationary cutoff operator. -/
noncomputable def finiteFilter {d : ℕ} {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (U : Euclidean d → H ≃ₗᵢ[ℂ] H)
    (hU : ∀ f, Continuous (fun y => U y f))
    (Ω : Set (Euclidean d)) (hΩ : MeasurableSet Ω) (hfin : volume Ω ≠ ⊤)
    (t : Euclidean d) {R : ℝ} (hR : 0 < R) : H →L[ℂ] H :=
  integratedUnitaryCLM U hU (integrable_finiteFilterKernel Ω hΩ hfin t hR)
/-- Finite stationary filters are self-adjoint without invoking Bochner existence. -/
theorem finiteFilter_isSelfAdjoint {d : ℕ} {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (U : Euclidean d → H ≃ₗᵢ[ℂ] H)
    (hU : ∀ f, Continuous (fun y => U y f))
    (hadd : ∀ z y f, U z (U y f) = U (z + y) f) (h0 : ∀ f, U 0 f = f)
    (Ω : Set (Euclidean d)) (hΩ : MeasurableSet Ω) (hfin : volume Ω ≠ ⊤)
    (t : Euclidean d) {R : ℝ} (hR : 0 < R) :
    IsSelfAdjoint (finiteFilter U hU Ω hΩ hfin t hR) := by
  change (integratedUnitaryCLM U hU (integrable_finiteFilterKernel Ω hΩ hfin t hR)).adjoint = _
  rw [integratedUnitaryCLM_adjoint U hU hadd h0]
  ext f
  apply integratedUnitary_congr_ae
  exact Filter.Eventually.of_forall (congrFun (adjointKernel_finiteFilterKernel Ω t R))
/-- Modulation translates the finite filter's actual Fourier symbol. -/
theorem integratedKernelSymbol_finiteFilterKernel {d : ℕ}
    (Ω : Set (Euclidean d)) (t θ : Euclidean d) (R : ℝ) :
    integratedKernelSymbol (finiteFilterKernel Ω t R) θ =
      integratedKernelSymbol (fun y => (fejerWeight R y : ℂ) * domainKernel Ω y) (t + θ) := by
  apply integral_congr_ae
  filter_upwards [] with y
  simp only [finiteFilterKernel, inner_add_right, Real.fourierChar.map_add_eq_mul, Circle.coe_mul,
    real_inner_comm t y]
  ring
/-- The actual finite filter has the translated smoothed-domain symbol. -/
theorem integratedKernelSymbol_finiteFilterKernel_eq_fejerCutoff {d : ℕ}
    (Ω : Set (Euclidean d)) (hΩ : MeasurableSet Ω) (hfin : volume Ω ≠ ⊤)
    (t : Euclidean d) {R : ℝ} (hR : 0 < R) (θ : Euclidean d) :
    integratedKernelSymbol (finiteFilterKernel Ω t R) θ =
      (fejerCutoff Ω R (t + θ) : ℂ) := by
  rw [integratedKernelSymbol_finiteFilterKernel]
  exact integratedKernelSymbol_fejerWeight_domainKernel hR hΩ hfin (t + θ)
/-- The finite stationary filters are contractions when spectral measures are supplied. -/
theorem norm_finiteFilter_le {d : ℕ} {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (U : Euclidean d → H ≃ₗᵢ[ℂ] H)
    (hU : ∀ f, Continuous (fun y => U y f))
    (hadd : ∀ z y f, U z (U y f) = U (z + y) f) (h0 : ∀ f, U 0 f = f)
    (hσ : ∀ f, ∃ σ, RepresentsCorrelation (unitaryCorrelation U f) σ)
    (Ω : Set (Euclidean d)) (hΩ : MeasurableSet Ω) (hfin : volume Ω ≠ ⊤)
    (t : Euclidean d) {R : ℝ} (hR : 0 < R) :
    ‖finiteFilter U hU Ω hΩ hfin t hR‖ ≤ 1 := by
  apply norm_integratedUnitaryCLM_le_symbol U hU hadd h0 hσ
    (integrable_finiteFilterKernel Ω hΩ hfin t hR) zero_le_one
  intro θ
  rw [integratedKernelSymbol_finiteFilterKernel_eq_fejerCutoff Ω hΩ hfin t hR θ]
  have hb := fejerCutoff_mem_Icc hΩ hR (t + θ)
  simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hb.1] using hb.2
end RieszEuclidean
