import RieszEuclidean.SpectralNorm

open MeasureTheory

namespace RieszEuclidean

variable {d : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- A uniform bound for the symbol bounds the action on a vector with a representing measure. -/
theorem norm_integratedUnitary_le_symbol [CompleteSpace H]
    (U : Euclidean d → H ≃ₗᵢ[ℂ] H)
    (hU : ∀ f, Continuous (fun y => U y f))
    (hadd : ∀ z y f, U z (U y f) = U (z + y) f)
    (h0 : ∀ f, U 0 f = f)
    {a : Euclidean d → ℂ} (ha : Integrable a) (f : H)
    {σ : Measure (Euclidean d)} (hσ : RepresentsCorrelation (unitaryCorrelation U f) σ)
    {M : ℝ} (hM : 0 ≤ M) (hb : ∀ θ, ‖integratedKernelSymbol a θ‖ ≤ M) :
    ‖integratedUnitary U a f‖ ≤ M * ‖f‖ := by
  letI := hσ.1
  have hs : ‖integratedUnitary U a f‖ ^ 2 ≤ M ^ 2 * ‖f‖ ^ 2 := by
    rw [integratedUnitary_spectral_norm_sq U hU hadd ha f hσ]
    calc
      (∫ θ, ‖integratedKernelSymbol a θ‖ ^ 2 ∂σ) ≤ ∫ _ : Euclidean d, M ^ 2 ∂σ := by
        apply integral_mono (integrable_integratedKernelSymbol_sq ha σ) (integrable_const _)
        intro θ
        exact pow_le_pow_left₀ (norm_nonneg _) (hb θ) 2
      _ = M ^ 2 * ‖f‖ ^ 2 := by
        rw [integral_const, smul_eq_mul, hσ.unitary_mass U h0 f]
        ring
  nlinarith [norm_nonneg (integratedUnitary U a f), norm_nonneg f,
    mul_nonneg hM (norm_nonneg f)]

/-- Spectral measures for all vectors give the uniform Fourier-symbol operator bound. -/
theorem norm_integratedUnitaryCLM_le_symbol [CompleteSpace H]
    (U : Euclidean d → H ≃ₗᵢ[ℂ] H)
    (hU : ∀ f, Continuous (fun y => U y f))
    (hadd : ∀ z y f, U z (U y f) = U (z + y) f)
    (h0 : ∀ f, U 0 f = f)
    (hσ : ∀ f, ∃ σ, RepresentsCorrelation (unitaryCorrelation U f) σ)
    {a : Euclidean d → ℂ} (ha : Integrable a)
    {M : ℝ} (hM : 0 ≤ M) (hb : ∀ θ, ‖integratedKernelSymbol a θ‖ ≤ M) :
    ‖integratedUnitaryCLM U hU ha‖ ≤ M := by
  apply (integratedUnitaryCLM U hU ha).opNorm_le_bound hM
  intro f
  obtain ⟨σ, hσf⟩ := hσ f
  exact norm_integratedUnitary_le_symbol U hU hadd h0 ha f hσf hM hb

/-- Fourier symbols respect subtraction of integrable kernels. -/
theorem integratedKernelSymbol_sub {a b : Euclidean d → ℂ}
    (ha : Integrable a) (hb : Integrable b) (θ : Euclidean d) :
    integratedKernelSymbol (fun y => a y - b y) θ =
      integratedKernelSymbol a θ - integratedKernelSymbol b θ := by
  simp only [integratedKernelSymbol, sub_mul]
  exact integral_sub (integrable_kernel_character ha θ) (integrable_kernel_character hb θ)

/-- Equal Fourier symbols give equal integrated operators, assuming spectral measures exist. -/
theorem integratedUnitaryCLM_eq_of_symbol_eq [CompleteSpace H]
    (U : Euclidean d → H ≃ₗᵢ[ℂ] H)
    (hU : ∀ f, Continuous (fun y => U y f))
    (hadd : ∀ z y f, U z (U y f) = U (z + y) f)
    (h0 : ∀ f, U 0 f = f)
    (hσ : ∀ f, ∃ σ, RepresentsCorrelation (unitaryCorrelation U f) σ)
    {a b : Euclidean d → ℂ} (ha : Integrable a) (hb : Integrable b)
    (hab : ∀ θ, integratedKernelSymbol a θ = integratedKernelSymbol b θ) :
    integratedUnitaryCLM U hU ha = integratedUnitaryCLM U hU hb := by
  have hz := norm_integratedUnitaryCLM_le_symbol U hU hadd h0 hσ (ha.sub hb)
    (M := 0) le_rfl (by
      intro θ
      change ‖integratedKernelSymbol (fun y => a y - b y) θ‖ ≤ 0
      rw [integratedKernelSymbol_sub ha hb, hab θ, _root_.sub_self, norm_zero])
  have he : integratedUnitaryCLM U hU (ha.sub hb) = 0 := norm_le_zero_iff.mp hz
  ext f
  have hf := congrArg (fun T : H →L[ℂ] H => T f) he
  change (∫ y, (a y - b y) • U y f) = 0 at hf
  simp only [sub_smul] at hf
  rw [integral_sub (integrable_unitary_smul U hU ha f)
    (integrable_unitary_smul U hU hb f)] at hf
  exact sub_eq_zero.mp hf

end RieszEuclidean
