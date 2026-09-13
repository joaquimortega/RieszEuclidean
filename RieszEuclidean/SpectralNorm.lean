import RieszEuclidean.IntegratedUnitary
import RieszEuclidean.SpectralMeasures
import Mathlib.MeasureTheory.Integral.Prod
open MeasureTheory
namespace RieszEuclidean
variable {d : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
/-- Absolute integrability of the correlation Gram kernel justifies Fubini. -/
theorem integrable_unitaryCorrelation_kernel
    (U : Euclidean d → H ≃ₗᵢ[ℂ] H)
    (hU : ∀ f, Continuous (fun y => U y f))
    {a : Euclidean d → ℂ} (ha : Integrable a) (f : H) :
    Integrable (fun p : Euclidean d × Euclidean d =>
      star (a p.2) * a p.1 * unitaryCorrelation U f (p.1 - p.2))
      (volume.prod volume) := by
  have hm := ((continuous_star.comp_aestronglyMeasurable
    ha.aestronglyMeasurable.snd).mul ha.aestronglyMeasurable.fst).mul
    ((continuous_unitaryCorrelation U hU f).comp
      (continuous_fst.sub continuous_snd)).aestronglyMeasurable
  apply ((ha.norm.mul_prod ha.norm).mul_const (‖f‖ ^ 2)).mono' hm
  filter_upwards [] with p
  change ‖star (a p.2) * a p.1 * unitaryCorrelation U f (p.1 - p.2)‖ ≤
    ‖a p.1‖ * ‖a p.2‖ * ‖f‖ ^ 2
  simp only [norm_mul, norm_star]
  calc
    ‖a p.2‖ * ‖a p.1‖ * ‖unitaryCorrelation U f (p.1 - p.2)‖ ≤
        ‖a p.2‖ * ‖a p.1‖ * ‖f‖ ^ 2 :=
      mul_le_mul_of_nonneg_left (norm_unitaryCorrelation_le U f _)
        (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    _ = ‖a p.1‖ * ‖a p.2‖ * ‖f‖ ^ 2 := by ring
/-- The positive-sign Fourier symbol of an integrated kernel. -/
noncomputable def integratedKernelSymbol (a : Euclidean d → ℂ) (θ : Euclidean d) : ℂ :=
  ∫ y, a y * (Real.fourierChar (inner (𝕜 := ℝ) y θ) : ℂ)
/-- Modulation by a Fourier character preserves integrability. -/
theorem integrable_kernel_character {a : Euclidean d → ℂ} (ha : Integrable a)
    (θ : Euclidean d) :
    Integrable (fun y => a y * (Real.fourierChar (inner (𝕜 := ℝ) y θ) : ℂ)) := by
  apply ha.norm.mono' (ha.aestronglyMeasurable.mul
    ((continuous_subtype_val.comp Real.continuous_fourierChar).comp
      (continuous_id.inner continuous_const)).aestronglyMeasurable)
  filter_upwards [] with y
  simp
/-- The three-variable Fourier Gram kernel is absolutely integrable. -/
theorem integrable_fourier_gram_kernel {a : Euclidean d → ℂ} (ha : Integrable a)
    (σ : Measure (Euclidean d)) [IsFiniteMeasure σ] :
    Integrable (fun q : (Euclidean d × Euclidean d) × Euclidean d =>
      (a q.1.1 * (Real.fourierChar (inner (𝕜 := ℝ) q.1.1 q.2) : ℂ)) *
      star (a q.1.2 * (Real.fourierChar (inner (𝕜 := ℝ) q.1.2 q.2) : ℂ)))
      ((volume.prod volume).prod σ) := by
  have hc₁ : Continuous (fun q : (Euclidean d × Euclidean d) × Euclidean d =>
      (Real.fourierChar (inner (𝕜 := ℝ) q.1.1 q.2) : ℂ)) :=
    (continuous_subtype_val.comp Real.continuous_fourierChar).comp
      ((continuous_fst.fst).inner continuous_snd)
  have hc₂ : Continuous (fun q : (Euclidean d × Euclidean d) × Euclidean d =>
      (Real.fourierChar (inner (𝕜 := ℝ) q.1.2 q.2) : ℂ)) :=
    (continuous_subtype_val.comp Real.continuous_fourierChar).comp
      ((continuous_fst.snd).inner continuous_snd)
  have hy : AEStronglyMeasurable (fun q : (Euclidean d × Euclidean d) × Euclidean d =>
      a q.1.1 * (Real.fourierChar (inner (𝕜 := ℝ) q.1.1 q.2) : ℂ))
      ((volume.prod volume).prod σ) :=
    ha.aestronglyMeasurable.fst.fst.mul
      hc₁.aestronglyMeasurable
  have hw : AEStronglyMeasurable (fun q : (Euclidean d × Euclidean d) × Euclidean d =>
      a q.1.2 * (Real.fourierChar (inner (𝕜 := ℝ) q.1.2 q.2) : ℂ))
      ((volume.prod volume).prod σ) :=
    ha.aestronglyMeasurable.snd.fst.mul
      hc₂.aestronglyMeasurable
  apply ((ha.norm.mul_prod ha.norm).mul_prod (integrable_const (μ := σ) (1 : ℝ))).mono'
    (hy.mul (continuous_star.comp_aestronglyMeasurable hw))
  filter_upwards [] with q
  change ‖(a q.1.1 * (Real.fourierChar (inner (𝕜 := ℝ) q.1.1 q.2) : ℂ)) *
    star (a q.1.2 * (Real.fourierChar (inner (𝕜 := ℝ) q.1.2 q.2) : ℂ))‖ ≤
    (‖a q.1.1‖ * ‖a q.1.2‖) * 1
  simp
/-- Character differences factor the Fourier Gram kernel with the required conjugation. -/
theorem fourier_gram_factor (a : Euclidean d → ℂ) (y w θ : Euclidean d) :
    star (a w) * a y * (Real.fourierChar (inner (𝕜 := ℝ) (y - w) θ) : ℂ) =
      (a y * (Real.fourierChar (inner (𝕜 := ℝ) y θ) : ℂ)) *
      star (a w * (Real.fourierChar (inner (𝕜 := ℝ) w θ) : ℂ)) := by
  rw [inner_sub_left, Real.fourierChar.map_sub_eq_div, div_eq_mul_inv,
    Circle.coe_mul, Circle.coe_inv_eq_conj]
  simp only [star_mul, starRingEnd_apply]
  ring
/-- Integrating a factored Fourier Gram kernel gives the squared symbol modulus. -/
theorem integral_fourier_gram (a : Euclidean d → ℂ) (θ : Euclidean d) :
    (∫ p : Euclidean d × Euclidean d,
      (a p.1 * (Real.fourierChar (inner (𝕜 := ℝ) p.1 θ) : ℂ)) *
      star (a p.2 * (Real.fourierChar (inner (𝕜 := ℝ) p.2 θ) : ℂ))
      ∂(volume.prod volume)) = (‖integratedKernelSymbol a θ‖ : ℂ) ^ 2 := by
  trans (∫ y, a y * (Real.fourierChar (inner (𝕜 := ℝ) y θ) : ℂ)) *
    (∫ w, star (a w * (Real.fourierChar (inner (𝕜 := ℝ) w θ) : ℂ)))
  · exact integral_prod_mul (L := ℂ) (μ := volume) (ν := volume)
      (fun y : Euclidean d => a y * (Real.fourierChar (inner (𝕜 := ℝ) y θ) : ℂ))
      (fun w : Euclidean d => star (a w * (Real.fourierChar (inner (𝕜 := ℝ) w θ) : ℂ)))
  change integratedKernelSymbol a θ *
    (∫ w, starRingEnd ℂ (a w * (Real.fourierChar (inner (𝕜 := ℝ) w θ) : ℂ))) = _
  rw [integral_conj]
  exact RCLike.mul_conj (integratedKernelSymbol a θ)
/-- A supplied representing measure gives the spectral norm identity for every L¹ kernel. -/
theorem integratedUnitary_spectral_norm_sq [CompleteSpace H]
    (U : Euclidean d → H ≃ₗᵢ[ℂ] H)
    (hU : ∀ f, Continuous (fun y => U y f))
    (hadd : ∀ z y f, U z (U y f) = U (z + y) f)
    {a : Euclidean d → ℂ} (ha : Integrable a) (f : H)
    {σ : Measure (Euclidean d)} (hσ : RepresentsCorrelation (unitaryCorrelation U f) σ) :
    ‖integratedUnitary U a f‖ ^ 2 = ∫ θ, ‖integratedKernelSymbol a θ‖ ^ 2 ∂σ := by
  letI := hσ.1
  have he : (‖integratedUnitary U a f‖ : ℂ) ^ 2 =
      ∫ θ, (‖integratedKernelSymbol a θ‖ : ℂ) ^ 2 ∂σ := by
    calc
      (‖integratedUnitary U a f‖ : ℂ) ^ 2 =
          ∫ y, ∫ w, star (a w) * a y * unitaryCorrelation U f (y - w) :=
        integratedUnitary_norm_sq U hU hadd ha f
      _ = ∫ p : Euclidean d × Euclidean d,
          star (a p.2) * a p.1 * unitaryCorrelation U f (p.1 - p.2)
          ∂(volume.prod volume) :=
        (integral_prod _ (integrable_unitaryCorrelation_kernel U hU ha f)).symm
      _ = ∫ p : Euclidean d × Euclidean d, ∫ θ,
          (a p.1 * (Real.fourierChar (inner (𝕜 := ℝ) p.1 θ) : ℂ)) *
          star (a p.2 * (Real.fourierChar (inner (𝕜 := ℝ) p.2 θ) : ℂ))
          ∂σ ∂(volume.prod volume) := by
        apply integral_congr_ae
        filter_upwards [] with p
        rw [hσ.2 (p.1 - p.2), ← integral_const_mul]
        apply integral_congr_ae
        filter_upwards [] with θ
        exact fourier_gram_factor a p.1 p.2 θ
      _ = ∫ θ, ∫ p : Euclidean d × Euclidean d,
          (a p.1 * (Real.fourierChar (inner (𝕜 := ℝ) p.1 θ) : ℂ)) *
          star (a p.2 * (Real.fourierChar (inner (𝕜 := ℝ) p.2 θ) : ℂ))
          ∂(volume.prod volume) ∂σ :=
        integral_integral_swap (integrable_fourier_gram_kernel ha σ)
      _ = ∫ θ, (‖integratedKernelSymbol a θ‖ : ℂ) ^ 2 ∂σ := by
        apply integral_congr_ae
        filter_upwards [] with θ
        exact integral_fourier_gram a θ
  have he' : ((‖integratedUnitary U a f‖ ^ 2 : ℝ) : ℂ) =
      ((∫ θ, ‖integratedKernelSymbol a θ‖ ^ 2 ∂σ : ℝ) : ℂ) := by
    calc
      ((‖integratedUnitary U a f‖ ^ 2 : ℝ) : ℂ) =
          ∫ θ, (‖integratedKernelSymbol a θ‖ : ℂ) ^ 2 ∂σ := by
        simpa only [Complex.ofReal_pow] using he
      _ = ∫ θ, ((‖integratedKernelSymbol a θ‖ ^ 2 : ℝ) : ℂ) ∂σ := by
        apply integral_congr_ae
        filter_upwards [] with θ
        exact (Complex.ofReal_pow _ _).symm
      _ = ((∫ θ, ‖integratedKernelSymbol a θ‖ ^ 2 ∂σ : ℝ) : ℂ) := integral_ofReal
  exact_mod_cast he'
/-- The kernel symbol is exactly the positive Euclidean Fourier transform. -/
theorem integratedKernelSymbol_eq_fourierInv (a : Euclidean d → ℂ) (θ : Euclidean d) :
    integratedKernelSymbol a θ = Real.fourierIntegralInv a θ := by
  rw [integratedKernelSymbol, Real.fourierIntegralInv_eq]
  apply integral_congr_ae
  filter_upwards [] with y
  simp [Circle.smul_def, real_inner_comm, mul_comm]
/-- The squared kernel symbol is integrable against every finite spectral measure. -/
theorem integrable_integratedKernelSymbol_sq {a : Euclidean d → ℂ} (ha : Integrable a)
    (σ : Measure (Euclidean d)) [IsFiniteMeasure σ] :
    Integrable (fun θ => ‖integratedKernelSymbol a θ‖ ^ 2) σ := by
  have hi := (integrable_fourier_gram_kernel ha σ).integral_prod_right
  have hi' : Integrable (fun θ => (‖integratedKernelSymbol a θ‖ : ℂ) ^ 2) σ :=
    hi.congr (Filter.Eventually.of_forall (integral_fourier_gram a))
  convert hi'.re using 1
  ext θ
  simp [← Complex.ofReal_pow]
end RieszEuclidean
