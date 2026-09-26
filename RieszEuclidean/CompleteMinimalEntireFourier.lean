import RieszEuclidean.FourierAgreement
import RieszEuclidean.DomainExtension
import RieszEuclidean.CompleteMinimalBasic
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Complex.CauchyIntegral

/-! Complex frequencies for the Fourier transform of boundedly supported functions. -/

noncomputable section
open MeasureTheory Filter Topology
open scoped BigOperators

namespace RieszEuclidean.CompleteMinimal

/-- Complex Euclidean frequency space with the same coordinate index as physical space. -/
abbrev ComplexEuclidean (d : ℕ) := EuclideanSpace ℂ (Fin d)

/-- Embed real frequencies coordinatewise into complex Euclidean space. -/
def realToComplex {d : ℕ} (x : Euclidean d) : ComplexEuclidean d :=
  (WithLp.equiv 2 (Fin d → ℂ)).symm (fun j => (x j : ℂ))

@[simp] theorem realToComplex_apply {d : ℕ} (x : Euclidean d) (j : Fin d) :
    realToComplex x j = (x j : ℂ) := rfl

@[simp] theorem realToComplex_norm {d : ℕ} (x : Euclidean d) :
    ‖realToComplex x‖ = ‖x‖ := by
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)]
  simp [PiLp.norm_sq_eq_of_L2, realToComplex]

/-- The complex bilinear extension of the real Euclidean pairing. -/
def complexPairing {d : ℕ} (x : Euclidean d) (z : ComplexEuclidean d) : ℂ :=
  ∑ j, (x j : ℂ) * z j

/-- The frequency pairing as a continuous complex-linear functional. -/
def complexPairingCLM {d : ℕ} (x : Euclidean d) : ComplexEuclidean d →L[ℂ] ℂ :=
  ∑ j, (x j : ℂ) • PiLp.proj 2 (fun _ : Fin d => ℂ) j

@[simp] theorem complexPairingCLM_apply {d : ℕ} (x : Euclidean d)
    (z : ComplexEuclidean d) : complexPairingCLM x z = complexPairing x z := by
  simp [complexPairingCLM, complexPairing]

@[simp] theorem complexPairing_realToComplex {d : ℕ} (x ξ : Euclidean d) :
    complexPairing x (realToComplex ξ) = (inner (𝕜 := ℝ) x ξ : ℂ) := by
  simp [complexPairing, PiLp.inner_apply, RCLike.inner_apply, mul_comm]

theorem complexPairing_norm_le {d : ℕ} (x : Euclidean d) (z : ComplexEuclidean d) :
    ‖complexPairing x z‖ ≤ (d : ℝ) * ‖x‖ * ‖z‖ := by
  calc
    ‖complexPairing x z‖ ≤ ∑ j : Fin d, ‖(x j : ℂ) * z j‖ := norm_sum_le _ _
    _ ≤ ∑ _j : Fin d, ‖x‖ * ‖z‖ := by
      apply Finset.sum_le_sum
      intro j _
      rw [norm_mul, Complex.norm_real]
      exact mul_le_mul (PiLp.norm_apply_le x j) (PiLp.norm_apply_le z j)
        (norm_nonneg _) (norm_nonneg _)
    _ = (d : ℝ) * ‖x‖ * ‖z‖ := by simp [mul_assoc]

/-- The negative-sign Fourier phase as a continuous complex-linear functional. -/
def fourierPhaseCLM {d : ℕ} (x : Euclidean d) : ComplexEuclidean d →L[ℂ] ℂ :=
  (-2 * (Real.pi : ℂ) * Complex.I) • complexPairingCLM x

/-- The exponential Fourier kernel at a possibly complex frequency. -/
def complexFourierKernel {d : ℕ} (x : Euclidean d) (z : ComplexEuclidean d) : ℂ :=
  Complex.exp (fourierPhaseCLM x z)

/-- The complex-frequency integral transform of a physical-space function. -/
def entireFourier {d : ℕ} (f : Euclidean d → ℂ) (z : ComplexEuclidean d) : ℂ :=
  ∫ x, f x * complexFourierKernel x z

theorem entireFourier_congr {d : ℕ} {f g : Euclidean d → ℂ} (h : f =ᵐ[volume] g) :
    entireFourier f = entireFourier g := by
  funext z
  apply integral_congr_ae
  filter_upwards [h] with x hx
  rw [hx]

@[simp] theorem entireFourier_zero {d : ℕ} :
    entireFourier (0 : Euclidean d → ℂ) = 0 := by
  funext z
  simp [entireFourier]

theorem entireFourier_smul {d : ℕ} (c : ℂ) (f : Euclidean d → ℂ) :
    entireFourier (c • f) = c • entireFourier f := by
  funext z
  simp only [entireFourier, Pi.smul_apply, smul_eq_mul, mul_assoc]
  exact integral_const_mul _ _

theorem complexPairing_continuous_left {d : ℕ} (z : ComplexEuclidean d) :
    Continuous (fun x : Euclidean d => complexPairing x z) := by
  unfold complexPairing
  fun_prop

theorem complexPairingCLM_continuous {d : ℕ} :
    Continuous (complexPairingCLM : Euclidean d → ComplexEuclidean d →L[ℂ] ℂ) := by
  unfold complexPairingCLM
  fun_prop

theorem fourierPhaseCLM_continuous {d : ℕ} :
    Continuous (fourierPhaseCLM : Euclidean d → ComplexEuclidean d →L[ℂ] ℂ) :=
  continuous_const.smul complexPairingCLM_continuous

theorem fourierPhaseCLM_norm_le {d : ℕ} (x : Euclidean d) :
    ‖fourierPhaseCLM x‖ ≤ 2 * Real.pi * d * ‖x‖ := by
  have hpair : ‖complexPairingCLM x‖ ≤ (d : ℝ) * ‖x‖ := by
    apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro z
    simpa only [complexPairingCLM_apply, mul_assoc] using complexPairing_norm_le x z
  calc
    ‖fourierPhaseCLM x‖ = 2 * Real.pi * ‖complexPairingCLM x‖ := by
      rw [fourierPhaseCLM, norm_smul (-2 * (Real.pi : ℂ) * Complex.I) (complexPairingCLM x)]
      simp [norm_mul, Real.pi_pos.le, abs_of_nonneg]
    _ ≤ 2 * Real.pi * ((d : ℝ) * ‖x‖) :=
      mul_le_mul_of_nonneg_left hpair (by positivity)
    _ = _ := by ring

theorem complexFourierKernel_continuous_left {d : ℕ} (z : ComplexEuclidean d) :
    Continuous (fun x : Euclidean d => complexFourierKernel x z) := by
  unfold complexFourierKernel fourierPhaseCLM
  simp only [ContinuousLinearMap.smul_apply, complexPairingCLM_apply, smul_eq_mul]
  exact Complex.continuous_exp.comp
    (continuous_const.mul (complexPairing_continuous_left z))

theorem complexFourierKernel_norm_le {d : ℕ} (x : Euclidean d)
    (z : ComplexEuclidean d) :
    ‖complexFourierKernel x z‖ ≤ Real.exp (2 * Real.pi * d * ‖x‖ * ‖z‖) := by
  rw [complexFourierKernel, Complex.norm_exp]
  apply Real.exp_le_exp.mpr
  calc
    (fourierPhaseCLM x z).re ≤ ‖fourierPhaseCLM x z‖ := Complex.re_le_norm _
    _ = 2 * Real.pi * ‖complexPairing x z‖ := by
      simp [fourierPhaseCLM, norm_mul, Real.pi_pos.le, abs_of_nonneg]
    _ ≤ 2 * Real.pi * ((d : ℝ) * ‖x‖ * ‖z‖) :=
      mul_le_mul_of_nonneg_left (complexPairing_norm_le x z) (by positivity)
    _ = _ := by ring

theorem entireFourier_integrable {d : ℕ} {f : Euclidean d → ℂ} {R : ℝ}
    (hf : Integrable f)
    (hsupp : ∀ᵐ x, f x ≠ 0 → ‖x‖ ≤ R) (z : ComplexEuclidean d) :
    Integrable (fun x => f x * complexFourierKernel x z) := by
  apply (hf.norm.mul_const (Real.exp (2 * Real.pi * d * R * ‖z‖))).mono'
    (hf.aestronglyMeasurable.mul
      (complexFourierKernel_continuous_left z).aestronglyMeasurable)
  filter_upwards [hsupp] with x hx
  change ‖f x * complexFourierKernel x z‖ ≤ _
  rw [norm_mul]
  by_cases hfx : f x = 0
  · simp [hfx]
  · apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    exact (complexFourierKernel_norm_le x z).trans
      (Real.exp_le_exp.mpr (by
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
        exact mul_le_mul_of_nonneg_left (hx hfx) (by positivity)))

theorem entireFourier_add {d : ℕ} {f g : Euclidean d → ℂ} {R S : ℝ}
    (hf : Integrable f) (hg : Integrable g)
    (hfSupp : ∀ᵐ x, f x ≠ 0 → ‖x‖ ≤ R)
    (hgSupp : ∀ᵐ x, g x ≠ 0 → ‖x‖ ≤ S) :
    entireFourier (f + g) = entireFourier f + entireFourier g := by
  funext z
  simp only [entireFourier, Pi.add_apply, add_mul]
  exact integral_add (entireFourier_integrable hf hfSupp z)
    (entireFourier_integrable hg hgSupp z)

/-- The complex-frequency transform has finite exponential type with an explicit bound. -/
theorem entireFourier_norm_le {d : ℕ} {f : Euclidean d → ℂ} {R : ℝ}
    (hf : Integrable f)
    (hsupp : ∀ᵐ x, f x ≠ 0 → ‖x‖ ≤ R) (z : ComplexEuclidean d) :
    ‖entireFourier f z‖ ≤ (∫ x, ‖f x‖) * Real.exp (2 * Real.pi * d * R * ‖z‖) := by
  unfold entireFourier
  calc
    _ ≤ ∫ x, ‖f x‖ * Real.exp (2 * Real.pi * d * R * ‖z‖) := by
      apply norm_integral_le_of_norm_le (hf.norm.mul_const _)
      filter_upwards [hsupp] with x hx
      rw [norm_mul]
      by_cases hfx : f x = 0
      · simp [hfx]
      · apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
        exact (complexFourierKernel_norm_le x z).trans
          (Real.exp_le_exp.mpr (by
            apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
            exact mul_le_mul_of_nonneg_left (hx hfx) (by positivity)))
    _ = _ := integral_mul_const _ _

/-- The derivative of the Fourier integrand with respect to complex frequency. -/
def entireFourierDerivativeIntegrand {d : ℕ} (f : Euclidean d → ℂ)
    (z : ComplexEuclidean d) (x : Euclidean d) : ComplexEuclidean d →L[ℂ] ℂ :=
  (f x * complexFourierKernel x z) • fourierPhaseCLM x

theorem complexFourierKernel_hasFDerivAt {d : ℕ} (x : Euclidean d)
    (z : ComplexEuclidean d) :
    HasFDerivAt (complexFourierKernel x)
      (complexFourierKernel x z • fourierPhaseCLM x) z :=
  (fourierPhaseCLM x).hasFDerivAt.cexp

theorem complexFourierKernel_realToComplex {d : ℕ} (x ξ : Euclidean d) :
    complexFourierKernel x (realToComplex ξ) =
      Complex.exp ((-2 * Real.pi * inner (𝕜 := ℝ) x ξ : ℝ) * Complex.I) := by
  unfold complexFourierKernel fourierPhaseCLM
  simp only [ContinuousLinearMap.smul_apply, complexPairingCLM_apply,
    complexPairing_realToComplex, smul_eq_mul]
  push_cast
  congr 1
  ring

theorem complexFourierKernel_real_eq_star_exponential {d : ℕ} (x ξ : Euclidean d) :
    complexFourierKernel x (realToComplex ξ) = star (exponential ξ x) := by
  rw [complexFourierKernel_realToComplex]
  unfold exponential
  change Complex.exp _ = starRingEnd ℂ (Complex.exp _)
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_mul, map_ofNat, Complex.conj_ofReal, Complex.conj_I]
  rw [real_inner_comm ξ x]
  push_cast
  ring

@[simp] theorem complexFourierKernel_real_norm {d : ℕ} (x ξ : Euclidean d) :
    ‖complexFourierKernel x (realToComplex ξ)‖ = 1 := by
  rw [complexFourierKernel_realToComplex, Complex.norm_exp]
  simp

theorem entireFourier_realToComplex {d : ℕ} (f : Euclidean d → ℂ)
    (ξ : Euclidean d) : entireFourier f (realToComplex ξ) = Real.fourierIntegral f ξ := by
  rw [entireFourier, Real.fourierIntegral_eq']
  apply integral_congr_ae
  filter_upwards with x
  rw [complexFourierKernel_realToComplex]
  simp only [smul_eq_mul, mul_comm]

/-- Agreement with the existing negative-sign unitary Fourier transform. -/
theorem entireFourier_eq_fourierL2 {d : ℕ} (f : FullL2 d)
    (hf : Integrable (f : Euclidean d → ℂ)) :
    (fun ξ => entireFourier f (realToComplex ξ)) =ᵐ[volume]
      (fourierL2Equiv d f : Euclidean d → ℂ) := by
  simpa only [entireFourier_realToComplex] using (fourierL2Equiv_eq_integral f hf).symm

theorem entireFourier_real_norm_le {d : ℕ} {f : Euclidean d → ℂ}
    (hf : Integrable f) (ξ : Euclidean d) :
    ‖entireFourier f (realToComplex ξ)‖ ≤ ∫ x, ‖f x‖ := by
  apply norm_integral_le_of_norm_le hf.norm
  filter_upwards with x
  simp [norm_mul, complexFourierKernel_real_norm]

/-- Differentiation under the integral is valid in every complex direction. -/
theorem entireFourier_hasFDerivAt {d : ℕ} {f : Euclidean d → ℂ} {R : ℝ}
    (hf : Integrable f) (hR : 0 ≤ R)
    (hsupp : ∀ᵐ x, f x ≠ 0 → ‖x‖ ≤ R) (z : ComplexEuclidean d) :
    HasFDerivAt (entireFourier f)
      (∫ x, entireFourierDerivativeIntegrand f z x) z := by
  let bound : Euclidean d → ℝ := fun x =>
    ‖f x‖ * Real.exp (2 * Real.pi * d * R * (‖z‖ + 1)) *
      (2 * Real.pi * d * R)
  have hmeas (w : ComplexEuclidean d) :
      AEStronglyMeasurable (fun x => f x * complexFourierKernel x w) :=
    (entireFourier_integrable hf hsupp w).aestronglyMeasurable
  have hdmeas : AEStronglyMeasurable (entireFourierDerivativeIntegrand f z) := by
    exact (hmeas z).smul fourierPhaseCLM_continuous.aestronglyMeasurable
  have hbound : ∀ᵐ x, ∀ w ∈ Metric.ball z 1,
      ‖entireFourierDerivativeIntegrand f w x‖ ≤ bound x := by
    filter_upwards [hsupp] with x hx w hw
    unfold entireFourierDerivativeIntegrand bound
    rw [norm_smul (f x * complexFourierKernel x w) (fourierPhaseCLM x), norm_mul]
    by_cases hfx : f x = 0
    · simp [hfx]
    · have hxR := hx hfx
      have hwz : ‖w‖ ≤ ‖z‖ + 1 := by
        have hd : ‖w - z‖ < 1 := by simpa only [Metric.mem_ball, dist_eq_norm] using hw
        calc
          ‖w‖ = ‖(w - z) + z‖ := by simp
          _ ≤ ‖w - z‖ + ‖z‖ := norm_add_le _ _
          _ ≤ ‖z‖ + 1 := by linarith
      have hk : ‖complexFourierKernel x w‖ ≤
          Real.exp (2 * Real.pi * d * R * (‖z‖ + 1)) := by
        apply (complexFourierKernel_norm_le x w).trans
        apply Real.exp_le_exp.mpr
        exact mul_le_mul
          (mul_le_mul_of_nonneg_left hxR (by positivity)) hwz
          (norm_nonneg _) (by positivity)
      have hp : ‖fourierPhaseCLM x‖ ≤ 2 * Real.pi * d * R :=
        (fourierPhaseCLM_norm_le x).trans
          (mul_le_mul_of_nonneg_left hxR (by positivity))
      exact mul_le_mul (mul_le_mul_of_nonneg_left hk (norm_nonneg _)) hp
        (norm_nonneg _) (by positivity)
  have hboundInt : Integrable bound :=
    (hf.norm.mul_const _).mul_const _
  have hdiff : ∀ᵐ x, ∀ w ∈ Metric.ball z 1,
      HasFDerivAt (fun w => f x * complexFourierKernel x w)
        (entireFourierDerivativeIntegrand f w x) w := by
    filter_upwards with x w _
    simpa only [entireFourierDerivativeIntegrand, smul_smul] using
      (complexFourierKernel_hasFDerivAt x w).const_mul (f x)
  exact hasFDerivAt_integral_of_dominated_of_fderiv_le zero_lt_one
    (Eventually.of_forall hmeas) (entireFourier_integrable hf hsupp z)
    hdmeas hbound hboundInt hdiff

theorem entireFourier_differentiable {d : ℕ} {f : Euclidean d → ℂ} {R : ℝ}
    (hf : Integrable f) (hR : 0 ≤ R)
    (hsupp : ∀ᵐ x, f x ≠ 0 → ‖x‖ ≤ R) :
    Differentiable ℂ (entireFourier f) :=
  fun z => (entireFourier_hasFDerivAt hf hR hsupp z).differentiableAt

/-- The first complex derivative is uniformly bounded on real frequencies. -/
theorem entireFourier_real_fderiv_norm_le {d : ℕ} {f : Euclidean d → ℂ} {R : ℝ}
    (hf : Integrable f) (hR : 0 ≤ R)
    (hsupp : ∀ᵐ x, f x ≠ 0 → ‖x‖ ≤ R) (ξ : Euclidean d) :
    ‖fderiv ℂ (entireFourier f) (realToComplex ξ)‖ ≤
      (∫ x, ‖f x‖) * (2 * Real.pi * d * R) := by
  rw [(entireFourier_hasFDerivAt hf hR hsupp (realToComplex ξ)).fderiv]
  calc
    _ ≤ ∫ x, ‖f x‖ * (2 * Real.pi * d * R) := by
      apply norm_integral_le_of_norm_le (hf.norm.mul_const _)
      filter_upwards [hsupp] with x hx
      unfold entireFourierDerivativeIntegrand
      rw [norm_smul (f x * complexFourierKernel x (realToComplex ξ))
        (fourierPhaseCLM x), norm_mul, complexFourierKernel_real_norm, mul_one]
      by_cases hfx : f x = 0
      · simp [hfx]
      · apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
        exact (fourierPhaseCLM_norm_le x).trans
          (mul_le_mul_of_nonneg_left (hx hfx) (by positivity))
    _ = _ := integral_mul_const _ _

/-- Restriction to every complex affine line is analytic. -/
theorem entireFourier_analyticAlongLine {d : ℕ} {f : Euclidean d → ℂ} {R : ℝ}
    (hf : Integrable f) (hR : 0 ≤ R)
    (hsupp : ∀ᵐ x, f x ≠ 0 → ‖x‖ ≤ R) (z u : ComplexEuclidean d) :
    AnalyticOnNhd ℂ (fun w : ℂ => entireFourier f (z + w • u)) Set.univ := by
  apply (Complex.analyticOnNhd_univ_iff_differentiable).mpr
  exact (entireFourier_differentiable hf hR hsupp).comp
    ((differentiable_const z).add (differentiable_id.smul_const u))

/-- Every domain L² representative has an integrable zero extension on a bounded domain. -/
theorem domainExtension_integrable {d : ℕ} {Ω : Set (Euclidean d)}
    (hΩ : MeasurableSet Ω) (hbounded : Bornology.IsBounded Ω) (f : DomainL2 Ω) :
    Integrable (domainExtension Ω hΩ f : Euclidean d → ℂ) := by
  letI : IsFiniteMeasure (volume.restrict Ω) :=
    isFiniteMeasure_restrict.mpr hbounded.measure_lt_top.ne
  have hf : Integrable (f : Euclidean d → ℂ) (volume.restrict Ω) :=
    (Lp.memLp f).integrable (by norm_num)
  have hi : Integrable (Ω.indicator (f : Euclidean d → ℂ)) :=
    (integrable_indicator_iff hΩ).mpr hf
  exact hi.congr (domainExtension_coe Ω hΩ f).symm

theorem domainExtension_supported_in_radius {d : ℕ} {Ω : Set (Euclidean d)}
    (hΩ : MeasurableSet Ω) (f : DomainL2 Ω) {R : ℝ}
    (hbound : ∀ x ∈ Ω, ‖x‖ ≤ R) :
    ∀ᵐ x, domainExtension Ω hΩ f x ≠ 0 → ‖x‖ ≤ R := by
  filter_upwards [domainExtension_coe Ω hΩ f] with x hx hfx
  by_cases hxΩ : x ∈ Ω
  · exact hbound x hxΩ
  · exact False.elim (hfx (hx.trans (Set.indicator_of_not_mem hxΩ _)))

/-- The complex Fourier transform of a domain L² function extended by zero. -/
def domainEntireFourier {d : ℕ} (Ω : Set (Euclidean d)) (hΩ : MeasurableSet Ω)
    (f : DomainL2 Ω) : ComplexEuclidean d → ℂ :=
  entireFourier (domainExtension Ω hΩ f)

/-- The complex transform, as a linear map on the actual bounded-domain L² space. -/
def domainEntireFourierLinear {d : ℕ} (Ω : Set (Euclidean d))
    (hΩ : MeasurableSet Ω) (hbounded : Bornology.IsBounded Ω) :
    DomainL2 Ω →ₗ[ℂ] (ComplexEuclidean d → ℂ) where
  toFun := domainEntireFourier Ω hΩ
  map_add' f g := by
    obtain ⟨R, _hR, hbound⟩ := hbounded.exists_pos_norm_le
    have hext : domainExtension Ω hΩ (f + g) =
        domainExtension Ω hΩ f + domainExtension Ω hΩ g :=
      (domainExtensionLI Ω hΩ).map_add f g
    have hae : (domainExtension Ω hΩ (f + g) : Euclidean d → ℂ) =ᵐ[volume]
        fun x => domainExtension Ω hΩ f x + domainExtension Ω hΩ g x := by
      rw [hext]
      exact Lp.coeFn_add _ _
    change entireFourier (domainExtension Ω hΩ (f + g)) =
      entireFourier (domainExtension Ω hΩ f) + entireFourier (domainExtension Ω hΩ g)
    rw [entireFourier_congr hae]
    exact entireFourier_add (domainExtension_integrable hΩ hbounded f)
      (domainExtension_integrable hΩ hbounded g)
      (domainExtension_supported_in_radius hΩ f hbound)
      (domainExtension_supported_in_radius hΩ g hbound)
  map_smul' c f := by
    have hext : domainExtension Ω hΩ (c • f) = c • domainExtension Ω hΩ f :=
      (domainExtensionLI Ω hΩ).map_smul c f
    have hae : (domainExtension Ω hΩ (c • f) : Euclidean d → ℂ) =ᵐ[volume]
        (c • (domainExtension Ω hΩ f : Euclidean d → ℂ)) := by
      rw [hext]
      exact Lp.coeFn_smul _ _
    change entireFourier (domainExtension Ω hΩ (c • f)) =
      c • entireFourier (domainExtension Ω hΩ f)
    rw [entireFourier_congr hae, entireFourier_smul]

/-- Actual L² functions on a bounded domain give holomorphic complex-frequency transforms. -/
theorem domainEntireFourier_differentiable {d : ℕ} {Ω : Set (Euclidean d)}
    (hΩ : MeasurableSet Ω) (hbounded : Bornology.IsBounded Ω) (f : DomainL2 Ω) :
    Differentiable ℂ (domainEntireFourier Ω hΩ f) := by
  obtain ⟨R, hR, hbound⟩ := hbounded.exists_pos_norm_le
  exact entireFourier_differentiable (domainExtension_integrable hΩ hbounded f) hR.le
    (domainExtension_supported_in_radius hΩ f hbound)

/-- Finite exponential type for the transform of an actual bounded-domain L² class. -/
theorem domainEntireFourier_finite_exponential_type {d : ℕ} {Ω : Set (Euclidean d)}
    (hΩ : MeasurableSet Ω) (hbounded : Bornology.IsBounded Ω) (f : DomainL2 Ω) :
    ∃ C T : ℝ, 0 ≤ C ∧ 0 ≤ T ∧
      ∀ z, ‖domainEntireFourier Ω hΩ f z‖ ≤ C * Real.exp (T * ‖z‖) := by
  obtain ⟨R, hR, hbound⟩ := hbounded.exists_pos_norm_le
  refine ⟨∫ x, ‖domainExtension Ω hΩ f x‖, 2 * Real.pi * d * R,
    integral_nonneg (fun _ => norm_nonneg _), by positivity, ?_⟩
  intro z
  exact entireFourier_norm_le (domainExtension_integrable hΩ hbounded f)
    (domainExtension_supported_in_radius hΩ f hbound) z

theorem domainEntireFourier_eq_fourierL2 {d : ℕ} {Ω : Set (Euclidean d)}
    (hΩ : MeasurableSet Ω) (hbounded : Bornology.IsBounded Ω) (f : DomainL2 Ω) :
    (fun ξ => domainEntireFourier Ω hΩ f (realToComplex ξ)) =ᵐ[volume]
      (fourierL2Equiv d (domainExtension Ω hΩ f) : Euclidean d → ℂ) :=
  entireFourier_eq_fourierL2 _ (domainExtension_integrable hΩ hbounded f)

/-- The complex-frequency extension determines its original domain L² class. -/
theorem domainEntireFourier_injective {d : ℕ} {Ω : Set (Euclidean d)}
    (hΩ : MeasurableSet Ω) (hbounded : Bornology.IsBounded Ω) :
    Function.Injective (domainEntireFourier Ω hΩ) := by
  intro f g hfg
  apply (domainExtensionLI Ω hΩ).injective
  apply (fourierL2Equiv d).injective
  apply Lp.ext
  filter_upwards [domainEntireFourier_eq_fourierL2 hΩ hbounded f,
    domainEntireFourier_eq_fourierL2 hΩ hbounded g] with ξ hf hg
  change fourierL2Equiv d (domainExtension Ω hΩ f) ξ =
    fourierL2Equiv d (domainExtension Ω hΩ g) ξ
  rw [← hf, ← hg, hfg]

theorem domainEntireFourier_real_integral {d : ℕ} {Ω : Set (Euclidean d)}
    (hΩ : MeasurableSet Ω) (f : DomainL2 Ω) (ξ : Euclidean d) :
    domainEntireFourier Ω hΩ f (realToComplex ξ) =
      ∫ x in Ω, f x * star (exponential ξ x) := by
  unfold domainEntireFourier entireFourier
  rw [← integral_indicator hΩ]
  apply integral_congr_ae
  filter_upwards [domainExtension_coe Ω hΩ f] with x hx
  rw [hx, complexFourierKernel_real_eq_star_exponential]
  by_cases hxΩ : x ∈ Ω
  · simp only [Set.indicator_of_mem hxΩ]
  · simp only [Set.indicator_of_not_mem hxΩ, zero_mul]

/-- Point evaluations on real frequencies are the actual exponential inner products. -/
theorem domainEntireFourier_real_inner {d : ℕ} {Ω : Set (Euclidean d)}
    (hΩ : MeasurableSet Ω) (hfinite : volume Ω ≠ ⊤) (f : DomainL2 Ω) (ξ : Euclidean d) :
    domainEntireFourier Ω hΩ f (realToComplex ξ) =
      inner (𝕜 := ℂ) (exponentialL2 Ω hfinite ξ) f := by
  rw [domainEntireFourier_real_integral, exponentialL2_inner]

/-- Both the transform and its first derivative are bounded on the real frequency space. -/
theorem domainEntireFourier_real_bounds {d : ℕ} {Ω : Set (Euclidean d)}
    (hΩ : MeasurableSet Ω) (hbounded : Bornology.IsBounded Ω) (f : DomainL2 Ω) :
    ∃ C : ℝ, ∀ ξ : Euclidean d,
      ‖domainEntireFourier Ω hΩ f (realToComplex ξ)‖ ≤ C ∧
      ‖fderiv ℂ (domainEntireFourier Ω hΩ f) (realToComplex ξ)‖ ≤ C := by
  obtain ⟨R, hR, hbound⟩ := hbounded.exists_pos_norm_le
  let A := ∫ x, ‖domainExtension Ω hΩ f x‖
  let T : ℝ := 2 * Real.pi * d * R
  refine ⟨max A (A * T), ?_⟩
  intro ξ
  constructor
  · exact (entireFourier_real_norm_le (domainExtension_integrable hΩ hbounded f) ξ).trans
      (le_max_left _ _)
  · exact (entireFourier_real_fderiv_norm_le (domainExtension_integrable hΩ hbounded f)
      hR.le (domainExtension_supported_in_radius hΩ f hbound) ξ).trans (le_max_right _ _)

end RieszEuclidean.CompleteMinimal
