/-
Copyright (c) 2025 Moritz Doll. All rights reserved.
Released under Apache 2.0 license; see third_party/mathlib/LICENSE.
Authors: Moritz Doll

The L² embedding below adapts the construction in Mathlib's
Analysis/Distribution/TemperedDistribution.lean at commit
9658bdd6ca3a5c557ef9a46698d9e7aedc6bcffd to this project's pinned Mathlib.
The remaining definitions specialize the existing Schwartz-space API.
-/
import RieszEuclidean.FourierAgreement
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.Topology.Algebra.Module.StrongTopology

/-! Tempered distributions and their basic support operations.

Distributions here are actual continuous complex-linear functionals on Schwartz
space. No support theorem or Paley–Wiener theorem is included in their definition.
-/

noncomputable section

open MeasureTheory SchwartzMap
open scoped SchwartzMap FourierTransform

namespace RieszEuclidean.CompleteMinimal

/-- Continuous complex-linear functionals on the Schwartz test space. -/
abbrev TemperedDistribution (d : ℕ) := 𝓢(Euclidean d, ℂ) →L[ℂ] ℂ

/-- The Fourier transform on distributions, by transposition of the negative-sign
Fourier transform on Schwartz functions. -/
def distributionFourierEquiv (d : ℕ) :
    TemperedDistribution d ≃L[ℂ] TemperedDistribution d :=
  (SchwartzMap.fourierTransformCLE ℂ).symm.arrowCongr
    (ContinuousLinearEquiv.refl ℂ ℂ)

/-- The negative-sign Fourier transform of a tempered distribution. -/
def distributionFourier {d : ℕ} (u : TemperedDistribution d) : TemperedDistribution d :=
  distributionFourierEquiv d u

/-- The inverse Fourier transform of a tempered distribution. -/
def distributionInverseFourier {d : ℕ} (u : TemperedDistribution d) :
    TemperedDistribution d := (distributionFourierEquiv d).symm u

@[simp] theorem distributionFourier_apply {d : ℕ} (u : TemperedDistribution d)
    (φ : 𝓢(Euclidean d, ℂ)) :
    distributionFourier u φ = u (SchwartzMap.fourierTransformCLE ℂ φ) := rfl

@[simp] theorem distributionInverseFourier_apply {d : ℕ} (u : TemperedDistribution d)
    (φ : 𝓢(Euclidean d, ℂ)) :
    distributionInverseFourier u φ = u ((SchwartzMap.fourierTransformCLE ℂ).symm φ) := rfl

@[simp] theorem distributionInverseFourier_fourier {d : ℕ} (u : TemperedDistribution d) :
    distributionInverseFourier (distributionFourier u) = u :=
  (distributionFourierEquiv d).symm_apply_apply u

@[simp] theorem distributionFourier_inverseFourier {d : ℕ} (u : TemperedDistribution d) :
    distributionFourier (distributionInverseFourier u) = u :=
  (distributionFourierEquiv d).apply_symm_apply u

theorem distributionFourier_injective {d : ℕ} :
    Function.Injective (@distributionFourier d) := (distributionFourierEquiv d).injective

/-- The Dirac distribution given by evaluation at a point. -/
def distributionDelta {d : ℕ} (x : Euclidean d) : TemperedDistribution d :=
  SchwartzMap.delta ℂ ℂ x

@[simp] theorem distributionDelta_apply {d : ℕ} (x : Euclidean d)
    (φ : 𝓢(Euclidean d, ℂ)) : distributionDelta x φ = φ x := rfl

/-- The distributional directional derivative, with its integration-by-parts sign. -/
def distributionDerivative {d : ℕ} (v : Euclidean d) (u : TemperedDistribution d) :
    TemperedDistribution d := -(u.comp (SchwartzMap.pderivCLM ℂ v))

@[simp] theorem distributionDerivative_apply {d : ℕ} (v : Euclidean d)
    (u : TemperedDistribution d) (φ : 𝓢(Euclidean d, ℂ)) :
    distributionDerivative v u φ = -u (SchwartzMap.pderivCLM ℂ v φ) := rfl

/-- The bilinear (unconjugated) pairing of an L² function with a test function. -/
def l2Distribution {d : ℕ} (f : FullL2 d) : TemperedDistribution d :=
  ((ContinuousLinearMap.mul ℂ ℂ).lpPairing volume 2 2 f).comp
    (SchwartzMap.toLpCLM ℂ ℂ 2 volume)

@[simp] theorem l2Distribution_apply {d : ℕ} (f : FullL2 d)
    (φ : 𝓢(Euclidean d, ℂ)) : l2Distribution f φ = ∫ x, f x * φ x := by
  simp only [l2Distribution, ContinuousLinearMap.comp_apply,
    SchwartzMap.toLpCLM_apply, ContinuousLinearMap.lpPairing_eq_integral,
    ContinuousLinearMap.mul_apply']
  apply integral_congr_ae
  filter_upwards [φ.coeFn_toLp 2 volume] with x hx
  rw [hx]

/-- Support in `S` means annihilating every compactly supported smooth test whose
closed support is disjoint from `S`. -/
def DistributionSupportedIn {d : ℕ} (u : TemperedDistribution d)
    (S : Set (Euclidean d)) : Prop :=
  ∀ φ : 𝓢(Euclidean d, ℂ), HasCompactSupport (φ : Euclidean d → ℂ) →
    Disjoint (tsupport (φ : Euclidean d → ℂ)) S → u φ = 0

theorem DistributionSupportedIn.mono {d : ℕ} {u : TemperedDistribution d}
    {S T : Set (Euclidean d)} (hu : DistributionSupportedIn u S) (hST : S ⊆ T) :
    DistributionSupportedIn u T := by
  intro φ hφ hdisj
  exact hu φ hφ (hdisj.mono_right hST)

theorem distributionSupportedIn_zero {d : ℕ} (S : Set (Euclidean d)) :
    DistributionSupportedIn (0 : TemperedDistribution d) S := by
  intro φ _ _
  rfl

theorem DistributionSupportedIn.add {d : ℕ} {u v : TemperedDistribution d}
    {S : Set (Euclidean d)} (hu : DistributionSupportedIn u S)
    (hv : DistributionSupportedIn v S) : DistributionSupportedIn (u + v) S := by
  intro φ hφ hdisj
  simp [hu φ hφ hdisj, hv φ hφ hdisj]

theorem DistributionSupportedIn.smul {d : ℕ} {u : TemperedDistribution d}
    {S : Set (Euclidean d)} (hu : DistributionSupportedIn u S) (c : ℂ) :
    DistributionSupportedIn (c • u) S := by
  intro φ hφ hdisj
  simp [hu φ hφ hdisj]

theorem distributionDelta_supported {d : ℕ} (x : Euclidean d) :
    DistributionSupportedIn (distributionDelta x) {x} := by
  intro φ _ hdisj
  change φ x = 0
  apply image_eq_zero_of_nmem_tsupport
  exact fun hx => Set.disjoint_left.mp hdisj hx (Set.mem_singleton x)

theorem tsupport_schwartz_pderiv_subset {d : ℕ} (v : Euclidean d)
    (φ : 𝓢(Euclidean d, ℂ)) :
    tsupport (SchwartzMap.pderivCLM ℂ v φ : Euclidean d → ℂ) ⊆
      tsupport (φ : Euclidean d → ℂ) := by
  apply closure_minimal _ isClosed_closure
  intro x hx
  by_contra h
  have hz := fderiv_of_not_mem_tsupport ℝ h
  exact hx (by simp [SchwartzMap.pderivCLM_apply, hz])

theorem DistributionSupportedIn.derivative {d : ℕ} {u : TemperedDistribution d}
    {S : Set (Euclidean d)} (hu : DistributionSupportedIn u S) (v : Euclidean d) :
    DistributionSupportedIn (distributionDerivative v u) S := by
  intro φ hφ hdisj
  have hs := tsupport_schwartz_pderiv_subset v φ
  have hc : HasCompactSupport (SchwartzMap.pderivCLM ℂ v φ : Euclidean d → ℂ) :=
    hφ.of_isClosed_subset isClosed_closure hs
  simp only [distributionDerivative_apply]
  rw [hu _ hc (hdisj.mono_left hs), neg_zero]

theorem l2Distribution_supported {d : ℕ} (f : FullL2 d) (S : Set (Euclidean d))
    (hf : ∀ᵐ x, x ∉ S → f x = 0) : DistributionSupportedIn (l2Distribution f) S := by
  intro φ _ hdisj
  rw [l2Distribution_apply]
  apply integral_eq_zero_of_ae
  filter_upwards [hf] with x hx
  by_cases hxS : x ∈ S
  · have hφx : φ x = 0 := image_eq_zero_of_nmem_tsupport
      (fun h => Set.disjoint_left.mp hdisj h hxS)
    simp [hφx]
  · simp [hx hxS]

theorem l2Distribution_injective {d : ℕ} : Function.Injective (@l2Distribution d) := by
  intro f g h
  apply Lp.ext
  apply ae_eq_of_integral_contDiff_smul_eq
    ((Lp.memLp f).locallyIntegrable (by norm_num))
    ((Lp.memLp g).locallyIntegrable (by norm_num))
  intro φ hφ hc
  let ψ := compactSchwartz (fun x => (φ x : ℂ))
    (Complex.ofRealCLM.contDiff.comp hφ) (hc.comp_left Complex.ofReal_zero)
  have hh := congrArg (fun u : TemperedDistribution d => u ψ) h
  change l2Distribution f ψ = l2Distribution g ψ at hh
  rw [l2Distribution_apply, l2Distribution_apply] at hh
  change (∫ x, f x * (φ x : ℂ)) = ∫ x, g x * (φ x : ℂ) at hh
  simpa only [Complex.real_smul, mul_comm] using hh

/-- A quantitative decay bound for multiplying a Schwartz test by a function of
polynomial growth. The bound involves finitely many Schwartz seminorms. -/
theorem polynomial_schwartz_bound {d N n : ℕ} {f : Euclidean d → ℂ} {C : ℝ}
    (hC : 0 ≤ C) (hf : ∀ x, ‖f x‖ ≤ C * (1 + ‖x‖) ^ N)
    (φ : 𝓢(Euclidean d, ℂ)) (x : Euclidean d) :
    ‖f x * φ x‖ ≤ (1 + ‖x‖) ^ (-(n : ℝ)) *
      (C * 2 ^ (N + n) *
        (Finset.Iic (N + n, 0)).sup (schwartzSeminormFamily ℂ (Euclidean d) ℂ) φ) := by
  have hp : 0 < 1 + ‖x‖ := by positivity
  have hs := one_add_le_sup_seminorm_apply (𝕜 := ℂ)
    (m := (N + n, 0)) (k := N + n) (n := 0) le_rfl le_rfl φ x
  simp only [norm_iteratedFDeriv_zero, schwartzSeminormFamily_apply] at hs
  rw [Real.rpow_neg hp.le, Real.rpow_natCast, ← div_eq_inv_mul,
    le_div_iff₀ (pow_pos hp _), norm_mul]
  calc
    ‖f x‖ * ‖φ x‖ * (1 + ‖x‖) ^ n
        ≤ (C * (1 + ‖x‖) ^ N) * ‖φ x‖ * (1 + ‖x‖) ^ n := by
          gcongr
          exact hf x
    _ = C * ((1 + ‖x‖) ^ (N + n) * ‖φ x‖) := by rw [pow_add]; ring
    _ ≤ C * (2 ^ (N + n) *
        (Finset.Iic (N + n, 0)).sup (schwartzSeminormFamily ℂ (Euclidean d) ℂ) φ) :=
      mul_le_mul_of_nonneg_left hs hC
    _ = _ := by ring

theorem polynomial_schwartz_integrable {d N : ℕ} {f : Euclidean d → ℂ} {C : ℝ}
    (hC : 0 ≤ C) (hf : ∀ x, ‖f x‖ ≤ C * (1 + ‖x‖) ^ N)
    (hm : AEStronglyMeasurable f volume) (φ : 𝓢(Euclidean d, ℂ)) :
    Integrable (fun x => f x * φ x) := by
  let n := (volume : Measure (Euclidean d)).integrablePower
  apply ((integrable_pow_neg_integrablePower (volume : Measure (Euclidean d))).mul_const
    (C * 2 ^ (N + n) *
      (Finset.Iic (N + n, 0)).sup (schwartzSeminormFamily ℂ (Euclidean d) ℂ) φ)).mono'
      (hm.mul φ.continuous.aestronglyMeasurable)
  exact Filter.Eventually.of_forall (polynomial_schwartz_bound hC hf φ)

/-- A measurable function with an explicit polynomial bound defines a continuous
functional on Schwartz space by the actual integral. Smoothness is unnecessary. -/
def polynomialDistribution {d N : ℕ} (f : Euclidean d → ℂ) {C : ℝ}
    (hC : 0 ≤ C) (hf : ∀ x, ‖f x‖ ≤ C * (1 + ‖x‖) ^ N)
    (hm : AEStronglyMeasurable f volume) : TemperedDistribution d := by
  refine SchwartzMap.mkCLMtoNormedSpace (fun φ => ∫ x, f x * φ x) ?_ ?_ ?_
  · intro φ ψ
    simp only [SchwartzMap.add_apply, mul_add]
    exact integral_add (polynomial_schwartz_integrable hC hf hm φ)
      (polynomial_schwartz_integrable hC hf hm ψ)
  · intro a φ
    simp only [SchwartzMap.smul_apply, smul_eq_mul, RingHom.id_apply]
    simp_rw [mul_left_comm (f _) a]
    exact integral_const_mul _ _
  · let n := (volume : Measure (Euclidean d)).integrablePower
    let J := ∫ x : Euclidean d, (1 + ‖x‖) ^ (-(n : ℝ))
    refine ⟨Finset.Iic (N + n, 0), J * C * 2 ^ (N + n), ?_, ?_⟩
    · have hJ : 0 ≤ J := integral_nonneg (fun x => by positivity)
      positivity
    · intro φ
      apply (norm_integral_le_integral_norm _).trans
      calc
        (∫ x, ‖f x * φ x‖) ≤ ∫ x, (1 + ‖x‖) ^ (-(n : ℝ)) *
            (C * 2 ^ (N + n) *
              (Finset.Iic (N + n, 0)).sup (schwartzSeminormFamily ℂ (Euclidean d) ℂ) φ) := by
          apply integral_mono (polynomial_schwartz_integrable hC hf hm φ).norm
            ((integrable_pow_neg_integrablePower (volume : Measure (Euclidean d))).mul_const _)
          exact polynomial_schwartz_bound hC hf φ
        _ = _ := by rw [integral_mul_const]; dsimp [J]; ring

@[simp] theorem polynomialDistribution_apply {d N : ℕ} (f : Euclidean d → ℂ) {C : ℝ}
    (hC : 0 ≤ C) (hf : ∀ x, ‖f x‖ ≤ C * (1 + ‖x‖) ^ N)
    (hm : AEStronglyMeasurable f volume) (φ : 𝓢(Euclidean d, ℂ)) :
    polynomialDistribution f hC hf hm φ = ∫ x, f x * φ x := rfl

/-- Pointwise complex conjugation preserves the Schwartz test space. -/
def schwartzConjugate {d : ℕ} (φ : 𝓢(Euclidean d, ℂ)) : 𝓢(Euclidean d, ℂ) where
  toFun := Complex.conjLIE ∘ φ
  smooth' := Complex.conjCLE.contDiff.comp φ.smooth'
  decay' := by
    intro k n
    obtain ⟨C, hC⟩ := φ.decay' k n
    exact ⟨C, fun x => by
      rw [Complex.conjLIE.norm_iteratedFDeriv_comp_left]
      exact hC x⟩

@[simp] theorem schwartzConjugate_apply {d : ℕ} (φ : 𝓢(Euclidean d, ℂ))
    (x : Euclidean d) : schwartzConjugate φ x = starRingEnd ℂ (φ x) := rfl

/-- Transposition on distributions agrees with the existing unitary L² transform. -/
theorem distributionFourier_l2Distribution {d : ℕ} (f : FullL2 d) :
    distributionFourier (l2Distribution f) = l2Distribution (fourierL2Equiv d f) := by
  ext φ
  rw [distributionFourier_apply, l2Distribution_apply, l2Distribution_apply]
  have h := fourierL2_pairing f (schwartzConjugate φ)
  simp only [schwartzConjugate_apply, map_star, star_star] at h
  have hc : (schwartzConjugate φ : Euclidean d → ℂ) =
      fun x => starRingEnd ℂ (φ x) := rfl
  rw [hc] at h
  simp only [inverseFourier_conj, map_star, star_star] at h
  simpa only [SchwartzMap.fourierTransformCLE_apply, Complex.conj_conj] using h.symm

theorem distributionInverseFourier_l2Distribution {d : ℕ} (f : FullL2 d) :
    distributionInverseFourier (l2Distribution f) =
      l2Distribution ((fourierL2Equiv d).symm f) := by
  apply distributionFourier_injective
  rw [distributionFourier_inverseFourier, distributionFourier_l2Distribution,
    LinearIsometryEquiv.apply_symm_apply]

end RieszEuclidean.CompleteMinimal
