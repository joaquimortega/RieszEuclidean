import RieszEuclidean.CompleteMinimalConvolutionSupport
import Mathlib.Analysis.Fourier.FourierTransformDeriv

/-!
# Fourier multiplication and actual distribution convolution

For a compactly supported integrable L² kernel, all moments are integrable and
its Fourier transform is a smooth function of temperate growth. Multiplication
by this transform preserves the Schwartz test space. Fourier transposition then
gives actual convolution, with the integrable kernel in the inner test action.
-/

noncomputable section
open MeasureTheory SchwartzMap Set
open scoped SchwartzMap FourierTransform ENNReal Pointwise

namespace RieszEuclidean.CompleteMinimal

variable {d : ℕ}

/-- Compact a.e. physical support supplies all the moments needed for Fourier differentiation. -/
theorem integrable_moments_of_compact_support {f : Euclidean d → ℂ} (hf : Integrable f)
    {K : Set (Euclidean d)} (hK : IsCompact K)
    (hs : ∀ᵐ x, x ∉ K → f x = 0) (n : ℕ) :
    Integrable (fun x => ‖x‖ ^ n * ‖f x‖) := by
  have hOn : IntegrableOn (fun x => ‖f x‖ * ‖x‖ ^ n) K :=
    hf.norm.integrableOn.mul_continuousOn (continuous_norm.pow n).continuousOn hK
  have hI := (integrable_indicator_iff hK.measurableSet).mpr hOn
  apply hI.congr
  filter_upwards [hs] with x hx
  by_cases hmem : x ∈ K
  · simp [hmem, mul_comm]
  · simp [hmem, hx hmem]

/-- A Fourier transform with all integrable moments has bounded derivatives of
every order, hence the precise temperate-growth property used by Schwartz multipliers. -/
theorem fourier_hasTemperateGrowth_of_moments {f : Euclidean d → ℂ}
    (hf : Integrable f) (hm : ∀ n : ℕ, Integrable (fun x => ‖x‖ ^ n * ‖f x‖)) :
    Function.HasTemperateGrowth (𝓕 f) := by
  refine ⟨Real.contDiff_fourierIntegral (N := ⊤) (fun n _ => hm n), ?_⟩
  intro n
  let g := fun x : Euclidean d => VectorFourier.fourierPowSMulRight (innerSL ℝ) f x n
  refine ⟨0, ∫ x, ‖g x‖, ?_⟩
  intro ξ
  rw [Real.iteratedFDeriv_fourierIntegral (N := ⊤) (fun k _ => hm k) hf.1 (by simp)]
  simpa only [pow_zero, mul_one] using
    VectorFourier.norm_fourierIntegral_le_integral_norm 𝐞 volume (innerₗ (Euclidean d)) g ξ

theorem fourier_hasTemperateGrowth_of_compact_support {f : Euclidean d → ℂ}
    (hf : Integrable f) {K : Set (Euclidean d)} (hK : IsCompact K)
    (hs : ∀ᵐ x, x ∉ K → f x = 0) : Function.HasTemperateGrowth (𝓕 f) :=
  fourier_hasTemperateGrowth_of_moments hf (integrable_moments_of_compact_support hf hK hs)

/-- Multiplication of an actual Schwartz test by a smooth function of temperate growth. -/
def schwartzMultiplierCLM (m : Euclidean d → ℂ) (hm : Function.HasTemperateGrowth m) :
    𝓢(Euclidean d, ℂ) →L[ℂ] 𝓢(Euclidean d, ℂ) :=
  SchwartzMap.bilinLeftCLM (ContinuousLinearMap.mul ℂ ℂ) hm

@[simp] theorem schwartzMultiplierCLM_apply (m : Euclidean d → ℂ)
    (hm : Function.HasTemperateGrowth m) (φ : 𝓢(Euclidean d, ℂ)) (x : Euclidean d) :
    schwartzMultiplierCLM m hm φ x = φ x * m x := rfl

/-- The Fourier-conjugated multiplier that will be identified with the actual
inner convolution action of the integrable physical kernel. -/
def kernelConvolutionTestCLM (f : Euclidean d → ℂ)
    (hm : Function.HasTemperateGrowth (𝓕 f)) :
    𝓢(Euclidean d, ℂ) →L[ℂ] 𝓢(Euclidean d, ℂ) :=
  (SchwartzMap.fourierTransformCLE ℂ).toContinuousLinearMap.comp
    ((schwartzMultiplierCLM (𝓕 f) hm).comp
      (SchwartzMap.fourierTransformCLE ℂ).symm.toContinuousLinearMap)

/-- Inverse Fourier transform converts physical test translation to the actual
negative Fourier phase, with no distributional identity assumed. -/
theorem inverseFourier_schwartzTranslate (φ : 𝓢(Euclidean d, ℂ)) (y ξ : Euclidean d) :
    (SchwartzMap.fourierTransformCLE ℂ).symm (schwartzTranslateCLM y φ) ξ =
      𝐞 (-inner (𝕜 := ℝ) y ξ) • ((SchwartzMap.fourierTransformCLE ℂ).symm φ ξ) := by
  have h := congrFun (VectorFourier.fourierIntegral_comp_add_right 𝐞 volume
    (-innerₗ (Euclidean d)) (φ : Euclidean d → ℂ) y) ξ
  simpa only [SchwartzMap.fourierTransformCLE_symm_apply, Real.fourierIntegralInv,
    Function.comp_def, schwartzTranslateCLM_apply, add_comm, LinearMap.neg_apply,
    innerₗ_apply] using h

/-- The outer Schwartz witness is exactly the iterated inner-kernel action.
The proof is scalar Fourier Fubini and Schwartz Fourier inversion. -/
theorem kernelConvolutionTestCLM_apply (f : Euclidean d → ℂ) (hf : Integrable f)
    (hm : Function.HasTemperateGrowth (𝓕 f)) (φ : 𝓢(Euclidean d, ℂ)) (y : Euclidean d) :
    kernelConvolutionTestCLM f hm φ y = ∫ x, f x * φ (y + x) := by
  let χ := (SchwartzMap.fourierTransformCLE ℂ).symm (schwartzTranslateCLM y φ)
  have hfirst : kernelConvolutionTestCLM f hm φ y = ∫ ξ, 𝓕 f ξ * χ ξ := by
    change 𝓕 (schwartzMultiplierCLM (𝓕 f) hm
      ((SchwartzMap.fourierTransformCLE ℂ).symm φ)) y = _
    rw [Real.fourierIntegral_eq]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun ξ => by
      dsimp only
      rw [schwartzMultiplierCLM_apply]
      dsimp [χ]
      rw [inverseFourier_schwartzTranslate]
      rw [real_inner_comm ξ y]
      simp [Circle.smul_def, mul_comm, mul_left_comm]
  rw [hfirst, integral_fourier_mul hf χ.integrable]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by
    dsimp only
    have hx := congrArg (fun ψ : 𝓢(Euclidean d, ℂ) => ψ x)
      ((SchwartzMap.fourierTransformCLE ℂ).apply_symm_apply (schwartzTranslateCLM y φ))
    change 𝓕 χ x = φ (y + x) at hx
    rw [hx]

/-- Multiplication of a tempered distribution by an actual smooth multiplier. -/
def distributionMultiply (m : Euclidean d → ℂ) (hm : Function.HasTemperateGrowth m)
    (u : TemperedDistribution d) : TemperedDistribution d :=
  u.comp (schwartzMultiplierCLM m hm)

@[simp] theorem distributionMultiply_apply (m : Euclidean d → ℂ)
    (hm : Function.HasTemperateGrowth m) (u : TemperedDistribution d)
    (φ : 𝓢(Euclidean d, ℂ)) :
    distributionMultiply m hm u φ = u (schwartzMultiplierCLM m hm φ) := rfl

/-- For regular distributions this operation is the actual pointwise product.
Polynomial bounds merely certify the integrals defining the two distributions. -/
theorem distributionMultiply_polynomialDistribution {N M : ℕ}
    (m q p : Euclidean d → ℂ) (hm : Function.HasTemperateGrowth m)
    {C D : ℝ} (hC : 0 ≤ C) (hq : ∀ x, ‖q x‖ ≤ C * (1 + ‖x‖) ^ N)
    (hqm : AEStronglyMeasurable q volume)
    (hD : 0 ≤ D) (hp : ∀ x, ‖p x‖ ≤ D * (1 + ‖x‖) ^ M)
    (hpm : AEStronglyMeasurable p volume) (hprod : ∀ x, p x = m x * q x) :
    distributionMultiply m hm (polynomialDistribution q hC hq hqm) =
      polynomialDistribution p hD hp hpm := by
  ext φ
  rw [distributionMultiply_apply, polynomialDistribution_apply, polynomialDistribution_apply]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by
    dsimp only
    rw [schwartzMultiplierCLM_apply, hprod]
    ring

/-- Fourier multiplication by an integrable kernel is actual distribution convolution.
The order places the L² kernel in the inner iterated test action. -/
theorem isDistributionConvolution_fourierMultiplier (f : FullL2 d)
    (hf : Integrable (f : Euclidean d → ℂ))
    (hm : Function.HasTemperateGrowth (𝓕 (f : Euclidean d → ℂ)))
    (v : TemperedDistribution d) :
    IsDistributionConvolution v (l2Distribution f)
      (distributionInverseFourier
        (distributionMultiply (𝓕 (f : Euclidean d → ℂ)) hm (distributionFourier v))) := by
  intro φ
  refine ⟨kernelConvolutionTestCLM f hm φ, ?_, rfl⟩
  intro x
  rw [kernelConvolutionTestCLM_apply _ hf, l2Distribution_apply]
  rfl

/-- Any proved Fourier-product identity therefore certifies genuine convolution. -/
theorem isDistributionConvolution_of_fourier_product (f : FullL2 d)
    (hf : Integrable (f : Euclidean d → ℂ))
    (hm : Function.HasTemperateGrowth (𝓕 (f : Euclidean d → ℂ)))
    {v w : TemperedDistribution d}
    (hproduct : distributionFourier w =
      distributionMultiply (𝓕 (f : Euclidean d → ℂ)) hm (distributionFourier v)) :
    IsDistributionConvolution v (l2Distribution f) w := by
  have hw : w = distributionInverseFourier
      (distributionMultiply (𝓕 (f : Euclidean d → ℂ)) hm (distributionFourier v)) := by
    rw [← hproduct, distributionInverseFourier_fourier]
  rw [hw]
  exact isDistributionConvolution_fourierMultiplier f hf hm v

/-- A compactly supported L² kernel needs no additional smoothness hypothesis:
its Fourier multiplier has temperate growth by the proved moment estimates. -/
theorem isDistributionConvolution_compact_fourierMultiplier (f : FullL2 d)
    (hf : Integrable (f : Euclidean d → ℂ)) {K : Set (Euclidean d)}
    (hK : IsCompact K) (hs : ∀ᵐ x, x ∉ K → f x = 0) (v : TemperedDistribution d) :
    IsDistributionConvolution v (l2Distribution f)
      (distributionInverseFourier
        (distributionMultiply (𝓕 (f : Euclidean d → ℂ))
          (fourier_hasTemperateGrowth_of_compact_support hf hK hs) (distributionFourier v))) :=
  isDistributionConvolution_fourierMultiplier f hf
    (fourier_hasTemperateGrowth_of_compact_support hf hK hs) v

/-- The John-ellipsoid conclusion with the kernel in the inner convolution action,
which is the order proved directly by the Fourier-multiplier bridge. -/
theorem TitchmarshLions.supportedIn_origin_of_john_right (hTL : TitchmarshLions d)
    {u v w : TemperedDistribution d} (hu : CompactlySupportedDistribution u)
    (hv : CompactlySupportedDistribution v) (hu0 : u ≠ 0) (hv0 : v ≠ 0)
    (hc : IsDistributionConvolution v u w) {K E : Set (Euclidean d)}
    (hK : Convex ℝ K) (hKclosed : IsClosed K) (hJ : IsJohnEllipsoid K E)
    (hEu : convexHull ℝ (distributionSupport u) = E)
    (hw : DistributionSupportedIn w K) : DistributionSupportedIn v {0} := by
  apply (distributionSupportedIn_support v).mono
  intro t ht
  apply Set.mem_singleton_iff.mpr
  apply hJ.eq_zero_of_translated_subset hK
  rintro _ ⟨x, hx, rfl⟩
  have hconv : t + x ∈ convexHull ℝ (distributionSupport w) := by
    rw [hTL v u w hv hu hv0 hu0 hc]
    exact Set.mem_add.mpr ⟨t, subset_convexHull ℝ _ ht, x, hEu.symm ▸ hx, rfl⟩
  exact convexHull_min (hw.support_subset hKclosed) hK hconv

end RieszEuclidean.CompleteMinimal
