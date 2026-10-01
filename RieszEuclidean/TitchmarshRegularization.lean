import RieszEuclidean.TitchmarshSupport
import RieszEuclidean.CompleteMinimalDistributionConvolution
import Mathlib.Analysis.Convolution

/-! Regularization of a compactly supported tempered distribution by a compact
smooth kernel. -/

noncomputable section
open MeasureTheory Set SchwartzMap
open scoped SchwartzMap Pointwise FourierTransform

namespace RieszEuclidean.CompleteMinimal

variable {d : ℕ}

/-- A functional which factors through a normed Banach jet space commutes with a
parameter integral as soon as that integral identity is known after applying
the jet map. This is the scalar interchange needed for distribution actions. -/
theorem continuousFunctional_integral_via_factorization
    {α E F : Type*} [MeasurableSpace α] {μ : Measure α}
    [TopologicalSpace E] [AddCommGroup E] [Module ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    (J : E →L[ℂ] F) (L : F →L[ℂ] ℂ) (u : E →L[ℂ] ℂ)
    (hfactor : L.comp J = u) {φ : E} (ψ : α → E)
    (hjet : J φ = ∫ t, J (ψ t) ∂μ)
    (hInt : Integrable (fun t => J (ψ t)) μ) :
    u φ = ∫ t, u (ψ t) ∂μ := by
  calc
    u φ = L (J φ) := by rw [← hfactor]; rfl
    _ = L (∫ t, J (ψ t) ∂μ) := by rw [hjet]
    _ = ∫ t, L (J (ψ t)) ∂μ := (L.integral_comp_comm hInt).symm
    _ = ∫ t, u (ψ t) ∂μ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun t => by
        rw [← hfactor]
        rfl

/-- Fubini for a compact kernel test, reduced to the finite-jet identity. Once
the jet embedding factors the distribution and the jet of the test convolution
is the integral of translated jets, the scalar distribution action commutes
with the kernel integral. -/
theorem distribution_apply_kernelConvolutionTest_eq_integral
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    (J : 𝓢(Euclidean d, ℂ) →L[ℂ] F) (L : F →L[ℂ] ℂ)
    (u : TemperedDistribution d) (hfactor : L.comp J = u)
    (f : Euclidean d → ℂ)
    (hm : Function.HasTemperateGrowth (𝓕 f)) (φ : 𝓢(Euclidean d, ℂ))
    (hjet : J (kernelConvolutionTestCLM f hm φ) =
      ∫ x, J (f x • schwartzTranslateCLM x φ))
    (hInt : Integrable (fun x => J (f x • schwartzTranslateCLM x φ))) :
    u (kernelConvolutionTestCLM f hm φ) =
      ∫ x, f x * u (schwartzTranslateCLM x φ) := by
  have hcomm := continuousFunctional_integral_via_factorization J L u hfactor
    (φ := kernelConvolutionTestCLM f hm φ)
    (ψ := fun x => f x • schwartzTranslateCLM x φ) hjet hInt
  rw [hcomm]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by
    simp only [map_smul, smul_eq_mul]

/-- Reflection `φ(x) ↦ φ(-x)` as a continuous linear map on Schwartz space. -/
def schwartzReflectCLM : 𝓢(Euclidean d, ℂ) →L[ℂ] 𝓢(Euclidean d, ℂ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (ContinuousLinearEquiv.neg ℝ)

@[simp] theorem schwartzReflectCLM_apply (ρ : 𝓢(Euclidean d, ℂ)) (y : Euclidean d) :
    schwartzReflectCLM ρ y = ρ (-y) := by simp [schwartzReflectCLM]

/-- The Schwartz test `y ↦ ρ(x-y)` used to regularize a distribution. -/
def regularizationTest (ρ : 𝓢(Euclidean d, ℂ)) (x : Euclidean d) :
    𝓢(Euclidean d, ℂ) := schwartzTranslateCLM (-x) (schwartzReflectCLM ρ)

@[simp] theorem regularizationTest_apply (ρ : 𝓢(Euclidean d, ℂ)) (x y : Euclidean d) :
    regularizationTest ρ x y = ρ (x - y) := by
  simp [regularizationTest, schwartzTranslateCLM_apply, schwartzReflectCLM_apply,
    sub_eq_add_neg, add_comm]

/-- Pointwise regularization of a distribution by a Schwartz kernel. -/
def distributionRegularization (u : TemperedDistribution d)
    (ρ : 𝓢(Euclidean d, ℂ)) (x : Euclidean d) : ℂ := u (regularizationTest ρ x)

theorem distributionRegularization_apply (u : TemperedDistribution d)
    (ρ : 𝓢(Euclidean d, ℂ)) (x : Euclidean d) :
    distributionRegularization u ρ x = u (regularizationTest ρ x) := rfl

/-- The Fourier-multiplier test action is ordinary convolution by the reflected
kernel. This converts it to Mathlib's compact-right-factor convolution calculus. -/
theorem kernelConvolutionTestCLM_eq_convolution (f : Euclidean d → ℂ)
    (hf : Integrable f) (hm : Function.HasTemperateGrowth (𝓕 f))
    (φ : 𝓢(Euclidean d, ℂ)) (y : Euclidean d) :
    kernelConvolutionTestCLM f hm φ y =
      MeasureTheory.convolution (φ : Euclidean d → ℂ)
        (fun z => f (-z)) (ContinuousLinearMap.mul ℝ ℂ) volume y := by
  rw [kernelConvolutionTestCLM_apply f hf hm]
  rw [MeasureTheory.convolution_def]
  let T : Euclidean d → Euclidean d := fun z => y + z
  have hT : MeasureTheory.MeasurePreserving T volume volume := by
    simpa [T] using MeasureTheory.measurePreserving_add_left volume y
  have heT : MeasurableEmbedding T := by
    simpa [T] using measurableEmbedding_addLeft y
  calc
    (∫ z, (f z) * φ (y + z)) = ∫ z, φ (T z) * f ((T z) - y) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun z => by
        simp [T, sub_add_cancel, mul_comm]
    _ = ∫ z, φ z * f (z - y) := by
      simpa only [T] using hT.integral_comp heT (fun z => φ z * f (z - y))
    _ = ∫ z, φ z * f (-(y - z)) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun z => by simp [sub_eq_add_neg, neg_sub]

theorem schwartzReflectCLM_tsupport_subset (ρ : 𝓢(Euclidean d, ℂ)) :
    tsupport (schwartzReflectCLM ρ : Euclidean d → ℂ) ⊆
      (fun x : Euclidean d => -x) ⁻¹' tsupport (ρ : Euclidean d → ℂ) := by
  change closure (Function.support (schwartzReflectCLM ρ : Euclidean d → ℂ)) ⊆ _
  apply IsClosed.closure_subset_iff
    ((isClosed_tsupport (ρ : Euclidean d → ℂ)).preimage continuous_neg) |>.mpr
  intro x hx
  change schwartzReflectCLM ρ x ≠ 0 at hx
  exact subset_tsupport _ (by simpa using hx)

theorem schwartzReflectCLM_hasCompactSupport {ρ : 𝓢(Euclidean d, ℂ)}
    (hρ : HasCompactSupport (ρ : Euclidean d → ℂ)) :
    HasCompactSupport (schwartzReflectCLM ρ : Euclidean d → ℂ) := by
  let T : Euclidean d → Euclidean d := fun x => -x
  have hpre : T ⁻¹' tsupport (ρ : Euclidean d → ℂ) =
      T '' tsupport (ρ : Euclidean d → ℂ) := by
    ext x
    constructor
    · intro hx
      refine ⟨T x, hx, ?_⟩
      simp [T]
    · rintro ⟨y, hy, rfl⟩
      simpa [T]
  have hK : IsCompact (T '' tsupport (ρ : Euclidean d → ℂ)) :=
    hρ.image continuous_neg
  exact hK.of_isClosed_subset isClosed_closure (by
    rw [← hpre]
    exact schwartzReflectCLM_tsupport_subset ρ)

/-- Compact smooth kernels make the actual inner convolution test smooth in its
translation parameter. The proof uses Mathlib's compact-right-factor convolution
regularity theorem after identifying the test action with ordinary convolution. -/
theorem kernelConvolutionTestCLM_contDiff (ρ φ : 𝓢(Euclidean d, ℂ))
    (hρ : HasCompactSupport (ρ : Euclidean d → ℂ)) (n : ℕ) :
    ContDiff ℝ n (kernelConvolutionTestCLM (ρ : Euclidean d → ℂ)
      (fourier_hasTemperateGrowth_of_compact_support ρ.integrable hρ
        (Filter.Eventually.of_forall fun _ hx => image_eq_zero_of_nmem_tsupport hx)) φ) := by
  let hm := fourier_hasTemperateGrowth_of_compact_support ρ.integrable hρ
    (Filter.Eventually.of_forall fun _ hx => image_eq_zero_of_nmem_tsupport hx)
  have heq : (fun y => kernelConvolutionTestCLM (ρ : Euclidean d → ℂ) hm φ y) =
      MeasureTheory.convolution (φ : Euclidean d → ℂ)
        (fun z => ρ (-z)) (ContinuousLinearMap.mul ℝ ℂ) volume := by
    funext y
    exact kernelConvolutionTestCLM_eq_convolution _ ρ.integrable hm φ y
  change ContDiff ℝ n (fun y => kernelConvolutionTestCLM (ρ : Euclidean d → ℂ) hm φ y)
  rw [heq]
  have hreflect : (schwartzReflectCLM ρ : Euclidean d → ℂ) = fun z => ρ (-z) := by
    funext z
    simp
  rw [← hreflect]
  simpa using HasCompactSupport.contDiff_convolution_right
    (n := n) (L := ContinuousLinearMap.mul ℝ ℂ) (μ := volume)
    (schwartzReflectCLM_hasCompactSupport hρ) φ.continuous.locallyIntegrable
    ((schwartzReflectCLM ρ).smooth n)


private theorem schwartz_fderiv_bound (φ : 𝓢(Euclidean d, ℂ)) (x : Euclidean d) :
    ‖fderiv ℝ φ x‖ ≤ SchwartzMap.seminorm ℂ 0 1 φ := by
  have h := φ.le_seminorm ℂ 0 1 x
  calc
    ‖fderiv ℝ φ x‖ = ‖iteratedFDeriv ℝ 0 (fderiv ℝ φ) x‖ := by simp
    _ = ‖iteratedFDeriv ℝ 1 φ x‖ := norm_iteratedFDeriv_fderiv
    _ ≤ SchwartzMap.seminorm ℂ 0 1 φ := by simpa using h

theorem regularizationTest_tsupport_subset (ρ : 𝓢(Euclidean d, ℂ))
    (x : Euclidean d) :
    tsupport (regularizationTest ρ x : Euclidean d → ℂ) ⊆
      (fun y : Euclidean d => x - y) ⁻¹' tsupport (ρ : Euclidean d → ℂ) := by
  change closure (Function.support (regularizationTest ρ x : Euclidean d → ℂ)) ⊆ _
  apply IsClosed.closure_subset_iff
    ((isClosed_tsupport (ρ : Euclidean d → ℂ)).preimage
      (continuous_const.sub continuous_id)) |>.mpr
  intro y hy
  change regularizationTest ρ x y ≠ 0 at hy
  have hy' : ρ (x - y) ≠ 0 := by
    simpa only [regularizationTest_apply] using hy
  exact subset_tsupport _ hy'

theorem regularizationTest_hasCompactSupport {ρ : 𝓢(Euclidean d, ℂ)}
    (hρ : HasCompactSupport (ρ : Euclidean d → ℂ)) (x : Euclidean d) :
    HasCompactSupport (regularizationTest ρ x : Euclidean d → ℂ) := by
  let T : Euclidean d → Euclidean d := fun y => x - y
  have hT : Continuous T := continuous_const.sub continuous_id
  have hpre : T ⁻¹' tsupport (ρ : Euclidean d → ℂ) =
      T '' tsupport (ρ : Euclidean d → ℂ) := by
    ext y
    constructor
    · intro hy
      refine ⟨T y, hy, ?_⟩
      simp [T]
    · rintro ⟨z, hz, rfl⟩
      simpa [T]
  have hK : IsCompact (T '' tsupport (ρ : Euclidean d → ℂ)) := hρ.image hT
  exact hK.of_isClosed_subset isClosed_closure (by
    rw [← hpre]
    exact regularizationTest_tsupport_subset ρ x)

theorem distributionRegularization_eq_zero_of_not_mem_add_support
    {u : TemperedDistribution d} (ρ : 𝓢(Euclidean d, ℂ))
    {x : Euclidean d} (hx : x ∉ distributionSupport u + tsupport (ρ : Euclidean d → ℂ)) :
    distributionRegularization u ρ x = 0 := by
  rw [distributionRegularization_apply]
  have hdisj : Disjoint (tsupport (regularizationTest ρ x : Euclidean d → ℂ))
      (distributionSupport u) := by
    apply Set.disjoint_left.mpr
    intro y hy hys
    have hxy : x - y ∈ tsupport (ρ : Euclidean d → ℂ) :=
      regularizationTest_tsupport_subset ρ x hy
    apply hx
    apply Set.mem_add.mpr
    refine ⟨y, hys, x - y, hxy, ?_⟩
    simp
  exact (distributionSupportedIn_support u).schwartz_test (regularizationTest ρ x) hdisj

theorem regularizationTest_ne_zero_of_regularization_ne_zero
    (u : TemperedDistribution d) (ρ : 𝓢(Euclidean d, ℂ)) (x : Euclidean d)
    (h : distributionRegularization u ρ x ≠ 0) : regularizationTest ρ x ≠ 0 := by
  intro hz
  apply h
  rw [distributionRegularization_apply, hz]
  simp

theorem distributionRegularization_test_of_reflected_translate
    (u : TemperedDistribution d) (φ : 𝓢(Euclidean d, ℂ)) (x : Euclidean d) :
    distributionRegularization u (regularizationTest φ x) x = u φ := by
  rw [distributionRegularization_apply]
  congr 1
  ext y
  simp [regularizationTest_apply]

/-- Every support point is detected at the same point by regularization with a
compact kernel whose support is the reflected local test support. -/
theorem distributionSupport_regularization_detect
    {u : TemperedDistribution d} {x : Euclidean d}
    (hx : x ∈ distributionSupport u) (U : Set (Euclidean d))
    (hU : IsOpen U) (hxU : x ∈ U) :
    ∃ ρ : 𝓢(Euclidean d, ℂ), HasCompactSupport (ρ : Euclidean d → ℂ) ∧
      (∀ z ∈ tsupport (ρ : Euclidean d → ℂ), x - z ∈ U) ∧
      distributionRegularization u ρ x ≠ 0 := by
  obtain ⟨φ, hφc, hφs, hφ⟩ := hx U hU hxU
  refine ⟨regularizationTest φ x, regularizationTest_hasCompactSupport hφc x, ?_, ?_⟩
  · intro z hz
    have hzx := regularizationTest_tsupport_subset φ x hz
    exact hφs hzx
  · rw [distributionRegularization_test_of_reflected_translate]
    exact hφ

/-- Regularizing an actual distribution convolution gives an outer distribution
acting on the inner regularization. This is the exact test-level identity before
any attempt to exchange distribution actions with ordinary integrals. -/
theorem IsDistributionConvolution.regularization_formula
    {u v w : TemperedDistribution d} (hc : IsDistributionConvolution u v w)
    (ρ : 𝓢(Euclidean d, ℂ)) (x : Euclidean d) :
    ∃ ψ : 𝓢(Euclidean d, ℂ),
      (∀ y : Euclidean d, ψ y = distributionRegularization v ρ (x - y)) ∧
      distributionRegularization w ρ x = u ψ := by
  obtain ⟨ψ, hψ, hw⟩ := hc (regularizationTest ρ x)
  refine ⟨ψ, ?_, ?_⟩
  · intro y
    rw [distributionRegularization_apply]
    have heq : schwartzTranslateCLM y (regularizationTest ρ x) =
        regularizationTest ρ (x - y) := by
      ext z
      simp [regularizationTest_apply, sub_eq_add_neg, add_assoc, add_comm, add_left_comm]
    exact (hψ y).trans (congrArg v heq)
  · rw [distributionRegularization_apply]
    exact hw

end RieszEuclidean.CompleteMinimal
