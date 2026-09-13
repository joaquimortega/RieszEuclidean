import RieszEuclidean.FourierAgreement
import RieszEuclidean.EuclideanBoxes
/-!
# Normalized Euclidean box Fejér kernels

The existing positive-sign L² Fourier unitary and its integral agreement give
Plancherel for L¹ ∩ L² functions. Applied to the actual coordinate-box indicator,
this proves the Fejér kernel is nonnegative, integrable, and has integral one.
-/

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace RieszEuclidean

/-- Squared norm is integrable for an L² representative. -/
theorem integrable_sq_norm_fullL2 {d : ℕ} (f : FullL2 d) :
    Integrable (fun x => ‖f x‖ ^ 2) :=
  (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable f)).mp (Lp.memLp f)

/-- The L² norm is the integral of the pointwise squared norm. -/
theorem integral_sq_norm_fullL2 {d : ℕ} (f : FullL2 d) :
    (∫ x, ‖f x‖ ^ 2) = ‖f‖ ^ 2 := by
  have h := congrArg Complex.re (L2.inner_def f f)
  change Complex.reCLM (inner (𝕜 := ℂ) f f) = Complex.reCLM (∫ x, inner (𝕜 := ℂ) (f x) (f x)) at h
  rw [← Complex.reCLM.integral_comp_comm (L2.integrable_inner (𝕜 := ℂ) f f)] at h
  simp only [Complex.reCLM_apply, inner_self_eq_norm_sq_to_K] at h
  change ( (‖f‖ : ℂ) ^ 2).re = ∫ x, ((‖f x‖ : ℂ) ^ 2).re at h
  simpa only [← Complex.ofReal_pow, Complex.ofReal_re] using h.symm

/-- Plancherel for an integrable function which also belongs to L². -/
theorem inverseFourier_sq_norm {d : ℕ} {f : Euclidean d → ℂ}
    (h1 : Integrable f) (h2 : MemLp f 2) :
    Integrable (fun x => ‖Real.fourierIntegralInv f x‖ ^ 2) ∧
      (∫ x, ‖Real.fourierIntegralInv f x‖ ^ 2) = ∫ x, ‖f x‖ ^ 2 := by
  let F := h2.toLp f
  have he : (F : Euclidean d → ℂ) =ᵐ[volume] f := h2.coeFn_toLp
  have hF : Integrable (F : Euclidean d → ℂ) := h1.congr he.symm
  have ht : Real.fourierIntegralInv F = Real.fourierIntegralInv f := by
    funext x
    rw [Real.fourierIntegralInv_eq, Real.fourierIntegralInv_eq]
    apply integral_congr_ae
    filter_upwards [he] with y hy
    rw [hy]
  have ha := paperFourierL2_eq_integral F hF
  rw [ht] at ha
  have hs : (fun x => ‖paperFourierL2 d F x‖ ^ 2) =ᵐ[volume]
      (fun x => ‖Real.fourierIntegralInv f x‖ ^ 2) := ha.fun_comp (fun z => ‖z‖ ^ 2)
  refine ⟨(integrable_sq_norm_fullL2 _).congr hs, ?_⟩
  rw [← integral_congr_ae hs, integral_sq_norm_fullL2,
    (paperFourierL2 d).norm_map, ← integral_sq_norm_fullL2 F]
  exact integral_congr_ae (he.fun_comp (fun z => ‖z‖ ^ 2))

/-- The nonnegative Fejér kernel of the actual Euclidean coordinate box. -/
def fejerKernel (d : ℕ) (R : ℝ) (x : Euclidean d) : ℝ :=
  (volume.real (euclideanBox d R))⁻¹ *
    ‖Real.fourierIntegralInv ((euclideanBox d R).indicator (fun _ => (1 : ℂ))) x‖ ^ 2

/-- The box transform is the exponential average appearing in the paper. -/
theorem inverseFourier_box_indicator (d : ℕ) (R : ℝ) (x : Euclidean d) :
    Real.fourierIntegralInv ((euclideanBox d R).indicator (fun _ => (1 : ℂ))) x =
      ∫ v in euclideanBox d R, exponential x v := by
  rw [Real.fourierIntegralInv_eq', ← integral_indicator (measurableSet_euclideanBox d R)]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun v => by
    by_cases hv : v ∈ euclideanBox d R
    · simp only [Set.indicator_of_mem hv, smul_eq_mul, mul_one, exponential]
      congr 1
      push_cast
      rw [real_inner_comm v x]
      ring
    · simp [hv]

/-- The kernel is exactly the normalized squared box exponential integral. -/
theorem fejerKernel_eq_box_integral (d : ℕ) (R : ℝ) (x : Euclidean d) :
    fejerKernel d R x = (volume.real (euclideanBox d R))⁻¹ *
      ‖∫ v in euclideanBox d R, exponential x v‖ ^ 2 := by
  rw [fejerKernel, inverseFourier_box_indicator]

/-- Fejér kernels are pointwise nonnegative. -/
theorem fejerKernel_nonneg (d : ℕ) (R : ℝ) (x : Euclidean d) :
    0 ≤ fejerKernel d R x := by
  exact mul_nonneg (inv_nonneg.mpr ENNReal.toReal_nonneg) (sq_nonneg _)

/-- A positive-side Euclidean box gives an integrable Fejér kernel of mass one. -/
theorem fejerKernel_integrable_integral (d : ℕ) {R : ℝ} (hR : 0 < R) :
    Integrable (fejerKernel d R) ∧ (∫ x, fejerKernel d R x) = 1 := by
  have hm := measurableSet_euclideanBox d R
  obtain ⟨hp, hf⟩ := volume_euclideanBox_pos_lt_top d hR
  have h1 : Integrable ((euclideanBox d R).indicator (fun _ => (1 : ℂ))) :=
    (integrable_indicator_iff hm).mpr (integrableOn_const.mpr (Or.inr hf))
  have h2 : MemLp ((euclideanBox d R).indicator (fun _ => (1 : ℂ))) 2 :=
    memLp_indicator_const 2 hm 1 (Or.inr hf.ne)
  obtain ⟨hi, he⟩ := inverseFourier_sq_norm h1 h2
  refine ⟨hi.const_mul _, ?_⟩
  change (∫ x, (volume.real (euclideanBox d R))⁻¹ *
    ‖Real.fourierIntegralInv ((euclideanBox d R).indicator (fun _ => (1 : ℂ))) x‖ ^ 2) = 1
  rw [integral_const_mul, he]
  have hind : (fun x => ‖(euclideanBox d R).indicator (fun _ => (1 : ℂ)) x‖ ^ 2) =
      (euclideanBox d R).indicator (fun _ => (1 : ℝ)) := by
    funext x
    by_cases hx : x ∈ euclideanBox d R <;> simp [hx]
  rw [hind, integral_indicator_const 1 hm, smul_eq_mul, mul_one]
  exact inv_mul_cancel₀ (ENNReal.toReal_pos hp.ne' hf.ne).ne'

end RieszEuclidean
