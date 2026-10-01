import RieszEuclidean.CompleteMinimalEntireFourier
import RieszEuclidean.TitchmarshFourierProduct
import Mathlib.Analysis.Calculus.ParametricIntegral

/-! Integral estimates and analyticity for the directional Laplace transform. -/

noncomputable section
set_option maxHeartbeats 600000
open MeasureTheory Filter Topology

namespace RieszEuclidean.CompleteMinimal

/-- The directional Laplace transform, with sign chosen for decay on `ℓ x < T`.
The support hypothesis is not built into the definition. -/
def titchmarshLaplaceIntegral {d : ℕ} (f : Euclidean d → ℂ)
    (ℓ : Euclidean d →L[ℝ] ℝ) (T : ℝ) (z : ℂ) : ℂ :=
  ∫ x, f x * Complex.exp (z * ((T - ℓ x : ℝ) : ℂ))

private theorem laplace_arg_bound {d : ℕ} {f : Euclidean d → ℂ}
    (ℓ : Euclidean d →L[ℝ] ℝ) (T R : ℝ)
    (hsupp : ∀ᵐ x, f x ≠ 0 → ‖x‖ ≤ R) :
    ∀ᵐ x, f x ≠ 0 → ‖((T - ℓ x : ℝ) : ℂ)‖ ≤ |T| + ‖ℓ‖ * R := by
  filter_upwards [hsupp] with x hx hfx
  rw [Complex.norm_real, Real.norm_eq_abs]
  calc
    |T - ℓ x| ≤ |T| + |ℓ x| := abs_sub _ _
    _ ≤ |T| + ‖ℓ‖ * ‖x‖ := by
      gcongr
      exact ContinuousLinearMap.le_opNorm ℓ x
    _ ≤ |T| + ‖ℓ‖ * R := by
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_left (hx hfx) (norm_nonneg _))

/-- Integrability of the Laplace integrand follows from bounded support. -/
theorem titchmarshLaplaceIntegral_integrable {d : ℕ} {f : Euclidean d → ℂ}
    (hf : Integrable f) (ℓ : Euclidean d →L[ℝ] ℝ) (T : ℝ) {R : ℝ}
    (hsupp : ∀ᵐ x, f x ≠ 0 → ‖x‖ ≤ R) (z : ℂ) :
    Integrable (fun x => f x * Complex.exp (z * ((T - ℓ x : ℝ) : ℂ))) := by
  let B : ℝ := |T| + ‖ℓ‖ * R
  let C : ℝ := Real.exp (‖z‖ * B)
  have hmeas : AEStronglyMeasurable
      (fun x => f x * Complex.exp (z * ((T - ℓ x : ℝ) : ℂ))) := by
    exact hf.aestronglyMeasurable.mul
      ((Complex.continuous_exp.comp
        (continuous_const.mul (Complex.continuous_ofReal.comp
          (continuous_const.sub ℓ.continuous)))).aestronglyMeasurable)
  apply (hf.norm.mul_const C).mono' hmeas
  filter_upwards [laplace_arg_bound ℓ T R hsupp] with x hx
  by_cases hfx : f x = 0
  · simp [hfx]
  · have harg : (z * ((T - ℓ x : ℝ) : ℂ)).re ≤ ‖z‖ * B := by
      calc
        _ ≤ ‖z * ((T - ℓ x : ℝ) : ℂ)‖ := Complex.re_le_norm _
        _ = ‖z‖ * ‖((T - ℓ x : ℝ) : ℂ)‖ := norm_mul _ _
        _ ≤ ‖z‖ * B := mul_le_mul_of_nonneg_left (hx hfx) (norm_nonneg _)
    rw [norm_mul, Complex.norm_exp]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    exact Real.exp_le_exp.mpr harg

/-- Bounded support makes the directional Laplace transform entire. This follows
by representing the real functional as an inner product and using the shifted
entire Fourier transform identity. -/
theorem titchmarshLaplaceIntegral_differentiable {d : ℕ}
    {f : Euclidean d → ℂ} (hf : Integrable f)
    (ℓ : Euclidean d →L[ℝ] ℝ) (T : ℝ) {R : ℝ} (hR : 0 ≤ R)
    (hsupp : ∀ᵐ x, f x ≠ 0 → ‖x‖ ≤ R) :
    Differentiable ℂ (titchmarshLaplaceIntegral f ℓ T) := by
  let v : Euclidean d := (InnerProductSpace.toDual ℝ (Euclidean d)).symm ℓ
  have hrepr : ℓ = innerSL ℝ v := by
    ext x
    simp only [innerSL_apply]
    exact (InnerProductSpace.toDual_symm_apply (x := x) (y := ℓ)).symm
  have hshift : Differentiable ℂ (fun z : ℂ =>
      Complex.exp (z * (T : ℂ)) *
        entireFourier f ((-(z * Complex.I) / (2 * Real.pi)) • realToComplex v)) := by
    have hfrequency : Differentiable ℂ (fun z : ℂ =>
        (-(z * Complex.I) / (2 * Real.pi)) • realToComplex v) := by fun_prop
    have hfourier := (entireFourier_differentiable hf hR hsupp).comp hfrequency
    have hexp : Differentiable ℂ (fun z : ℂ => Complex.exp (z * (T : ℂ))) := by fun_prop
    exact hexp.mul hfourier
  have hEq (z : ℂ) : titchmarshLaplaceIntegral f ℓ T z =
      Complex.exp (z * (T : ℂ)) *
        entireFourier f ((-(z * Complex.I) / (2 * Real.pi)) • realToComplex v) := by
    rw [hrepr]
    change (∫ x, f x * Complex.exp (z * ((T - inner (𝕜 := ℝ) v x : ℝ) : ℂ))) = _
    have hz0 : realToComplex (0 : Euclidean d) = 0 := by
      ext j
      simp [realToComplex]
    have hkernel (x : Euclidean d) : complexFourierKernel x 0 = 1 := by
      rw [← hz0, complexFourierKernel_realToComplex]
      simp
    have hshifted := integral_directionalLaplace_eq_entireFourier_shift f v 0 T z
    rw [hz0] at hshifted
    calc
      (∫ x, f x * Complex.exp (z * ((T - inner (𝕜 := ℝ) v x : ℝ) : ℂ))) =
          ∫ x, f x * Complex.exp (z * ((T - inner (𝕜 := ℝ) v x : ℝ) : ℂ)) *
            complexFourierKernel x 0 := by
        apply integral_congr_ae
        filter_upwards with x
        rw [hkernel x]
        ring
      _ = _ := by simpa using hshifted
  intro z
  apply (hshift z).congr_of_eventuallyEq
  filter_upwards with w
  exact hEq w

/-- On either closed half-plane pointing away from the support, the transform is
bounded by the `L¹` norm. -/
theorem titchmarshLaplaceIntegral_norm_le {d : ℕ} {f : Euclidean d → ℂ}
    (hf : Integrable f) (ℓ : Euclidean d →L[ℝ] ℝ) (T : ℝ) (z : ℂ)
    (hz : (0 ≤ z.re ∧ ∀ᵐ x, f x ≠ 0 → T ≤ ℓ x) ∨
      (z.re ≤ 0 ∧ ∀ᵐ x, f x ≠ 0 → ℓ x ≤ T)) :
    ‖titchmarshLaplaceIntegral f ℓ T z‖ ≤ ∫ x, ‖f x‖ := by
  apply norm_integral_le_of_norm_le hf.norm
  rcases hz with ⟨hzRe, hside⟩ | ⟨hzRe, hside⟩
  · filter_upwards [hside] with x hx
    by_cases hfx : f x = 0
    · simp [hfx]
    · rw [norm_mul, Complex.norm_exp]
      have hRe : (z * ↑(T - ℓ x)).re = z.re * (T - ℓ x) := by simp [Complex.mul_re]
      rw [hRe]
      have hle : z.re * (T - ℓ x) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos hzRe (by linarith [hx hfx])
      exact mul_le_of_le_one_right (norm_nonneg _) (Real.exp_le_one_iff.mpr hle)
  · filter_upwards [hside] with x hx
    by_cases hfx : f x = 0
    · simp [hfx]
    · rw [norm_mul, Complex.norm_exp]
      have hRe : (z * ↑(T - ℓ x)).re = z.re * (T - ℓ x) := by simp [Complex.mul_re]
      rw [hRe]
      have hle : z.re * (T - ℓ x) ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg hzRe (by linarith [hx hfx])
      exact mul_le_of_le_one_right (norm_nonneg _) (Real.exp_le_one_iff.mpr hle)

/-- Strict support below the boundary forces decay along the negative real axis. -/
theorem titchmarshLaplaceIntegral_tendsto_neg_real {d : ℕ}
    {f : Euclidean d → ℂ} (hf : Integrable f)
    (ℓ : Euclidean d →L[ℝ] ℝ) (T : ℝ)
    (hstrict : ∀ᵐ x, f x ≠ 0 → ℓ x < T) :
    Tendsto (fun t : ℝ => titchmarshLaplaceIntegral f ℓ T (-(t : ℂ)))
      Filter.atTop (nhds 0) := by
  have hpoint : ∀ᵐ x, Tendsto
      (fun t : ℝ => f x * Complex.exp (-(t : ℂ) * ((T - ℓ x : ℝ) : ℂ)))
      atTop (nhds 0) := by
    filter_upwards [hstrict] with x hx
    by_cases hfx : f x = 0
    · simp [hfx]
    · have hpos : 0 < T - ℓ x := sub_pos.mpr (hx hfx)
      have hreal : Tendsto (fun t : ℝ => Real.exp (-t * (T - ℓ x))) atTop (nhds 0) := by
        have hlin : Tendsto (fun t : ℝ => t * (T - ℓ x)) atTop atTop :=
          tendsto_id.atTop_mul_const hpos
        convert Real.tendsto_exp_neg_atTop_nhds_zero.comp hlin using 1
        ext t
        congr 1
        ring
      have hc : Tendsto (fun t : ℝ => Complex.exp (-(t : ℂ) * ↑(T - ℓ x)))
          atTop (nhds 0) := by
        have heq : (fun t : ℝ => Complex.exp (-(t : ℂ) * ↑(T - ℓ x))) =
            fun t => (Complex.ofReal (Real.exp (-t * (T - ℓ x)))) := by
          funext t
          calc
            Complex.exp (-(t : ℂ) * ↑(T - ℓ x)) =
                Complex.exp ((-t * (T - ℓ x) : ℝ) : ℂ) := by congr 1; push_cast; ring
            _ = Complex.ofReal (Real.exp (-t * (T - ℓ x))) := by rw [← Complex.ofReal_exp]
        have hcont := (Complex.continuous_ofReal.tendsto 0).comp hreal
        convert hcont using 1
      simpa [mul_comm] using hc.const_mul (f x)
  have hdom : ∀ᶠ t : ℝ in atTop, ∀ᵐ x,
      ‖f x * Complex.exp (-(t : ℂ) * ↑(T - ℓ x))‖ ≤ ‖f x‖ := by
    filter_upwards [eventually_atTop.2 ⟨0, fun t ht => ht⟩] with t ht
    filter_upwards [hstrict] with x hx
    rw [norm_mul, Complex.norm_exp]
    have hRe : (-(t : ℂ) * ↑(T - ℓ x)).re = -t * (T - ℓ x) := by simp [Complex.mul_re]
    rw [hRe]
    by_cases hfx : f x = 0
    · simp [hfx]
    · have hpos : 0 ≤ T - ℓ x := sub_nonneg.mpr (le_of_lt (hx hfx))
      exact mul_le_of_le_one_right (norm_nonneg _)
        (Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ht) hpos))
  have hmeas (t : ℝ) : AEStronglyMeasurable
      (fun x => f x * Complex.exp (-(t : ℂ) * ↑(T - ℓ x))) := by
    exact hf.aestronglyMeasurable.mul
      ((Complex.continuous_exp.comp
        (continuous_const.mul (Complex.continuous_ofReal.comp
          (continuous_const.sub ℓ.continuous)))).aestronglyMeasurable)
  have hlim : ∀ᵐ x, Tendsto
      (fun t : ℝ => f x * Complex.exp (-(t : ℂ) * ↑(T - ℓ x))) atTop (nhds (0 : ℂ)) := hpoint
  have h := tendsto_integral_filter_of_dominated_convergence (fun x => ‖f x‖)
    (Filter.Eventually.of_forall hmeas) hdom hf.norm hlim
  simpa [titchmarshLaplaceIntegral] using h

end RieszEuclidean.CompleteMinimal
