import RieszEuclidean.Affine
import RieszEuclidean.FejerWeights
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Complex.RealDeriv
open MeasureTheory Set
namespace RieszEuclidean
/-- The unit-speed complex exponential is Lipschitz with constant one. -/
theorem norm_exp_mul_I_sub_le (a b : ℝ) :
    ‖Complex.exp (a * Complex.I) - Complex.exp (b * Complex.I)‖ ≤ |a - b| := by
  have hd (t : ℝ) : HasDerivAt (fun r : ℝ => Complex.exp (r * Complex.I))
      (Complex.exp (t * Complex.I) * Complex.I) t := by
    convert ((hasDerivAt_id t).ofReal_comp.mul_const Complex.I).cexp using 1
    simp
  have h := (convex_univ : Convex ℝ (univ : Set ℝ)).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun t _ => (hd t).hasDerivWithinAt) (C := 1)
    (fun t _ => by simp [norm_mul, Complex.norm_exp, Complex.mul_re])
    (mem_univ b) (mem_univ a)
  simpa using h
/-- Euclidean characters vary with Lipschitz constant `2π‖y‖` in frequency. -/
theorem norm_exponential_sub_le (t s y : Euclidean d) :
    ‖exponential t y - exponential s y‖ ≤ 2 * Real.pi * ‖t - s‖ * ‖y‖ := by
  have h := norm_exp_mul_I_sub_le (2 * Real.pi * inner (𝕜 := ℝ) t y)
    (2 * Real.pi * inner (𝕜 := ℝ) s y)
  have he (v : Euclidean d) : exponential v y =
      Complex.exp ((2 * Real.pi * inner (𝕜 := ℝ) v y : ℝ) * Complex.I) := by
    unfold exponential
    congr 1
    push_cast
    ring
  rw [he, he]
  calc
    _ ≤ |2 * Real.pi * inner (𝕜 := ℝ) t y - 2 * Real.pi * inner (𝕜 := ℝ) s y| := h
    _ = (2 * Real.pi) * |inner (𝕜 := ℝ) (t - s) y| := by
      rw [inner_sub_left, ← mul_sub, abs_mul, abs_of_nonneg (by positivity : 0 ≤ 2 * Real.pi)]
    _ ≤ _ := by
      have hi := abs_real_inner_le_norm (t - s) y
      nlinarith [Real.pi_pos]
variable {d : ℕ} {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
/-- The actual modulated integral of an operator-vector kernel. -/
noncomputable def modulatedOperatorValue (A : Euclidean d → H →L[ℂ] H)
    (t : Euclidean d) (f : H) : H := ∫ y, exponential t y • A y f
/-- An integrable operator-norm envelope makes every modulated orbit integrable. -/
theorem integrable_modulatedOperator (A : Euclidean d → H →L[ℂ] H)
    (hA : ∀ f, AEStronglyMeasurable (fun y => A y f) volume)
    {C : Euclidean d → ℝ} (hC : Integrable C) (hbound : ∀ y, ‖A y‖ ≤ C y)
    (t : Euclidean d) (f : H) : Integrable (fun y => exponential t y • A y f) := by
  apply (hC.mul_const ‖f‖).mono'
    ((show Continuous (exponential t) by unfold exponential; fun_prop).aestronglyMeasurable.smul (hA f))
  exact Filter.Eventually.of_forall fun y => by
    rw [norm_smul, exponential_norm, one_mul]
    exact (A y).le_opNorm f |>.trans (mul_le_mul_of_nonneg_right (hbound y) (norm_nonneg f))
/-- The envelope gives the vector norm bound. -/
theorem norm_modulatedOperatorValue_le (A : Euclidean d → H →L[ℂ] H)
    {C : Euclidean d → ℝ} (hC : Integrable C) (hbound : ∀ y, ‖A y‖ ≤ C y)
    (t : Euclidean d) (f : H) :
    ‖modulatedOperatorValue A t f‖ ≤ (∫ y, C y) * ‖f‖ := by
  rw [← integral_mul_const]
  apply norm_integral_le_of_norm_le (hC.mul_const ‖f‖)
  exact Filter.Eventually.of_forall fun y => by
    rw [norm_smul, exponential_norm, one_mul]
    exact (A y).le_opNorm f |>.trans (mul_le_mul_of_nonneg_right (hbound y) (norm_nonneg f))
/-- Integration of the operator-vector kernel is complex linear. -/
noncomputable def modulatedOperatorLinear (A : Euclidean d → H →L[ℂ] H)
    (hA : ∀ f, AEStronglyMeasurable (fun y => A y f) volume)
    {C : Euclidean d → ℝ} (hC : Integrable C) (hbound : ∀ y, ‖A y‖ ≤ C y)
    (t : Euclidean d) : H →ₗ[ℂ] H where
  toFun := modulatedOperatorValue A t
  map_add' f g := by
    simp only [modulatedOperatorValue, map_add, smul_add]
    exact integral_add (integrable_modulatedOperator A hA hC hbound t f)
      (integrable_modulatedOperator A hA hC hbound t g)
  map_smul' c f := by
    simp only [modulatedOperatorValue, map_smul, RingHom.id_apply]
    simp_rw [smul_comm (exponential t _) c]
    exact integral_smul c _
/-- The modulated integral defines a bounded complex-linear operator. -/
noncomputable def modulatedOperator (A : Euclidean d → H →L[ℂ] H)
    (hA : ∀ f, AEStronglyMeasurable (fun y => A y f) volume)
    {C : Euclidean d → ℝ} (hC : Integrable C) (hbound : ∀ y, ‖A y‖ ≤ C y)
    (t : Euclidean d) : H →L[ℂ] H :=
  (modulatedOperatorLinear A hA hC hbound t).mkContinuous (∫ y, C y)
    (norm_modulatedOperatorValue_le A hC hbound t)
/-- Evaluation is the actual vector-valued integral. -/
theorem modulatedOperator_apply (A : Euclidean d → H →L[ℂ] H)
    (hA : ∀ f, AEStronglyMeasurable (fun y => A y f) volume)
    {C : Euclidean d → ℝ} (hC : Integrable C) (hbound : ∀ y, ‖A y‖ ≤ C y)
    (t : Euclidean d) (f : H) :
    modulatedOperator A hA hC hbound t f = ∫ y, exponential t y • A y f := rfl
/-- The operator norm is bounded by the integral of its envelope. -/
theorem norm_modulatedOperator_le (A : Euclidean d → H →L[ℂ] H)
    (hA : ∀ f, AEStronglyMeasurable (fun y => A y f) volume)
    {C : Euclidean d → ℝ} (hC : Integrable C) (hbound : ∀ y, ‖A y‖ ≤ C y)
    (t : Euclidean d) : ‖modulatedOperator A hA hC hbound t‖ ≤ ∫ y, C y := by
  apply ContinuousLinearMap.opNorm_le_bound _ (integral_nonneg (fun y =>
    (norm_nonneg (A y)).trans (hbound y)))
  exact norm_modulatedOperatorValue_le A hC hbound t
/-- An integrable first moment gives the quantitative frequency Lipschitz bound. -/
theorem norm_modulatedOperator_sub_le (A : Euclidean d → H →L[ℂ] H)
    (hA : ∀ f, AEStronglyMeasurable (fun y => A y f) volume)
    {C : Euclidean d → ℝ} (hC : Integrable C) (hbound : ∀ y, ‖A y‖ ≤ C y)
    (hmoment : Integrable (fun y => ‖y‖ * C y)) (t s : Euclidean d) :
    ‖modulatedOperator A hA hC hbound t - modulatedOperator A hA hC hbound s‖ ≤
      (2 * Real.pi * ∫ y, ‖y‖ * C y) * ‖t - s‖ := by
  have hCpos (y) : 0 ≤ C y := (norm_nonneg (A y)).trans (hbound y)
  have hmpos : 0 ≤ ∫ y, ‖y‖ * C y :=
    integral_nonneg (fun y => mul_nonneg (norm_nonneg y) (hCpos y))
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro f
  change ‖(∫ y, exponential t y • A y f) - ∫ y, exponential s y • A y f‖ ≤ _
  rw [← integral_sub (integrable_modulatedOperator A hA hC hbound t f)
    (integrable_modulatedOperator A hA hC hbound s f)]
  have hb : Integrable (fun y => (2 * Real.pi * ‖t - s‖ * ‖f‖) * (‖y‖ * C y)) :=
    hmoment.const_mul _
  calc
    _ ≤ ∫ y, (2 * Real.pi * ‖t - s‖ * ‖f‖) * (‖y‖ * C y) := by
      apply norm_integral_le_of_norm_le hb
      exact Filter.Eventually.of_forall fun y => by
        rw [← sub_smul, norm_smul]
        calc
          _ ≤ (2 * Real.pi * ‖t - s‖ * ‖y‖) * (C y * ‖f‖) :=
            mul_le_mul (norm_exponential_sub_le t s y)
              ((A y).le_opNorm f |>.trans (mul_le_mul_of_nonneg_right (hbound y) (norm_nonneg f)))
              (norm_nonneg _) (by positivity)
          _ = _ := by ring
    _ = _ := by rw [integral_const_mul]; ring
/-- The actual operator kernel after finite Fejér averaging. -/
noncomputable def fejerOperatorKernel (A : Euclidean d → H →L[ℂ] H) (R : ℝ)
    (y : Euclidean d) : H →L[ℂ] H := (fejerWeight R y : ℂ) • A y
/-- Fejér averaging preserves per-vector strong measurability. -/
theorem aestronglyMeasurable_fejerOperatorKernel (A : Euclidean d → H →L[ℂ] H)
    (hA : ∀ f, AEStronglyMeasurable (fun y => A y f) volume) (R : ℝ) (f : H) :
    AEStronglyMeasurable (fun y => fejerOperatorKernel A R y f) volume :=
  ((Complex.continuous_ofReal.comp (continuous_fejerWeight R)).aestronglyMeasurable).smul (hA f)
/-- The original envelope also bounds every positive-radius averaged operator kernel. -/
theorem norm_fejerOperatorKernel_le (A : Euclidean d → H →L[ℂ] H)
    {C : Euclidean d → ℝ} (hbound : ∀ y, ‖A y‖ ≤ C y) {R : ℝ} (hR : 0 < R)
    (y : Euclidean d) : ‖fejerOperatorKernel A R y‖ ≤ C y := by
  calc
    _ ≤ ‖(fejerWeight R y : ℂ)‖ * ‖A y‖ := norm_smul_le _ _
    _ ≤ C y := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (fejerWeight_nonneg R y)]
      exact (mul_le_of_le_one_left (norm_nonneg (A y)) (fejerWeight_le_one hR y)).trans (hbound y)
/-- The finite Fejér average of the modulated operator. -/
noncomputable def fejerModulatedOperator (A : Euclidean d → H →L[ℂ] H)
    (hA : ∀ f, AEStronglyMeasurable (fun y => A y f) volume)
    {C : Euclidean d → ℝ} (hC : Integrable C) (hbound : ∀ y, ‖A y‖ ≤ C y)
    (t : Euclidean d) (R : ℝ) : H →L[ℂ] H :=
  if hR : 0 < R then modulatedOperator (fejerOperatorKernel A R)
    (aestronglyMeasurable_fejerOperatorKernel A hA R) hC
    (norm_fejerOperatorKernel_le A hbound hR) t else 0
/-- At every positive radius the average is exactly the weighted vector integral. -/
theorem fejerModulatedOperator_apply (A : Euclidean d → H →L[ℂ] H)
    (hA : ∀ f, AEStronglyMeasurable (fun y => A y f) volume)
    {C : Euclidean d → ℝ} (hC : Integrable C) (hbound : ∀ y, ‖A y‖ ≤ C y)
    (t : Euclidean d) {R : ℝ} (hR : 0 < R) (f : H) :
    fejerModulatedOperator A hA hC hbound t R f =
      ∫ y, ((fejerWeight R y : ℂ) * exponential t y) • A y f := by
  simp only [fejerModulatedOperator, dif_pos hR, modulatedOperator_apply, fejerOperatorKernel,
    ContinuousLinearMap.smul_apply, ← mul_smul, mul_comm]
/-- The Fejér approximation error has an envelope bound independent of the modulation. -/
theorem norm_fejerModulatedOperator_sub_le (A : Euclidean d → H →L[ℂ] H)
    (hA : ∀ f, AEStronglyMeasurable (fun y => A y f) volume)
    {C : Euclidean d → ℝ} (hC : Integrable C) (hbound : ∀ y, ‖A y‖ ≤ C y)
    (t : Euclidean d) {R : ℝ} (hR : 0 < R) :
    ‖fejerModulatedOperator A hA hC hbound t R - modulatedOperator A hA hC hbound t‖ ≤
      ∫ y, |fejerWeight R y - 1| * C y := by
  have hCpos y : 0 ≤ C y := (norm_nonneg (A y)).trans (hbound y)
  have he : (fun y => |fejerWeight R y - 1| * C y) =
      fun y => C y - fejerWeight R y • C y := by
    funext y
    rw [abs_of_nonpos (sub_nonpos.mpr (fejerWeight_le_one hR y))]
    simp only [smul_eq_mul]
    ring
  have hi : Integrable (fun y => |fejerWeight R y - 1| * C y) := by
    rw [he]
    exact hC.sub (integrable_fejerWeight_smul hC hR)
  apply ContinuousLinearMap.opNorm_le_bound _ (integral_nonneg fun y =>
    mul_nonneg (abs_nonneg _) (hCpos y))
  intro f
  change ‖fejerModulatedOperator A hA hC hbound t R f - modulatedOperator A hA hC hbound t f‖ ≤ _
  rw [fejerModulatedOperator, dif_pos hR, modulatedOperator_apply, modulatedOperator_apply,
    ← integral_sub (integrable_modulatedOperator _
      (aestronglyMeasurable_fejerOperatorKernel A hA R) hC
      (norm_fejerOperatorKernel_le A hbound hR) t f)
      (integrable_modulatedOperator A hA hC hbound t f), ← integral_mul_const]
  apply norm_integral_le_of_norm_le (hi.mul_const ‖f‖)
  exact Filter.Eventually.of_forall fun y => by
    change ‖exponential t y • ((fejerWeight R y : ℂ) • A y f) - exponential t y • A y f‖ ≤ _
    rw [← smul_sub, norm_smul, exponential_norm, one_mul]
    have heq : (fejerWeight R y : ℂ) • A y f - A y f =
        ((fejerWeight R y : ℂ) - 1) • A y f := by rw [sub_smul, one_smul]
    rw [heq, norm_smul, ← Complex.ofReal_one, ← Complex.ofReal_sub,
      Complex.norm_real, Real.norm_eq_abs]
    calc
      _ ≤ |fejerWeight R y - 1| * (C y * ‖f‖) :=
        mul_le_mul_of_nonneg_left ((A y).le_opNorm f |>.trans
          (mul_le_mul_of_nonneg_right (hbound y) (norm_nonneg f))) (abs_nonneg _)
      _ = _ := by ring
/-- The common Fejér approximation-error bound tends to zero. -/
theorem tendsto_fejer_envelope_error {C : Euclidean d → ℝ} (hC : Integrable C)
    (hCpos : ∀ y, 0 ≤ C y) :
    Filter.Tendsto (fun R : ℝ => ∫ y, |fejerWeight R y - 1| * C y)
      Filter.atTop (nhds 0) := by
  have h := tendsto_integral_norm_fejerWeight_smul_sub hC
  convert h using 1
  funext R
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun y => by
    change |fejerWeight R y - 1| * C y = ‖fejerWeight R y • C y - C y‖
    rw [Real.norm_eq_abs]
    simp only [smul_eq_mul]
    have heq : fejerWeight R y * C y - C y = (fejerWeight R y - 1) * C y := by ring
    rw [heq, abs_mul, abs_of_nonneg (hCpos y)]
/-- Finite Fejér averages converge in operator norm, even along arbitrary varying modulations. -/
theorem tendsto_fejerModulatedOperator_error (A : Euclidean d → H →L[ℂ] H)
    (hA : ∀ f, AEStronglyMeasurable (fun y => A y f) volume)
    {C : Euclidean d → ℝ} (hC : Integrable C) (hbound : ∀ y, ‖A y‖ ≤ C y)
    (t : ℝ → Euclidean d) :
    Filter.Tendsto (fun R : ℝ =>
      ‖fejerModulatedOperator A hA hC hbound (t R) R - modulatedOperator A hA hC hbound (t R)‖)
      Filter.atTop (nhds 0) := by
  apply squeeze_zero' (Filter.Eventually.of_forall fun R => norm_nonneg _) ?_
    (tendsto_fejer_envelope_error hC fun y => (norm_nonneg (A y)).trans (hbound y))
  filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with R hR
  exact norm_fejerModulatedOperator_sub_le A hA hC hbound (t R) hR
end RieszEuclidean
