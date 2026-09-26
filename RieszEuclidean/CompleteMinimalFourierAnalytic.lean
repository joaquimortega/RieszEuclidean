import RieszEuclidean.CompleteMinimalEntireFourier
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.Normed.Algebra.Exponential

/-! Multivariate analytic power series for bounded-support Fourier integrals. -/

noncomputable section
open MeasureTheory Filter Topology
open scoped BigOperators ENNReal

namespace RieszEuclidean.CompleteMinimal

/-- The multilinear product of `n` copies of the Fourier phase. -/
def fourierPhasePower {d : ℕ} (n : ℕ) (x : Euclidean d) :
    ContinuousMultilinearMap ℂ (fun _ : Fin n => ComplexEuclidean d) ℂ :=
  (ContinuousMultilinearMap.mkPiAlgebra ℂ (Fin n) ℂ).compContinuousLinearMap
    (fun _ => fourierPhaseCLM x)

@[simp] theorem fourierPhasePower_apply {d n : ℕ} (x : Euclidean d)
    (v : Fin n → ComplexEuclidean d) :
    fourierPhasePower n x v = ∏ j, fourierPhaseCLM x (v j) := rfl

theorem fourierPhasePower_norm_le {d : ℕ} (n : ℕ) (x : Euclidean d) :
    ‖fourierPhasePower n x‖ ≤ (2 * Real.pi * d * ‖x‖) ^ n := by
  calc
    ‖fourierPhasePower n x‖ ≤
        ‖ContinuousMultilinearMap.mkPiAlgebra ℂ (Fin n) ℂ‖ *
          ∏ _j : Fin n, ‖fourierPhaseCLM x‖ :=
      ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
    _ = ‖fourierPhaseCLM x‖ ^ n := by simp
    _ ≤ _ := pow_le_pow_left₀ (norm_nonneg _) (fourierPhaseCLM_norm_le x) n

theorem fourierPhasePower_continuous {d : ℕ} (n : ℕ) :
    Continuous (fourierPhasePower (d := d) n) := by
  let C := ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear ℂ
    (fun _ : Fin n => ComplexEuclidean d) (fun _ : Fin n => ℂ) ℂ
  have h : Continuous (fun x : Euclidean d => C (fun _ => fourierPhaseCLM x)) :=
    C.cont.comp (continuous_pi (fun _ => fourierPhaseCLM_continuous))
  exact h.clm_apply continuous_const

/-- The integrand defining a Taylor coefficient of the Fourier transform at zero. -/
def fourierTaylorIntegrand {d : ℕ} (f : Euclidean d → ℂ) (n : ℕ) (x : Euclidean d) :
    ContinuousMultilinearMap ℂ (fun _ : Fin n => ComplexEuclidean d) ℂ :=
  ((n.factorial : ℂ)⁻¹ * f x) • fourierPhasePower n x

theorem fourierTaylorIntegrand_bound {d : ℕ} {f : Euclidean d → ℂ} {R : ℝ}
    (hsupp : ∀ᵐ x, f x ≠ 0 → ‖x‖ ≤ R) (n : ℕ) :
    ∀ᵐ x, ‖fourierTaylorIntegrand f n x‖ ≤
      ‖f x‖ * ((2 * Real.pi * d * R) ^ n / n.factorial) := by
  classical
  filter_upwards [hsupp] with x hx
  by_cases hfx : f x = 0
  · rw [fourierTaylorIntegrand, hfx, mul_zero, zero_smul ℂ (fourierPhasePower n x),
      norm_zero, norm_zero, zero_mul]
  · have hpow : (2 * Real.pi * d * ‖x‖) ^ n ≤ (2 * Real.pi * d * R) ^ n := by
      gcongr
      exact hx hfx
    have hnorm := (fourierPhasePower_norm_le n x).trans hpow
    rw [fourierTaylorIntegrand,
      norm_smul ((n.factorial : ℂ)⁻¹ * f x) (fourierPhasePower n x),
      norm_mul, norm_inv, Complex.norm_natCast]
    calc
      (↑n.factorial)⁻¹ * ‖f x‖ * ‖fourierPhasePower n x‖ ≤
          (↑n.factorial)⁻¹ * ‖f x‖ * (2 * Real.pi * d * R) ^ n := by gcongr
      _ = _ := by ring

private theorem integrable_smul_of_dominated {α E : Type*} [MeasurableSpace α]
    [TopologicalSpace α] [OpensMeasurableSpace α] [SecondCountableTopology α]
    [NormedAddCommGroup E] [SMul ℂ E] [ContinuousSMul ℂ E] {μ : Measure α}
    {a : α → ℂ} {p : α → E} {b : α → ℝ}
    (ha : AEStronglyMeasurable a μ) (hp : Continuous p)
    (hb : Integrable b μ) (hbound : ∀ᵐ x ∂μ, ‖a x • p x‖ ≤ b x) :
    Integrable (fun x => a x • p x) μ :=
  hb.mono' (ha.smul hp.aestronglyMeasurable) hbound

theorem fourierTaylorIntegrand_integrable {d : ℕ} {f : Euclidean d → ℂ} {R : ℝ}
    (hf : Integrable f)
    (hsupp : ∀ᵐ x, f x ≠ 0 → ‖x‖ ≤ R) (n : ℕ) :
    Integrable (fourierTaylorIntegrand f n) := by
  exact integrable_smul_of_dominated
    (a := fun x => (n.factorial : ℂ)⁻¹ * f x)
    (p := fourierPhasePower (d := d) n)
    (b := fun x => ‖f x‖ * ((2 * Real.pi * d * R) ^ n / n.factorial))
    (aestronglyMeasurable_const.mul hf.aestronglyMeasurable)
    (fourierPhasePower_continuous n)
    (hf.norm.mul_const ((2 * Real.pi * d * R) ^ n / n.factorial))
    (fourierTaylorIntegrand_bound hsupp n)

/-- Actual integral coefficients of the Fourier power series at zero. -/
def fourierTaylorSeries {d : ℕ} (f : Euclidean d → ℂ) :
    FormalMultilinearSeries ℂ (ComplexEuclidean d) ℂ :=
  fun n => ∫ x, fourierTaylorIntegrand f n x

theorem fourierTaylorSeries_norm_le {d : ℕ} {f : Euclidean d → ℂ} {R : ℝ}
    (hf : Integrable f)
    (hsupp : ∀ᵐ x, f x ≠ 0 → ‖x‖ ≤ R) (n : ℕ) :
    ‖fourierTaylorSeries f n‖ ≤
      (∫ x, ‖f x‖) * ((2 * Real.pi * d * R) ^ n / n.factorial) := by
  apply (norm_integral_le_integral_norm _).trans
  calc
    (∫ x, ‖fourierTaylorIntegrand f n x‖) ≤
        ∫ x, ‖f x‖ * ((2 * Real.pi * d * R) ^ n / n.factorial) :=
      integral_mono_ae (fourierTaylorIntegrand_integrable hf hsupp n).norm
        (hf.norm.mul_const _) (fourierTaylorIntegrand_bound hsupp n)
    _ = _ := integral_mul_const _ _

theorem fourierTaylorSeries_radius_pos {d : ℕ} {f : Euclidean d → ℂ} {R : ℝ}
    (hf : Integrable f) (hR : 0 ≤ R)
    (hsupp : ∀ᵐ x, f x ≠ 0 → ‖x‖ ≤ R) :
    (1 : ℝ≥0∞) ≤ (fourierTaylorSeries f).radius := by
  apply (fourierTaylorSeries f).le_radius_of_bound
    ((∫ x, ‖f x‖) * Real.exp (2 * Real.pi * d * R)) (r := 1)
  intro n
  simp only [NNReal.coe_one, one_pow, mul_one]
  apply (fourierTaylorSeries_norm_le hf hsupp n).trans
  exact mul_le_mul_of_nonneg_left (Real.pow_div_factorial_le_exp _ (by positivity) n)
    (integral_nonneg (fun x => norm_nonneg _))

theorem fourierTaylorSeries_diagonal {d : ℕ} {f : Euclidean d → ℂ} {R : ℝ}
    (hf : Integrable f) (hsupp : ∀ᵐ x, f x ≠ 0 → ‖x‖ ≤ R)
    (n : ℕ) (y : ComplexEuclidean d) :
    fourierTaylorSeries f n (fun _ => y) =
      ∫ x, f x * (fourierPhaseCLM x y) ^ n / (n.factorial : ℂ) := by
  rw [fourierTaylorSeries, ContinuousMultilinearMap.integral_apply
    (fourierTaylorIntegrand_integrable hf hsupp n)]
  apply integral_congr_ae
  filter_upwards with x
  simp only [fourierTaylorIntegrand, ContinuousMultilinearMap.smul_apply,
    fourierPhasePower_apply, Finset.prod_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  ring

theorem fourierTaylorSeries_hasSum {d : ℕ} {f : Euclidean d → ℂ} {R : ℝ}
    (hf : Integrable f)
    (hsupp : ∀ᵐ x, f x ≠ 0 → ‖x‖ ≤ R) (y : ComplexEuclidean d) :
    HasSum (fun n => fourierTaylorSeries f n (fun _ => y)) (entireFourier f y) := by
  let T := 2 * Real.pi * d * R * ‖y‖
  let F := fun (n : ℕ) (x : Euclidean d) =>
    f x * (fourierPhaseCLM x y) ^ n / (n.factorial : ℂ)
  let B := fun (n : ℕ) (x : Euclidean d) => ‖f x‖ * (T ^ n / n.factorial)
  have hmeas : ∀ n, AEStronglyMeasurable (F n) volume := by
    intro n
    have hm : AEStronglyMeasurable
        (fun x => (f x * (fourierPhaseCLM x y) ^ n) * (n.factorial : ℂ)⁻¹) volume :=
      (hf.aestronglyMeasurable.mul
        ((fourierPhaseCLM_continuous.clm_apply continuous_const).pow n).aestronglyMeasurable).mul
          aestronglyMeasurable_const
    simpa only [F, div_eq_mul_inv] using hm
  have hbound : ∀ n, ∀ᵐ x, ‖F n x‖ ≤ B n x := by
    intro n
    filter_upwards [hsupp] with x hx
    by_cases hfx : f x = 0
    · simp [F, B, hfx]
    · have hphase : ‖fourierPhaseCLM x y‖ ≤ T := by
        apply (ContinuousLinearMap.le_opNorm _ _).trans
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg y)
        apply (fourierPhaseCLM_norm_le x).trans
        exact mul_le_mul_of_nonneg_left (hx hfx) (by positivity)
      dsimp [F, B]
      simp only [norm_div, norm_mul, norm_pow, Complex.norm_natCast]
      rw [mul_div_assoc]
      exact mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hphase n)
          (by positivity)) (norm_nonneg _)
  have hsumB (x : Euclidean d) : HasSum (fun n => B n x) (‖f x‖ * Real.exp T) := by
    simpa only [B, ← Real.exp_eq_exp_ℝ] using
      (NormedSpace.expSeries_div_hasSum_exp ℝ T).mul_left ‖f x‖
  have hint : Integrable (fun x => ∑' n, B n x) := by
    have he : (fun x => ∑' n, B n x) = fun x => ‖f x‖ * Real.exp T :=
      funext (fun x => (hsumB x).tsum_eq)
    rw [he]
    exact hf.norm.mul_const _
  have hlim : ∀ᵐ x, HasSum (fun n => F n x) (f x * complexFourierKernel x y) := by
    filter_upwards with x
    simpa only [F, mul_div_assoc, complexFourierKernel, ← Complex.exp_eq_exp_ℂ] using
      (NormedSpace.expSeries_div_hasSum_exp ℂ (fourierPhaseCLM x y)).mul_left (f x)
  have h := hasSum_integral_of_dominated_convergence B hmeas hbound
    (Filter.Eventually.of_forall (fun x => (hsumB x).summable)) hint hlim
  simpa only [fourierTaylorSeries_diagonal hf hsupp, entireFourier, F] using h

/-- The Fourier integral has a genuine multivariate analytic expansion at zero. -/
theorem entireFourier_hasFPowerSeries_zero {d : ℕ} {f : Euclidean d → ℂ} {R : ℝ}
    (hf : Integrable f) (hR : 0 ≤ R) (hsupp : ∀ᵐ x, f x ≠ 0 → ‖x‖ ≤ R) :
    HasFPowerSeriesOnBall (entireFourier f) (fourierTaylorSeries f) 0 1 := by
  refine ⟨fourierTaylorSeries_radius_pos hf hR hsupp, zero_lt_one, ?_⟩
  intro y _
  simpa only [zero_add] using fourierTaylorSeries_hasSum hf hsupp y

/-- Compact support gives multivariate analyticity, with no holomorphy-to-analyticity assumption. -/
theorem entireFourier_analyticAt {d : ℕ} {f : Euclidean d → ℂ} {R : ℝ}
    (hf : Integrable f) (hR : 0 ≤ R) (hsupp : ∀ᵐ x, f x ≠ 0 → ‖x‖ ≤ R)
    (z : ComplexEuclidean d) : AnalyticAt ℂ (entireFourier f) z := by
  let g := fun x => f x * complexFourierKernel x z
  have hg : Integrable g := entireFourier_integrable hf hsupp z
  have hgSupp : ∀ᵐ x, g x ≠ 0 → ‖x‖ ≤ R := by
    filter_upwards [hsupp] with x hx hgx
    apply hx
    intro hfx
    exact hgx (by simp [g, hfx])
  refine ⟨fourierTaylorSeries g, 1, fourierTaylorSeries_radius_pos hg hR hgSupp,
    zero_lt_one, ?_⟩
  intro y _
  have h := fourierTaylorSeries_hasSum hg hgSupp y
  convert h using 1
  unfold entireFourier
  apply integral_congr_ae
  filter_upwards with x
  simp [g, complexFourierKernel, map_add, Complex.exp_add, mul_assoc]

theorem entireFourier_analyticOnNhd {d : ℕ} {f : Euclidean d → ℂ} {R : ℝ}
    (hf : Integrable f) (hR : 0 ≤ R) (hsupp : ∀ᵐ x, f x ≠ 0 → ‖x‖ ≤ R) :
    AnalyticOnNhd ℂ (entireFourier f) Set.univ :=
  fun z _ => entireFourier_analyticAt hf hR hsupp z

end RieszEuclidean.CompleteMinimal
