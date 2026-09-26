import RieszEuclidean.CompleteMinimalEntireFourier
import RieszEuclidean.CompleteMinimalPoisson
import Mathlib.Analysis.SpecialFunctions.Log.PosLog
import Mathlib.Analysis.Analytic.IsolatedZeros

/-!
# Exponential growth and reduction of entire division to complex lines

The entire-division theorem `cm:lem:type` follows from uniform estimates on
complex lines. The Jensen and Poisson inequalities used in the proof are proved
in `CompleteMinimalJensen` and `CompleteMinimalPoisson`.
-/

noncomputable section

open MeasureTheory Metric
open scoped Interval

namespace RieszEuclidean.CompleteMinimal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- A genuine global exponential growth bound, including the compact remainder. -/
def FiniteExponentialType (f : E → ℂ) : Prop :=
  ∃ C R : ℝ, 0 < C ∧ 0 ≤ R ∧ ∀ z : E, ‖f z‖ ≤ C * Real.exp (R * ‖z‖)

omit [NormedSpace ℂ E] in
/-- Allowing a zero leading constant does not change the growth class. -/
theorem finiteExponentialType_of_nonnegative_bound {f : E → ℂ} {C R : ℝ}
    (hC : 0 ≤ C) (hR : 0 ≤ R)
    (hbound : ∀ z : E, ‖f z‖ ≤ C * Real.exp (R * ‖z‖)) :
    FiniteExponentialType f := by
  refine ⟨C + 1, R, by positivity, hR, ?_⟩
  intro z
  exact (hbound z).trans
    (mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le)

omit [NormedSpace ℂ E] in
/-- Products of functions of finite exponential type have finite exponential type. -/
theorem FiniteExponentialType.mul {f g : E → ℂ}
    (hf : FiniteExponentialType f) (hg : FiniteExponentialType g) :
    FiniteExponentialType (fun z => f z * g z) := by
  obtain ⟨C, R, hC, hR, hfb⟩ := hf
  obtain ⟨D, S, hD, hS, hgb⟩ := hg
  refine ⟨C * D, R + S, mul_pos hC hD, add_nonneg hR hS, ?_⟩
  intro z
  rw [norm_mul]
  calc
    ‖f z‖ * ‖g z‖ ≤ (C * Real.exp (R * ‖z‖)) * (D * Real.exp (S * ‖z‖)) :=
      mul_le_mul (hfb z) (hgb z) (norm_nonneg _) (by positivity)
    _ = (C * D) * Real.exp ((R + S) * ‖z‖) := by rw [add_mul, Real.exp_add]; ring

/-- The bounded-domain Fourier estimates already proved in this development
belong to the genuine global exponential-type class. -/
theorem finiteExponentialType_domainEntireFourier {d : ℕ} {Ω : Set (Euclidean d)}
    (hΩ : MeasurableSet Ω) (hbounded : Bornology.IsBounded Ω) (f : DomainL2 Ω) :
    FiniteExponentialType (domainEntireFourier Ω hΩ f) := by
  obtain ⟨C, R, hC, hR, hbound⟩ := domainEntireFourier_finite_exponential_type hΩ hbounded f
  exact finiteExponentialType_of_nonnegative_bound hC hR hbound

/-- Restriction to a complex line through the origin. -/
def complexLineRestriction (f : E → ℂ) (u : E) : ℂ → ℂ := fun w => f (w • u)

theorem differentiable_complexLineRestriction {f : E → ℂ}
    (hf : Differentiable ℂ f) (u : E) : Differentiable ℂ (complexLineRestriction f u) :=
  hf.comp ((ContinuousLinearMap.id ℂ ℂ).smulRight u).differentiable

/-- One global bound restricts uniformly to every line of unit direction. -/
theorem finiteExponentialType_uniform_line_bound {f : E → ℂ}
    (hf : FiniteExponentialType f) :
    ∃ C R : ℝ, 0 < C ∧ 0 ≤ R ∧ ∀ u : E, ‖u‖ ≤ 1 →
      ∀ w : ℂ, ‖complexLineRestriction f u w‖ ≤ C * Real.exp (R * ‖w‖) := by
  obtain ⟨C, R, hC, hR, hbound⟩ := hf
  refine ⟨C, R, hC, hR, ?_⟩
  intro u hu w
  apply (hbound (w • u)).trans
  apply mul_le_mul_of_nonneg_left _ hC.le
  apply Real.exp_le_exp.mpr
  rw [norm_smul]
  apply mul_le_mul_of_nonneg_left _ hR
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hu (norm_nonneg w)

/-- Conversely, uniform bounds on all complex lines give a global bound. The
zero direction includes the origin and avoids a positive-dimension assumption. -/
theorem finiteExponentialType_of_uniform_line_bound {f : E → ℂ}
    {C R : ℝ} (hC : 0 < C) (hR : 0 ≤ R)
    (hbound : ∀ u : E, ‖u‖ ≤ 1 → ∀ w : ℂ,
      ‖complexLineRestriction f u w‖ ≤ C * Real.exp (R * ‖w‖)) :
    FiniteExponentialType f := by
  refine ⟨C, R, hC, hR, ?_⟩
  intro z
  by_cases hz : z = 0
  · simpa [complexLineRestriction, hz] using hbound 0 (by simp) 0
  · let u : E := ((‖z‖ : ℂ)⁻¹) • z
    have hu : ‖u‖ = 1 := norm_smul_inv_norm hz
    have hw : (‖z‖ : ℂ) • u = z := by
      dsimp only [u]
      rw [smul_smul, mul_inv_cancel₀, one_smul]
      exact_mod_cast (norm_ne_zero_iff.mpr hz)
    have h := hbound u hu.le (‖z‖ : ℂ)
    simpa only [complexLineRestriction, hw, Complex.norm_real, Real.norm_eq_abs, abs_norm] using h

omit [NormedSpace ℂ E] in
/-- Scaling by a nonzero constant preserves finite exponential type. -/
theorem FiniteExponentialType.div_const {f : E → ℂ} (hf : FiniteExponentialType f)
    {c : ℂ} (hc : c ≠ 0) : FiniteExponentialType (fun z => f z / c) := by
  obtain ⟨C, R, hC, hR, hbound⟩ := hf
  refine ⟨C / ‖c‖, R, div_pos hC (norm_pos_iff.mpr hc), hR, ?_⟩
  intro z
  rw [norm_div, div_mul_eq_mul_div]
  exact div_le_div_of_nonneg_right (hbound z) (norm_nonneg c)

omit [NormedSpace ℂ E] in
/-- Dividing numerator and denominator by `D 0` leaves the factorization intact
and makes the denominator exactly one at the origin. -/
theorem normalize_entire_factorization {A D G : E → ℂ}
    (hADG : ∀ z, A z = D z * G z) (hD0 : D 0 ≠ 0) :
    (fun z => D z / D 0) 0 = 1 ∧
      ∀ z, A z / D 0 = (D z / D 0) * G z := by
  refine ⟨div_self hD0, ?_⟩
  intro z
  rw [hADG z]
  ring

omit [NormedSpace ℂ E] in
/-- A global exponential bound survives the denominator normalization. -/
theorem normalized_factorization_exponential_type {A D G : E → ℂ}
    (hADG : ∀ z, A z = D z * G z) (hD0 : D 0 ≠ 0)
    (hA : FiniteExponentialType A) (hD : FiniteExponentialType D) :
    FiniteExponentialType (fun z => A z / D 0) ∧
      FiniteExponentialType (fun z => D z / D 0) ∧
      (fun z => D z / D 0) 0 = 1 ∧
      ∀ z, A z / D 0 = (D z / D 0) * G z :=
  ⟨hA.div_const hD0, hD.div_const hD0, normalize_entire_factorization hADG hD0⟩

/-- Normalization by a constant also preserves entireness. -/
theorem differentiable_div_const {f : E → ℂ} (hf : Differentiable ℂ f) (c : ℂ) :
    Differentiable ℂ (fun z => f z / c) := by
  simpa only [div_eq_mul_inv] using hf.mul_const c⁻¹

/-- Entire factorization restricts to every complex line with the same
nonzero denominator value at the origin. -/
theorem entire_factorization_complexLineRestriction {A D G : E → ℂ}
    (hA : Differentiable ℂ A) (hD : Differentiable ℂ D) (hG : Differentiable ℂ G)
    (hADG : ∀ z, A z = D z * G z) (hD0 : D 0 ≠ 0) (u : E) :
    Differentiable ℂ (complexLineRestriction A u) ∧
      Differentiable ℂ (complexLineRestriction D u) ∧
      Differentiable ℂ (complexLineRestriction G u) ∧
      complexLineRestriction D u 0 ≠ 0 ∧
      ∀ w, complexLineRestriction A u w =
        complexLineRestriction D u w * complexLineRestriction G u w := by
  refine ⟨differentiable_complexLineRestriction hA u,
    differentiable_complexLineRestriction hD u, differentiable_complexLineRestriction hG u, ?_, ?_⟩
  · simpa only [complexLineRestriction, zero_smul] using hD0
  · exact fun w => hADG (w • u)

/-- Log-positive is a continuous function of the norm, including at zeros. -/
theorem posLog_norm_eq_log_max (z : ℂ) :
    Real.posLog ‖z‖ = Real.log (max 1 ‖z‖) := by
  by_cases hz : ‖z‖ ≤ 1
  · rw [max_eq_left hz, Real.log_one]
    exact (Real.posLog_eq_zero_iff _).mpr (by simpa only [abs_norm] using hz)
  · rw [max_eq_right (le_of_not_ge hz)]
    exact Real.posLog_eq_log (by simpa only [abs_norm] using le_of_not_ge hz)

theorem continuous_posLog_norm {X : Type*} [TopologicalSpace X]
    {f : X → ℂ} (hf : Continuous f) : Continuous (fun z => Real.posLog ‖f z‖) := by
  simp_rw [posLog_norm_eq_log_max]
  exact (continuous_const.max hf.norm).log fun z =>
    ne_of_gt (lt_of_lt_of_le zero_lt_one (le_max_left _ _))

/-- Positive logarithms convert exponential bounds to affine bounds. -/
theorem posLog_norm_le_of_exponential_bound {z : ℂ} {C R s : ℝ}
    (hC : 0 < C) (hR : 0 ≤ R) (hs : 0 ≤ s)
    (hbound : ‖z‖ ≤ C * Real.exp (R * s)) :
    Real.posLog ‖z‖ ≤ Real.posLog C + R * s := by
  apply (Real.monotoneOn_posLog (norm_nonneg z) ((mul_pos hC (Real.exp_pos _)).le) hbound).trans
  apply (Real.posLog_mul (a := C) (b := Real.exp (R * s))).trans
  have hlog : Real.posLog (Real.exp (R * s)) = R * s := by
    rw [Real.posLog_def, Real.log_exp, max_eq_right (mul_nonneg hR hs)]
  rw [hlog]

/-- The pointwise quotient estimate away from denominator zeros. -/
theorem posLog_norm_quotient_le {a d g : ℂ} (hadg : a = d * g) (hd : d ≠ 0) :
    Real.posLog ‖g‖ ≤ Real.posLog ‖a‖ + Real.posLog ‖d‖⁻¹ := by
  have hg : g = a / d := by rw [hadg]; field_simp
  rw [hg, norm_div, div_eq_mul_inv]
  exact Real.posLog_mul

/-- A logarithmic bound controls the ordinary norm also at zeros. -/
theorem norm_le_exp_posLog (z : ℂ) : ‖z‖ ≤ Real.exp (Real.posLog ‖z‖) :=
  (Real.le_exp_log _).trans (Real.exp_le_exp.mpr (le_max_right _ _))

/-- Uniform affine bounds for positive logarithms along complex lines imply
finite exponential type. -/
theorem finiteExponentialType_of_uniform_posLog_line_bound {f : E → ℂ}
    {a b : ℝ} (hb : 0 ≤ b)
    (hbound : ∀ u : E, ‖u‖ ≤ 1 → ∀ w : ℂ,
      Real.posLog ‖complexLineRestriction f u w‖ ≤ a + b * ‖w‖) :
    FiniteExponentialType f := by
  apply finiteExponentialType_of_uniform_line_bound (Real.exp_pos a) hb
  intro u hu w
  calc
    ‖complexLineRestriction f u w‖ ≤
        Real.exp (Real.posLog ‖complexLineRestriction f u w‖) := norm_le_exp_posLog _
    _ ≤ Real.exp (a + b * ‖w‖) := Real.exp_le_exp.mpr (hbound u hu w)
    _ = Real.exp a * Real.exp (b * ‖w‖) := Real.exp_add _ _

omit [NormedSpace ℂ E] in
/-- The compact remainder in the paper can be absorbed into the leading
constant of an exponential bound. -/
theorem finiteExponentialType_of_bound_outside_unitBall [ProperSpace E]
    {f : E → ℂ} (hf : Continuous f) {C R : ℝ} (hC : 0 < C) (hR : 0 ≤ R)
    (hbound : ∀ z : E, 1 ≤ ‖z‖ → ‖f z‖ ≤ C * Real.exp (R * ‖z‖)) :
    FiniteExponentialType f := by
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : E) 1).bddAbove_image hf.norm.continuousOn
  refine ⟨max C M, R, lt_of_lt_of_le hC (le_max_left _ _), hR, ?_⟩
  intro z
  have hexp : 1 ≤ Real.exp (R * ‖z‖) := Real.one_le_exp (mul_nonneg hR (norm_nonneg z))
  by_cases hz : 1 ≤ ‖z‖
  · exact (hbound z hz).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le)
  · have hzB : z ∈ closedBall (0 : E) 1 := by
      simpa only [mem_closedBall, dist_zero_right] using (le_of_not_ge hz)
    calc
      ‖f z‖ ≤ M := hM ⟨z, hzB, rfl⟩
      _ ≤ max C M := le_max_right _ _
      _ ≤ max C M * Real.exp (R * ‖z‖) :=
        le_mul_of_one_le_right (le_trans hC.le (le_max_left _ _)) hexp

/-- The variant needed after using a Poisson estimate only outside radius one. -/
theorem finiteExponentialType_of_posLog_line_bound_outside_unitBall [ProperSpace E]
    {f : E → ℂ} (hf : Continuous f) {a b : ℝ} (hb : 0 ≤ b)
    (hbound : ∀ u : E, ‖u‖ ≤ 1 → ∀ w : ℂ, 1 ≤ ‖w‖ →
      Real.posLog ‖complexLineRestriction f u w‖ ≤ a + b * ‖w‖) :
    FiniteExponentialType f := by
  apply finiteExponentialType_of_bound_outside_unitBall hf (Real.exp_pos a) hb
  intro z hz
  have hz0 : z ≠ 0 := by
    intro heq
    simp only [heq, norm_zero] at hz
    linarith
  let u : E := ((‖z‖ : ℂ)⁻¹) • z
  have hu : ‖u‖ = 1 := norm_smul_inv_norm hz0
  have hw : (‖z‖ : ℂ) • u = z := by
    dsimp only [u]
    rw [smul_smul, mul_inv_cancel₀, one_smul]
    exact_mod_cast norm_ne_zero_iff.mpr hz0
  have hlog := hbound u hu.le (‖z‖ : ℂ) (by simpa using hz)
  simp only [complexLineRestriction, hw, Complex.norm_real, Real.norm_eq_abs, abs_norm] at hlog
  calc
    ‖f z‖ ≤ Real.exp (Real.posLog ‖f z‖) := norm_le_exp_posLog _
    _ ≤ Real.exp (a + b * ‖z‖) := Real.exp_le_exp.mpr hlog
    _ = Real.exp a * Real.exp (b * ‖z‖) := Real.exp_add _ _

/-- The angular circle mean used in Jensen's and Poisson's estimates. -/
def angularCircleMean (f : ℂ → ℝ) (r : ℝ) : ℝ :=
  (2 * Real.pi)⁻¹ * ∫ θ in (0 : ℝ)..2 * Real.pi, f (circleMap 0 r θ)

/-- A uniform upper bound on a circle is also an upper bound on its angular mean. -/
theorem angularCircleMean_le_const {f : ℂ → ℝ} {r M : ℝ}
    (hf : IntervalIntegrable (fun θ => f (circleMap 0 r θ)) volume 0 (2 * Real.pi))
    (hbound : ∀ θ, f (circleMap 0 r θ) ≤ M) : angularCircleMean f r ≤ M := by
  unfold angularCircleMean
  have h := intervalIntegral.integral_mono (by positivity : (0 : ℝ) ≤ 2 * Real.pi)
    hf intervalIntegrable_const hbound
  have hm : (∫ _θ in (0 : ℝ)..2 * Real.pi, M) = (2 * Real.pi) * M := by simp
  rw [hm] at h
  have hpos : 0 < 2 * Real.pi := by positivity
  apply (mul_le_mul_of_nonneg_left h (inv_nonneg.mpr hpos.le)).trans_eq
  rw [← mul_assoc, inv_mul_cancel₀ hpos.ne', one_mul]

/-- A finite exponential bound yields the uniform circle estimate for its
positive logarithm used in the paper's Jensen argument. -/
theorem angularCircleMean_posLog_le_of_exponential_bound {f : ℂ → ℂ}
    (hf : Continuous f) {C R r : ℝ} (hC : 0 < C) (hR : 0 ≤ R) (hr : 0 ≤ r)
    (hbound : ∀ w, ‖f w‖ ≤ C * Real.exp (R * ‖w‖)) :
    angularCircleMean (fun w => Real.posLog ‖f w‖) r ≤ Real.posLog C + R * r := by
  apply angularCircleMean_le_const
  · exact ((continuous_posLog_norm hf).comp (continuous_circleMap 0 r)).intervalIntegrable _ _
  · intro θ
    apply posLog_norm_le_of_exponential_bound hC hR hr
    simpa only [norm_circleMap_zero, abs_of_nonneg hr] using hbound (circleMap 0 r θ)

/-- On a circle avoiding zeros, the negative logarithm is integrable and its
mean is the positive-log mean minus the ordinary-log mean. -/
theorem angularCircleMean_posLog_inv_eq {D : ℂ → ℂ} (hD : Continuous D)
    {r : ℝ} (hDz : ∀ θ : ℝ, D (circleMap 0 r θ) ≠ 0) :
    angularCircleMean (fun w => Real.posLog ‖D w‖⁻¹) r =
      angularCircleMean (fun w => Real.posLog ‖D w‖) r -
        angularCircleMean (fun w => Real.log ‖D w‖) r := by
  have hcircle : Continuous (fun θ => D (circleMap 0 r θ)) :=
    hD.comp (continuous_circleMap 0 r)
  have hpos := ((continuous_posLog_norm hD).comp (continuous_circleMap 0 r)).intervalIntegrable (μ := volume)
    (0 : ℝ) (2 * Real.pi)
  have hlog := (hcircle.norm.log (fun θ => norm_ne_zero_iff.mpr (hDz θ))).intervalIntegrable (μ := volume)
    (0 : ℝ) (2 * Real.pi)
  have heq : (fun w => Real.posLog ‖D w‖⁻¹) =
      (fun w => Real.posLog ‖D w‖ - Real.log ‖D w‖) := by
    funext w
    have h := Real.posLog_sub_posLog_inv (r := ‖D w‖)
    linarith
  rw [heq]
  unfold angularCircleMean
  simp only [Function.comp_def] at hpos hlog ⊢
  rw [intervalIntegral.integral_sub hpos hlog, mul_sub]

/-- The mean-log lower bound from Jensen implies the precise negative-log
estimate used in division. This is an arithmetic consequence; the Jensen
lower bound itself is an explicit hypothesis. -/
theorem angularCircleMean_posLog_inv_le_of_log_nonneg {D : ℂ → ℂ}
    (hD : Continuous D) {r : ℝ} (hDz : ∀ θ : ℝ, D (circleMap 0 r θ) ≠ 0)
    (hJensen : 0 ≤ angularCircleMean (fun w => Real.log ‖D w‖) r) :
    angularCircleMean (fun w => Real.posLog ‖D w‖⁻¹) r ≤
      angularCircleMean (fun w => Real.posLog ‖D w‖) r := by
  rw [angularCircleMean_posLog_inv_eq hD hDz]
  linarith

/-- The algebraic mean estimate for division on a zero-free circle. The
Jensen lower bound is supplied separately by `jensen_diskRealMean_log_norm`. -/
theorem angularCircleMean_quotient_posLog_le {A D G : ℂ → ℂ}
    (hA : Continuous A) (hD : Continuous D) (hG : Continuous G)
    (hADG : ∀ w, A w = D w * G w) {r : ℝ}
    (hDz : ∀ θ : ℝ, D (circleMap 0 r θ) ≠ 0)
    (hJensen : 0 ≤ angularCircleMean (fun w => Real.log ‖D w‖) r) :
    angularCircleMean (fun w => Real.posLog ‖G w‖) r ≤
      angularCircleMean (fun w => Real.posLog ‖A w‖) r +
        angularCircleMean (fun w => Real.posLog ‖D w‖) r := by
  have hAc := ((continuous_posLog_norm hA).comp (continuous_circleMap 0 r)).intervalIntegrable (μ := volume)
    (0 : ℝ) (2 * Real.pi)
  have hGc := ((continuous_posLog_norm hG).comp (continuous_circleMap 0 r)).intervalIntegrable (μ := volume)
    (0 : ℝ) (2 * Real.pi)
  have hDc : Continuous (fun θ => (D (circleMap 0 r θ))⁻¹) :=
    (hD.comp (continuous_circleMap 0 r)).inv₀ hDz
  have hDi : IntervalIntegrable (fun θ => Real.posLog ‖D (circleMap 0 r θ)‖⁻¹)
      volume 0 (2 * Real.pi) := by
    simpa only [norm_inv] using (continuous_posLog_norm hDc).intervalIntegrable (μ := volume)
      (0 : ℝ) (2 * Real.pi)
  have hmono := intervalIntegral.integral_mono
    (by positivity : (0 : ℝ) ≤ 2 * Real.pi) hGc (hAc.add hDi)
    (fun θ => posLog_norm_quotient_le (hADG (circleMap 0 r θ)) (hDz θ))
  have hmean : angularCircleMean (fun w => Real.posLog ‖G w‖) r ≤
      angularCircleMean (fun w => Real.posLog ‖A w‖) r +
        angularCircleMean (fun w => Real.posLog ‖D w‖⁻¹) r := by
    unfold angularCircleMean
    simp only [Function.comp_def] at hAc hDi ⊢
    rw [← mul_add, ← intervalIntegral.integral_add hAc hDi]
    exact mul_le_mul_of_nonneg_left hmono (by positivity)
  exact hmean.trans (add_le_add_left
    (angularCircleMean_posLog_inv_le_of_log_nonneg hD hDz hJensen) _)

/-- The explicit circle bound from the paper, once Jensen's analytic lower
bound has been supplied for that radius. -/
theorem angularCircleMean_quotient_posLog_le_exponential {A D G : ℂ → ℂ}
    (hA : Continuous A) (hD : Continuous D) (hG : Continuous G)
    (hADG : ∀ w, A w = D w * G w) {C R r : ℝ}
    (hC : 0 < C) (hR : 0 ≤ R) (hr : 0 ≤ r)
    (hAbound : ∀ w, ‖A w‖ ≤ C * Real.exp (R * ‖w‖))
    (hDbound : ∀ w, ‖D w‖ ≤ C * Real.exp (R * ‖w‖))
    (hDz : ∀ θ : ℝ, D (circleMap 0 r θ) ≠ 0)
    (hJensen : 0 ≤ angularCircleMean (fun w => Real.log ‖D w‖) r) :
    angularCircleMean (fun w => Real.posLog ‖G w‖) r ≤ 2 * Real.posLog C + 2 * R * r := by
  have hquot := angularCircleMean_quotient_posLog_le hA hD hG hADG hDz hJensen
  have hAm := angularCircleMean_posLog_le_of_exponential_bound hA hC hR hr hAbound
  have hDm := angularCircleMean_posLog_le_of_exponential_bound hD hC hR hr hDbound
  linarith

/-- An entire function nonzero at the origin has only finitely many zeros
in each closed disk. -/
theorem finite_zeros_in_closedBall {D : ℂ → ℂ} (hD : Differentiable ℂ D)
    (hD0 : D 0 ≠ 0) (r : ℝ) :
    (closedBall (0 : ℂ) r ∩ {z : ℂ | D z = 0}).Finite := by
  have ha : AnalyticOnNhd ℂ D Set.univ := fun z _ => hD.analyticAt z
  have hcod : {z : ℂ | D z ≠ 0} ∈ Filter.codiscreteWithin (Set.univ : Set ℂ) := by
    rcases ha.eqOn_zero_or_eventually_ne_zero_of_preconnected isPreconnected_univ with h | h
    · exact False.elim (hD0 (h (Set.mem_univ 0)))
    · exact h
  have heq : ({z : ℂ | D z ≠ 0}ᶜ ∩ Set.univ : Set ℂ) = {z : ℂ | D z = 0} := by
    ext z
    simp
  have hdisc : DiscreteTopology {z : ℂ | D z = 0} :=
    heq ▸ discreteTopology_of_codiscreteWithin hcod
  have hclosed : IsClosed {z : ℂ | D z = 0} := isClosed_eq hD.continuous continuous_const
  exact ((isCompact_closedBall (0 : ℂ) r).inter_right hclosed).finite
    (DiscreteTopology.of_subset hdisc Set.inter_subset_right)

/-- There is a zero-free integration circle at some radius in every positive
interval. This lets a Jensen/Poisson proof avoid limiting circles through zeros. -/
theorem exists_zero_free_circle_radius {D : ℂ → ℂ} (hD : Differentiable ℂ D)
    (hD0 : D 0 ≠ 0) {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    ∃ r ∈ Set.Ioo a b, ∀ θ : ℝ, D (circleMap 0 r θ) ≠ 0 := by
  have hz := finite_zeros_in_closedBall hD hD0 b
  obtain ⟨r, hr, hnot⟩ := (Set.Ioo_infinite hab).exists_not_mem_finite (hz.image norm)
  refine ⟨r, hr, ?_⟩
  intro θ hzero
  apply hnot
  refine ⟨circleMap 0 r θ, ⟨?_, hzero⟩, ?_⟩
  · rw [mem_closedBall, dist_zero_right, norm_circleMap_zero, abs_of_pos (ha.trans_lt hr.1)]
    exact hr.2.le
  · rw [norm_circleMap_zero, abs_of_pos (ha.trans_lt hr.1)]

/-- The factor-three kernel estimate remains valid at any radius at least twice
that of the evaluation point, including a nearby zero-free radius. -/
theorem norm_herglotzKernel_le_three_of_two_norm_le {ζ w : ℂ} (hw : w ≠ 0)
    (hζ : 2 * ‖w‖ ≤ ‖ζ‖) : ‖(ζ + w) / (ζ - w)‖ ≤ 3 := by
  have hwpos : 0 < ‖w‖ := norm_pos_iff.mpr hw
  have hsub := norm_sub_norm_le ζ w
  have hdenpos : 0 < ‖ζ - w‖ := by linarith
  rw [norm_div]
  apply (div_le_iff₀ hdenpos).mpr
  have hnum := norm_add_le ζ w
  linarith

/-- The factor three in the Poisson estimate is uniform: the Herglotz kernel
is bounded by three on the circle of radius twice the evaluation radius. -/
theorem norm_herglotzKernel_le_three {ζ w : ℂ} (hw : w ≠ 0)
    (hζ : ‖ζ‖ = 2 * ‖w‖) : ‖(ζ + w) / (ζ - w)‖ ≤ 3 := by
  have hwpos : 0 < ‖w‖ := norm_pos_iff.mpr hw
  have hden : ‖w‖ ≤ ‖ζ - w‖ := by
    have h := norm_sub_norm_le ζ w
    rw [hζ] at h
    linarith
  have hdenpos : 0 < ‖ζ - w‖ := hwpos.trans_le hden
  rw [norm_div]
  apply (div_le_iff₀ hdenpos).mpr
  have hnum := norm_add_le ζ w
  rw [hζ] at hnum
  linarith

/-- The corresponding real Poisson weight lies between zero and three.
This proves only the kernel estimate; it does not assert Poisson's formula. -/
theorem re_herglotzKernel_mem_Icc {ζ w : ℂ} (hw : w ≠ 0)
    (hζ : ‖ζ‖ = 2 * ‖w‖) : ((ζ + w) / (ζ - w)).re ∈ Set.Icc (0 : ℝ) 3 := by
  have hnorm := norm_herglotzKernel_le_three hw hζ
  refine ⟨?_, (Complex.re_le_norm _).trans hnorm⟩
  have hsq : Complex.normSq w ≤ Complex.normSq ζ := by
    rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq, hζ]
    nlinarith [norm_nonneg w]
  have hnum : (ζ + w).re * (ζ - w).re + (ζ + w).im * (ζ - w).im =
      Complex.normSq ζ - Complex.normSq w := by
    simp only [Complex.add_re, Complex.sub_re, Complex.add_im, Complex.sub_im,
      Complex.normSq_apply]
    ring
  rw [Complex.div_re, ← add_div, hnum]
  exact div_nonneg (sub_nonneg.mpr hsq) (Complex.normSq_nonneg _)

/-- Choose one circle avoiding the zeros of both functions. The second
function may vanish at the origin; a nonzero value elsewhere suffices. -/
theorem exists_common_zero_free_circle_radius {D G : ℂ → ℂ}
    (hD : Differentiable ℂ D) (hG : Differentiable ℂ G) (hD0 : D 0 ≠ 0)
    {w : ℂ} (hGw : G w ≠ 0) {a b : ℝ} (ha : 0 ≤ a) (hab : a < b)
    (hwb : ‖w‖ < b) :
    ∃ r ∈ Set.Ioo a b, (∀ θ : ℝ, D (circleMap 0 r θ) ≠ 0) ∧
      (∀ θ : ℝ, G (circleMap 0 r θ) ≠ 0) := by
  have hzD := finite_zeros_in_closedBall hD hD0 b
  have hzG := disk_finite_zeros (ρ := b) (R := b + 1) (by linarith)
    hG.differentiableOn (w := w)
    (by simpa only [mem_ball, dist_zero_right] using (by linarith : ‖w‖ < b + 1)) hGw
  obtain ⟨r, hr, hnot⟩ := (Set.Ioo_infinite hab).exists_not_mem_finite
    ((hzD.union hzG).image norm)
  have hrpos : 0 < r := ha.trans_lt hr.1
  have hcircle (θ : ℝ) : circleMap 0 r θ ∈ closedBall (0 : ℂ) b := by
    rw [mem_closedBall, dist_zero_right, norm_circleMap_zero, abs_of_pos hrpos]
    exact hr.2.le
  refine ⟨r, hr, ?_, ?_⟩
  · intro θ hzero
    apply hnot
    refine ⟨circleMap 0 r θ, Or.inl ⟨hcircle θ, hzero⟩, ?_⟩
    rw [norm_circleMap_zero, abs_of_pos hrpos]
  · intro θ hzero
    apply hnot
    refine ⟨circleMap 0 r θ, Or.inr ⟨hcircle θ, hzero⟩, ?_⟩
    rw [norm_circleMap_zero, abs_of_pos hrpos]

/-- Entire division preserves finite exponential type (`cm:lem:type`). The
origin value of the denominator supplies the uniform Jensen lower bound;
Poisson's inequality on each complex line then controls the quotient. -/
theorem finiteExponentialType_entire_quotient [ProperSpace E]
    {A D G : E → ℂ} (hA : Differentiable ℂ A) (hD : Differentiable ℂ D)
    (hG : Differentiable ℂ G) (hADG : ∀ z, A z = D z * G z) (hD0 : D 0 ≠ 0)
    (hAtype : FiniteExponentialType A) (hDtype : FiniteExponentialType D) :
    FiniteExponentialType G := by
  let A' : E → ℂ := fun z => A z / D 0
  let D' : E → ℂ := fun z => D z / D 0
  have hA' : Differentiable ℂ A' := differentiable_div_const hA (D 0)
  have hD' : Differentiable ℂ D' := differentiable_div_const hD (D 0)
  have hD'0 : D' 0 = 1 := div_self hD0
  have hEq : ∀ z, A' z = D' z * G z := (normalize_entire_factorization hADG hD0).2
  obtain ⟨CA, RA, hCA, hRA, hAb⟩ :=
    finiteExponentialType_uniform_line_bound (hAtype.div_const hD0)
  obtain ⟨CD, RD, hCD, hRD, hDb⟩ :=
    finiteExponentialType_uniform_line_bound (hDtype.div_const hD0)
  let C : ℝ := max CA CD
  let R : ℝ := max RA RD
  have hC : 0 < C := hCA.trans_le (le_max_left _ _)
  have hR : 0 ≤ R := hRA.trans (le_max_left _ _)
  have hAb' (u : E) (hu : ‖u‖ ≤ 1) (w : ℂ) :
      ‖complexLineRestriction A' u w‖ ≤ C * Real.exp (R * ‖w‖) := by
    apply (hAb u hu w).trans
    exact mul_le_mul (le_max_left _ _)
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg w)))
      (Real.exp_pos _).le hC.le
  have hDb' (u : E) (hu : ‖u‖ ≤ 1) (w : ℂ) :
      ‖complexLineRestriction D' u w‖ ≤ C * Real.exp (R * ‖w‖) := by
    apply (hDb u hu w).trans
    exact mul_le_mul (le_max_right _ _)
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg w)))
      (Real.exp_pos _).le hC.le
  apply finiteExponentialType_of_posLog_line_bound_outside_unitBall
    hG.continuous (a := 6 * Real.posLog C) (b := 18 * R) (by positivity)
  intro u hu w hw
  let a := complexLineRestriction A' u
  let d := complexLineRestriction D' u
  let g := complexLineRestriction G u
  have ha : Differentiable ℂ a := differentiable_complexLineRestriction hA' u
  have hd : Differentiable ℂ d := differentiable_complexLineRestriction hD' u
  have hg : Differentiable ℂ g := differentiable_complexLineRestriction hG u
  have hd0 : d 0 = 1 := by simpa only [d, complexLineRestriction, zero_smul] using hD'0
  have hEq' (ζ : ℂ) : a ζ = d ζ * g ζ := hEq (ζ • u)
  change Real.posLog ‖g w‖ ≤ 6 * Real.posLog C + 18 * R * ‖w‖
  by_cases hgw : g w = 0
  · simp only [hgw, norm_zero, Real.posLog_def, Real.log_zero, max_self]
    positivity
  · obtain ⟨r, hr, hdz, hgz⟩ := exists_common_zero_free_circle_radius hd hg
      (by rw [hd0]; exact one_ne_zero) hgw
      (a := 2 * ‖w‖) (b := 3 * ‖w‖) (by positivity) (by linarith)
      (by linarith)
    have hrpos : 0 < r := (by positivity : 0 ≤ 2 * ‖w‖).trans_lt hr.1
    have hJ := jensen_diskRealMean_log_norm hrpos (R := r + 1) (by linarith)
      hd.differentiableOn (by rw [hd0]; exact one_ne_zero) hdz
    have hJ' : 0 ≤ angularCircleMean (fun ζ => Real.log ‖d ζ‖) r := by
      simpa only [hd0, norm_one, Real.log_one, diskRealMean, angularCircleMean] using hJ
    have hm := angularCircleMean_quotient_posLog_le_exponential
      ha.continuous hd.continuous hg.continuous hEq' hC hR hrpos.le
      (hAb' u hu) (hDb' u hu) hdz hJ'
    have hp := posLog_norm_le_three_diskRealMean hrpos (R := r + 1)
      (by linarith) hg.differentiableOn (w := w) hr.1.le hgz
    change Real.posLog ‖g w‖ ≤ 3 * angularCircleMean (fun ζ => Real.posLog ‖g ζ‖) r at hp
    have hrR : R * r ≤ R * (3 * ‖w‖) := mul_le_mul_of_nonneg_left hr.2.le hR
    linarith

/-- The form of `cm:lem:type` with a single exponential bound for the sum
of the numerator and denominator norms. The signs of its constants need not
be assumed: the nonzero denominator forces a positive leading constant. -/
theorem finiteExponentialType_entire_quotient_of_sum_bound [ProperSpace E]
    {A D G : E → ℂ} (hA : Differentiable ℂ A) (hD : Differentiable ℂ D)
    (hG : Differentiable ℂ G) (hADG : ∀ z, A z = D z * G z) (hD0 : D 0 ≠ 0)
    {C R : ℝ} (hbound : ∀ z, ‖A z‖ + ‖D z‖ ≤ C * Real.exp (R * ‖z‖)) :
    FiniteExponentialType G := by
  have hzero := hbound 0
  simp only [norm_zero, mul_zero, Real.exp_zero, mul_one] at hzero
  have hC : 0 < C := by linarith [norm_pos_iff.mpr hD0, norm_nonneg (A 0)]
  have hb (z : E) : ‖A z‖ + ‖D z‖ ≤ C * Real.exp (max R 0 * ‖z‖) := by
    exact (hbound z).trans (mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg z)))
      hC.le)
  apply finiteExponentialType_entire_quotient hA hD hG hADG hD0
  · refine ⟨C, max R 0, hC, le_max_right _ _, fun z => ?_⟩
    exact (le_add_of_nonneg_right (norm_nonneg (D z))).trans (hb z)
  · refine ⟨C, max R 0, hC, le_max_right _ _, fun z => ?_⟩
    exact (le_add_of_nonneg_left (norm_nonneg (A z))).trans (hb z)

end RieszEuclidean.CompleteMinimal
