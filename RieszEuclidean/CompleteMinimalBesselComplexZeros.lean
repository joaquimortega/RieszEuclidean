import RieszEuclidean.CompleteMinimalBesselAsymptotic
import RieszEuclidean.CompleteMinimalDivision
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# Complex zeros of the ball-transform square function

The self-adjoint radial equation identifies a complex zero with a positive
real Rayleigh quotient. No infinite product representation is assumed.
-/

noncomputable section
open MeasureTheory Metric Filter Topology
open scoped Interval

namespace RieszEuclidean.CompleteMinimal

private theorem squareFunction_differentiable (n : ℕ) :
    Differentiable ℂ (ballSquareFunction n) :=
  (Complex.analyticOnNhd_univ_iff_differentiable).mp (ballSquareFunction_analytic n)

private theorem squareFunction_deriv_differentiable (n : ℕ) :
    Differentiable ℂ (deriv (ballSquareFunction n)) := by
  intro z
  have h := (hasFPowerSeriesOnBall_deriv (ballSquareFunction_hasFPowerSeries n)).analyticOnNhd
  exact (h z (by simp)).differentiableAt

private def spectralProfile (n : ℕ) (v : ℂ) (z : ℂ) := ballSquareFunction n (v * z ^ 2)
private def spectralSlope (n : ℕ) (v : ℂ) (z : ℂ) :=
  2 * v * z * deriv (ballSquareFunction n) (v * z ^ 2)
private def spectralFlux (n : ℕ) (v : ℂ) (z : ℂ) :=
  2 * v * z ^ (n + 3) * deriv (ballSquareFunction n) (v * z ^ 2)

private theorem spectralProfile_hasDerivAt (n : ℕ) (v z : ℂ) :
    HasDerivAt (spectralProfile n v) (spectralSlope n v z) z := by
  have h := ((squareFunction_differentiable n) (v * z ^ 2)).hasDerivAt.comp z
    (((hasDerivAt_id z).pow 2).const_mul v)
  convert h using 1
  simp only [spectralSlope, Nat.cast_ofNat, pow_one, id_eq, mul_one]
  ring

private theorem spectralFlux_eq (n : ℕ) (v z : ℂ) :
    spectralFlux n v z = z ^ (n + 2) * spectralSlope n v z := by
  simp only [spectralFlux, spectralSlope]
  rw [show n + 3 = (n + 2) + 1 by omega, pow_succ]
  ring

private theorem spectralFlux_hasDerivAt (n : ℕ) (v z : ℂ) :
    HasDerivAt (spectralFlux n v) (-v * z ^ (n + 2) * spectralProfile n v z) z := by
  have h := (((hasDerivAt_id z).pow (n + 3)).const_mul (2 * v)).mul
    (((squareFunction_deriv_differentiable n) (v * z ^ 2)).hasDerivAt.comp z
      (((hasDerivAt_id z).pow 2).const_mul v))
  convert h using 1
  have ho := ballSquareFunction_ode n (v * z ^ 2)
  simp only [spectralProfile, id_eq, Nat.cast_ofNat, pow_one, mul_one,
    Function.comp_apply, show n + 3 - 1 = n + 2 by omega]
  push_cast at ho ⊢
  rw [show n + 3 = (n + 2) + 1 by omega, pow_succ]
  linear_combination -v * z ^ (n + 2) * ho

private theorem spectral_conj_hasDerivAt (n : ℕ) (v : ℂ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => starRingEnd ℂ (spectralProfile n v s))
      (starRingEnd ℂ (spectralSlope n v t)) t := by
  have h := (Complex.conjCLE.toContinuousLinearMap.hasFDerivAt.comp t
    (spectralProfile_hasDerivAt n v (t : ℂ)).comp_ofReal.hasFDerivAt).hasDerivAt
  simpa only [Function.comp_def, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.one_apply, one_smul, ContinuousLinearEquiv.coe_coe,
    Complex.conjCLE_apply] using h

private theorem spectral_mass_pos (n : ℕ) (v : ℂ) :
    0 < ∫ t in (0 : ℝ)..1, t ^ (n + 2) * ‖spectralProfile n v t‖ ^ 2 := by
  have hu : Continuous (fun t : ℝ => spectralProfile n v t) :=
    ((squareFunction_differentiable n).continuous.comp
      (continuous_const.mul (Complex.continuous_ofReal.pow 2)))
  have hu0 : spectralProfile n v 0 ≠ 0 := by
    simp only [spectralProfile, zero_pow (by norm_num : 2 ≠ 0), mul_zero]
    have h := radialBallFourier_eq_squareFunction n 0
    have hF : ballSquareFunction n 0 = 1 := by simpa using h.symm
    rw [hF]
    exact one_ne_zero
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (hu.continuousAt.eventually_ne hu0)
  let c : ℝ := min ε 1 / 2
  have hcpos : 0 < c := by dsimp only [c]; positivity
  have hcle : c ≤ 1 := by dsimp only [c]; linarith [min_le_right ε 1]
  have hce : c < ε := by dsimp only [c]; linarith [min_le_left ε 1]
  have huc : spectralProfile n v c ≠ 0 := hball
    (by simpa only [mem_ball, dist_zero_right, Real.norm_eq_abs, abs_of_pos hcpos] using hce)
  apply intervalIntegral.integral_pos zero_lt_one
    ((continuous_id.pow (n + 2)).mul (hu.norm.pow 2)).continuousOn
  · intro t ht
    exact mul_nonneg (pow_nonneg ht.1.le _) (sq_nonneg _)
  · exact ⟨c, ⟨hcpos.le, hcle⟩, mul_pos (pow_pos hcpos _) (sq_pos_of_pos (norm_pos_iff.mpr huc))⟩

private theorem spectral_energy_identity (n : ℕ) {v : ℂ}
    (hv : ballSquareFunction n v = 0) :
    v * ((∫ t in (0 : ℝ)..1, t ^ (n + 2) * ‖spectralProfile n v t‖ ^ 2) : ℝ) =
      ((∫ t in (0 : ℝ)..1, t ^ (n + 2) * ‖spectralSlope n v t‖ ^ 2) : ℝ) := by
  have hu : Continuous (fun t : ℝ => spectralProfile n v t) :=
    (continuous_iff_continuousAt.mpr (fun z => (spectralProfile_hasDerivAt n v z).continuousAt)).comp
      Complex.continuous_ofReal
  have hs : Continuous (fun t : ℝ => spectralSlope n v t) := by
    unfold spectralSlope
    exact (continuous_const.mul Complex.continuous_ofReal).mul
      ((squareFunction_deriv_differentiable n).continuous.comp
        (continuous_const.mul (Complex.continuous_ofReal.pow 2)))
  have hp : Continuous (fun t : ℝ => spectralFlux n v t) :=
    (continuous_iff_continuousAt.mpr (fun z => (spectralFlux_hasDerivAt n v z).continuousAt)).comp
      Complex.continuous_ofReal
  have hm : Continuous (fun t : ℝ => t ^ (n + 2) * ‖spectralProfile n v t‖ ^ 2) :=
    (continuous_id.pow (n + 2)).mul (hu.norm.pow 2)
  have he : Continuous (fun t : ℝ => t ^ (n + 2) * ‖spectralSlope n v t‖ ^ 2) :=
    (continuous_id.pow (n + 2)).mul (hs.norm.pow 2)
  have hleft : Continuous (fun t : ℝ => -v * (t : ℂ) ^ (n + 2) * spectralProfile n v t) :=
    (continuous_const.mul (Complex.continuous_ofReal.pow (n + 2))).mul hu
  have hright : Continuous (fun t : ℝ => starRingEnd ℂ (spectralSlope n v t)) :=
    Complex.continuous_conj.comp hs
  have h := intervalIntegral.integral_deriv_mul_eq_sub_of_hasDerivAt
    hp.continuousOn (Complex.continuous_conj.comp hu).continuousOn
    (fun t _ => (spectralFlux_hasDerivAt n v (t : ℂ)).comp_ofReal)
    (fun t _ => spectral_conj_hasDerivAt n v t)
    (hleft.intervalIntegrable (μ := volume) 0 1)
    (hright.intervalIntegrable (μ := volume) 0 1)
  have hend : spectralFlux n v 1 * starRingEnd ℂ (spectralProfile n v 1) -
      spectralFlux n v 0 * starRingEnd ℂ (spectralProfile n v 0) = 0 := by
    simp [spectralProfile, spectralFlux, hv]
  simp only [Function.comp_apply, Complex.ofReal_one, Complex.ofReal_zero, hend] at h
  have heq (t : ℝ) :
      (-v * (t : ℂ) ^ (n + 2) * spectralProfile n v t) *
          starRingEnd ℂ (spectralProfile n v t) +
        spectralFlux n v t * starRingEnd ℂ (spectralSlope n v t) =
      -v * ((t ^ (n + 2) * ‖spectralProfile n v t‖ ^ 2 : ℝ) : ℂ) +
        ((t ^ (n + 2) * ‖spectralSlope n v t‖ ^ 2 : ℝ) : ℂ) := by
    rw [spectralFlux_eq]
    have hprod (a : ℂ) : a * starRingEnd ℂ a = (‖a‖ ^ 2 : ℝ) := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    simp only [Complex.ofReal_mul, Complex.ofReal_pow]
    calc
      _ = -v * (t : ℂ) ^ (n + 2) *
          (spectralProfile n v t * starRingEnd ℂ (spectralProfile n v t)) +
          (t : ℂ) ^ (n + 2) *
          (spectralSlope n v t * starRingEnd ℂ (spectralSlope n v t)) := by ring
      _ = _ := by rw [hprod, hprod]; push_cast; ring
  have hint : (∫ t in (0 : ℝ)..1,
      -v * ((t ^ (n + 2) * ‖spectralProfile n v t‖ ^ 2 : ℝ) : ℂ) +
        ((t ^ (n + 2) * ‖spectralSlope n v t‖ ^ 2 : ℝ) : ℂ)) = 0 := by
    exact (intervalIntegral.integral_congr (fun t _ => (heq t).symm)).trans h
  have hmi : IntervalIntegrable (fun t : ℝ =>
      -v * ((t ^ (n + 2) * ‖spectralProfile n v t‖ ^ 2 : ℝ) : ℂ)) volume 0 1 := by
    simpa only [Function.comp_def] using
      ((continuous_const.mul (Complex.continuous_ofReal.comp hm)).intervalIntegrable (μ := volume) 0 1)
  have hei : IntervalIntegrable (fun t : ℝ =>
      ((t ^ (n + 2) * ‖spectralSlope n v t‖ ^ 2 : ℝ) : ℂ)) volume 0 1 := by
    simpa only [Function.comp_def] using
      ((Complex.continuous_ofReal.comp he).intervalIntegrable (μ := volume) 0 1)
  rw [intervalIntegral.integral_add hmi hei,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_ofReal,
    intervalIntegral.integral_ofReal] at hint
  linear_combination -hint

/-- Every complex zero of the ball-transform square function is positive real.
This follows from the radial self-adjoint equation, without a product formula. -/
theorem ballSquareFunction_zero_positive_real (n : ℕ) {v : ℂ}
    (hv : ballSquareFunction n v = 0) : ∃ a : ℝ, 0 < a ∧ v = (a : ℂ) := by
  let M : ℝ := ∫ t in (0 : ℝ)..1, t ^ (n + 2) * ‖spectralProfile n v t‖ ^ 2
  let T : ℝ := ∫ t in (0 : ℝ)..1, t ^ (n + 2) * ‖spectralSlope n v t‖ ^ 2
  have hM : 0 < M := spectral_mass_pos n v
  have hT : 0 ≤ T := by
    apply intervalIntegral.integral_nonneg zero_le_one
    intro t ht
    exact mul_nonneg (pow_nonneg ht.1 _) (sq_nonneg _)
  have hid : v * (M : ℂ) = (T : ℂ) := spectral_energy_identity n hv
  have him : v.im * M = 0 := by
    simpa only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_add] using
      congrArg Complex.im hid
  have hvim : v.im = 0 := (mul_eq_zero.mp him).resolve_right hM.ne'
  have hre : v.re * M = T := by
    simpa only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero] using
      congrArg Complex.re hid
  have hvr : 0 ≤ v.re := by nlinarith
  have hvne : v ≠ 0 := by
    intro heq
    have h := radialBallFourier_eq_squareFunction n 0
    have hF : ballSquareFunction n 0 = 1 := by simpa using h.symm
    rw [heq, hF] at hv
    exact one_ne_zero hv
  have hvrne : v.re ≠ 0 := by
    intro heq
    apply hvne
    exact Complex.ext (by simpa using heq) (by simpa using hvim)
  refine ⟨v.re, lt_of_le_of_ne hvr hvrne.symm, ?_⟩
  exact Complex.ext (by simp) (by simpa using hvim)

/-- All zeros of the square function are simple, including as complex zeros. -/
theorem ballSquareFunction_deriv_ne_zero_at_zero (n : ℕ) {v : ℂ}
    (hv : ballSquareFunction n v = 0) : deriv (ballSquareFunction n) v ≠ 0 := by
  obtain ⟨a, ha, rfl⟩ := ballSquareFunction_zero_positive_real n hv
  let s : ℝ := Real.sqrt a
  have hs : 0 < s := Real.sqrt_pos.mpr ha
  have hsq : (s : ℂ) ^ 2 = (a : ℂ) := by exact_mod_cast Real.sq_sqrt ha.le
  have hz : realRadialBallFourier n s = 0 := by
    rw [realRadialBallFourier, radialBallFourier_eq_squareFunction, hsq, hv]
    rfl
  intro hderiv
  apply realRadialBallFourier_deriv_ne_zero_at_zero n hs hz
  rw [realRadialBallFourier_deriv, radialBallFourier_deriv, hsq, hderiv]
  simp

/-- The analytic unit remaining after removal of a square-function zero. -/
theorem ballSquareFunction_simple_factor (n : ℕ) {v : ℂ}
    (hv : ballSquareFunction n v = 0) :
    ∃ h : ℂ → ℂ, AnalyticAt ℂ h v ∧ h v ≠ 0 ∧
      ∀ z, ballSquareFunction n z = (z - v) * h z := by
  obtain ⟨p, hp⟩ := (ballSquareFunction_analytic n) v (Set.mem_univ _)
  refine ⟨dslope (ballSquareFunction n) v, ⟨p.fslope, hp.has_fpower_series_dslope_fslope⟩, ?_, ?_⟩
  · rw [dslope_same]
    exact ballSquareFunction_deriv_ne_zero_at_zero n hv
  · intro z
    have h := sub_smul_dslope (ballSquareFunction n) v z
    simpa only [smul_eq_mul, hv, sub_zero] using h.symm

/-- Analyticity of the normalized squared-frequency polynomial. -/
theorem ballQuadraticForm_analyticAt (d : ℕ) (z : ComplexEuclidean d) :
    AnalyticAt ℂ (ballQuadraticForm d) z := by
  exact analyticAt_const.mul (Finset.analyticAt_sum _ (fun i _ =>
    ((PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin d => ℂ) i).analyticAt z).pow 2))

/-- Every complex ball-transform zero belongs to a positive radial quadric
and admits its equation times an actual analytic unit. -/
theorem normalizedBallFourier_zero_local_factor (n : ℕ)
    {z₀ : ComplexEuclidean (n + 1)} (hz : normalizedBallFourier (n + 1) z₀ = 0) :
    ∃ s : ℝ, 0 < s ∧ realRadialBallFourier n s = 0 ∧
      ballQuadraticForm (n + 1) z₀ = (s : ℂ) ^ 2 ∧
      ∃ u : ComplexEuclidean (n + 1) → ℂ, AnalyticAt ℂ u z₀ ∧ u z₀ ≠ 0 ∧
        ∀ᶠ z in 𝓝 z₀, normalizedBallFourier (n + 1) z =
          (squareSum (fun j => z j) - (s / (2 * Real.pi) : ℂ) ^ 2) * u z := by
  have hF : ballSquareFunction n (ballQuadraticForm (n + 1) z₀) = 0 := by
    rwa [normalizedBallFourier_eq_squareFunction] at hz
  obtain ⟨a, ha, hqa⟩ := ballSquareFunction_zero_positive_real n hF
  let s : ℝ := Real.sqrt a
  have hs : 0 < s := Real.sqrt_pos.mpr ha
  have hsq : (s : ℂ) ^ 2 = (a : ℂ) := by exact_mod_cast Real.sq_sqrt ha.le
  have hq : ballQuadraticForm (n + 1) z₀ = (s : ℂ) ^ 2 := hqa.trans hsq.symm
  have hsroot : realRadialBallFourier n s = 0 := by
    rw [realRadialBallFourier, radialBallFourier_eq_squareFunction, ← hq, hF]
    rfl
  obtain ⟨h, hh, hhne, hfactor⟩ := ballSquareFunction_simple_factor n hF
  let u : ComplexEuclidean (n + 1) → ℂ := fun z =>
    (2 * Real.pi : ℂ) ^ 2 * h (ballQuadraticForm (n + 1) z)
  have hp : (2 * Real.pi : ℂ) ≠ 0 := by
    exact_mod_cast (mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) Real.pi_ne_zero)
  refine ⟨s, hs, hsroot, hq, u,
    analyticAt_const.mul (hh.comp (ballQuadraticForm_analyticAt (n + 1) z₀)), ?_, ?_⟩
  · exact mul_ne_zero (pow_ne_zero 2 hp) hhne
  · apply Filter.Eventually.of_forall
    intro z
    rw [normalizedBallFourier_eq_squareFunction, hfactor]
    dsimp only [u]
    rw [hq]
    unfold ballQuadraticForm squareSum
    push_cast
    field_simp
    ring

/-- Global multivariable analyticity follows from the entire scalar square
function composed with the squared-frequency polynomial. -/
theorem normalizedBallFourier_analytic (n : ℕ) :
    AnalyticOnNhd ℂ (normalizedBallFourier (n + 1)) Set.univ := by
  intro z _
  have h := ((ballSquareFunction_analytic n) (ballQuadraticForm (n + 1) z)
    (Set.mem_univ _)).comp (ballQuadraticForm_analyticAt (n + 1) z)
  convert h using 1
  funext w
  exact normalizedBallFourier_eq_squareFunction n w

/-- Any enumeration covering all positive radial roots gives the genuine
simple-quadric geometry used in global analytic division. -/
theorem normalizedBallFourier_hasSimpleQuadricZeros_of_cover (n : ℕ) {ι : Type*}
    (radius : ι → ℝ)
    (hcover : ∀ s : ℝ, 0 < s → realRadialBallFourier n s = 0 →
      ∃ i, s = 2 * Real.pi * radius i) :
    HasSimpleQuadricZeros (normalizedBallFourier (n + 1)) radius := by
  intro z₀ hz
  obtain ⟨s, hs, hsroot, hq, u, hu, hune, hfactor⟩ :=
    normalizedBallFourier_zero_local_factor n hz
  obtain ⟨i, hi⟩ := hcover s hs hsroot
  have hp : (2 * Real.pi : ℂ) ≠ 0 := by
    exact_mod_cast (mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) Real.pi_ne_zero)
  have hquad : squareSum (fun j => z₀ j) = (radius i : ℂ) ^ 2 := by
    have hscale : (2 * Real.pi : ℂ) ^ 2 *
        (squareSum (fun j => z₀ j) - (radius i : ℂ) ^ 2) = 0 := by
      rw [hi] at hq
      unfold ballQuadraticForm at hq
      unfold squareSum
      push_cast at hq
      linear_combination hq
    exact sub_eq_zero.mp ((mul_eq_zero.mp hscale).resolve_left (pow_ne_zero 2 hp))
  have hsr : (s / (2 * Real.pi) : ℂ) = (radius i : ℂ) := by
    rw [hi]
    push_cast
    field_simp
  refine ⟨i, hquad, u, hu, hune, ?_⟩
  simpa only [hsr] using hfactor

end RieszEuclidean.CompleteMinimal
