import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Fourier.RiemannLebesgueLemma
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Integrals
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import RieszEuclidean.CompleteMinimalEntireFourier
import RieszEuclidean.CompleteMinimalQuadric

/-!
# The normalized ball transform

This file uses the actual Fourier transform of the unit-ball indicator.
The moment expansion below is an integral identity, rather than an assumed
identification with a special function. The zero product and sharp asymptotic
estimates require additional theorems and are not postulated here.
-/

noncomputable section
open MeasureTheory Filter Topology
open scoped BigOperators

namespace RieszEuclidean.CompleteMinimal

/-- The open physical unit ball. -/
def physicalUnitBall (d : ℕ) : Set (Euclidean d) := Metric.ball 0 1

/-- The complex indicator of the physical unit ball. -/
def ballIndicator (d : ℕ) : Euclidean d → ℂ :=
  (physicalUnitBall d).indicator (fun _ => 1)

/-- The real Lebesgue volume of the physical unit ball. -/
def ballVolume (d : ℕ) : ℝ := volume.real (physicalUnitBall d)

theorem physicalUnitBall_measurable (d : ℕ) : MeasurableSet (physicalUnitBall d) :=
  measurableSet_ball

theorem physicalUnitBall_volume_lt_top (d : ℕ) : volume (physicalUnitBall d) < ⊤ :=
  (Metric.isBounded_ball (x := (0 : Euclidean d)) (r := 1)).measure_lt_top

theorem ballVolume_pos (d : ℕ) : 0 < ballVolume d := by
  exact ENNReal.toReal_pos (Metric.measure_ball_pos volume 0 zero_lt_one).ne'
    (physicalUnitBall_volume_lt_top d).ne

theorem ballIndicator_integrable (d : ℕ) : Integrable (ballIndicator d) := by
  apply (integrable_indicator_iff (physicalUnitBall_measurable d)).mpr
  exact integrableOn_const.mpr (Or.inr (physicalUnitBall_volume_lt_top d))

theorem ballIndicator_support_bound (d : ℕ) :
    ∀ᵐ x, ballIndicator d x ≠ 0 → ‖x‖ ≤ 1 := by
  filter_upwards with x hx
  have hmem : x ∈ physicalUnitBall d := by
    by_contra h
    exact hx (Set.indicator_of_not_mem h _)
  exact (mem_ball_zero_iff.mp hmem).le

theorem ballIndicator_integral (d : ℕ) : ∫ x, ballIndicator d x = (ballVolume d : ℂ) := by
  rw [ballIndicator, integral_indicator (physicalUnitBall_measurable d)]
  simp [ballVolume, integral_const]

/-- The entire Fourier transform of the normalized unit-ball indicator. -/
def normalizedBallFourier (d : ℕ) (z : ComplexEuclidean d) : ℂ :=
  entireFourier (ballIndicator d) z / (ballVolume d : ℂ)

@[simp]
theorem normalizedBallFourier_zero (d : ℕ) : normalizedBallFourier d 0 = 1 := by
  have hv : (ballVolume d : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ballVolume_pos d).ne'
  simp [normalizedBallFourier, entireFourier, complexFourierKernel,
    ballIndicator_integral, hv]

theorem normalizedBallFourier_eq_setIntegral (d : ℕ) (z : ComplexEuclidean d) :
    normalizedBallFourier d z =
      (∫ x in physicalUnitBall d, complexFourierKernel x z) / (ballVolume d : ℂ) := by
  unfold normalizedBallFourier entireFourier ballIndicator
  rw [← integral_indicator (physicalUnitBall_measurable d)]
  congr 1
  apply integral_congr_ae
  filter_upwards with x
  by_cases hx : x ∈ physicalUnitBall d <;> simp [hx]

theorem normalizedBallFourier_differentiable (d : ℕ) :
    Differentiable ℂ (normalizedBallFourier d) := by
  change Differentiable ℂ (fun z => entireFourier (ballIndicator d) z / (ballVolume d : ℂ))
  have h := (entireFourier_differentiable (ballIndicator_integrable d) zero_le_one
    (ballIndicator_support_bound d)).const_smul ((ballVolume d : ℂ)⁻¹)
  simpa [normalizedBallFourier, smul_eq_mul, div_eq_mul_inv, mul_comm] using h

theorem normalizedBallFourier_analyticAlongLine (d : ℕ) (z u : ComplexEuclidean d) :
    AnalyticOnNhd ℂ (fun w : ℂ => normalizedBallFourier d (z + w • u)) Set.univ := by
  apply (Complex.analyticOnNhd_univ_iff_differentiable).mpr
  exact (normalizedBallFourier_differentiable d).comp
    ((differentiable_const z).add (differentiable_id.smul_const u))

theorem ballIndicator_comp_isometry {d : ℕ} (A : Euclidean d ≃ₗᵢ[ℝ] Euclidean d) :
    ballIndicator d ∘ A = ballIndicator d := by
  funext x
  simp only [Function.comp_apply, ballIndicator, physicalUnitBall, Set.indicator,
    mem_ball_zero_iff, A.norm_map]

theorem normalizedBallFourier_real_isometry {d : ℕ}
    (A : Euclidean d ≃ₗᵢ[ℝ] Euclidean d) (ξ : Euclidean d) :
    normalizedBallFourier d (realToComplex (A ξ)) =
      normalizedBallFourier d (realToComplex ξ) := by
  unfold normalizedBallFourier
  rw [entireFourier_realToComplex, entireFourier_realToComplex,
    ← Real.fourierIntegral_comp_linearIsometry A, ballIndicator_comp_isometry]

theorem ballIndicator_norm_integral (d : ℕ) : ∫ x, ‖ballIndicator d x‖ = ballVolume d := by
  have he : (fun x => ‖ballIndicator d x‖) =
      (physicalUnitBall d).indicator (fun _ => (1 : ℝ)) := by
    funext x
    by_cases hx : x ∈ physicalUnitBall d <;> simp [ballIndicator, hx]
  rw [he, integral_indicator (physicalUnitBall_measurable d)]
  simp [ballVolume, integral_const]

theorem normalizedBallFourier_real_norm_le (d : ℕ) (ξ : Euclidean d) :
    ‖normalizedBallFourier d (realToComplex ξ)‖ ≤ 1 := by
  rw [normalizedBallFourier, norm_div, Complex.norm_real,
    Real.norm_of_nonneg (ballVolume_pos d).le]
  apply (div_le_one (ballVolume_pos d)).mpr
  exact (entireFourier_real_norm_le (ballIndicator_integrable d) ξ).trans_eq
    (ballIndicator_norm_integral d)

theorem normalizedBallFourier_real_eq_of_norm_eq {d : ℕ} (ξ η : Euclidean d)
    (h : ‖ξ‖ = ‖η‖) :
    normalizedBallFourier d (realToComplex ξ) =
      normalizedBallFourier d (realToComplex η) := by
  have he := normalizedBallFourier_real_isometry (ℝ ∙ (ξ - η))ᗮ.reflection ξ
  rw [Submodule.reflection_sub h] at he
  exact he.symm

/-- A complex frequency on the first coordinate axis, with Fourier scaling removed. -/
def radialFrequency (n : ℕ) (s : ℂ) : ComplexEuclidean (n + 1) :=
  EuclideanSpace.single 0 (s / (2 * Real.pi : ℂ))

/-- The normalized ball transform in its scalar radial variable. -/
def radialBallFourier (n : ℕ) (s : ℂ) : ℂ :=
  normalizedBallFourier (n + 1) (radialFrequency n s)

theorem radialFrequency_eq_smul (n : ℕ) (s : ℂ) :
    radialFrequency n s = s • radialFrequency n 1 := by
  ext i
  simp [radialFrequency, EuclideanSpace.single_apply, PiLp.smul_apply,
    div_eq_mul_inv, smul_eq_mul]

@[simp]
theorem radialBallFourier_zero (n : ℕ) : radialBallFourier n 0 = 1 := by
  simp [radialBallFourier, radialFrequency, EuclideanSpace.single]

theorem radialBallFourier_analytic (n : ℕ) :
    AnalyticOnNhd ℂ (radialBallFourier n) Set.univ := by
  change AnalyticOnNhd ℂ (fun s => normalizedBallFourier (n + 1) (radialFrequency n s)) Set.univ
  have h := normalizedBallFourier_analyticAlongLine (n + 1) 0 (radialFrequency n 1)
  have he : (fun s => normalizedBallFourier (n + 1) (radialFrequency n s)) =
      (fun s => normalizedBallFourier (n + 1) (0 + s • radialFrequency n 1)) := by
    funext s
    rw [radialFrequency_eq_smul]
    simp
  rw [he]
  exact h

theorem realToComplex_single {d : ℕ} (i : Fin d) (s : ℝ) :
    realToComplex (EuclideanSpace.single i s) = EuclideanSpace.single i (s : ℂ) := by
  ext j
  by_cases hj : j = i <;> simp [EuclideanSpace.single_apply, hj]

/-- The real-frequency ball transform is genuinely radial, with the manuscript's `2π` scaling. -/
theorem normalizedBallFourier_real_radial (n : ℕ) (ξ : Euclidean (n + 1)) :
    normalizedBallFourier (n + 1) (realToComplex ξ) =
      radialBallFourier n (2 * Real.pi * ‖ξ‖ : ℝ) := by
  have h := normalizedBallFourier_real_eq_of_norm_eq ξ
    (EuclideanSpace.single 0 ‖ξ‖) (by simp)
  rw [realToComplex_single] at h
  convert h using 1
  simp [radialBallFourier, radialFrequency, Real.pi_ne_zero]

/-- Qualitative Fourier decay, without asserting a sharp Bessel asymptotic. -/
theorem normalizedBallFourier_real_tendsto_zero (d : ℕ) :
    Tendsto (fun ξ : Euclidean d => normalizedBallFourier d (realToComplex ξ))
      (cocompact (Euclidean d)) (𝓝 0) := by
  have h := (tendsto_integral_exp_inner_smul_cocompact
    (f := ballIndicator d)).div_const (ballVolume d : ℂ)
  simpa [normalizedBallFourier, entireFourier_realToComplex,
    Real.fourierIntegral_eq] using h

/-- On the complex radial line the zero set is locally finite. -/
theorem radialBallFourier_zeros_locallyFinite (n : ℕ) (z : ℂ) :
    ∃ U ∈ 𝓝 z, Set.Finite (U ∩ {s : ℂ | radialBallFourier n s = 0}) := by
  have h := (radialBallFourier_analytic n).eqOn_zero_or_eventually_ne_zero_of_preconnected
    isPreconnected_univ
  rcases h with hzero | hdiscrete
  · have h₀ := hzero (Set.mem_univ (0 : ℂ))
    simp at h₀
  · have hlocal := codiscreteWithin_iff_locallyFiniteComplementWithin.mp hdiscrete
      z (Set.mem_univ z)
    obtain ⟨U, hU, hfinite⟩ := hlocal
    refine ⟨U, hU, ?_⟩
    convert hfinite using 1
    ext s
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_diff, Set.mem_univ,
      true_and, not_not]

theorem fourierPhaseCLM_radialFrequency (n : ℕ) (x : Euclidean (n + 1)) (s : ℂ) :
    fourierPhaseCLM x (radialFrequency n s) = (-Complex.I * (x 0 : ℂ)) * s := by
  have hp : (2 * Real.pi : ℂ) ≠ 0 := by exact_mod_cast (mul_ne_zero (by norm_num) Real.pi_ne_zero)
  simp [fourierPhaseCLM, complexPairingCLM_apply, complexPairing, radialFrequency,
    EuclideanSpace.single_apply, Finset.mul_sum, Finset.sum_ite_eq', smul_eq_mul]
  field_simp
  ring

/-- A normalized coordinate moment giving a radial Taylor coefficient. -/
def radialBallMoment (n k : ℕ) : ℂ :=
  (∫ x in physicalUnitBall (n + 1), (-Complex.I * (x 0 : ℂ)) ^ k / (k.factorial : ℂ)) /
    (ballVolume (n + 1) : ℂ)

/-- The integrand of a radial Taylor term before integration over the ball. -/
def radialTaylorTerm (n : ℕ) (s : ℂ) (k : ℕ) (x : Euclidean (n + 1)) : ℂ :=
  ((-Complex.I * (x 0 : ℂ)) * s) ^ k / (k.factorial : ℂ)

theorem radialTaylorTerm_continuous (n : ℕ) (s : ℂ) (k : ℕ) :
    Continuous (radialTaylorTerm n s k) := by
  unfold radialTaylorTerm
  fun_prop

theorem radialTaylorTerm_norm_le (n : ℕ) (s : ℂ) (k : ℕ) (x : Euclidean (n + 1))
    (hx : x ∈ physicalUnitBall (n + 1)) :
    ‖radialTaylorTerm n s k x‖ ≤ ‖s‖ ^ k / (k.factorial : ℝ) := by
  have hxnorm : ‖x‖ ≤ 1 := (mem_ball_zero_iff.mp hx).le
  have hx₀ : ‖(-Complex.I * (x 0 : ℂ)) * s‖ ≤ ‖s‖ := by
    simp only [norm_mul, norm_neg, Complex.norm_I, one_mul, Complex.norm_real]
    exact (mul_le_mul_of_nonneg_right ((PiLp.norm_apply_le x 0).trans hxnorm)
      (norm_nonneg s)).trans_eq (one_mul _)
  unfold radialTaylorTerm
  simp only [norm_div, norm_pow, Complex.norm_natCast]
  exact div_le_div_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hx₀ k) (by positivity)

theorem radialBallMoment_norm_le (n k : ℕ) :
    ‖radialBallMoment n k‖ ≤ 1 / (k.factorial : ℝ) := by
  have hint : Integrable (fun _ : Euclidean (n + 1) => 1 / (k.factorial : ℝ))
      (volume.restrict (physicalUnitBall (n + 1))) :=
    integrableOn_const.mpr (Or.inr (physicalUnitBall_volume_lt_top (n + 1)))
  have hbound : ∀ᵐ x ∂volume.restrict (physicalUnitBall (n + 1)),
      ‖(-Complex.I * (x 0 : ℂ)) ^ k / (k.factorial : ℂ)‖ ≤ 1 / (k.factorial : ℝ) := by
    filter_upwards [ae_restrict_mem (physicalUnitBall_measurable (n + 1))] with x hx
    simpa [radialTaylorTerm] using radialTaylorTerm_norm_le n 1 k x hx
  have h := norm_integral_le_of_norm_le hint hbound
  rw [radialBallMoment, norm_div, Complex.norm_real,
    Real.norm_of_nonneg (ballVolume_pos (n + 1)).le]
  apply (div_le_iff₀ (ballVolume_pos (n + 1))).mpr
  simpa [integral_const, ballVolume, smul_eq_mul, mul_comm] using h

theorem radialTaylorBound_integrable (n : ℕ) (s : ℂ) :
    Integrable (fun _ : Euclidean (n + 1) => ∑' k : ℕ, ‖s‖ ^ k / (k.factorial : ℝ))
      (volume.restrict (physicalUnitBall (n + 1))) := by
  exact (integrableOn_const (C := ∑' k : ℕ, ‖s‖ ^ k / (k.factorial : ℝ))).mpr
    (Or.inr (physicalUnitBall_volume_lt_top (n + 1)))

theorem radialBallMoment_eq_zero_of_odd (n : ℕ) {k : ℕ} (hk : Odd k) :
    radialBallMoment n k = 0 := by
  let f : Euclidean (n + 1) → ℂ := fun x =>
    (-Complex.I * (x 0 : ℂ)) ^ k / (k.factorial : ℂ)
  let g := (physicalUnitBall (n + 1)).indicator f
  have hodd : (fun x => g (-x)) = (fun x => -g x) := by
    funext x
    have hneg : (-x) ∈ physicalUnitBall (n + 1) ↔ x ∈ physicalUnitBall (n + 1) := by
      simp [physicalUnitBall, mem_ball_zero_iff]
    by_cases hx : x ∈ physicalUnitBall (n + 1)
    · simp only [g, Set.indicator_of_mem hx, Set.indicator_of_mem (hneg.mpr hx)]
      dsimp [f]
      rw [Complex.ofReal_neg]
      have he : -Complex.I * -(x 0 : ℂ) = -(-Complex.I * (x 0 : ℂ)) := by ring
      rw [he, hk.neg_pow, neg_div]
    · simp [g, hx, hneg]
  have hi := integral_neg_eq_self g volume
  change (∫ x, g (-x)) = ∫ x, g x at hi
  rw [hodd, integral_neg] at hi
  have hz : (∫ x, g x) = 0 := by linear_combination -hi / 2
  rw [radialBallMoment, ← integral_indicator (physicalUnitBall_measurable (n + 1))]
  change (∫ x, g x) / (ballVolume (n + 1) : ℂ) = 0
  rw [hz, zero_div]

/-- Exact entire power series of the radial ball Fourier transform, with integral coefficients. -/
theorem radialBallFourier_hasSum (n : ℕ) (s : ℂ) :
    HasSum (fun k => radialBallMoment n k * s ^ k) (radialBallFourier n s) := by
  let F : ℕ → Euclidean (n + 1) → ℂ := radialTaylorTerm n s
  let bound : ℕ → Euclidean (n + 1) → ℝ := fun k _ => ‖s‖ ^ k / k.factorial
  have hmeas : ∀ k, AEStronglyMeasurable (F k) (volume.restrict (physicalUnitBall (n + 1))) := by
    intro k
    exact (radialTaylorTerm_continuous n s k).aestronglyMeasurable
  have hbound : ∀ k, ∀ᵐ x ∂volume.restrict (physicalUnitBall (n + 1)),
      ‖F k x‖ ≤ bound k x := by
    intro k
    filter_upwards [ae_restrict_mem (physicalUnitBall_measurable (n + 1))] with x hx
    exact radialTaylorTerm_norm_le n s k x hx
  have hsummable : ∀ᵐ x ∂volume.restrict (physicalUnitBall (n + 1)),
      Summable (fun k => bound k x) :=
    Eventually.of_forall fun _ => Real.summable_pow_div_factorial ‖s‖
  have hint : Integrable (fun x => ∑' k, bound k x)
      (volume.restrict (physicalUnitBall (n + 1))) := radialTaylorBound_integrable n s
  have hlim : ∀ᵐ x ∂volume.restrict (physicalUnitBall (n + 1)),
      HasSum (fun k => F k x) (complexFourierKernel x (radialFrequency n s)) := by
    filter_upwards with x
    rw [complexFourierKernel, fourierPhaseCLM_radialFrequency]
    simpa only [F, radialTaylorTerm, ← Complex.exp_eq_exp_ℂ] using
      NormedSpace.expSeries_div_hasSum_exp ℂ ((-Complex.I * (x 0 : ℂ)) * s)
  have h := (hasSum_integral_of_dominated_convergence bound hmeas hbound hsummable hint hlim).div_const
    (ballVolume (n + 1) : ℂ)
  rw [radialBallFourier, normalizedBallFourier_eq_setIntegral]
  convert h using 1
  funext k
  dsimp [F, radialTaylorTerm, radialBallMoment]
  simp_rw [mul_pow, mul_div_right_comm]
  rw [integral_mul_const]
  ring

theorem radialBallFourier_even (n : ℕ) (s : ℂ) :
    radialBallFourier n (-s) = radialBallFourier n s := by
  have he : ∀ k, radialBallMoment n k * (-s) ^ k = radialBallMoment n k * s ^ k := by
    intro k
    rcases Nat.even_or_odd k with hk | hk
    · rw [hk.neg_pow]
    · simp [radialBallMoment_eq_zero_of_odd n hk]
  exact ((radialBallFourier_hasSum n (-s)).congr_fun (fun k => (he k).symm)).unique
    (radialBallFourier_hasSum n s)

theorem radialBallFourier_hasSum_odd_zero (n : ℕ) (s : ℂ) :
    HasSum (fun k => radialBallMoment n (2 * k + 1) * s ^ (2 * k + 1)) 0 := by
  convert (hasSum_zero : HasSum (fun _ : ℕ => (0 : ℂ)) 0) using 1
  funext k
  rw [radialBallMoment_eq_zero_of_odd n (by exact ⟨k, by rw [two_mul]⟩), zero_mul]

/-- The radial transform's entire series is even, including in odd dimensions. -/
theorem radialBallFourier_hasSum_even (n : ℕ) (s : ℂ) :
    HasSum (fun k => radialBallMoment n (2 * k) * (s ^ 2) ^ k) (radialBallFourier n s) := by
  have hall := radialBallFourier_hasSum n s
  have hinj : Function.Injective (fun k : ℕ => 2 * k) :=
    mul_right_injective₀ (by norm_num : (2 : ℕ) ≠ 0)
  have hzero : ∀ k, k ∉ Set.range (fun j : ℕ => 2 * j) → radialBallMoment n k * s ^ k = 0 := by
    intro k hk
    rcases Nat.even_or_odd k with he | ho
    · obtain ⟨j, hj⟩ := he
      exact False.elim (hk ⟨j, by simpa only [two_mul] using hj.symm⟩)
    · rw [radialBallMoment_eq_zero_of_odd n ho, zero_mul]
  have h := (hinj.hasSum_iff hzero).mpr hall
  simpa only [Function.comp_def, pow_mul] using h

/-- The even radial Taylor series expressed in the squared radial variable. -/
def ballSquareSeries (n : ℕ) : FormalMultilinearSeries ℂ ℂ ℂ :=
  FormalMultilinearSeries.ofScalars ℂ (fun k => radialBallMoment n (2 * k))

/-- The even radial series is entire in the squared variable; no square-root branch is chosen. -/
theorem ballSquareSeries_radius (n : ℕ) : (ballSquareSeries n).radius = ⊤ := by
  apply FormalMultilinearSeries.radius_eq_top_of_summable_norm
  intro r
  apply Summable.of_nonneg_of_le (fun k => mul_nonneg (norm_nonneg _) (by positivity))
    (fun k => ?_) (Real.summable_pow_div_factorial (r : ℝ))
  rw [ballSquareSeries, FormalMultilinearSeries.ofScalars_norm]
  have hfactorial : (k.factorial : ℝ) ≤ (2 * k).factorial := by
    exact_mod_cast Nat.factorial_le (Nat.le_mul_of_pos_left k (by decide : 0 < 2))
  have h := (radialBallMoment_norm_le n (2 * k)).trans
    (one_div_le_one_div_of_le (by positivity : (0 : ℝ) < k.factorial) hfactorial)
  calc
    ‖radialBallMoment n (2 * k)‖ * (r : ℝ) ^ k ≤ (1 / (k.factorial : ℝ)) * (r : ℝ) ^ k :=
      mul_le_mul_of_nonneg_right h (by positivity)
    _ = _ := by ring

/-- The entire function of the squared radial variable defined by the ball series. -/
def ballSquareFunction (n : ℕ) : ℂ → ℂ := (ballSquareSeries n).sum

theorem ballSquareFunction_analytic (n : ℕ) : AnalyticOnNhd ℂ (ballSquareFunction n) Set.univ := by
  have hpos : 0 < (ballSquareSeries n).radius := by rw [ballSquareSeries_radius]; exact ENNReal.zero_lt_top
  have h := ((ballSquareSeries n).hasFPowerSeriesOnBall hpos).analyticOnNhd
  simpa [ballSquareFunction, ballSquareSeries_radius] using h

theorem radialBallFourier_eq_squareFunction (n : ℕ) (s : ℂ) :
    radialBallFourier n s = ballSquareFunction n (s ^ 2) := by
  rw [ballSquareFunction, ballSquareSeries, FormalMultilinearSeries.sum]
  simp only [FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul]
  exact (radialBallFourier_hasSum_even n s).tsum_eq.symm

/-- The complex quadratic form with the Fourier normalization factor. -/
def ballQuadraticForm (d : ℕ) (z : ComplexEuclidean d) : ℂ :=
  (2 * Real.pi : ℂ) ^ 2 * ∑ i, z i ^ 2

theorem ballQuadraticForm_differentiable (d : ℕ) :
    Differentiable ℂ (ballQuadraticForm d) := by
  change Differentiable ℂ (fun z : ComplexEuclidean d => (2 * Real.pi : ℂ) ^ 2 * ∑ i, z i ^ 2)
  apply Differentiable.const_mul (𝕜 := ℂ)
  apply Differentiable.sum
  intro i _
  have hproj : Differentiable ℂ (fun z : ComplexEuclidean d => z i) :=
    (PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin d => ℂ) i).differentiable
  exact hproj.pow 2

theorem ballQuadraticForm_realToComplex {d : ℕ} (ξ : Euclidean d) :
    ballQuadraticForm d (realToComplex ξ) = (2 * Real.pi * ‖ξ‖ : ℝ) ^ 2 := by
  have hnorm : (∑ i, ξ i ^ 2) = ‖ξ‖ ^ 2 := by
    simpa [Real.norm_eq_abs, sq_abs] using (PiLp.norm_sq_eq_of_L2 (fun _ : Fin d => ℝ) ξ).symm
  simp only [ballQuadraticForm, realToComplex_apply]
  norm_cast
  rw [hnorm]
  ring

theorem realToComplex_add_real_smul {d : ℕ} (x y : Euclidean d) (t : ℝ) :
    realToComplex (x + t • y) = realToComplex x + (t : ℂ) • realToComplex y := by
  ext i
  simp [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]

/-- The actual ball transform is given on all complex frequencies by the same even series.
The squares are complex squares; conjugation and square-root branches do not occur. -/
theorem normalizedBallFourier_eq_squareFunction (n : ℕ) (z : ComplexEuclidean (n + 1)) :
    normalizedBallFourier (n + 1) z = ballSquareFunction n (ballQuadraticForm (n + 1) z) := by
  let x : Euclidean (n + 1) := (WithLp.equiv 2 _).symm (fun i => (z i).re)
  let y : Euclidean (n + 1) := (WithLp.equiv 2 _).symm (fun i => (z i).im)
  let L : ℂ → ComplexEuclidean (n + 1) := fun w => realToComplex x + w • realToComplex y
  have hL : Differentiable ℂ L :=
    (differentiable_const _).add (differentiable_id.smul_const _)
  have hF : Differentiable ℂ (fun w => normalizedBallFourier (n + 1) (L w) -
      ballSquareFunction n (ballQuadraticForm (n + 1) (L w))) :=
    ((normalizedBallFourier_differentiable (n + 1)).comp hL).sub
      (((Complex.analyticOnNhd_univ_iff_differentiable).mp (ballSquareFunction_analytic n)).comp
        ((ballQuadraticForm_differentiable (n + 1)).comp hL))
  have hreal : ∀ t : ℝ, normalizedBallFourier (n + 1) (L t) -
      ballSquareFunction n (ballQuadraticForm (n + 1) (L t)) = 0 := by
    intro t
    have he : L t = realToComplex (x + t • y) := (realToComplex_add_real_smul x y t).symm
    rw [he, normalizedBallFourier_real_radial, radialBallFourier_eq_squareFunction,
      ballQuadraticForm_realToComplex, sub_self]
  have hz : L Complex.I = z := by
    ext i
    simp only [L, PiLp.add_apply, PiLp.smul_apply, realToComplex_apply, x, y,
      WithLp.equiv_symm_pi_apply, smul_eq_mul]
    apply Complex.ext <;> simp
  have h := entire_zero_of_real_zero _ hF hreal Complex.I
  rw [hz] at h
  exact sub_eq_zero.mp h

theorem integral_volumeIoiPow_eq (m : ℕ) (g : ℝ → ℝ) :
    (∫ r : Set.Ioi (0 : ℝ), g r ∂Measure.volumeIoiPow m) =
      ∫ r in Set.Ioi (0 : ℝ), r ^ m * g r := by
  simp only [Measure.volumeIoiPow, ENNReal.ofReal]
  rw [integral_withDensity_eq_integral_smul
    (measurable_subtype_coe.pow_const m).real_toNNReal,
    integral_subtype_comap measurableSet_Ioi (fun r : ℝ => Real.toNNReal (r ^ m) • g r)]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro r hr
  change Real.toNNReal (r ^ m) • g r = r ^ m * g r
  rw [NNReal.smul_def, Real.coe_toNNReal _ (pow_nonneg hr.le _), smul_eq_mul]

/-- A coordinate moment on the unit sphere with its polar measure. -/
def coordinateSphereMoment (n k : ℕ) : ℝ :=
  ∫ θ : Metric.sphere (0 : Euclidean (n + 1)) 1, (θ.val 0) ^ k
    ∂(volume : Measure (Euclidean (n + 1))).toSphere

/-- Full polar decomposition for one homogeneous coordinate moment and an arbitrary radial factor. -/
theorem coordinateMoment_polar (n k : ℕ) (g : ℝ → ℝ) :
    (∫ x : Euclidean (n + 1), (x 0) ^ k * g ‖x‖) =
      coordinateSphereMoment n k * (∫ r in Set.Ioi (0 : ℝ), r ^ (n + k) * g r) := by
  letI : IsLocallyFiniteMeasure ((volume : Measure (Euclidean (n + 1))).toSphere) :=
    IsFiniteMeasure.toIsLocallyFiniteMeasure _
  let H := homeomorphUnitSphereProd (Euclidean (n + 1))
  let F : Metric.sphere (0 : Euclidean (n + 1)) 1 × Set.Ioi (0 : ℝ) → ℝ :=
    fun u => (u.1.val 0) ^ k * ((u.2.val) ^ k * g u.2.val)
  have hcomp : ∀ x : ({(0 : Euclidean (n + 1))}ᶜ : Set (Euclidean (n + 1))),
      F (H x) = (x.val 0) ^ k * g ‖x.val‖ := by
    intro x
    have hx : ‖x.val‖ ≠ 0 := norm_ne_zero_iff.mpr x.prop
    simp only [F, H, homeomorphUnitSphereProd_apply_fst_coe,
      homeomorphUnitSphereProd_apply_snd_coe, PiLp.smul_apply, smul_eq_mul, mul_pow]
    field_simp
    ring
  calc
    _ = ∫ x : ({(0 : Euclidean (n + 1))}ᶜ : Set (Euclidean (n + 1))),
        (x.val 0) ^ k * g ‖x.val‖ ∂(volume.comap Subtype.val) := by
      rw [integral_subtype_comap (measurableSet_singleton _).compl
        (fun x : Euclidean (n + 1) => (x 0) ^ k * g ‖x‖),
        restrict_compl_singleton]
    _ = ∫ u, F u ∂(volume : Measure (Euclidean (n + 1))).toSphere.prod
        (Measure.volumeIoiPow n) := by
      have h := (volume : Measure (Euclidean (n + 1))).measurePreserving_homeomorphUnitSphereProd.integral_comp
        H.measurableEmbedding F
      simpa only [H, hcomp, finrank_euclideanSpace, Fintype.card_fin, Nat.add_sub_cancel] using h
    _ = coordinateSphereMoment n k *
        (∫ r : Set.Ioi (0 : ℝ), r.val ^ k * g r.val ∂Measure.volumeIoiPow n) := by
      exact integral_prod_mul (μ := (volume : Measure (Euclidean (n + 1))).toSphere)
        (ν := Measure.volumeIoiPow n)
        (fun θ : Metric.sphere (0 : Euclidean (n + 1)) 1 => (θ.val 0) ^ k)
        (fun r : Set.Ioi (0 : ℝ) => r.val ^ k * g r.val)
    _ = _ := by
      rw [integral_volumeIoiPow_eq n (fun r : ℝ => r ^ k * g r)]
      congr 1
      apply setIntegral_congr_fun measurableSet_Ioi
      intro r _
      change r ^ n * (r ^ k * g r) = r ^ (n + k) * g r
      rw [pow_add]
      ring

theorem gaussian_even_moment (k : ℕ) :
    (∫ x : ℝ, x ^ (2 * k) * Real.exp (-x ^ (2 : ℕ))) = Real.Gamma (k + 1 / 2 : ℝ) := by
  let f : ℝ → ℝ := fun x => x ^ (2 * k) * Real.exp (-x ^ (2 : ℕ))
  have hf : Integrable f := by
    simpa only [f, Real.rpow_natCast, neg_one_mul] using
      integrable_rpow_mul_exp_neg_mul_sq (b := 1) (s := (2 * k : ℕ))
        (by norm_num) (by exact lt_of_lt_of_le (by norm_num : (-1 : ℝ) < 0) (Nat.cast_nonneg _))
  have heven : Even (2 * k) := ⟨k, by rw [two_mul]⟩
  have he : (fun x => f (-x)) = f := by
    funext x
    simp only [f, heven.neg_pow, neg_sq]
  have hhalf : (∫ x in Set.Ioi (0 : ℝ), f x) = (1 / 2 : ℝ) * Real.Gamma (k + 1 / 2 : ℝ) := by
    have h := integral_rpow_mul_exp_neg_rpow (p := 2) (q := (2 * k : ℕ))
      (by norm_num) (by exact lt_of_lt_of_le (by norm_num : (-1 : ℝ) < 0) (Nat.cast_nonneg _))
    have harg : (((2 * k : ℕ) : ℝ) + 1) / 2 = k + 1 / 2 := by push_cast; ring
    simpa only [f, Real.rpow_natCast, Real.rpow_two, harg] using h
  have hneg := integral_comp_neg_Iic 0 f
  rw [he, neg_zero] at hneg
  change (∫ x, f x) = _
  rw [← integral_add_compl measurableSet_Ioi hf, Set.compl_Ioi, hneg, hhalf]
  ring

/-- A coordinate moment weighted by the standard radial Gaussian. -/
def gaussianCoordinateMoment (n k : ℕ) : ℝ :=
  ∫ x : Euclidean (n + 1), (x 0) ^ (2 * k) * Real.exp (-‖x‖ ^ (2 : ℕ))

theorem gaussianCoordinateMoment_eq (n k : ℕ) :
    gaussianCoordinateMoment n k = (Real.sqrt Real.pi) ^ n * Real.Gamma (k + 1 / 2 : ℝ) := by
  let f : Fin (n + 1) → ℝ → ℝ := fun i t =>
    if i = 0 then t ^ (2 * k) * Real.exp (-t ^ (2 : ℕ)) else Real.exp (-t ^ (2 : ℕ))
  have hprod : ∀ x : Euclidean (n + 1), ∏ i, f i (x i) =
      (x 0) ^ (2 * k) * Real.exp (-‖x‖ ^ (2 : ℕ)) := by
    intro x
    simp only [Fin.prod_univ_succ, f, if_pos rfl, Fin.succ_ne_zero, if_false, ite_true, ite_false]
    rw [← Real.exp_sum]
    have hnorm : ‖x‖ ^ (2 : ℕ) = ∑ i, (x i) ^ (2 : ℕ) := by
      simpa [Real.norm_eq_abs, sq_abs] using PiLp.norm_sq_eq_of_L2 (fun _ : Fin (n + 1) => ℝ) x
    rw [hnorm, Fin.sum_univ_succ]
    simp only [Finset.sum_neg_distrib]
    rw [neg_add, Real.exp_add]
    ring
  have hchange := (EuclideanSpace.volume_preserving_measurableEquiv (Fin (n + 1))).integral_comp
    (EuclideanSpace.measurableEquiv (Fin (n + 1))).measurableEmbedding
    (fun x : Fin (n + 1) → ℝ => ∏ i, f i (x i))
  have hchange' : gaussianCoordinateMoment n k =
      ∫ x : Fin (n + 1) → ℝ, ∏ i, f i (x i) := by
    simpa only [gaussianCoordinateMoment, EuclideanSpace.coe_measurableEquiv, hprod] using hchange
  rw [hchange', integral_fintype_prod_eq_prod, Fin.prod_univ_succ]
  simp only [f, if_pos rfl, Fin.succ_ne_zero, if_false, ite_true, ite_false]
  rw [gaussian_even_moment]
  have hgauss : (∫ x : ℝ, Real.exp (-x ^ (2 : ℕ))) = Real.sqrt Real.pi := by
    simpa only [neg_one_mul, div_one] using integral_gaussian (1 : ℝ)
  simp only [hgauss, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  ring

theorem gaussianCoordinateMoment_polar (n k : ℕ) :
    gaussianCoordinateMoment n k = coordinateSphereMoment n (2 * k) *
      ((1 / 2 : ℝ) * Real.Gamma ((n + 2 * k + 1 : ℕ) / 2 : ℝ)) := by
  rw [gaussianCoordinateMoment,
    coordinateMoment_polar n (2 * k) (fun r : ℝ => Real.exp (-r ^ (2 : ℕ)))]
  congr 1
  have h := integral_rpow_mul_exp_neg_rpow (p := 2) (q := (n + 2 * k : ℕ))
    (by norm_num) (by exact lt_of_lt_of_le (by norm_num : (-1 : ℝ) < 0) (Nat.cast_nonneg _))
  have harg : ((n + 2 * k + 1 : ℕ) : ℝ) = ((n + 2 * k : ℕ) : ℝ) + 1 := by
    push_cast
    ring
  rw [harg]
  simpa only [Real.rpow_natCast, Real.rpow_two] using h

/-- A coordinate moment over the physical unit ball. -/
def ballCoordinateMoment (n k : ℕ) : ℝ :=
  ∫ x in physicalUnitBall (n + 1), (x 0) ^ k

theorem ballCoordinateMoment_polar (n k : ℕ) :
    ballCoordinateMoment n k = coordinateSphereMoment n k / (n + k + 1 : ℕ) := by
  let g : ℝ → ℝ := (Set.Iio (1 : ℝ)).indicator (fun _ => 1)
  have hfun : (fun x : Euclidean (n + 1) => (x 0) ^ k * g ‖x‖) =
      (physicalUnitBall (n + 1)).indicator (fun x => (x 0) ^ k) := by
    funext x
    by_cases hx : ‖x‖ < 1 <;> simp [g, physicalUnitBall, Set.indicator, mem_ball_zero_iff, hx]
  have hrad : (∫ r in Set.Ioi (0 : ℝ), r ^ (n + k) * g r) = 1 / (n + k + 1 : ℕ) := by
    have hfunr : (fun r : ℝ => r ^ (n + k) * g r) =
        (Set.Iio (1 : ℝ)).indicator (fun r => r ^ (n + k)) := by
      funext r
      by_cases hr : r < 1 <;> simp [g, Set.indicator, hr]
    rw [hfunr, setIntegral_indicator measurableSet_Iio]
    have hint : Set.Ioi (0 : ℝ) ∩ Set.Iio 1 = Set.Ioo 0 1 := by ext r; simp
    rw [hint, ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one,
      integral_pow]
    simp
  have h := coordinateMoment_polar n k g
  rw [hfun, integral_indicator (physicalUnitBall_measurable (n + 1)), hrad] at h
  simpa only [ballCoordinateMoment, div_eq_mul_inv, one_mul] using h

/-- Evaluation of the even coordinate moments of the real Euclidean unit ball. -/
theorem ballCoordinateMoment_even_eq (n k : ℕ) :
    ballCoordinateMoment n (2 * k) = (Real.sqrt Real.pi) ^ n *
      Real.Gamma (k + 1 / 2 : ℝ) / Real.Gamma ((n + 2 * k + 3 : ℕ) / 2 : ℝ) := by
  let b : ℝ := (n + 2 * k + 1 : ℕ) / 2
  have hb : 0 < b := by dsimp [b]; positivity
  have harg : ((n + 2 * k + 3 : ℕ) : ℝ) / 2 = b + 1 := by dsimp [b]; push_cast; ring
  have hG : Real.Gamma (b + 1) ≠ 0 := (Real.Gamma_pos_of_pos (by positivity)).ne'
  have hA : coordinateSphereMoment n (2 * k) * Real.Gamma b =
      2 * ((Real.sqrt Real.pi) ^ n * Real.Gamma (k + 1 / 2 : ℝ)) := by
    have h := gaussianCoordinateMoment_polar n k
    rw [gaussianCoordinateMoment_eq] at h
    change _ = coordinateSphereMoment n (2 * k) * ((1 / 2 : ℝ) * Real.Gamma b) at h
    linarith
  rw [ballCoordinateMoment_polar, harg]
  apply (eq_div_iff hG).mpr
  rw [Real.Gamma_add_one hb.ne']
  dsimp [b]
  field_simp
  dsimp [b] at hA
  have hnum : ((k : ℝ) * 2 + 1) / 2 = (k : ℝ) + 1 / 2 := by ring
  rw [hnum]
  push_cast at hA
  nlinarith [hA]

theorem ballCoordinateMoment_even_recurrence (n k : ℕ) :
    ballCoordinateMoment n (2 * (k + 1)) =
      ((2 * k + 1 : ℕ) : ℝ) / (n + 2 * k + 3 : ℕ) * ballCoordinateMoment n (2 * k) := by
  rw [ballCoordinateMoment_even_eq, ballCoordinateMoment_even_eq]
  have ha : ((k + 1 : ℕ) : ℝ) + 1 / 2 = (k : ℝ) + 1 / 2 + 1 := by push_cast; ring
  have hb : ((n + 2 * (k + 1) + 3 : ℕ) : ℝ) / 2 =
      ((n + 2 * k + 3 : ℕ) : ℝ) / 2 + 1 := by push_cast; ring
  rw [ha, hb, Real.Gamma_add_one (by positivity : (k : ℝ) + 1 / 2 ≠ 0),
    Real.Gamma_add_one (by positivity : ((n + 2 * k + 3 : ℕ) : ℝ) / 2 ≠ 0)]
  field_simp
  ring

theorem radialBallMoment_even_eq_coordinateMoment (n k : ℕ) :
    radialBallMoment n (2 * k) = (-1 : ℂ) ^ k * (ballCoordinateMoment n (2 * k) : ℂ) /
      (((2 * k).factorial : ℂ) * (ballVolume (n + 1) : ℂ)) := by
  have hpow : (-Complex.I) ^ (2 * k) = (-1 : ℂ) ^ k := by
    rw [pow_mul]
    simp
  rw [radialBallMoment]
  simp_rw [mul_pow, hpow, integral_div, integral_const_mul, ← Complex.ofReal_pow,
    integral_complex_ofReal]
  rw [ballCoordinateMoment]
  ring

/-- The recurrence obtained from the actual ball moments, in the squared radial variable. -/
theorem radialBallMoment_even_recurrence (n k : ℕ) :
    radialBallMoment n (2 * (k + 1)) =
      -radialBallMoment n (2 * k) /
        ((2 : ℂ) * (k + 1 : ℕ) * (n + 2 * k + 3 : ℕ)) := by
  rw [radialBallMoment_even_eq_coordinateMoment, radialBallMoment_even_eq_coordinateMoment,
    ballCoordinateMoment_even_recurrence]
  rw [Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_natCast, Complex.ofReal_natCast,
    pow_succ]
  have hfac : (2 * (k + 1)).factorial = (2 * k + 2) * (2 * k + 1) * (2 * k).factorial := by
    have he : 2 * (k + 1) = 2 * k + 1 + 1 := by rw [Nat.mul_add, Nat.mul_one]
    rw [he, Nat.factorial_succ, Nat.factorial_succ]
    ring
  rw [hfac]
  have hv : (ballVolume (n + 1) : ℂ) ≠ 0 := by
    exact_mod_cast (ballVolume_pos (n + 1)).ne'
  have hf : ((2 * k).factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hk : (k : ℂ) + 1 ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero k)
  have hk' : 2 * (k : ℂ) + 1 ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (Nat.add_pos_right (2 * k) (by decide : 0 < 1)))
  have hk'' : 2 * (k : ℂ) + 2 ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (Nat.add_pos_right (2 * k) (by decide : 0 < 2))
  have hn : (n : ℂ) + 2 * k + 3 ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (Nat.add_pos_right (n + 2 * k) (by decide : 0 < 3))
  have hbig : (2 * (k : ℂ) + 2) * (2 * k + 1) * ((2 * k).factorial : ℂ) *
      (ballVolume (n + 1) : ℂ) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero hk'' hk') hf) hv
  push_cast
  field_simp [hv, hf, hk, hk', hk'', hn, hbig]
  ring

/-- The formal scalar derivative of a complex multilinear power series. -/
def scalarDerivativeSeries (p : FormalMultilinearSeries ℂ ℂ ℂ) :
    FormalMultilinearSeries ℂ ℂ ℂ :=
  (ContinuousLinearMap.apply ℂ ℂ (1 : ℂ)).compFormalMultilinearSeries p.derivSeries

theorem scalarDerivativeSeries_coeff (p : FormalMultilinearSeries ℂ ℂ ℂ) (k : ℕ) :
    (scalarDerivativeSeries p).coeff k = (k + 1 : ℕ) * p.coeff (k + 1) := by
  change p.derivSeries.coeff k 1 = _
  rw [FormalMultilinearSeries.derivSeries_coeff_one, nsmul_eq_mul]

theorem hasFPowerSeriesOnBall_deriv {f : ℂ → ℂ} {p : FormalMultilinearSeries ℂ ℂ ℂ}
    {x : ℂ} {r : ENNReal} (h : HasFPowerSeriesOnBall f p x r) :
    HasFPowerSeriesOnBall (deriv f) (scalarDerivativeSeries p) x r := by
  exact (ContinuousLinearMap.apply ℂ ℂ (1 : ℂ)).comp_hasFPowerSeriesOnBall h.fderiv

theorem ballSquareFunction_hasFPowerSeries (n : ℕ) :
    HasFPowerSeriesOnBall (ballSquareFunction n) (ballSquareSeries n) 0 ⊤ := by
  have hpos : 0 < (ballSquareSeries n).radius := by
    rw [ballSquareSeries_radius]
    exact ENNReal.zero_lt_top
  simpa only [ballSquareFunction, ballSquareSeries_radius] using
    (ballSquareSeries n).hasFPowerSeriesOnBall hpos

theorem ballSquareFunction_deriv_hasSum (n : ℕ) (z : ℂ) :
    HasSum (fun k => (k + 1 : ℕ) * radialBallMoment n (2 * (k + 1)) * z ^ k)
      (deriv (ballSquareFunction n) z) := by
  have h := (hasFPowerSeriesOnBall_deriv (ballSquareFunction_hasFPowerSeries n)).hasSum
    (y := z) (by simp)
  simpa only [zero_add, FormalMultilinearSeries.apply_eq_pow_smul_coeff,
    scalarDerivativeSeries_coeff, ballSquareSeries, FormalMultilinearSeries.coeff_ofScalars,
    smul_eq_mul, mul_comm] using h

theorem ballSquareFunction_deriv2_hasSum (n : ℕ) (z : ℂ) :
    HasSum (fun k => (k + 1 : ℕ) * (k + 2 : ℕ) *
      radialBallMoment n (2 * (k + 2)) * z ^ k)
      (deriv (deriv (ballSquareFunction n)) z) := by
  have h := (hasFPowerSeriesOnBall_deriv
    (hasFPowerSeriesOnBall_deriv (ballSquareFunction_hasFPowerSeries n))).hasSum
    (y := z) (by simp)
  convert h using 1
  · funext k
    rw [FormalMultilinearSeries.apply_eq_pow_smul_coeff, scalarDerivativeSeries_coeff,
      scalarDerivativeSeries_coeff]
    simp only [ballSquareSeries, FormalMultilinearSeries.coeff_ofScalars, smul_eq_mul]
    push_cast
    ring
  · simp

/-- The normalized ball transform solves the Bessel equation in the squared radial variable. -/
theorem ballSquareFunction_ode (n : ℕ) (z : ℂ) :
    4 * z * deriv (deriv (ballSquareFunction n)) z +
      2 * (n + 3 : ℕ) * deriv (ballSquareFunction n) z + ballSquareFunction n z = 0 := by
  let c : ℕ → ℂ := fun k => radialBallMoment n (2 * k)
  have hc : ∀ k : ℕ, (4 * k * (k + 1 : ℕ) + 2 * (n + 3 : ℕ) * (k + 1 : ℕ)) *
      c (k + 1) + c k = 0 := by
    intro k
    dsimp [c]
    rw [radialBallMoment_even_recurrence]
    have hk : (k : ℂ) + 1 ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero k)
    have hn : (n : ℂ) + 2 * k + 3 ≠ 0 := by
      exact_mod_cast Nat.ne_of_gt (Nat.add_pos_right (n + 2 * k) (by decide : 0 < 3))
    push_cast
    field_simp [hk, hn]
    ring
  let f : ℕ → ℂ := fun k => (k : ℂ) * (k + 1 : ℕ) * c (k + 1) * z ^ k
  have hshift : HasSum (fun k => f (k + 1)) (z * deriv (deriv (ballSquareFunction n)) z) := by
    convert (ballSquareFunction_deriv2_hasSum n z).mul_left z using 1
    funext k
    dsimp [f, c]
    have he : k + 1 + 1 = k + 2 := rfl
    rw [he, pow_succ]
    ring
  have hsecond : HasSum f (z * deriv (deriv (ballSquareFunction n)) z) := by
    have h := (hasSum_nat_add_iff 1).mp hshift
    simpa only [Finset.sum_range_one, f, Nat.cast_zero, zero_mul, add_zero] using h
  have hfirst := ballSquareFunction_deriv_hasSum n z
  have hzero := (ballSquareFunction_hasFPowerSeries n).hasSum (y := z) (by simp)
  have hsum := ((hsecond.mul_left (4 : ℂ)).add
    (hfirst.mul_left (2 * (n + 3 : ℕ) : ℂ))).add hzero
  have heq : ∀ k, 4 * f k + (2 * (n + 3 : ℕ) : ℂ) *
      ((k + 1 : ℕ) * radialBallMoment n (2 * (k + 1)) * z ^ k) +
      ballSquareSeries n k (fun _ => z) = 0 := by
    intro k
    rw [FormalMultilinearSeries.apply_eq_pow_smul_coeff]
    simp only [ballSquareSeries, FormalMultilinearSeries.coeff_ofScalars, smul_eq_mul]
    dsimp [f]
    have h := congrArg (fun w : ℂ => w * z ^ k) (hc k)
    dsimp [c] at h ⊢
    linear_combination h
  have h := hsum.congr_fun (fun k => (heq k).symm)
  have hz := h.unique (hasSum_zero : HasSum (fun _ : ℕ => (0 : ℂ)) 0)
  simpa only [zero_add, mul_assoc] using hz

theorem radialBallFourier_hasDerivAt (n : ℕ) (s : ℂ) :
    HasDerivAt (radialBallFourier n)
      (2 * s * deriv (ballSquareFunction n) (s ^ 2)) s := by
  have hf := ((ballSquareFunction_analytic n) (s ^ 2) (Set.mem_univ _)).differentiableAt.hasDerivAt
  have h := hf.comp s ((hasDerivAt_id s).pow 2)
  convert h using 1
  · funext z
    exact radialBallFourier_eq_squareFunction n z
  · simp only [Nat.cast_ofNat, pow_one, id_eq, Function.comp_apply]
    ring

theorem radialBallFourier_deriv (n : ℕ) (s : ℂ) :
    deriv (radialBallFourier n) s = 2 * s * deriv (ballSquareFunction n) (s ^ 2) :=
  (radialBallFourier_hasDerivAt n s).deriv

theorem radialBallFourier_deriv_hasDerivAt (n : ℕ) (s : ℂ) :
    HasDerivAt (deriv (radialBallFourier n))
      (2 * deriv (ballSquareFunction n) (s ^ 2) +
        4 * s ^ 2 * deriv (deriv (ballSquareFunction n)) (s ^ 2)) s := by
  have hf : AnalyticAt ℂ (deriv (ballSquareFunction n)) (s ^ 2) := by
    have h := (hasFPowerSeriesOnBall_deriv (ballSquareFunction_hasFPowerSeries n)).analyticOnNhd
    apply h
    simp
  have h := ((hasDerivAt_id s).const_mul (2 : ℂ)).mul
    (hf.differentiableAt.hasDerivAt.comp s ((hasDerivAt_id s).pow 2))
  convert h using 1
  · funext z
    exact radialBallFourier_deriv n z
  · simp only [Nat.cast_ofNat, pow_one, id_eq, Function.comp_apply]
    ring

theorem radialBallFourier_ode (n : ℕ) (s : ℂ) :
    s * deriv (deriv (radialBallFourier n)) s +
      (n + 2 : ℕ) * deriv (radialBallFourier n) s + s * radialBallFourier n s = 0 := by
  rw [(radialBallFourier_deriv_hasDerivAt n s).deriv, radialBallFourier_deriv,
    radialBallFourier_eq_squareFunction]
  have h := congrArg (fun w : ℂ => s * w) (ballSquareFunction_ode n (s ^ 2))
  push_cast at h ⊢
  linear_combination h

/-- The real restriction of the scalar radial ball transform. -/
def realRadialBallFourier (n : ℕ) (s : ℝ) : ℝ := (radialBallFourier n s).re

@[simp]
theorem realRadialBallFourier_zero (n : ℕ) : realRadialBallFourier n 0 = 1 := by
  simp [realRadialBallFourier]

theorem realRadialBallFourier_hasDerivAt (n : ℕ) (s : ℝ) :
    HasDerivAt (realRadialBallFourier n) (deriv (radialBallFourier n) s).re s := by
  exact ((radialBallFourier_analytic n) s (Set.mem_univ _)).differentiableAt.hasDerivAt.real_of_complex

theorem realRadialBallFourier_deriv (n : ℕ) (s : ℝ) :
    deriv (realRadialBallFourier n) s = (deriv (radialBallFourier n) s).re :=
  (realRadialBallFourier_hasDerivAt n s).deriv

theorem realRadialBallFourier_deriv_hasDerivAt (n : ℕ) (s : ℝ) :
    HasDerivAt (deriv (realRadialBallFourier n))
      (deriv (deriv (radialBallFourier n)) s).re s := by
  have h := (((radialBallFourier_analytic n).deriv) s (Set.mem_univ _)).differentiableAt.hasDerivAt.real_of_complex
  convert h using 1
  funext t
  exact realRadialBallFourier_deriv n t

theorem realRadialBallFourier_ode (n : ℕ) (s : ℝ) :
    s * deriv (deriv (realRadialBallFourier n)) s +
      (n + 2 : ℕ) * deriv (realRadialBallFourier n) s + s * realRadialBallFourier n s = 0 := by
  rw [(realRadialBallFourier_deriv_hasDerivAt n s).deriv, realRadialBallFourier_deriv]
  have h := congrArg Complex.re (radialBallFourier_ode n (s : ℂ))
  simpa only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.natCast_re, Complex.natCast_im, zero_mul, sub_zero, Complex.zero_re,
    realRadialBallFourier] using h

theorem radialBallFourier_ofReal_im (n : ℕ) (s : ℝ) :
    (radialBallFourier n s).im = 0 := by
  have h := Complex.hasSum_im (radialBallFourier_hasSum_even n (s : ℂ))
  have hz : ∀ k, (radialBallMoment n (2 * k) * ((s : ℂ) ^ 2) ^ k).im = 0 := by
    intro k
    have he : radialBallMoment n (2 * k) * ((s : ℂ) ^ 2) ^ k =
        ((((-1 : ℝ) ^ k * ballCoordinateMoment n (2 * k) /
          (((2 * k).factorial : ℝ) * ballVolume (n + 1))) * (s ^ (2 : ℕ)) ^ k : ℝ) : ℂ) := by
      rw [radialBallMoment_even_eq_coordinateMoment]
      push_cast
      rfl
    rw [he]
    rfl
  have h0 := h.congr_fun (fun k => (hz k).symm)
  exact h0.unique (hasSum_zero : HasSum (fun _ : ℕ => (0 : ℝ)) 0)

theorem radialBallFourier_ofReal_eq (n : ℕ) (s : ℝ) :
    radialBallFourier n s = (realRadialBallFourier n s : ℂ) := by
  apply Complex.ext
  · rfl
  · simp only [Complex.ofReal_im, radialBallFourier_ofReal_im]

theorem exists_pos_realRadialBallFourier_ne_zero (n : ℕ) :
    ∃ s : ℝ, 0 < s ∧ realRadialBallFourier n s ≠ 0 := by
  have h : ∀ᶠ s in 𝓝 (0 : ℝ), realRadialBallFourier n s ≠ 0 :=
    (realRadialBallFourier_hasDerivAt n 0).continuousAt.eventually_ne (by simp)
  obtain ⟨ε, hε, hsub⟩ := Metric.mem_nhds_iff.mp h
  refine ⟨ε / 2, by positivity, hsub ?_⟩
  simp only [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos (by positivity : 0 < ε / 2)]
  linarith

theorem exists_pos_le_realRadialBallFourier_ne_zero (n : ℕ) {b : ℝ} (hb : 0 < b) :
    ∃ s : ℝ, 0 < s ∧ s ≤ b ∧ realRadialBallFourier n s ≠ 0 := by
  have h : ∀ᶠ s in 𝓝 (0 : ℝ), realRadialBallFourier n s ≠ 0 :=
    (realRadialBallFourier_hasDerivAt n 0).continuousAt.eventually_ne (by simp)
  obtain ⟨ε, hε, hsub⟩ := Metric.mem_nhds_iff.mp h
  have hm : 0 < min ε b := lt_min hε hb
  refine ⟨min ε b / 2, by positivity, ?_, hsub ?_⟩
  · exact (by linarith : min ε b / 2 ≤ min ε b).trans (min_le_right _ _)
  · simp only [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos (by positivity : 0 < min ε b / 2)]
    have he := min_le_left ε b
    linarith

/-- The radial transform multiplied by its asymptotic power weight. -/
def weightedRadialBallFourier (n : ℕ) (s : ℝ) : ℝ :=
  s ^ ((n + 2 : ℕ) / 2 : ℝ) * realRadialBallFourier n s

/-- The derivative of the weighted radial transform on positive radii. -/
def weightedRadialBallFourierDeriv (n : ℕ) (s : ℝ) : ℝ :=
  ((n + 2 : ℕ) / 2 : ℝ) * s ^ (((n + 2 : ℕ) / 2 : ℝ) - 1) * realRadialBallFourier n s +
    s ^ ((n + 2 : ℕ) / 2 : ℝ) * deriv (realRadialBallFourier n) s

theorem weightedRadialBallFourier_hasDerivAt (n : ℕ) {s : ℝ} (hs : 0 < s) :
    HasDerivAt (weightedRadialBallFourier n) (weightedRadialBallFourierDeriv n s) s := by
  have h := (Real.hasDerivAt_rpow_const (p := ((n + 2 : ℕ) / 2 : ℝ)) (Or.inl hs.ne')).mul
    (realRadialBallFourier_hasDerivAt n s)
  simpa only [weightedRadialBallFourier, weightedRadialBallFourierDeriv,
    realRadialBallFourier_deriv] using h

/-- Conjugating the actual radial equation gives an oscillator with an inverse-square potential. -/
theorem weightedRadialBallFourierDeriv_hasDerivAt (n : ℕ) {s : ℝ} (hs : 0 < s) :
    HasDerivAt (weightedRadialBallFourierDeriv n)
      ((((n : ℝ) * (n + 2) / 4) / s ^ (2 : ℕ) - 1) * weightedRadialBallFourier n s) s := by
  let a : ℝ := (n + 2 : ℕ) / 2
  have hfirst := ((Real.hasDerivAt_rpow_const (p := a - 1) (Or.inl hs.ne')).const_mul a).mul
    (realRadialBallFourier_hasDerivAt n s)
  have hsecond := (Real.hasDerivAt_rpow_const (p := a) (Or.inl hs.ne')).mul
    (realRadialBallFourier_deriv_hasDerivAt n s)
  have h := hfirst.add hsecond
  convert h using 1
  rw [← realRadialBallFourier_deriv, ← (realRadialBallFourier_deriv_hasDerivAt n s).deriv]
  have hpa : s ^ a = s ^ (a - 2) * s ^ (2 : ℕ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hs]
    congr 1
    push_cast
    ring
  have hpa' : s ^ (a - 1) = s ^ (a - 2) * s := by
    calc
      s ^ (a - 1) = s ^ ((a - 2) + 1) := congrArg (fun t : ℝ => s ^ t) (by ring)
      _ = s ^ (a - 2) * s ^ (1 : ℝ) := Real.rpow_add hs _ _
      _ = _ := by rw [Real.rpow_one]
  have harg : a - 1 - 1 = a - 2 := by ring
  change (((n : ℝ) * (n + 2) / 4) / s ^ (2 : ℕ) - 1) *
        (s ^ a * realRadialBallFourier n s) =
      (a * ((a - 1) * s ^ (a - 1 - 1)) * realRadialBallFourier n s +
        a * s ^ (a - 1) * deriv (realRadialBallFourier n) s) +
        (a * s ^ (a - 1) * deriv (realRadialBallFourier n) s +
          s ^ a * deriv (deriv (realRadialBallFourier n)) s)
  rw [harg, hpa, hpa']
  have hode := realRadialBallFourier_ode n s
  have hc : (n : ℝ) * (n + 2) / 4 = a * (a - 1) := by dsimp [a]; push_cast; ring
  have hn : ((n + 2 : ℕ) : ℝ) = 2 * a := by dsimp [a]; ring
  rw [hc]
  rw [hn] at hode
  field_simp [hs.ne']
  linear_combination -(s ^ (a - 2) * s ^ (3 : ℕ)) * hode

theorem exists_pos_weightedRadialBallFourier_energy (n : ℕ) :
    ∃ s : ℝ, 0 < s ∧ 0 < (weightedRadialBallFourier n s) ^ (2 : ℕ) +
      (weightedRadialBallFourierDeriv n s) ^ (2 : ℕ) := by
  obtain ⟨s, hs, hk⟩ := exists_pos_realRadialBallFourier_ne_zero n
  have hh : weightedRadialBallFourier n s ≠ 0 :=
    mul_ne_zero (Real.rpow_pos_of_pos hs _).ne' hk
  exact ⟨s, hs, add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero hh) (sq_nonneg _)⟩

@[simp]
theorem radialBallMoment_zero (n : ℕ) : radialBallMoment n 0 = 1 := by
  have hv : (ballVolume (n + 1) : ℂ) ≠ 0 := by exact_mod_cast (ballVolume_pos (n + 1)).ne'
  unfold ballVolume at hv
  simp [radialBallMoment, integral_const, ballVolume, hv]

/-- Explicit Bessel-series coefficients, derived from ball integration and the Gamma recurrence. -/
theorem radialBallMoment_even_eq_gamma (n k : ℕ) :
    radialBallMoment n (2 * k) = (-1 : ℂ) ^ k *
      (Real.Gamma ((n + 3 : ℕ) / 2 : ℝ) : ℂ) /
      ((4 : ℂ) ^ k * (k.factorial : ℂ) *
        (Real.Gamma ((k : ℝ) + (n + 3 : ℕ) / 2) : ℂ)) := by
  let a : ℝ := (n + 3 : ℕ) / 2
  have hG : ∀ k : ℕ, (Real.Gamma ((k : ℝ) + a) : ℂ) ≠ 0 := by
    intro k
    exact_mod_cast (Real.Gamma_pos_of_pos (by positivity : 0 < (k : ℝ) + a)).ne'
  induction k with
  | zero =>
    simpa only [Nat.mul_zero, radialBallMoment_zero, pow_zero, Nat.factorial_zero,
      Nat.cast_one, Nat.cast_zero, Complex.ofReal_zero, zero_add, one_mul] using
      (div_self (hG 0)).symm
  | succ k ih =>
    change radialBallMoment n (2 * (k + 1)) = _
    rw [radialBallMoment_even_recurrence, ih, pow_succ, pow_succ, Nat.factorial_succ]
    have harg : ((k + 1 : ℕ) : ℝ) + (n + 3 : ℕ) / 2 = (k : ℝ) + a + 1 := by
      dsimp [a]
      push_cast
      ring
    rw [harg, Real.Gamma_add_one (by positivity : (k : ℝ) + a ≠ 0), Complex.ofReal_mul]
    push_cast
    field_simp [hG k]
    dsimp [a]
    push_cast
    ring

theorem radialBallFourier_hasSum_gamma (n : ℕ) (s : ℂ) :
    HasSum (fun k : ℕ => (-1 : ℂ) ^ k * (Real.Gamma ((n + 3 : ℕ) / 2 : ℝ) : ℂ) /
      ((4 : ℂ) ^ k * (k.factorial : ℂ) *
        (Real.Gamma ((k : ℝ) + (n + 3 : ℕ) / 2) : ℂ)) * (s ^ 2) ^ k)
      (radialBallFourier n s) := by
  simpa only [radialBallMoment_even_eq_gamma] using radialBallFourier_hasSum_even n s

end RieszEuclidean.CompleteMinimal
