import RieszEuclidean.CompleteMinimalBessel
import RieszEuclidean.CompleteMinimalPolynomialGrowth
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Topology.MetricSpace.HausdorffDistance

/-!
# Oscillator asymptotics for the normalized radial ball transform

The inverse-square perturbation of the harmonic oscillator has bounded energy
and convergent rotating coefficients. All conclusions are derived from its
actual differential equation.
-/

noncomputable section
open Set Filter
open scoped Topology

namespace RieszEuclidean.CompleteMinimal

/-- Harmonic-oscillator energy. -/
def oscillatorEnergy (h p : ℝ → ℝ) (s : ℝ) : ℝ := h s ^ 2 + p s ^ 2

/-- The cosine coefficient obtained by rotating the oscillator state. -/
def oscillatorCosCoefficient (h p : ℝ → ℝ) (s : ℝ) : ℝ :=
  h s * Real.cos s - p s * Real.sin s

/-- The sine coefficient obtained by rotating the oscillator state. -/
def oscillatorSinCoefficient (h p : ℝ → ℝ) (s : ℝ) : ℝ :=
  h s * Real.sin s + p s * Real.cos s

/-- Rotation preserves the oscillator energy. -/
theorem oscillator_coefficients_energy (h p : ℝ → ℝ) (s : ℝ) :
    oscillatorCosCoefficient h p s ^ 2 + oscillatorSinCoefficient h p s ^ 2 =
      oscillatorEnergy h p s := by
  dsimp [oscillatorCosCoefficient, oscillatorSinCoefficient, oscillatorEnergy]
  nlinarith [Real.sin_sq_add_cos_sq s]

/-- Reconstruction of the first oscillator coordinate. -/
theorem oscillator_reconstruct (h p : ℝ → ℝ) (s : ℝ) :
    h s = oscillatorCosCoefficient h p s * Real.cos s +
      oscillatorSinCoefficient h p s * Real.sin s ∧
    p s = -oscillatorCosCoefficient h p s * Real.sin s +
      oscillatorSinCoefficient h p s * Real.cos s := by
  dsimp [oscillatorCosCoefficient, oscillatorSinCoefficient]
  constructor
  · nlinarith [congrArg (fun t : ℝ => h s * t) (Real.sin_sq_add_cos_sq s)]
  · nlinarith [congrArg (fun t : ℝ => p s * t) (Real.sin_sq_add_cos_sq s)]

/-- The derivative of the energy follows from the exact inverse-square ODE. -/
theorem oscillatorEnergy_hasDerivAt {h p : ℝ → ℝ} {c s : ℝ}
    (hh : HasDerivAt h (p s) s) (hp : HasDerivAt p ((c / s ^ 2 - 1) * h s) s) :
    HasDerivAt (oscillatorEnergy h p) (2 * c / s ^ 2 * h s * p s) s := by
  convert (hh.pow 2).add (hp.pow 2) using 1
  dsimp [oscillatorEnergy]
  ring

/-- Variation of constants for the cosine coefficient. -/
theorem oscillatorCosCoefficient_hasDerivAt {h p : ℝ → ℝ} {c s : ℝ}
    (hh : HasDerivAt h (p s) s) (hp : HasDerivAt p ((c / s ^ 2 - 1) * h s) s) :
    HasDerivAt (oscillatorCosCoefficient h p) (-c / s ^ 2 * h s * Real.sin s) s := by
  convert (hh.mul (Real.hasDerivAt_cos s)).sub (hp.mul (Real.hasDerivAt_sin s)) using 1
  dsimp [oscillatorCosCoefficient]
  ring

/-- Variation of constants for the sine coefficient. -/
theorem oscillatorSinCoefficient_hasDerivAt {h p : ℝ → ℝ} {c s : ℝ}
    (hh : HasDerivAt h (p s) s) (hp : HasDerivAt p ((c / s ^ 2 - 1) * h s) s) :
    HasDerivAt (oscillatorSinCoefficient h p) (c / s ^ 2 * h s * Real.cos s) s := by
  convert (hh.mul (Real.hasDerivAt_sin s)).add (hp.mul (Real.hasDerivAt_cos s)) using 1
  dsimp [oscillatorSinCoefficient]
  ring

/-- The elementary reciprocal derivative used in the tail estimates. -/
theorem tail_reciprocal_hasDerivAt (C : ℝ) {s : ℝ} (hs : s ≠ 0) :
    HasDerivAt (fun t : ℝ => C / t) (-C / s ^ 2) s := by
  convert (hasDerivAt_const s C).div (hasDerivAt_id s) hs using 1
  simp

/-- An upper energy weight whose derivative is nonpositive. -/
theorem oscillator_upper_weight_hasDerivAt {h p : ℝ → ℝ} {c s : ℝ} (hs : s ≠ 0)
    (hh : HasDerivAt h (p s) s) (hp : HasDerivAt p ((c / s ^ 2 - 1) * h s) s) :
    HasDerivAt (fun t => oscillatorEnergy h p t * Real.exp (|c| / t))
      (Real.exp (|c| / s) / s ^ 2 *
        (2 * c * h s * p s - |c| * oscillatorEnergy h p s)) s := by
  convert (oscillatorEnergy_hasDerivAt hh hp).mul
    ((tail_reciprocal_hasDerivAt |c| hs).exp) using 1
  ring

/-- A lower energy weight whose derivative is nonnegative. -/
theorem oscillator_lower_weight_hasDerivAt {h p : ℝ → ℝ} {c s : ℝ} (hs : s ≠ 0)
    (hh : HasDerivAt h (p s) s) (hp : HasDerivAt p ((c / s ^ 2 - 1) * h s) s) :
    HasDerivAt (fun t => oscillatorEnergy h p t * Real.exp (-|c| / t))
      (Real.exp (-|c| / s) / s ^ 2 *
        (2 * c * h s * p s + |c| * oscillatorEnergy h p s)) s := by
  convert (oscillatorEnergy_hasDerivAt hh hp).mul
    ((tail_reciprocal_hasDerivAt (-|c|) hs).exp) using 1
  ring

/-- The quadratic energy controls its mixed product for either sign of the potential. -/
theorem oscillator_mixed_energy_bound (h p : ℝ → ℝ) (c s : ℝ) :
    |2 * c * h s * p s| ≤ |c| * oscillatorEnergy h p s := by
  rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  have hh := sq_abs (h s)
  have hp := sq_abs (p s)
  dsimp [oscillatorEnergy]
  nlinarith [abs_nonneg c, sq_nonneg (|h s| - |p s|)]

/-- Positive-tail ODE hypotheses produce monotone upper and lower energy weights. -/
theorem oscillator_weight_monotonicity {h p : ℝ → ℝ} {c a : ℝ} (ha : 0 < a)
    (hh : ∀ s ∈ Ici a, HasDerivAt h (p s) s)
    (hp : ∀ s ∈ Ici a, HasDerivAt p ((c / s ^ 2 - 1) * h s) s) :
    AntitoneOn (fun s => oscillatorEnergy h p s * Real.exp (|c| / s)) (Ici a) ∧
    MonotoneOn (fun s => oscillatorEnergy h p s * Real.exp (-|c| / s)) (Ici a) := by
  have hupper := fun s (hs : s ∈ Ici a) =>
    oscillator_upper_weight_hasDerivAt (ne_of_gt (ha.trans_le hs)) (hh s hs) (hp s hs)
  have hlower := fun s (hs : s ∈ Ici a) =>
    oscillator_lower_weight_hasDerivAt (ne_of_gt (ha.trans_le hs)) (hh s hs) (hp s hs)
  constructor
  · apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici a)
      (fun s hs => (hupper s hs).continuousAt.continuousWithinAt)
      (fun s hs => (hupper s (interior_subset hs)).hasDerivWithinAt)
    intro s hs
    apply mul_nonpos_of_nonneg_of_nonpos (by positivity)
    exact sub_nonpos.mpr ((le_abs_self _).trans (oscillator_mixed_energy_bound h p c s))
  · apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici a)
      (fun s hs => (hlower s hs).continuousAt.continuousWithinAt)
      (fun s hs => (hlower s (interior_subset hs)).hasDerivWithinAt)
    intro s hs
    apply mul_nonneg (by positivity)
    have hbound := oscillator_mixed_energy_bound h p c s
    have habs := neg_abs_le (2 * c * h s * p s)
    linarith

/-- Uniform upper energy and a strictly positive lower energy are consequences of the ODE. -/
theorem oscillator_energy_bounds {h p : ℝ → ℝ} {c a : ℝ} (ha : 0 < a)
    (hh : ∀ s ∈ Ici a, HasDerivAt h (p s) s)
    (hp : ∀ s ∈ Ici a, HasDerivAt p ((c / s ^ 2 - 1) * h s) s) (s : ℝ) (hs : a ≤ s) :
    oscillatorEnergy h p a * Real.exp (-|c| / a) ≤ oscillatorEnergy h p s ∧
    oscillatorEnergy h p s ≤ oscillatorEnergy h p a * Real.exp (|c| / a) := by
  obtain ⟨hu, hl⟩ := oscillator_weight_monotonicity ha hh hp
  have hE : 0 ≤ oscillatorEnergy h p s := add_nonneg (sq_nonneg _) (sq_nonneg _)
  constructor
  · apply (hl (mem_Ici.mpr le_rfl) hs hs).trans
    apply mul_le_of_le_one_right hE
    exact Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (abs_nonneg c))
      (ha.trans_le hs).le)
  · apply le_trans ?_ (hu (mem_Ici.mpr le_rfl) hs hs)
    apply le_mul_of_one_le_right hE
    exact Real.one_le_exp_iff.mpr (div_nonneg (abs_nonneg c) (ha.trans_le hs).le)

/-- A bounded scalar function with inverse-square derivative bound converges with
an explicit inverse-linear error. The proof uses monotone reciprocal corrections. -/
theorem inverse_square_derivative_asymptotic {f f' : ℝ → ℝ} {a C M : ℝ}
    (ha : 0 < a) (hC : 0 ≤ C) (hf : ∀ s ∈ Ici a, HasDerivAt f (f' s) s)
    (hbound : ∀ s ∈ Ici a, |f s| ≤ M)
    (hderiv : ∀ s ∈ Ici a, |f' s| ≤ C / s ^ 2) :
    ∃ L : ℝ, Tendsto f atTop (𝓝 L) ∧ ∀ s ∈ Ici a, |f s - L| ≤ C / s := by
  have hminus := fun s (hs : s ∈ Ici a) =>
    (hf s hs).sub (tail_reciprocal_hasDerivAt C (ne_of_gt (ha.trans_le hs)))
  have hplus := fun s (hs : s ∈ Ici a) =>
    (hf s hs).add (tail_reciprocal_hasDerivAt C (ne_of_gt (ha.trans_le hs)))
  have hm : MonotoneOn (fun s => f s - C / s) (Ici a) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici a)
      (fun s hs => (hminus s hs).continuousAt.continuousWithinAt)
      (fun s hs => (hminus s (interior_subset hs)).hasDerivWithinAt)
    intro s hs
    have hd := (abs_le.mp (hderiv s (interior_subset hs))).1
    simp only [neg_div] at *
    linarith
  have hp : AntitoneOn (fun s => f s + C / s) (Ici a) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici a)
      (fun s hs => (hplus s hs).continuousAt.continuousWithinAt)
      (fun s hs => (hplus s (interior_subset hs)).hasDerivWithinAt)
    intro s hs
    have hd := (abs_le.mp (hderiv s (interior_subset hs))).2
    simp only [neg_div] at *
    linarith
  let g : ℝ → ℝ := fun s => f (max a s) - C / max a s
  have hgmono : Monotone g := fun s t hst =>
    hm (mem_Ici.mpr (le_max_left a s)) (mem_Ici.mpr (le_max_left a t))
      (max_le_max le_rfl hst)
  have hgbdd : BddAbove (range g) := by
    refine ⟨M, ?_⟩
    rintro _ ⟨s, rfl⟩
    dsimp [g]
    have hd : 0 ≤ C / max a s := div_nonneg hC (ha.trans_le (le_max_left _ _)).le
    exact (sub_le_self _ hd).trans ((le_abs_self _).trans
      (hbound _ (mem_Ici.mpr (le_max_left a s))))
  let L : ℝ := ⨆ s, g s
  have hglim : Tendsto g atTop (𝓝 L) := tendsto_atTop_ciSup hgmono hgbdd
  have hmlim : Tendsto (fun s => f s - C / s) atTop (𝓝 L) := by
    apply hglim.congr'
    filter_upwards [eventually_ge_atTop a] with s hs
    simp only [g, max_eq_right hs]
  have hrecip : Tendsto (fun s : ℝ => C / s) atTop (𝓝 0) := tendsto_id.const_div_atTop C
  have hflim : Tendsto f atTop (𝓝 L) := by
    simpa only [sub_add_cancel, add_zero] using hmlim.add hrecip
  refine ⟨L, hflim, ?_⟩
  intro s hs
  have hlower : f s - C / s ≤ L := by
    apply ge_of_tendsto hmlim
    filter_upwards [eventually_ge_atTop s] with t ht
    exact hm hs (hs.trans ht) ht
  have hupper : L ≤ f s + C / s := by
    have hplim : Tendsto (fun t => f t + C / t) atTop (𝓝 L) := by
      simpa only [add_zero] using hflim.add hrecip
    apply le_of_tendsto hplim
    filter_upwards [eventually_ge_atTop s] with t ht
    exact hp hs (hs.trans ht) ht
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- The exact ODE bounds both coordinates of the oscillator state on its positive tail. -/
theorem oscillator_state_bounded {h p : ℝ → ℝ} {c a : ℝ} (ha : 0 < a)
    (hh : ∀ s ∈ Ici a, HasDerivAt h (p s) s)
    (hp : ∀ s ∈ Ici a, HasDerivAt p ((c / s ^ 2 - 1) * h s) s) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ s ∈ Ici a, |h s| ≤ M ∧ |p s| ≤ M := by
  let U := oscillatorEnergy h p a * Real.exp (|c| / a)
  have hU : 0 ≤ U := mul_nonneg (add_nonneg (sq_nonneg _) (sq_nonneg _)) (Real.exp_pos _).le
  refine ⟨U + 1, by positivity, ?_⟩
  intro s hs
  have hE := (oscillator_energy_bounds ha hh hp s hs).2
  change h s ^ 2 + p s ^ 2 ≤ U at hE
  constructor
  · nlinarith [sq_abs (h s), abs_nonneg (h s), sq_nonneg (p s), sq_nonneg (|h s| - 1)]
  · nlinarith [sq_abs (p s), abs_nonneg (p s), sq_nonneg (h s), sq_nonneg (|p s| - 1)]

/-- Both rotating coefficients have limits with inverse-linear errors. These limits
have nonzero energy whenever the original oscillator state is nonzero. -/
theorem oscillator_coefficient_asymptotics {h p : ℝ → ℝ} {c a : ℝ} (ha : 0 < a)
    (hh : ∀ s ∈ Ici a, HasDerivAt h (p s) s)
    (hp : ∀ s ∈ Ici a, HasDerivAt p ((c / s ^ 2 - 1) * h s) s)
    (hne : 0 < oscillatorEnergy h p a) :
    ∃ A B C : ℝ, 0 ≤ C ∧ 0 < A ^ 2 + B ^ 2 ∧
      Tendsto (oscillatorCosCoefficient h p) atTop (𝓝 A) ∧
      Tendsto (oscillatorSinCoefficient h p) atTop (𝓝 B) ∧
      ∀ s ∈ Ici a, |oscillatorCosCoefficient h p s - A| ≤ C / s ∧
        |oscillatorSinCoefficient h p s - B| ≤ C / s := by
  obtain ⟨M, hM, hstate⟩ := oscillator_state_bounded ha hh hp
  let C := |c| * M
  have hC : 0 ≤ C := mul_nonneg (abs_nonneg c) hM
  have hcos : ∀ s ∈ Ici a, |oscillatorCosCoefficient h p s| ≤ 2 * M := by
    intro s hs
    calc
      _ ≤ |h s * Real.cos s| + |p s * Real.sin s| := abs_sub _ _
      _ = |h s| * |Real.cos s| + |p s| * |Real.sin s| := by rw [abs_mul, abs_mul]
      _ ≤ M * 1 + M * 1 := by
        gcongr
        · exact (hstate s hs).1
        · exact Real.abs_cos_le_one s
        · exact (hstate s hs).2
        · exact Real.abs_sin_le_one s
      _ = _ := by ring
  have hsin : ∀ s ∈ Ici a, |oscillatorSinCoefficient h p s| ≤ 2 * M := by
    intro s hs
    calc
      _ ≤ |h s * Real.sin s| + |p s * Real.cos s| := abs_add _ _
      _ = |h s| * |Real.sin s| + |p s| * |Real.cos s| := by rw [abs_mul, abs_mul]
      _ ≤ M * 1 + M * 1 := by
        gcongr
        · exact (hstate s hs).1
        · exact Real.abs_sin_le_one s
        · exact (hstate s hs).2
        · exact Real.abs_cos_le_one s
      _ = _ := by ring
  have hcosderiv : ∀ s ∈ Ici a, |-c / s ^ 2 * h s * Real.sin s| ≤ C / s ^ 2 := by
    intro s hs
    rw [abs_mul, abs_mul, abs_div, abs_neg, abs_of_nonneg (sq_nonneg s)]
    calc
      _ ≤ (|c| / s ^ 2) * M * 1 := by
        gcongr
        · exact (hstate s hs).1
        · exact Real.abs_sin_le_one s
      _ = _ := by dsimp [C]; ring
  have hsinderiv : ∀ s ∈ Ici a, |c / s ^ 2 * h s * Real.cos s| ≤ C / s ^ 2 := by
    intro s hs
    rw [abs_mul, abs_mul, abs_div, abs_of_nonneg (sq_nonneg s)]
    calc
      _ ≤ (|c| / s ^ 2) * M * 1 := by
        gcongr
        · exact (hstate s hs).1
        · exact Real.abs_cos_le_one s
      _ = _ := by dsimp [C]; ring
  obtain ⟨A, hA, hAbound⟩ := inverse_square_derivative_asymptotic ha hC
    (fun s hs => oscillatorCosCoefficient_hasDerivAt (hh s hs) (hp s hs)) hcos hcosderiv
  obtain ⟨B, hB, hBbound⟩ := inverse_square_derivative_asymptotic ha hC
    (fun s hs => oscillatorSinCoefficient_hasDerivAt (hh s hs) (hp s hs)) hsin hsinderiv
  have henergy : Tendsto (fun s => oscillatorEnergy h p s) atTop (𝓝 (A ^ 2 + B ^ 2)) := by
    simpa only [oscillator_coefficients_energy] using (hA.pow 2).add (hB.pow 2)
  have hlower : oscillatorEnergy h p a * Real.exp (-|c| / a) ≤ A ^ 2 + B ^ 2 := by
    apply ge_of_tendsto henergy
    filter_upwards [eventually_ge_atTop a] with s hs
    exact (oscillator_energy_bounds ha hh hp s hs).1
  refine ⟨A, B, C, hC, (mul_pos hne (Real.exp_pos _)).trans_le hlower, hA, hB, ?_⟩
  intro s hs
  exact ⟨hAbound s hs, hBbound s hs⟩

/-- The nonzero solution of the inverse-square oscillator is asymptotic to a
nonzero harmonic oscillation, with an explicit `O(1/s)` error for both coordinates. -/
theorem inverse_square_oscillator_asymptotic {h p : ℝ → ℝ} {c a : ℝ} (ha : 0 < a)
    (hh : ∀ s ∈ Ici a, HasDerivAt h (p s) s)
    (hp : ∀ s ∈ Ici a, HasDerivAt p ((c / s ^ 2 - 1) * h s) s)
    (hne : 0 < oscillatorEnergy h p a) :
    ∃ A B C : ℝ, 0 < C ∧ 0 < A ^ 2 + B ^ 2 ∧ ∀ s ∈ Ici a,
      |h s - (A * Real.cos s + B * Real.sin s)| ≤ C / s ∧
      |p s - (-A * Real.sin s + B * Real.cos s)| ≤ C / s := by
  obtain ⟨A, B, C, hC, hne, _, _, hbound⟩ := oscillator_coefficient_asymptotics ha hh hp hne
  refine ⟨A, B, 2 * C + 1, by positivity, hne, ?_⟩
  intro s hs
  have hpos : 0 < s := ha.trans_le hs
  obtain ⟨hb₁, hb₂⟩ := hbound s hs
  obtain ⟨hr, pr⟩ := oscillator_reconstruct h p s
  have hcos := Real.abs_cos_le_one s
  have hsin := Real.abs_sin_le_one s
  constructor
  · calc
      _ = |(oscillatorCosCoefficient h p s - A) * Real.cos s +
          (oscillatorSinCoefficient h p s - B) * Real.sin s| := by rw [hr]; congr 1; ring
      _ ≤ |(oscillatorCosCoefficient h p s - A) * Real.cos s| +
          |(oscillatorSinCoefficient h p s - B) * Real.sin s| := abs_add _ _
      _ ≤ C / s * 1 + C / s * 1 := by rw [abs_mul, abs_mul]; gcongr
      _ ≤ (2 * C + 1) / s := by
        have := div_pos (by norm_num : (0 : ℝ) < 1) hpos
        linarith [show (2 * C + 1) / s = 2 * (C / s) + 1 / s by ring]
  · calc
      _ = |-(oscillatorCosCoefficient h p s - A) * Real.sin s +
          (oscillatorSinCoefficient h p s - B) * Real.cos s| := by rw [pr]; congr 1; ring
      _ ≤ |-(oscillatorCosCoefficient h p s - A) * Real.sin s| +
          |(oscillatorSinCoefficient h p s - B) * Real.cos s| := abs_add _ _
      _ ≤ C / s * 1 + C / s * 1 := by rw [abs_mul, abs_mul, abs_neg]; gcongr
      _ ≤ (2 * C + 1) / s := by
        have := div_pos (by norm_num : (0 : ℝ) < 1) hpos
        linarith [show (2 * C + 1) / s = 2 * (C / s) + 1 / s by ring]

/-- Every positive-tail zero is simple, with a uniform quantitative derivative lower bound. -/
theorem oscillator_derivative_lower_at_zeros {h p : ℝ → ℝ} {c a : ℝ} (ha : 0 < a)
    (hh : ∀ s ∈ Ici a, HasDerivAt h (p s) s)
    (hp : ∀ s ∈ Ici a, HasDerivAt p ((c / s ^ 2 - 1) * h s) s)
    (hne : 0 < oscillatorEnergy h p a) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ s ∈ Ici a, h s = 0 → δ ≤ |p s| := by
  let L := oscillatorEnergy h p a * Real.exp (-|c| / a)
  have hL : 0 < L := mul_pos hne (Real.exp_pos _)
  refine ⟨Real.sqrt L, Real.sqrt_pos.mpr hL, ?_⟩
  intro s hs hz
  apply Real.sqrt_le_iff.mpr
  refine ⟨abs_nonneg _, ?_⟩
  have henergy := (oscillator_energy_bounds ha hh hp s hs).1
  simpa only [oscillatorEnergy, hz, zero_pow (by norm_num : 2 ≠ 0), zero_add, sq_abs] using henergy

/-- The second coordinate also has a uniform derivative bound, directly from the ODE. -/
theorem oscillator_second_derivative_bounded {h p : ℝ → ℝ} {c a : ℝ} (ha : 0 < a)
    (hh : ∀ s ∈ Ici a, HasDerivAt h (p s) s)
    (hp : ∀ s ∈ Ici a, HasDerivAt p ((c / s ^ 2 - 1) * h s) s) :
    ∃ K : ℝ, 0 < K ∧ ∀ s ∈ Ici a, |(c / s ^ 2 - 1) * h s| ≤ K := by
  obtain ⟨M, hM, hstate⟩ := oscillator_state_bounded ha hh hp
  let K := (|c| / a ^ 2 + 1) * M + 1
  refine ⟨K, by dsimp [K]; positivity, ?_⟩
  intro s hs
  have hsq : a ^ 2 ≤ s ^ 2 := by
    have hsa : a ≤ s := hs
    nlinarith [ha.trans_le hsa]
  have hcoef : |c / s ^ 2 - 1| ≤ |c| / a ^ 2 + 1 := by
    calc
      _ ≤ |c / s ^ 2| + |(1 : ℝ)| := abs_sub _ _
      _ = |c| / s ^ 2 + 1 := by rw [abs_div, abs_of_nonneg (sq_nonneg s), abs_one]
      _ ≤ _ := by gcongr
  rw [abs_mul]
  have h := mul_le_mul hcoef (hstate s hs).1 (abs_nonneg _) (by positivity)
  dsimp [K]
  linarith

/-- Distinct zeros on the positive tail have a uniform positive separation. -/
theorem oscillator_zeros_separated {h p : ℝ → ℝ} {c a : ℝ} (ha : 0 < a)
    (hh : ∀ s ∈ Ici a, HasDerivAt h (p s) s)
    (hp : ∀ s ∈ Ici a, HasDerivAt p ((c / s ^ 2 - 1) * h s) s)
    (hne : 0 < oscillatorEnergy h p a) :
    ∃ η : ℝ, 0 < η ∧ ∀ x y : ℝ, a ≤ x → x < y → h x = 0 → h y = 0 → η ≤ y - x := by
  obtain ⟨δ, hδ, hlower⟩ := oscillator_derivative_lower_at_zeros ha hh hp hne
  obtain ⟨K, hK, hupper⟩ := oscillator_second_derivative_bounded ha hh hp
  refine ⟨δ / K, div_pos hδ hK, ?_⟩
  intro x y hx hxy hzx hzy
  have hcont : ContinuousOn h (Icc x y) := fun t ht =>
    (hh t (hx.trans ht.1)).continuousAt.continuousWithinAt
  obtain ⟨t, ht, hpt⟩ := exists_hasDerivAt_eq_zero hxy hcont (hzx.trans hzy.symm)
    (fun t ht => hh t (hx.trans ht.1.le))
  have hmean := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun s (hs : s ∈ Ici a) => (hp s hs).hasDerivWithinAt)
    (fun s (hs : s ∈ Ici a) => by simpa only [Real.norm_eq_abs] using hupper s hs)
    (convex_Ici a) hx (hx.trans ht.1.le)
  rw [hpt, zero_sub, norm_neg, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_pos (sub_pos.mpr ht.1)] at hmean
  apply (div_le_iff₀ hK).mpr
  calc
    δ ≤ |p x| := hlower x hx hzx
    _ ≤ K * (t - x) := hmean
    _ ≤ (y - x) * K := by nlinarith [ht.2]

/-- A state nonzero at one positive point is nonzero at every positive point.
The same weighted estimates propagate positivity backward as well as forward. -/
theorem oscillator_energy_positive {h p : ℝ → ℝ} {c a : ℝ} (ha : 0 < a)
    (hh : ∀ s : ℝ, 0 < s → HasDerivAt h (p s) s)
    (hp : ∀ s : ℝ, 0 < s → HasDerivAt p ((c / s ^ 2 - 1) * h s) s)
    (hne : 0 < oscillatorEnergy h p a) (s : ℝ) (hs : 0 < s) :
    0 < oscillatorEnergy h p s := by
  by_cases has : a ≤ s
  · exact (mul_pos hne (Real.exp_pos _)).trans_le
      (oscillator_energy_bounds ha (fun t ht => hh t (ha.trans_le ht))
        (fun t ht => hp t (ha.trans_le ht)) s has).1
  · have hsa : s ≤ a := (lt_of_not_ge has).le
    have hbound := (oscillator_energy_bounds hs (fun t ht => hh t (hs.trans_le ht))
      (fun t ht => hp t (hs.trans_le ht)) a hsa).2
    by_contra hbad
    have hE : 0 ≤ oscillatorEnergy h p s := add_nonneg (sq_nonneg _) (sq_nonneg _)
    have hzero : oscillatorEnergy h p s = 0 := le_antisymm (le_of_not_gt hbad) hE
    rw [hzero, zero_mul] at hbound
    exact (not_le_of_gt hne) hbound

/-- The actual weighted ball transform has strictly positive energy at every positive radius. -/
theorem weightedRadialBallFourier_energy_pos (n : ℕ) {s : ℝ} (hs : 0 < s) :
    0 < oscillatorEnergy (weightedRadialBallFourier n) (weightedRadialBallFourierDeriv n) s := by
  obtain ⟨a, ha, hne⟩ := exists_pos_weightedRadialBallFourier_energy n
  exact oscillator_energy_positive ha (fun _ ht => weightedRadialBallFourier_hasDerivAt n ht)
    (fun _ ht => weightedRadialBallFourierDeriv_hasDerivAt n ht) hne s hs

/-- The actual ball-transform ODE produces a nonzero harmonic asymptotic, including
its differentiated weighted state, without any asymptotic assumption. -/
theorem weightedRadialBallFourier_asymptotic (n : ℕ) :
    ∃ a A B C : ℝ, 0 < a ∧ 0 < C ∧ 0 < A ^ 2 + B ^ 2 ∧ ∀ s : ℝ, a ≤ s →
      |weightedRadialBallFourier n s - (A * Real.cos s + B * Real.sin s)| ≤ C / s ∧
      |weightedRadialBallFourierDeriv n s - (-A * Real.sin s + B * Real.cos s)| ≤ C / s := by
  obtain ⟨a, ha, hne⟩ := exists_pos_weightedRadialBallFourier_energy n
  obtain ⟨A, B, C, hC, hAB, hbound⟩ := inverse_square_oscillator_asymptotic ha
    (fun _ ht => weightedRadialBallFourier_hasDerivAt n (ha.trans_le ht))
    (fun _ ht => weightedRadialBallFourierDeriv_hasDerivAt n (ha.trans_le ht)) hne
  exact ⟨a, A, B, C, ha, hC, hAB, hbound⟩

/-- Every positive real zero of the actual normalized ball transform is simple. -/
theorem realRadialBallFourier_deriv_ne_zero_at_zero (n : ℕ) {s : ℝ} (hs : 0 < s)
    (hz : realRadialBallFourier n s = 0) : deriv (realRadialBallFourier n) s ≠ 0 := by
  intro hderiv
  have henergy := weightedRadialBallFourier_energy_pos n hs
  simp only [oscillatorEnergy, weightedRadialBallFourier, weightedRadialBallFourierDeriv,
    hz, hderiv, mul_zero, zero_add, zero_pow (by norm_num : 2 ≠ 0)] at henergy
  exact (lt_irrefl 0) henergy

/-- The derivative at the actual positive ball-transform zeros has a uniform
weighted lower bound on each positive tail. -/
theorem realRadialBallFourier_derivative_lower_at_zeros (n : ℕ) {a : ℝ} (ha : 0 < a) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ s : ℝ, a ≤ s → realRadialBallFourier n s = 0 →
      δ ≤ s ^ ((n + 2 : ℕ) / 2 : ℝ) * |deriv (realRadialBallFourier n) s| := by
  obtain ⟨δ, hδ, hbound⟩ := oscillator_derivative_lower_at_zeros ha
    (fun _ ht => weightedRadialBallFourier_hasDerivAt n (ha.trans_le ht))
    (fun _ ht => weightedRadialBallFourierDeriv_hasDerivAt n (ha.trans_le ht))
    (weightedRadialBallFourier_energy_pos n ha)
  refine ⟨δ, hδ, ?_⟩
  intro s hs hz
  have h := hbound s hs (by simp only [weightedRadialBallFourier, hz, mul_zero])
  simpa only [weightedRadialBallFourierDeriv, hz, mul_zero, zero_add, abs_mul,
    abs_of_pos (Real.rpow_pos_of_pos (ha.trans_le hs) _)] using h

/-- The actual positive real zeros have a uniform minimum separation on each tail. -/
theorem realRadialBallFourier_zeros_separated (n : ℕ) {a : ℝ} (ha : 0 < a) :
    ∃ η : ℝ, 0 < η ∧ ∀ x y : ℝ, a ≤ x → x < y →
      realRadialBallFourier n x = 0 → realRadialBallFourier n y = 0 → η ≤ y - x := by
  obtain ⟨η, hη, hgap⟩ := oscillator_zeros_separated ha
    (fun _ ht => weightedRadialBallFourier_hasDerivAt n (ha.trans_le ht))
    (fun _ ht => weightedRadialBallFourierDeriv_hasDerivAt n (ha.trans_le ht))
    (weightedRadialBallFourier_energy_pos n ha)
  refine ⟨η, hη, ?_⟩
  intro x y hx hxy hzx hzy
  exact hgap x y hx hxy (by simp only [weightedRadialBallFourier, hzx, mul_zero])
    (by simp only [weightedRadialBallFourier, hzy, mul_zero])

/-- The normalized ball transform has its true dimension-dependent polynomial decay. -/
theorem realRadialBallFourier_decay (n : ℕ) {a : ℝ} (ha : 0 < a) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ s : ℝ, a ≤ s →
      |realRadialBallFourier n s| ≤ M * s ^ (-((n + 2 : ℕ) / 2 : ℝ)) := by
  obtain ⟨M, hM, hstate⟩ := oscillator_state_bounded ha
    (fun _ ht => weightedRadialBallFourier_hasDerivAt n (ha.trans_le ht))
    (fun _ ht => weightedRadialBallFourierDeriv_hasDerivAt n (ha.trans_le ht))
  refine ⟨M, hM, ?_⟩
  intro s hs
  have hpos := ha.trans_le hs
  have hp := Real.rpow_pos_of_pos hpos ((n + 2 : ℕ) / 2 : ℝ)
  have h := (hstate s hs).1
  rw [weightedRadialBallFourier, abs_mul, abs_of_pos hp] at h
  rw [Real.rpow_neg hpos.le]
  calc
    _ = (s ^ ((n + 2 : ℕ) / 2 : ℝ) * |realRadialBallFourier n s|) *
        (s ^ ((n + 2 : ℕ) / 2 : ℝ))⁻¹ := by field_simp
    _ ≤ M * (s ^ ((n + 2 : ℕ) / 2 : ℝ))⁻¹ := mul_le_mul_of_nonneg_right h (inv_nonneg.mpr hp.le)

/-- A nonzero harmonic combination has periodically recurring positive and negative extrema. -/
theorem harmonic_oscillation_phase {A B : ℝ} (hne : 0 < A ^ 2 + B ^ 2) :
    ∃ θ D : ℝ, 0 < D ∧ ∀ n : ℕ,
      A * Real.cos (θ + n * (2 * Real.pi)) + B * Real.sin (θ + n * (2 * Real.pi)) = D ∧
      A * Real.cos (θ + n * (2 * Real.pi) + Real.pi) +
        B * Real.sin (θ + n * (2 * Real.pi) + Real.pi) = -D := by
  let z : ℂ := A + B * Complex.I
  have hz : z ≠ 0 := by
    intro hz
    have hA := congrArg Complex.re hz
    have hB := congrArg Complex.im hz
    simp only [z, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero, Complex.zero_re,
      Complex.add_im, Complex.mul_im, mul_one, zero_add, Complex.zero_im] at hA hB
    nlinarith
  let θ := z.arg
  let D := ‖z‖
  have hD : 0 < D := norm_pos_iff.mpr hz
  have hcos : D * Real.cos θ = A := by simp [D, θ, Complex.norm_mul_cos_arg, z]
  have hsin : D * Real.sin θ = B := by simp [D, θ, Complex.norm_mul_sin_arg, z]
  have hvalue : A * Real.cos θ + B * Real.sin θ = D := by
    rw [← hcos, ← hsin]
    nlinarith [congrArg (fun t : ℝ => D * t) (Real.sin_sq_add_cos_sq θ)]
  refine ⟨θ, D, hD, ?_⟩
  intro n
  constructor
  · simpa only [Real.cos_add_nat_mul_two_pi, Real.sin_add_nat_mul_two_pi] using hvalue
  · simp only [Real.cos_add_pi, Real.sin_add_pi, Real.cos_add_nat_mul_two_pi,
      Real.sin_add_nat_mul_two_pi]
    linarith

/-- A nonzero inverse-square oscillator has zeros beyond every real threshold. -/
theorem inverse_square_oscillator_zeros_unbounded {h p : ℝ → ℝ} {c a : ℝ} (ha : 0 < a)
    (hh : ∀ s ∈ Ici a, HasDerivAt h (p s) s)
    (hp : ∀ s ∈ Ici a, HasDerivAt p ((c / s ^ 2 - 1) * h s) s)
    (hne : 0 < oscillatorEnergy h p a) (R : ℝ) :
    ∃ s : ℝ, R < s ∧ a ≤ s ∧ h s = 0 := by
  obtain ⟨A, B, C, hC, hAB, hbound⟩ := inverse_square_oscillator_asymptotic ha hh hp hne
  obtain ⟨θ, D, hD, hphase⟩ := harmonic_oscillation_phase hAB
  let T := max a (max R (C / D)) + 1
  obtain ⟨n, hn⟩ := exists_nat_gt ((T - θ) / (2 * Real.pi))
  let x := θ + n * (2 * Real.pi)
  let y := x + Real.pi
  have hxT : T < x := by
    have hn := (div_lt_iff₀ (by positivity : 0 < 2 * Real.pi)).mp hn
    dsimp [x]
    linarith
  have hmax : max a (max R (C / D)) < x := (lt_add_one _).trans hxT
  have hxa : a ≤ x := (le_max_left a (max R (C / D))).trans hmax.le
  have hxR : R < x :=
    ((le_max_left R (C / D)).trans (le_max_right a (max R (C / D)))).trans_lt hmax
  have hxCD : C / D < x :=
    ((le_max_right R (C / D)).trans (le_max_right a (max R (C / D)))).trans_lt hmax
  have hxy : x < y := by dsimp [y]; linarith [Real.pi_pos]
  have hxpos := ha.trans_le hxa
  have hypos := hxpos.trans hxy
  have hcx : C / x < D := by
    apply (div_lt_iff₀ hxpos).mpr
    have h := (div_lt_iff₀ hD).mp hxCD
    nlinarith
  have hcy : C / y < D := by
    apply (div_lt_iff₀ hypos).mpr
    have h := (div_lt_iff₀ hD).mp (hxCD.trans hxy)
    nlinarith
  have hxerr := (hbound x hxa).1
  have hyerr := (hbound y (hxa.trans hxy.le)).1
  rw [(hphase n).1] at hxerr
  change |h y - (A * Real.cos (θ + n * (2 * Real.pi) + Real.pi) +
    B * Real.sin (θ + n * (2 * Real.pi) + Real.pi))| ≤ C / y at hyerr
  rw [(hphase n).2] at hyerr
  have hxsign : 0 < h x := by have := (abs_le.mp hxerr).1; linarith
  have hysign : h y < 0 := by have := (abs_le.mp hyerr).2; linarith
  have hcont : ContinuousOn h (Icc x y) := fun t ht =>
    (hh t (hxa.trans ht.1)).continuousAt.continuousWithinAt
  obtain ⟨s, hs, hz⟩ := intermediate_value_Icc' hxy.le hcont ⟨hysign.le, hxsign.le⟩
  exact ⟨s, hxR.trans_le hs.1, hxa.trans hs.1, hz⟩

/-- The actual normalized ball transform has positive real zeros arbitrarily far out. -/
theorem realRadialBallFourier_zeros_unbounded (n : ℕ) (R : ℝ) :
    ∃ s : ℝ, max 0 R < s ∧ realRadialBallFourier n s = 0 := by
  obtain ⟨a, ha, hne⟩ := exists_pos_weightedRadialBallFourier_energy n
  obtain ⟨s, hs, hsa, hz⟩ := inverse_square_oscillator_zeros_unbounded ha
    (fun _ ht => weightedRadialBallFourier_hasDerivAt n (ha.trans_le ht))
    (fun _ ht => weightedRadialBallFourierDeriv_hasDerivAt n (ha.trans_le ht)) hne (max 0 R)
  have hpos : 0 < s := (le_max_left 0 R).trans_lt hs
  refine ⟨s, hs, ?_⟩
  exact (mul_eq_zero.mp hz).resolve_left (Real.rpow_pos_of_pos hpos _).ne'

/-- Fixed-width recurring intervals on which the normalized oscillator is bounded away
from zero. Both the width and the lower bound are uniform. -/
theorem inverse_square_oscillator_recurring_intervals {h p : ℝ → ℝ} {c a : ℝ} (ha : 0 < a)
    (hh : ∀ s ∈ Ici a, HasDerivAt h (p s) s)
    (hp : ∀ s ∈ Ici a, HasDerivAt p ((c / s ^ 2 - 1) * h s) s)
    (hne : 0 < oscillatorEnergy h p a) :
    ∃ δ η : ℝ, ∃ q : ℕ → ℝ, 0 < δ ∧ 0 < η ∧
      (∀ k, a ≤ q k) ∧ (∀ k, q k + δ ≤ q (k + 1)) ∧
      (∀ R : ℝ, ∃ k, R ≤ q k) ∧
      ∀ k t, t ∈ Ioc (q k) (q k + δ) → η ≤ |h t| := by
  obtain ⟨A, B, C, hC, hAB, hbound⟩ := inverse_square_oscillator_asymptotic ha hh hp hne
  obtain ⟨θ, D, hD, hphase⟩ := harmonic_oscillation_phase hAB
  obtain ⟨M, hM, hstate⟩ := oscillator_state_bounded ha hh hp
  let δ := min Real.pi (D / (4 * (M + 1)))
  have hδ : 0 < δ := lt_min Real.pi_pos (div_pos hD (by positivity))
  have hδpi : δ ≤ Real.pi := min_le_left _ _
  have hδD : δ * (4 * (M + 1)) ≤ D :=
    (le_div_iff₀ (by positivity : 0 < 4 * (M + 1))).mp (min_le_right _ _)
  let T := max a (2 * C / D) + 1
  obtain ⟨N, hN⟩ := exists_nat_gt ((T - θ) / (2 * Real.pi))
  let q : ℕ → ℝ := fun k => θ + ((k + N : ℕ) : ℝ) * (2 * Real.pi)
  have hbase : T < q 0 := by
    have hN := (div_lt_iff₀ (by positivity : 0 < 2 * Real.pi)).mp hN
    dsimp [q]
    push_cast
    linarith
  have hqmono : Monotone q := by
    intro k j hkj
    dsimp [q]
    gcongr
  have hqT : ∀ k, T < q k := fun k => hbase.trans_le (hqmono (Nat.zero_le k))
  have hqa : ∀ k, a ≤ q k := fun k =>
    (le_max_left a (2 * C / D)).trans ((lt_add_one _).trans (hqT k)).le
  have hqC : ∀ k, 2 * C / D < q k := fun k =>
    (le_max_right a (2 * C / D)).trans_lt ((lt_add_one _).trans (hqT k))
  refine ⟨δ, D / 4, q, hδ, by positivity, hqa, ?_, ?_, ?_⟩
  · intro k
    dsimp [q]
    push_cast
    nlinarith [Real.pi_pos]
  · intro R
    obtain ⟨k, hk⟩ := exists_nat_gt ((R - θ) / (2 * Real.pi))
    refine ⟨k, ?_⟩
    have hk := (div_lt_iff₀ (by positivity : 0 < 2 * Real.pi)).mp hk
    dsimp [q]
    push_cast
    nlinarith [Real.pi_pos]
  · intro k t ht
    have hcenter := (hbound (q k) (hqa k)).1
    rw [(hphase (k + N)).1] at hcenter
    have hqpos := ha.trans_le (hqa k)
    have hsmall : C / q k < D / 2 := by
      have hc := (div_lt_iff₀ hD).mp (hqC k)
      apply (div_lt_iff₀ hqpos).mpr
      calc
        C = (2 * C) / 2 := by ring
        _ < (q k * D) / 2 := div_lt_div_of_pos_right hc (by norm_num)
        _ = D / 2 * q k := by ring
    have hcenterpos : D / 2 ≤ h (q k) := by
      have := (abs_le.mp hcenter).1
      linarith
    have hmean := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun s (hs : s ∈ Ici a) => (hh s hs).hasDerivWithinAt)
      (fun s (hs : s ∈ Ici a) => by simpa only [Real.norm_eq_abs] using (hstate s hs).2)
      (convex_Ici a) (hqa k) ((hqa k).trans ht.1.le)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (sub_pos.mpr ht.1)] at hmean
    have hd : M * (t - q k) ≤ D / 4 := by
      have htd : t - q k ≤ δ := by linarith only [ht.2]
      have hmul := mul_le_mul_of_nonneg_left htd hM
      calc
        _ ≤ M * δ := hmul
        _ ≤ M * δ + δ := le_add_of_nonneg_right hδ.le
        _ = (δ * (4 * (M + 1))) / 4 := by ring
        _ ≤ D / 4 := div_le_div_of_nonneg_right hδD (by norm_num)
    have hdrop : h (q k) - h t ≤ D / 4 := by
      apply (le_abs_self _).trans
      simpa only [abs_sub_comm] using hmean.trans hd
    have htpos : D / 4 ≤ h t := by
      calc
        _ = D / 2 - D / 4 := by ring
        _ ≤ h (q k) - D / 4 := sub_le_sub_right hcenterpos _
        _ ≤ h t := (sub_le_iff_le_add).mpr (by
          simpa only [add_comm] using (sub_le_iff_le_add).mp hdrop)
    exact htpos.trans (le_abs_self _)

/-- Squaring the dimensional normalization recovers its integer decay exponent. -/
theorem weightedRadialBallFourier_sq (n : ℕ) {s : ℝ} (hs : 0 < s) :
    weightedRadialBallFourier n s ^ 2 = s ^ (n + 2) * realRadialBallFourier n s ^ 2 := by
  rw [weightedRadialBallFourier, mul_pow]
  congr 1
  rw [← Real.rpow_natCast (s ^ ((n + 2 : ℕ) / 2 : ℝ)) 2,
    ← Real.rpow_mul hs.le, ← Real.rpow_natCast s (n + 2)]
  congr 1
  push_cast
  ring

/-- The actual normalized ball Fourier transform supplies the recurring sharp
square-decay lower bound required for the polynomial L² degree obstruction. -/
theorem normalizedBallFourier_recurringSquareLowerBound (n : ℕ) :
    RecurringRadialSquareLowerBound
      (fun ξ : RealPoint (n + 1) => normalizedBallFourier (n + 1) (realToComplex ξ)) (n + 2) := by
  obtain ⟨δ, η, q, hδ, hη, hqpos, hqgap, hqunbounded, hlower⟩ :=
    inverse_square_oscillator_recurring_intervals (a := 1) (by norm_num)
      (fun _ ht => weightedRadialBallFourier_hasDerivAt n (by linarith [show (1 : ℝ) ≤ _ from ht]))
      (fun _ ht => weightedRadialBallFourierDeriv_hasDerivAt n (by linarith [show (1 : ℝ) ≤ _ from ht]))
      (weightedRadialBallFourier_energy_pos n (by norm_num : (0 : ℝ) < 1))
  have hπ : 0 < 2 * Real.pi := by positivity
  let Q : ℕ → ℝ := fun k => q k / (2 * Real.pi)
  let Δ := δ / (2 * Real.pi)
  have hΔ : 0 < Δ := div_pos hδ hπ
  apply recurringRadialSquareLowerBound_of_intervals _ _ (η ^ 2 / (2 * Real.pi) ^ (n + 2))
    Δ (div_pos (sq_pos_of_pos hη) (pow_pos hπ _)) hΔ Q
  · intro k
    change q k / (2 * Real.pi) + δ / (2 * Real.pi) ≤ q (k + 1) / (2 * Real.pi)
    rw [← add_div]
    exact (div_le_div_iff_of_pos_right hπ).mpr (hqgap k)
  · intro R
    obtain ⟨k, hk⟩ := hqunbounded (R * (2 * Real.pi))
    exact ⟨k, (le_div_iff₀ hπ).mpr hk⟩
  · intro k θ r hr
    have hqr : 0 < q k := lt_of_lt_of_le (by norm_num) (hqpos k)
    have hrpos : 0 < r := (div_pos hqr hπ).trans hr.1
    have hscaled : (2 * Real.pi) * r ∈ Ioc (q k) (q k + δ) := by
      constructor
      · have h := (div_lt_iff₀ hπ).mp hr.1
        linarith
      · have h := hr.2
        change r ≤ q k / (2 * Real.pi) + δ / (2 * Real.pi) at h
        rw [← add_div] at h
        have h := (le_div_iff₀ hπ).mp h
        linarith
    have hh := hlower k ((2 * Real.pi) * r) hscaled
    have hsq : η ^ 2 ≤ ((2 * Real.pi) * r) ^ (n + 2) *
        |realRadialBallFourier n ((2 * Real.pi) * r)| ^ 2 := by
      have h : η ^ 2 ≤ |weightedRadialBallFourier n ((2 * Real.pi) * r)| ^ 2 := by
        nlinarith [abs_nonneg (weightedRadialBallFourier n ((2 * Real.pi) * r))]
      simpa only [sq_abs, weightedRadialBallFourier_sq n (mul_pos hπ hrpos), sq_abs] using h
    have hθ : ‖θ.val‖ = 1 := by
      simpa only [Metric.mem_sphere, dist_zero_right] using θ.property
    rw [normalizedBallFourier_real_radial, norm_smul, Real.norm_eq_abs, abs_of_pos hrpos,
      hθ, mul_one, radialBallFourier_ofReal_eq, Complex.norm_real, Real.norm_eq_abs]
    apply (div_le_iff₀ (pow_pos hπ (n + 2))).mpr
    convert hsq using 1
    ring

/-- A positive derivative on a small interval locates an actual nearby zero whenever
its central value is small. This is the quantitative inverse-function estimate used below. -/
theorem exists_zero_near_of_derivative_lower {f f' : ℝ → ℝ} {s ρ d : ℝ}
    (hρ : 0 < ρ) (hd : 0 < d)
    (hf : ∀ t ∈ Icc (s - ρ) (s + ρ), HasDerivAt f (f' t) t)
    (hlower : ∀ t ∈ Icc (s - ρ) (s + ρ), d ≤ f' t)
    (hsmall : |f s| ≤ d * ρ) :
    ∃ t : ℝ, f t = 0 ∧ |t - s| ≤ |f s| / d := by
  let L := |f s| / d
  have hL : 0 ≤ L := div_nonneg (abs_nonneg _) hd.le
  have hLρ : L ≤ ρ := (div_le_iff₀ hd).mpr (by simpa only [mul_comm] using hsmall)
  have hdL : d * L = |f s| := by dsimp [L]; field_simp
  have hs : s ∈ Icc (s - ρ) (s + ρ) := ⟨by linarith, by linarith⟩
  have hmon : MonotoneOn (fun t => f t - d * t) (Icc (s - ρ) (s + ρ)) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc _ _)
      (fun t ht => ((hf t ht).sub ((hasDerivAt_id t).const_mul d)).continuousAt.continuousWithinAt)
      (fun t ht => ((hf t (interior_subset ht)).sub
        ((hasDerivAt_id t).const_mul d)).hasDerivWithinAt)
    intro t ht
    simpa only [mul_one] using sub_nonneg.mpr (hlower t (interior_subset ht))
  by_cases hsign : 0 ≤ f s
  · have hl : s - L ∈ Icc (s - ρ) (s + ρ) := ⟨by linarith, by linarith⟩
    have hineq := hmon hl hs (by linarith : s - L ≤ s)
    dsimp only at hineq
    have hleft : f (s - L) ≤ 0 := by
      have habs : |f s| = f s := abs_of_nonneg hsign
      nlinarith only [hineq, hdL, habs]
    have hcont : ContinuousOn f (Icc (s - L) s) := fun t ht =>
      (hf t ⟨hl.1.trans ht.1, ht.2.trans hs.2⟩).continuousAt.continuousWithinAt
    obtain ⟨t, ht, hz⟩ := intermediate_value_Icc (by linarith : s - L ≤ s) hcont ⟨hleft, hsign⟩
    refine ⟨t, hz, abs_le.mpr ⟨?_, ?_⟩⟩ <;> linarith [ht.1, ht.2]
  · have hr : s + L ∈ Icc (s - ρ) (s + ρ) := ⟨by linarith, by linarith⟩
    have hineq := hmon hs hr (by linarith : s ≤ s + L)
    dsimp only at hineq
    have habs : |f s| = -f s := abs_of_neg (lt_of_not_ge hsign)
    have hright : 0 ≤ f (s + L) := by nlinarith only [hineq, hdL, habs]
    have hcont : ContinuousOn f (Icc s (s + L)) := fun t ht =>
      (hf t ⟨hs.1.trans ht.1, ht.2.trans hr.2⟩).continuousAt.continuousWithinAt
    obtain ⟨t, ht, hz⟩ := intermediate_value_Icc (by linarith : s ≤ s + L) hcont
      ⟨(lt_of_not_ge hsign).le, hright⟩
    refine ⟨t, hz, abs_le.mpr ⟨?_, ?_⟩⟩ <;> linarith [ht.1, ht.2]

/-- Positive state energy and a bounded second derivative give the actual quantitative
distance-to-zero lower bound, by locating a root near every sufficiently small value. -/
theorem state_energy_distance_lower {h p p' : ℝ → ℝ} {a u K : ℝ} (hu : 0 < u) (hK : 0 < K)
    (hh : ∀ s ∈ Ici a, HasDerivAt h (p s) s)
    (hp : ∀ s ∈ Ici a, HasDerivAt p (p' s) s)
    (henergy : ∀ s ∈ Ici a, u ^ 2 ≤ h s ^ 2 + p s ^ 2)
    (hsecond : ∀ s ∈ Ici a, |p' s| ≤ K)
    (Z : Set ℝ) (hzero : ∀ t, a ≤ t → h t = 0 → t ∈ Z) :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℝ, a + 1 ≤ s →
      C * min 1 (Metric.infDist s Z) ≤ |h s| := by
  let ρ := min 1 (u / (8 * K))
  have hρ : 0 < ρ := lt_min (by norm_num) (div_pos hu (by positivity))
  have hρone : ρ ≤ 1 := min_le_left _ _
  have hρK : K * ρ ≤ u / 8 := by
    have hb := (le_div_iff₀ (by positivity : 0 < 8 * K)).mp
      (min_le_right 1 (u / (8 * K)))
    nlinarith only [hb]
  let τ := u * ρ / 8
  let C := min τ (u / 4)
  have hτ : 0 < τ := by dsimp [τ]; positivity
  have hC : 0 < C := lt_min hτ (by positivity)
  refine ⟨C, hC, ?_⟩
  intro s hs
  by_cases hbig : τ ≤ |h s|
  · exact (mul_le_of_le_one_right hC.le (min_le_left _ _)).trans
      ((min_le_left _ _).trans hbig)
  · have hsmall : |h s| < τ := lt_of_not_ge hbig
    have hhs : |h s| < u / 2 := by
      have hm := mul_le_mul_of_nonneg_left hρone hu.le
      dsimp [τ] at hsmall
      nlinarith only [hsmall, hm, hu]
    have hps : u / 2 ≤ |p s| := by
      have hE := henergy s (by linarith : a ≤ s)
      nlinarith only [hE, hhs, abs_nonneg (h s), abs_nonneg (p s), sq_abs (h s), sq_abs (p s), hu]
    have hlowWindow : a ≤ s - ρ := by linarith only [hs, hρone]
    have hclose : ∀ t ∈ Icc (s - ρ) (s + ρ), |p t - p s| ≤ u / 8 := by
      intro t ht
      have hta : a ≤ t := hlowWindow.trans ht.1
      have hmean := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
        (fun t (ht : t ∈ Ici a) => (hp t ht).hasDerivWithinAt)
        (fun t (ht : t ∈ Ici a) => by simpa only [Real.norm_eq_abs] using hsecond t ht)
        (convex_Ici a) (by linarith : a ≤ s) hta
      have hdist : |t - s| ≤ ρ := abs_le.mpr ⟨by linarith only [ht.1], by linarith only [ht.2]⟩
      rw [Real.norm_eq_abs, Real.norm_eq_abs] at hmean
      exact hmean.trans ((mul_le_mul_of_nonneg_left hdist hK.le).trans hρK)
    have hsmall' : |h s| ≤ (u / 4) * ρ := by
      dsimp [τ] at hsmall
      nlinarith only [hsmall, hu, hρ]
    have hnear : ∃ t : ℝ, h t = 0 ∧ |t - s| ≤ |h s| / (u / 4) := by
      by_cases hsign : 0 ≤ p s
      · apply exists_zero_near_of_derivative_lower hρ (by positivity)
          (fun t ht => hh t (hlowWindow.trans ht.1)) ?_ hsmall'
        intro t ht
        have hdiff := (abs_le.mp (hclose t ht)).1
        rw [abs_of_nonneg hsign] at hps
        linarith only [hdiff, hps, hu]
      · obtain ⟨t, hz, hdist⟩ := exists_zero_near_of_derivative_lower (f := fun t => -h t)
          (f' := fun t => -p t) hρ (by positivity : 0 < u / 4)
          (fun t ht => (hh t (hlowWindow.trans ht.1)).neg) (by
            intro t ht
            have hdiff := (abs_le.mp (hclose t ht)).2
            rw [abs_of_neg (lt_of_not_ge hsign)] at hps
            change u / 4 ≤ -p t
            linarith only [hdiff, hps, hu]) (by simpa only [abs_neg] using hsmall')
        exact ⟨t, neg_eq_zero.mp hz, by simpa only [abs_neg] using hdist⟩
    obtain ⟨t, htzero, htdist⟩ := hnear
    have hdistρ : |t - s| ≤ ρ := htdist.trans ((div_le_iff₀ (by positivity : 0 < u / 4)).mpr
      (by simpa only [mul_comm] using hsmall'))
    have hta : a ≤ t := by have := (abs_le.mp hdistρ).1; linarith only [this, hlowWindow]
    have hinf : Metric.infDist s Z ≤ |h s| / (u / 4) := by
      apply (Metric.infDist_le_dist_of_mem (hzero t hta htzero)).trans
      simpa only [Real.dist_eq, abs_sub_comm] using htdist
    calc
      _ ≤ C * Metric.infDist s Z := mul_le_mul_of_nonneg_left (min_le_right _ _) hC.le
      _ ≤ (u / 4) * Metric.infDist s Z := mul_le_mul_of_nonneg_right
        (min_le_right _ _) Metric.infDist_nonneg
      _ ≤ (u / 4) * (|h s| / (u / 4)) := mul_le_mul_of_nonneg_left hinf (by positivity)
      _ = _ := by field_simp; ring

/-- The actual radial ball transform, with any positive real scaling, has the
quantitative distance factor needed for polynomial quotient cancellation. -/
theorem realRadialBallFourier_scaled_distance_lower (n : ℕ) {scale : ℝ} (hscale : 0 < scale) :
    ∃ C R : ℝ, 0 < C ∧ ∀ r : ℝ, R < r →
      C / (1 + ‖r‖) ^ (n + 2) *
        min 1 (Metric.infDist r {t : ℝ | realRadialBallFourier n (scale * t) = 0}) ≤
          |realRadialBallFourier n (scale * r)| := by
  let h := weightedRadialBallFourier n
  let p := weightedRadialBallFourierDeriv n
  let c : ℝ := (n : ℝ) * (n + 2) / 4
  let p' := fun s : ℝ => (c / s ^ 2 - 1) * h s
  have hh := fun s (hs : 0 < s) => weightedRadialBallFourier_hasDerivAt n hs
  have hp := fun s (hs : 0 < s) => weightedRadialBallFourierDeriv_hasDerivAt n hs
  obtain ⟨K, hK, hsecond⟩ := oscillator_second_derivative_bounded hscale
    (fun s hs => hh s (hscale.trans_le hs)) (fun s hs => hp s (hscale.trans_le hs))
  let L := oscillatorEnergy h p scale * Real.exp (-|c| / scale)
  have hL : 0 < L := mul_pos (weightedRadialBallFourier_energy_pos n hscale) (Real.exp_pos _)
  let D := min 1 (scale ^ 2)
  have hD : 0 < D := lt_min (by norm_num) (sq_pos_of_pos hscale)
  let u := Real.sqrt (L * D)
  have hu : 0 < u := Real.sqrt_pos.mpr (mul_pos hL hD)
  have hscaledh : ∀ r ∈ Ici (1 : ℝ),
      HasDerivAt (fun t => h (scale * t)) (scale * p (scale * r)) r := by
    intro r hr
    have hrpos : 0 < r := lt_of_lt_of_le (by norm_num) hr
    convert (hh (scale * r) (mul_pos hscale hrpos)).comp r ((hasDerivAt_id r).const_mul scale) using 1
    ring
  have hscaledp : ∀ r ∈ Ici (1 : ℝ),
      HasDerivAt (fun t => scale * p (scale * t)) (scale ^ 2 * p' (scale * r)) r := by
    intro r hr
    have hrpos : 0 < r := lt_of_lt_of_le (by norm_num) hr
    convert ((hp (scale * r) (mul_pos hscale hrpos)).comp r ((hasDerivAt_id r).const_mul scale)).const_mul scale using 1
    dsimp [p', h, c]
    ring
  have hscaledE : ∀ r ∈ Ici (1 : ℝ), u ^ 2 ≤ h (scale * r) ^ 2 + (scale * p (scale * r)) ^ 2 := by
    intro r hr
    have hsr : scale ≤ scale * r := by nlinarith only [hscale, show (1 : ℝ) ≤ r from hr]
    have hE := (oscillator_energy_bounds hscale (fun s hs => hh s (hscale.trans_le hs))
      (fun s hs => hp s (hscale.trans_le hs)) (scale * r) hsr).1
    change L ≤ h (scale * r) ^ 2 + p (scale * r) ^ 2 at hE
    rw [Real.sq_sqrt (mul_pos hL hD).le]
    calc
      _ ≤ D * (h (scale * r) ^ 2 + p (scale * r) ^ 2) := by nlinarith only [hE, hD]
      _ ≤ h (scale * r) ^ 2 + (scale * p (scale * r)) ^ 2 := by
        have h1 := mul_le_mul_of_nonneg_right (min_le_left 1 (scale ^ 2)) (sq_nonneg (h (scale * r)))
        have h2 := mul_le_mul_of_nonneg_right (min_le_right 1 (scale ^ 2)) (sq_nonneg (p (scale * r)))
        dsimp [D]
        nlinarith only [h1, h2]
  have hscaledK : ∀ r ∈ Ici (1 : ℝ), |scale ^ 2 * p' (scale * r)| ≤ scale ^ 2 * K := by
    intro r hr
    rw [abs_mul, abs_of_nonneg (sq_nonneg scale)]
    apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
    exact hsecond (scale * r) (by
      change scale ≤ scale * r
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hr hscale.le)
  obtain ⟨C, hC, hdist⟩ := state_energy_distance_lower (a := 1) hu (mul_pos (sq_pos_of_pos hscale) hK)
    hscaledh hscaledp hscaledE hscaledK
    {t : ℝ | realRadialBallFourier n (scale * t) = 0} (by
      intro t ht hz
      have htpos : 0 < t := lt_of_lt_of_le (by norm_num) ht
      exact (mul_eq_zero.mp hz).resolve_left (Real.rpow_pos_of_pos (mul_pos hscale htpos) _).ne')
  refine ⟨C / scale ^ (n + 2), max 2 (1 / scale), div_pos hC (pow_pos hscale _), ?_⟩
  intro r hr
  have hr2 : 2 < r := (le_max_left _ _).trans_lt hr
  have hrpos : 0 < r := by linarith only [hr2]
  have hsr : 1 ≤ scale * r := by
    have h := (div_lt_iff₀ hscale).mp ((le_max_right _ _).trans_lt hr)
    linarith only [h]
  have hweight : (scale * r) ^ ((n + 2 : ℕ) / 2 : ℝ) ≤ scale ^ (n + 2) * (1 + ‖r‖) ^ (n + 2) := by
    calc
      _ ≤ (scale * r) ^ ((n + 2 : ℕ) : ℝ) := Real.rpow_le_rpow_of_exponent_le hsr (by
        push_cast
        linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ (n : ℝ))])
      _ = scale ^ (n + 2) * r ^ (n + 2) := by rw [Real.rpow_natCast, mul_pow]
      _ ≤ _ := by
        gcongr
        rw [Real.norm_eq_abs, abs_of_pos hrpos]
        linarith
  have hdist := hdist r (by linarith only [hr2])
  change C * min 1 (Metric.infDist r {t : ℝ | realRadialBallFourier n (scale * t) = 0}) ≤
    |weightedRadialBallFourier n (scale * r)| at hdist
  rw [weightedRadialBallFourier, abs_mul, abs_of_pos (Real.rpow_pos_of_pos (mul_pos hscale hrpos) _)] at hdist
  have hbound := hdist.trans (mul_le_mul_of_nonneg_right hweight (abs_nonneg _))
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ (by positivity : 0 < (1 + ‖r‖) ^ (n + 2))).mpr
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ (pow_pos hscale (n + 2))).mpr
  convert hbound using 1
  ring

/-- The physical `2π` radial profile of the actual ball Fourier transform has the
integer polynomial distance lower bound used for division on real frequencies. -/
theorem radialBallFourier_physical_distance_lower (n : ℕ) :
    ∃ C R : ℝ, 0 < C ∧ ∀ r : ℝ, R < r →
      C / (1 + ‖r‖) ^ (n + 2) * min 1
        (Metric.infDist r {t : ℝ | radialBallFourier n ((2 * Real.pi * t : ℝ) : ℂ) = 0}) ≤
          ‖radialBallFourier n ((2 * Real.pi * r : ℝ) : ℂ)‖ := by
  simpa only [radialBallFourier_ofReal_eq, Complex.ofReal_eq_zero, Complex.norm_real,
    Real.norm_eq_abs] using
    realRadialBallFourier_scaled_distance_lower n (scale := 2 * Real.pi) (by positivity)

end RieszEuclidean.CompleteMinimal
