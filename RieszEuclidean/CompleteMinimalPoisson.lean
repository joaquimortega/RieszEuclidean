/-
The Poisson-kernel argument is adapted from Mathlib's
Analysis/Complex/Poisson.lean at 9658bdd6ca3a5c557ef9a46698d9e7aedc6bcffd.
Copyright (c) 2026 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license; see third_party/mathlib/LICENSE.
Upstream authors: Mihai Iancu, Stefan Kebekus, Sebastian Schleissinger.
The proofs below are written against the project's pinned Mathlib APIs.
-/
import RieszEuclidean.CompleteMinimalJensen
import Mathlib.Analysis.NormedSpace.Pointwise
import Mathlib.Analysis.SpecialFunctions.Log.PosLog

/-!
# Circle identities from the Cauchy formula

The circle identities use the Cauchy integral theorem of the pinned Mathlib.
The real-kernel decomposition is an elementary algebraic version of the
argument in Mathlib's `Analysis/Complex/Poisson.lean` at commit
`9658bdd6ca3a5c557ef9a46698d9e7aedc6bcffd`.
-/

noncomputable section

open MeasureTheory Metric Set Filter Topology

namespace RieszEuclidean.CompleteMinimal

/-- Normalized angular mean with complex values. -/
def diskComplexMean (f : ℂ → ℂ) (r : ℝ) : ℂ :=
  ((2 * Real.pi : ℝ) : ℂ)⁻¹ * ∫ θ in (0 : ℝ)..2 * Real.pi, f (circleMap 0 r θ)

/-- Normalized angular mean with real values. -/
def diskRealMean (f : ℂ → ℝ) (r : ℝ) : ℝ :=
  (2 * Real.pi)⁻¹ * ∫ θ in (0 : ℝ)..2 * Real.pi, f (circleMap 0 r θ)

private theorem circle_mem_closedBall {r : ℝ} (hr : 0 ≤ r) (θ : ℝ) :
    circleMap 0 r θ ∈ closedBall (0 : ℂ) r := by
  simp only [mem_closedBall, dist_zero_right, norm_circleMap_zero, abs_of_nonneg hr, le_refl]

/-- Cauchy's formula expressed as a weighted angular mean. -/
theorem diskComplexMean_cauchy {f : ℂ → ℂ} {r : ℝ} (hr : 0 < r)
    (hf : DifferentiableOn ℂ f (closedBall (0 : ℂ) r)) {w : ℂ}
    (hw : w ∈ ball (0 : ℂ) r) :
    diskComplexMean (fun ζ => ζ / (ζ - w) * f ζ) r = f w := by
  have hcl : closure (ball (0 : ℂ) r) = closedBall (0 : ℂ) r := closure_ball _ hr.ne'
  have hdiff : DiffContOnCl ℂ f (ball (0 : ℂ) r) :=
    (hcl ▸ hf).diffContOnCl
  have hC := hdiff.circleIntegral_sub_inv_smul hw
  rw [circleIntegral] at hC
  simp only [deriv_circleMap, smul_eq_mul] at hC
  have hi : (∫ θ in (0 : ℝ)..2 * Real.pi,
      circleMap 0 r θ * Complex.I * ((circleMap 0 r θ - w)⁻¹ * f (circleMap 0 r θ))) =
      Complex.I * ∫ θ in (0 : ℝ)..2 * Real.pi,
        circleMap 0 r θ / (circleMap 0 r θ - w) * f (circleMap 0 r θ) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro θ _
    simp only [div_eq_mul_inv]
    ring
  rw [hi] at hC
  have hC' : (∫ θ in (0 : ℝ)..2 * Real.pi,
      circleMap 0 r θ / (circleMap 0 r θ - w) * f (circleMap 0 r θ)) =
      ((2 * Real.pi : ℝ) : ℂ) * f w := by
    apply mul_left_cancel₀ Complex.I_ne_zero
    rw [hC]
    push_cast
    ring
  unfold diskComplexMean
  rw [hC', ← mul_assoc, inv_mul_cancel₀, one_mul]
  exact_mod_cast (by positivity : (2 * Real.pi : ℝ) ≠ 0)

/-- The ordinary angular mean of a holomorphic function is its center value. -/
theorem diskComplexMean_eq_center {f : ℂ → ℂ} {r : ℝ} (hr : 0 < r)
    (hf : DifferentiableOn ℂ f (closedBall (0 : ℂ) r)) : diskComplexMean f r = f 0 := by
  have h := diskComplexMean_cauchy hr hf (mem_ball_self hr)
  have heq : (∫ θ in (0 : ℝ)..2 * Real.pi,
      circleMap 0 r θ / (circleMap 0 r θ - 0) * f (circleMap 0 r θ)) =
      ∫ θ in (0 : ℝ)..2 * Real.pi, f (circleMap 0 r θ) := by
    apply intervalIntegral.integral_congr
    intro θ _
    have hn : circleMap 0 r θ ≠ 0 := by
      apply norm_ne_zero_iff.mp
      rw [norm_circleMap_zero, abs_of_pos hr]
      exact hr.ne'
    simp [hn]
  simpa only [diskComplexMean, heq] using h

/-- Taking real parts commutes with the angular mean. -/
theorem diskRealMean_re {f : ℂ → ℂ} {r : ℝ}
    (hf : IntervalIntegrable (fun θ => f (circleMap 0 r θ)) volume 0 (2 * Real.pi)) :
    diskRealMean (fun ζ => (f ζ).re) r = (diskComplexMean f r).re := by
  unfold diskRealMean diskComplexMean
  rw [show (∫ θ in (0 : ℝ)..2 * Real.pi, (f (circleMap 0 r θ)).re) =
      (∫ θ in (0 : ℝ)..2 * Real.pi, f (circleMap 0 r θ)).re from
    Complex.reCLM.intervalIntegral_comp_comm hf]
  simp

/-- The logarithmic circle identity for a zero-free disk. -/
theorem diskRealMean_log_norm_eq_center_of_zero_free {f : ℂ → ℂ} {r R : ℝ}
    (hr : 0 < r) (hrR : r < R)
    (hf : DifferentiableOn ℂ f (ball (0 : ℂ) R))
    (hfn : ∀ z ∈ ball (0 : ℂ) R, f z ≠ 0) :
    diskRealMean (fun ζ => Real.log ‖f ζ‖) r = Real.log ‖f 0‖ := by
  obtain ⟨L, hL, hlog⟩ := exists_disk_log_norm (hr.trans hrR) hf hfn
  have hclosed : closedBall (0 : ℂ) r ⊆ ball (0 : ℂ) R := closedBall_subset_ball hrR
  have hLi : IntervalIntegrable (fun θ => L (circleMap 0 r θ)) volume 0 (2 * Real.pi) :=
    (hL.continuousOn.comp (continuous_circleMap 0 r).continuousOn
      (fun θ _ => hclosed (circle_mem_closedBall hr.le θ))).intervalIntegrable
  have heq : diskRealMean (fun ζ => Real.log ‖f ζ‖) r = diskRealMean (fun ζ => (L ζ).re) r := by
    unfold diskRealMean
    congr 1
    apply intervalIntegral.integral_congr
    intro θ _
    exact hlog _ (hclosed (circle_mem_closedBall hr.le θ))
  rw [heq, diskRealMean_re hLi, diskComplexMean_eq_center hr (hL.mono hclosed)]
  exact (hlog 0 (mem_ball_self (hr.trans hrR))).symm

private theorem disk_aux_den_ne_zero {r : ℝ} (hr : 0 < r) {w : ℂ}
    (hw : ‖w‖ < r) {z : ℂ} (hz : ‖z‖ ≤ r) :
    ((r : ℂ) ^ 2 - (starRingEnd ℂ) w * z) ≠ 0 := by
  intro heq
  have heq' : (r : ℂ) ^ 2 = (starRingEnd ℂ) w * z := sub_eq_zero.mp heq
  have hn := congrArg norm heq'
  simp only [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr,
    norm_mul, Complex.norm_conj] at hn
  have hmul := mul_le_mul_of_nonneg_left hz (norm_nonneg w)
  nlinarith

private theorem disk_kernel_decomposition {r : ℝ} (hr : 0 < r) {w ζ : ℂ}
    (hw : ‖w‖ < r) (hζ : ‖ζ‖ = r) :
    ((((ζ + w) / (ζ - w)).re : ℝ) : ℂ) =
      ζ / (ζ - w) + ((starRingEnd ℂ) w * ζ) / ((r : ℂ)^2 - (starRingEnd ℂ) w * ζ) := by
  have hζn : ζ ≠ 0 := norm_ne_zero_iff.mp (by rw [hζ]; exact hr.ne')
  have hζw : ζ - w ≠ 0 := sub_ne_zero.mpr (by intro heq; subst ζ; linarith)
  have hcζw : (starRingEnd ℂ) ζ - (starRingEnd ℂ) w ≠ 0 := by
    simpa only [← map_sub, map_ne_zero] using hζw
  have haux := disk_aux_den_ne_zero hr hw hζ.le
  have hζconj : ζ * (starRingEnd ℂ) ζ = (r : ℂ)^2 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hζ]
    push_cast
    rfl
  have hconj : ((starRingEnd ℂ) ζ + (starRingEnd ℂ) w) /
      ((starRingEnd ℂ) ζ - (starRingEnd ℂ) w) =
      ((r : ℂ)^2 + (starRingEnd ℂ) w * ζ) / ((r : ℂ)^2 - (starRingEnd ℂ) w * ζ) := by
    calc
      _ = (((starRingEnd ℂ) ζ + (starRingEnd ℂ) w) * ζ) /
          (((starRingEnd ℂ) ζ - (starRingEnd ℂ) w) * ζ) := by
        rw [mul_div_mul_right _ _ hζn]
      _ = _ := by
        congr 1
        · calc
            _ = ζ * (starRingEnd ℂ) ζ + (starRingEnd ℂ) w * ζ := by ring
            _ = _ := by rw [hζconj]
        · calc
            _ = ζ * (starRingEnd ℂ) ζ - (starRingEnd ℂ) w * ζ := by ring
            _ = _ := by rw [hζconj]
  rw [Complex.re_eq_add_conj, map_div₀, map_add, map_sub, hconj]
  field_simp
  ring

private theorem circle_continuous_of_continuousOn_closedBall {f : ℂ → ℂ} {r : ℝ}
    (hr : 0 ≤ r) (hf : ContinuousOn f (closedBall (0 : ℂ) r)) :
    Continuous (fun θ : ℝ => f (circleMap 0 r θ)) := by
  apply continuous_iff_continuousOn_univ.mpr
  exact hf.comp (continuous_circleMap 0 r).continuousOn
    (fun θ _ => circle_mem_closedBall hr θ)

/-- The real Poisson kernel reproduces a holomorphic function, directly from
Cauchy's formula and an analytic reflected kernel vanishing at the origin. -/
theorem diskComplexMean_poisson {f : ℂ → ℂ} {r : ℝ} (hr : 0 < r)
    (hf : DifferentiableOn ℂ f (closedBall (0 : ℂ) r)) {w : ℂ}
    (hw : w ∈ ball (0 : ℂ) r) :
    diskComplexMean (fun ζ => (((ζ + w) / (ζ - w)).re : ℂ) * f ζ) r = f w := by
  have hwr : ‖w‖ < r := by simpa only [mem_ball, dist_zero_right] using hw
  let a : ℂ → ℂ := fun z => (starRingEnd ℂ) w * z / ((r : ℂ)^2 - (starRingEnd ℂ) w * z)
  have ha : DifferentiableOn ℂ a (closedBall (0 : ℂ) r) := by
    apply DifferentiableOn.div
      ((differentiable_const _).mul differentiable_id).differentiableOn
      ((differentiable_const _).sub ((differentiable_const _).mul differentiable_id)).differentiableOn
    intro z hz
    exact disk_aux_den_ne_zero hr hwr (by simpa only [mem_closedBall, dist_zero_right] using hz)
  have hmeanA : diskComplexMean (fun ζ => a ζ * f ζ) r = 0 := by
    rw [diskComplexMean_eq_center hr (ha.mul hf)]
    simp [a]
  have hmeanF := diskComplexMean_cauchy hr hf hw
  have hfc := circle_continuous_of_continuousOn_closedBall hr.le hf.continuousOn
  have hkc : Continuous (fun θ => circleMap 0 r θ / (circleMap 0 r θ - w)) := by
    apply (continuous_circleMap 0 r).div ((continuous_circleMap 0 r).sub continuous_const)
    intro θ heq
    have hnorm : ‖circleMap 0 r θ‖ = r := by rw [norm_circleMap_zero, abs_of_pos hr]
    rw [sub_eq_zero.mp heq] at hnorm
    linarith
  have hfirst := (hkc.mul hfc).intervalIntegrable (μ := volume) (0 : ℝ) (2 * Real.pi)
  have hsecond := (circle_continuous_of_continuousOn_closedBall hr.le (ha.mul hf).continuousOn).intervalIntegrable (μ := volume) (0 : ℝ) (2 * Real.pi)
  have heq : diskComplexMean (fun ζ => (((ζ + w) / (ζ - w)).re : ℂ) * f ζ) r =
      diskComplexMean (fun ζ => ζ / (ζ - w) * f ζ) r +
        diskComplexMean (fun ζ => a ζ * f ζ) r := by
    unfold diskComplexMean
    rw [← mul_add, ← intervalIntegral.integral_add hfirst hsecond]
    congr 1
    apply intervalIntegral.integral_congr
    intro θ _
    dsimp only
    rw [disk_kernel_decomposition (ζ := circleMap 0 r θ) hr hwr
      (by rw [norm_circleMap_zero, abs_of_pos hr]), add_mul]
  rw [heq, hmeanF, hmeanA, add_zero]

/-- The weighted Poisson circle identity for the real part of a holomorphic function. -/
theorem diskRealMean_poisson_re {f : ℂ → ℂ} {r : ℝ} (hr : 0 < r)
    (hf : DifferentiableOn ℂ f (closedBall (0 : ℂ) r)) {w : ℂ}
    (hw : w ∈ ball (0 : ℂ) r) :
    diskRealMean (fun ζ => ((ζ + w) / (ζ - w)).re * (f ζ).re) r = (f w).re := by
  have hfc := circle_continuous_of_continuousOn_closedBall hr.le hf.continuousOn
  have hkc : Continuous (fun θ => ((circleMap 0 r θ + w) / (circleMap 0 r θ - w)).re) := by
    apply (Complex.continuous_re.comp (f := fun θ => (circleMap 0 r θ + w) / (circleMap 0 r θ - w)))
    apply ((continuous_circleMap 0 r).add continuous_const).div
      ((continuous_circleMap 0 r).sub continuous_const)
    intro θ heq
    have hnorm : ‖circleMap 0 r θ‖ = r := by rw [norm_circleMap_zero, abs_of_pos hr]
    have hwr : ‖w‖ < r := by simpa only [mem_ball, dist_zero_right] using hw
    rw [sub_eq_zero.mp heq] at hnorm
    linarith
  have hint := ((Complex.continuous_ofReal.comp hkc).mul hfc).intervalIntegrable (μ := volume) (0 : ℝ) (2 * Real.pi)
  have h := diskRealMean_re (f := fun ζ => (((ζ + w) / (ζ - w)).re : ℂ) * f ζ) (r := r) hint
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] at h
  rw [h, diskComplexMean_poisson hr hf hw]

/-- On a zero-free disk, the logarithm of the norm satisfies the Poisson identity. -/
theorem diskRealMean_poisson_log_norm_of_zero_free {f : ℂ → ℂ} {r R : ℝ}
    (hr : 0 < r) (hrR : r < R)
    (hf : DifferentiableOn ℂ f (ball (0 : ℂ) R))
    (hfn : ∀ z ∈ ball (0 : ℂ) R, f z ≠ 0) {w : ℂ}
    (hw : w ∈ ball (0 : ℂ) r) :
    diskRealMean (fun ζ => ((ζ + w) / (ζ - w)).re * Real.log ‖f ζ‖) r = Real.log ‖f w‖ := by
  obtain ⟨L, hL, hlog⟩ := exists_disk_log_norm (hr.trans hrR) hf hfn
  have hclosed : closedBall (0 : ℂ) r ⊆ ball (0 : ℂ) R := closedBall_subset_ball hrR
  have heq : diskRealMean (fun ζ => ((ζ + w) / (ζ - w)).re * Real.log ‖f ζ‖) r =
      diskRealMean (fun ζ => ((ζ + w) / (ζ - w)).re * (L ζ).re) r := by
    unfold diskRealMean
    congr 1
    apply intervalIntegral.integral_congr
    intro θ _
    dsimp only
    rw [hlog _ (hclosed (circle_mem_closedBall hr.le θ))]
  rw [heq, diskRealMean_poisson_re hr (hL.mono hclosed) hw]
  exact (hlog _ (ball_subset_ball hrR.le hw)).symm

private theorem reflection_normSq (c : ℝ) (a z : ℂ) :
    Complex.normSq (1 - (c : ℂ) * (starRingEnd ℂ) a * z) =
      1 + c^2 * Complex.normSq a * Complex.normSq z - 2 * c * (z * (starRingEnd ℂ) a).re := by
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.mul_re,
    Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.conj_re,
    Complex.conj_im, Complex.one_re, Complex.one_im]
  ring

private theorem reflection_circle_norm {r : ℝ} (hr : 0 < r) (a ζ : ℂ)
    (hζ : ‖ζ‖ = r) :
    ‖ζ - a‖ = r * ‖1 - (((r^2)⁻¹ : ℝ) : ℂ) * (starRingEnd ℂ) a * ζ‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (mul_nonneg hr.le (norm_nonneg _))).mp
  rw [mul_pow, ← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq,
    reflection_normSq, Complex.normSq_sub, Complex.normSq_eq_norm_sq ζ, hζ]
  field_simp
  ring

private theorem reflection_norm_bound {r : ℝ} (hr : 0 < r) {a w : ℂ}
    (ha : ‖a‖ ≤ r) (hw : ‖w‖ ≤ r) :
    ‖w - a‖ ≤ r * ‖1 - (((r^2)⁻¹ : ℝ) : ℂ) * (starRingEnd ℂ) a * w‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hr.le (norm_nonneg _))).mp
  rw [mul_pow, ← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq,
    reflection_normSq, Complex.normSq_sub]
  have haSq : Complex.normSq a ≤ r^2 := by rw [Complex.normSq_eq_norm_sq]; nlinarith [norm_nonneg a]
  have hwSq : Complex.normSq w ≤ r^2 := by rw [Complex.normSq_eq_norm_sq]; nlinarith [norm_nonneg w]
  have hprod : 0 ≤ (r^2 - Complex.normSq a) * (r^2 - Complex.normSq w) :=
    mul_nonneg (sub_nonneg.mpr haSq) (sub_nonneg.mpr hwSq)
  have hpowpos : 0 < r^2 := pow_pos hr _
  have hid : r^2 * (1 + ((r^2)⁻¹)^2 * Complex.normSq a * Complex.normSq w -
      2 * (r^2)⁻¹ * (w * (starRingEnd ℂ) a).re) -
      (Complex.normSq w + Complex.normSq a - 2 * (w * (starRingEnd ℂ) a).re) =
      ((r^2 - Complex.normSq a) * (r^2 - Complex.normSq w)) / r^2 := by
    field_simp [hr.ne']
    ring
  apply sub_nonneg.mp
  rw [hid]
  exact div_nonneg hprod hpowpos.le

private theorem exists_zero_free_larger_disk {f : ℂ → ℂ} {r : ℝ} (hr : 0 < r)
    (hf : Continuous f) (hfn : ∀ z ∈ closedBall (0 : ℂ) r, f z ≠ 0) :
    ∃ R : ℝ, r < R ∧ ∀ z ∈ ball (0 : ℂ) R, f z ≠ 0 := by
  have hopen : IsOpen {z : ℂ | f z ≠ 0} := (isClosed_eq hf continuous_const).isOpen_compl
  obtain ⟨ε, hε, hsub⟩ := (isCompact_closedBall (0 : ℂ) r).exists_thickening_subset_open hopen hfn
  rw [thickening_closedBall hε hr.le] at hsub
  exact ⟨ε + r, by linarith, hsub⟩

/-- The logarithmic mean identity also holds under the concrete assumption that
an entire function has no zeros on the whole closed integration disk. -/
theorem diskRealMean_log_norm_eq_center_of_entire_zero_free {f : ℂ → ℂ} {r : ℝ}
    (hr : 0 < r) (hf : Differentiable ℂ f)
    (hfn : ∀ z ∈ closedBall (0 : ℂ) r, f z ≠ 0) :
    diskRealMean (fun ζ => Real.log ‖f ζ‖) r = Real.log ‖f 0‖ := by
  obtain ⟨R, hrR, hRfn⟩ := exists_zero_free_larger_disk hr hf.continuous hfn
  exact diskRealMean_log_norm_eq_center_of_zero_free hr hrR hf.differentiableOn hRfn

/-- The logarithmic Poisson identity for an entire function zero-free on the
closed integration disk. -/
theorem diskRealMean_poisson_log_norm_of_entire_zero_free {f : ℂ → ℂ} {r : ℝ}
    (hr : 0 < r) (hf : Differentiable ℂ f)
    (hfn : ∀ z ∈ closedBall (0 : ℂ) r, f z ≠ 0) {w : ℂ}
    (hw : w ∈ ball (0 : ℂ) r) :
    diskRealMean (fun ζ => ((ζ + w) / (ζ - w)).re * Real.log ‖f ζ‖) r = Real.log ‖f w‖ := by
  obtain ⟨R, hrR, hRfn⟩ := exists_zero_free_larger_disk hr hf.continuous hfn
  exact diskRealMean_poisson_log_norm_of_zero_free hr hrR hf.differentiableOn hRfn hw

private theorem circle_poissonKernel_continuous {r : ℝ} (hr : 0 < r) {w : ℂ}
    (hw : ‖w‖ < r) :
    Continuous (fun θ => ((circleMap 0 r θ + w) / (circleMap 0 r θ - w)).re) := by
  apply (Complex.continuous_re.comp (f := fun θ => (circleMap 0 r θ + w) / (circleMap 0 r θ - w)))
  apply ((continuous_circleMap 0 r).add continuous_const).div
    ((continuous_circleMap 0 r).sub continuous_const)
  intro θ heq
  have hnorm : ‖circleMap 0 r θ‖ = r := by rw [norm_circleMap_zero, abs_of_pos hr]
  rw [sub_eq_zero.mp heq] at hnorm
  linarith

private theorem diskRealMean_add {f g : ℂ → ℝ} {r : ℝ}
    (hf : IntervalIntegrable (fun θ => f (circleMap 0 r θ)) volume 0 (2 * Real.pi))
    (hg : IntervalIntegrable (fun θ => g (circleMap 0 r θ)) volume 0 (2 * Real.pi)) :
    diskRealMean (fun ζ => f ζ + g ζ) r = diskRealMean f r + diskRealMean g r := by
  unfold diskRealMean
  rw [intervalIntegral.integral_add hf hg, mul_add]

private theorem diskRealMean_const_mul (c : ℝ) (f : ℂ → ℝ) (r : ℝ) :
    diskRealMean (fun ζ => c * f ζ) r = c * diskRealMean f r := by
  unfold diskRealMean
  rw [intervalIntegral.integral_const_mul]
  ring

private theorem diskRealMean_poisson_const {r : ℝ} (hr : 0 < r) {w : ℂ}
    (hw : w ∈ ball (0 : ℂ) r) (c : ℝ) :
    diskRealMean (fun ζ => ((ζ + w) / (ζ - w)).re * c) r = c := by
  simpa only [Complex.ofReal_re] using diskRealMean_poisson_re hr
    (f := fun _ => (c : ℂ)) (differentiable_const _).differentiableOn hw

private theorem reflection_zero_free {r : ℝ} (hr : 0 < r) {a : ℂ} (ha : ‖a‖ < r) :
    ∀ z ∈ closedBall (0 : ℂ) r,
      1 - (((r^2)⁻¹ : ℝ) : ℂ) * (starRingEnd ℂ) a * z ≠ 0 := by
  intro z hz heq
  have hn := congrArg norm (sub_eq_zero.mp heq)
  simp only [norm_one, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_inv, abs_pow, abs_of_pos hr, Complex.norm_conj] at hn
  field_simp [hr.ne'] at hn
  have hzNorm : ‖z‖ ≤ r := by simpa only [mem_closedBall, dist_zero_right] using hz
  have hmul := mul_le_mul_of_nonneg_left hzNorm (norm_nonneg a)
  nlinarith

private theorem log_linearFactor_integrable {r : ℝ} (hr : 0 < r) {a : ℂ}
    (ha : ‖a‖ ≠ r) :
    IntervalIntegrable (fun θ => Real.log ‖circleMap 0 r θ - a‖) volume 0 (2 * Real.pi) := by
  apply Continuous.intervalIntegrable
  apply ((continuous_circleMap 0 r).sub continuous_const).norm.log
  intro θ heq
  have hza : circleMap 0 r θ = a := sub_eq_zero.mp (norm_eq_zero.mp heq)
  have h := norm_circleMap_zero r θ
  rw [hza, abs_of_pos hr] at h
  exact ha h

/-- A single linear zero contributes a nonnegative correction to the logarithmic
Poisson formula. The reflected factor proves this even when the zero lies inside
rather than outside the integration disk. -/
theorem log_linearFactor_le_diskRealMean_poisson {r : ℝ} (hr : 0 < r) {a w : ℂ}
    (ha : ‖a‖ ≠ r) (hw : w ∈ ball (0 : ℂ) r) (hwa : w ≠ a) :
    Real.log ‖w - a‖ ≤
      diskRealMean (fun ζ => ((ζ + w) / (ζ - w)).re * Real.log ‖ζ - a‖) r := by
  rcases lt_or_gt_of_ne ha with ha | ha
  · let b : ℂ → ℂ := fun z => 1 - (((r^2)⁻¹ : ℝ) : ℂ) * (starRingEnd ℂ) a * z
    have hb : Differentiable ℂ b := by fun_prop
    have hbn : ∀ z ∈ closedBall (0 : ℂ) r, b z ≠ 0 := reflection_zero_free hr ha
    have hwr : ‖w‖ < r := by simpa only [mem_ball, dist_zero_right] using hw
    have hker := circle_poissonKernel_continuous hr hwr
    have hbθ := circle_continuous_of_continuousOn_closedBall hr.le hb.continuous.continuousOn
    have hlogbθ := hbθ.norm.log (fun θ => norm_ne_zero_iff.mpr (hbn _ (circle_mem_closedBall hr.le θ)))
    have hconsti : IntervalIntegrable (fun θ =>
        ((circleMap 0 r θ + w) / (circleMap 0 r θ - w)).re * Real.log r) volume 0 (2 * Real.pi) :=
      (hker.mul continuous_const).intervalIntegrable (μ := volume) (0 : ℝ) (2 * Real.pi)
    have hlogbi := (hker.mul hlogbθ).intervalIntegrable (μ := volume) (0 : ℝ) (2 * Real.pi)
    have hmean : diskRealMean (fun ζ => ((ζ + w) / (ζ - w)).re * Real.log ‖ζ - a‖) r =
        Real.log r + Real.log ‖b w‖ := by
      have heq : diskRealMean (fun ζ => ((ζ + w) / (ζ - w)).re * Real.log ‖ζ - a‖) r =
          diskRealMean (fun ζ => ((ζ + w) / (ζ - w)).re * Real.log r +
            ((ζ + w) / (ζ - w)).re * Real.log ‖b ζ‖) r := by
        unfold diskRealMean
        congr 1
        apply intervalIntegral.integral_congr
        intro θ _
        dsimp only
        rw [reflection_circle_norm hr a (circleMap 0 r θ)
          (by rw [norm_circleMap_zero, abs_of_pos hr]), Real.log_mul hr.ne'
            (norm_ne_zero_iff.mpr (hbn _ (circle_mem_closedBall hr.le θ))), mul_add]
      rw [heq, diskRealMean_add
        (f := fun ζ => ((ζ + w) / (ζ - w)).re * Real.log r)
        (g := fun ζ => ((ζ + w) / (ζ - w)).re * Real.log ‖b ζ‖) hconsti hlogbi,
        diskRealMean_poisson_const hr hw (Real.log r),
        diskRealMean_poisson_log_norm_of_entire_zero_free hr hb hbn hw]
    rw [hmean, ← Real.log_mul hr.ne' (norm_ne_zero_iff.mpr (hbn w (ball_subset_closedBall hw)))]
    apply Real.log_le_log (norm_pos_iff.mpr (sub_ne_zero.mpr hwa))
    exact reflection_norm_bound hr ha.le hwr.le
  · have hf : Differentiable ℂ (fun z => z - a) := differentiable_id.sub_const a
    have hfn : ∀ z ∈ closedBall (0 : ℂ) r, z - a ≠ 0 := by
      intro z hz hzero
      have hzNorm : ‖z‖ ≤ r := by simpa only [mem_closedBall, dist_zero_right] using hz
      rw [sub_eq_zero.mp hzero] at hzNorm
      linarith
    exact (diskRealMean_poisson_log_norm_of_entire_zero_free hr hf hfn hw).symm.le

private theorem prod_linearFactors_ne_zero (l : List (ℂ × ℕ)) (z : ℂ)
    (hn : ∀ p ∈ l, z ≠ p.1) : (l.map (fun p => (z - p.1)^p.2)).prod ≠ 0 := by
  induction l with
  | nil => simp
  | cons p l ih =>
      simp only [List.map_cons, List.prod_cons]
      exact mul_ne_zero (pow_ne_zero _ (sub_ne_zero.mpr (hn p (List.mem_cons_self))))
        (ih (fun p hp => hn p (List.mem_cons_of_mem _ hp)))

private theorem log_norm_linearFactors (l : List (ℂ × ℕ)) (z : ℂ)
    (hn : ∀ p ∈ l, z ≠ p.1) :
    Real.log ‖(l.map (fun p => (z - p.1)^p.2)).prod‖ =
      (l.map (fun p => (p.2 : ℝ) * Real.log ‖z - p.1‖)).sum := by
  induction l with
  | nil => simp
  | cons p l ih =>
      have hp := hn p List.mem_cons_self
      have hl : ∀ p ∈ l, z ≠ p.1 := fun p hp => hn p (List.mem_cons_of_mem _ hp)
      simp only [List.map_cons, List.prod_cons, norm_mul, List.sum_cons]
      rw [Real.log_mul (norm_ne_zero_iff.mpr (pow_ne_zero _ (sub_ne_zero.mpr hp)))
        (norm_ne_zero_iff.mpr (prod_linearFactors_ne_zero l z hl)), norm_pow, Real.log_pow, ih hl]

private theorem roots_ne_of_factorization (l : List (ℂ × ℕ)) (g : ℂ → ℂ) (z : ℂ)
    (hn : ∀ p ∈ l, 0 < p.2) (hprod : (l.map (fun p => (z - p.1)^p.2)).prod * g z ≠ 0) :
    (∀ p ∈ l, z ≠ p.1) ∧ g z ≠ 0 := by
  obtain ⟨hpoly, hg⟩ := mul_ne_zero_iff.mp hprod
  refine ⟨?_, hg⟩
  intro p hp hzp
  apply hpoly
  apply List.prod_eq_zero_iff.mpr
  apply List.mem_map.mpr
  exact ⟨p, hp, by simp [hzp, (hn p hp).ne']⟩

private theorem diskRealMean_list_sum {ι : Type*} (l : List ι) (f : ι → ℂ → ℝ) (r : ℝ)
    (hint : ∀ p ∈ l, IntervalIntegrable (fun θ => f p (circleMap 0 r θ)) volume 0 (2 * Real.pi)) :
    IntervalIntegrable (fun θ => (l.map (fun p => f p (circleMap 0 r θ))).sum) volume 0 (2 * Real.pi) ∧
      diskRealMean (fun ζ => (l.map (fun p => f p ζ)).sum) r = (l.map (fun p => diskRealMean (f p) r)).sum := by
  induction l with
  | nil => simp [diskRealMean]
  | cons p l ih =>
      have hp := hint p List.mem_cons_self
      obtain ⟨hli, hmean⟩ := ih (fun p hp => hint p (List.mem_cons_of_mem _ hp))
      refine ⟨by simpa only [List.map_cons, List.sum_cons] using hp.add hli, ?_⟩
      simp only [List.map_cons, List.sum_cons]
      rw [diskRealMean_add (f := f p) (g := fun ζ => (l.map (fun p => f p ζ)).sum) hp hli, hmean]

/-- The logarithmic Poisson inequality for an arbitrary holomorphic function,
including functions with zeros inside the disk. Only boundary zeros and a zero
at the evaluation point are excluded; zeros inside are factored with their actual orders. -/
theorem log_norm_le_diskRealMean_poisson {f : ℂ → ℂ} {r R : ℝ}
    (hr : 0 < r) (hrR : r < R)
    (hf : DifferentiableOn ℂ f (ball (0 : ℂ) R)) {w : ℂ}
    (hw : w ∈ ball (0 : ℂ) r) (hfw : f w ≠ 0)
    (hfn : ∀ θ : ℝ, f (circleMap 0 r θ) ≠ 0) :
    Real.log ‖f w‖ ≤ diskRealMean (fun ζ => ((ζ + w) / (ζ - w)).re * Real.log ‖f ζ‖) r := by
  let ρ : ℝ := (r + R) / 2
  have hrρ : r < ρ := by dsimp [ρ]; linarith
  have hρR : ρ < R := by dsimp [ρ]; linarith
  have hρsub : ball (0 : ℂ) ρ ⊆ ball (0 : ℂ) R := ball_subset_ball hρR.le
  have hcircleρ : ∀ θ, circleMap 0 r θ ∈ ball (0 : ℂ) ρ :=
    fun θ => closedBall_subset_ball hrρ (circle_mem_closedBall hr.le θ)
  obtain ⟨l, hl, g, hg, hgn, hfg⟩ := factor_disk_zeros hρR hf
    (ball_subset_ball hrR.le hw) hfw
  have horders : ∀ p ∈ l, 0 < p.2 := fun p hp => (hl p hp).2
  have hwfacts := roots_ne_of_factorization l g w horders
    (by rw [← hfg w (ball_subset_ball hrR.le hw)]; exact hfw)
  have hcirclefacts : ∀ θ, (∀ p ∈ l, circleMap 0 r θ ≠ p.1) ∧ g (circleMap 0 r θ) ≠ 0 := by
    intro θ
    apply roots_ne_of_factorization l g _ horders
    rw [← hfg _ (hρsub (hcircleρ θ))]
    exact hfn θ
  have hrootr : ∀ p ∈ l, ‖p.1‖ ≠ r := by
    intro p hp hnorm
    have hcircle : circleMap 0 r p.1.arg = p.1 := by
      rw [circleMap_zero, ← hnorm]
      exact Complex.norm_mul_exp_arg_mul_I _
    exact (hcirclefacts p.1.arg).1 p hp hcircle
  have hlogw : Real.log ‖f w‖ =
      (l.map (fun p => (p.2 : ℝ) * Real.log ‖w - p.1‖)).sum + Real.log ‖g w‖ := by
    rw [hfg w (ball_subset_ball hrR.le hw), norm_mul,
      Real.log_mul (norm_ne_zero_iff.mpr (prod_linearFactors_ne_zero l w hwfacts.1))
        (norm_ne_zero_iff.mpr hwfacts.2), log_norm_linearFactors l w hwfacts.1]
  have hlogcircle : ∀ θ, Real.log ‖f (circleMap 0 r θ)‖ =
      (l.map (fun p => (p.2 : ℝ) * Real.log ‖circleMap 0 r θ - p.1‖)).sum +
        Real.log ‖g (circleMap 0 r θ)‖ := by
    intro θ
    rw [hfg _ (hρsub (hcircleρ θ)), norm_mul,
      Real.log_mul (norm_ne_zero_iff.mpr (prod_linearFactors_ne_zero l _ (hcirclefacts θ).1))
        (norm_ne_zero_iff.mpr (hcirclefacts θ).2), log_norm_linearFactors l _ (hcirclefacts θ).1]
  have hwr : ‖w‖ < r := by simpa only [mem_ball, dist_zero_right] using hw
  have hker := circle_poissonKernel_continuous hr hwr
  let T : (ℂ × ℕ) → ℂ → ℝ := fun p ζ =>
    (p.2 : ℝ) * (((ζ + w) / (ζ - w)).re * Real.log ‖ζ - p.1‖)
  have hTi : ∀ p ∈ l, IntervalIntegrable (fun θ => T p (circleMap 0 r θ)) volume 0 (2 * Real.pi) := by
    intro p hp
    simpa only [T, mul_comm] using
      ((log_linearFactor_integrable hr (hrootr p hp)).mul_continuousOn hker.continuousOn).const_mul (p.2 : ℝ)
  obtain ⟨hsumi, hsummean⟩ := diskRealMean_list_sum l T r hTi
  have hgθ : Continuous (fun θ => g (circleMap 0 r θ)) := by
    apply continuous_iff_continuousOn_univ.mpr
    exact hg.continuousOn.comp (continuous_circleMap 0 r).continuousOn
      (fun θ _ => hρsub (hcircleρ θ))
  have hgi := (hker.mul (hgθ.norm.log
    (fun θ => norm_ne_zero_iff.mpr (hcirclefacts θ).2))).intervalIntegrable
      (μ := volume) (0 : ℝ) (2 * Real.pi)
  have heq : diskRealMean (fun ζ => ((ζ + w) / (ζ - w)).re * Real.log ‖f ζ‖) r =
      (l.map (fun p => (p.2 : ℝ) * diskRealMean
        (fun ζ => ((ζ + w) / (ζ - w)).re * Real.log ‖ζ - p.1‖) r)).sum + Real.log ‖g w‖ := by
    have hcircleEq : diskRealMean (fun ζ => ((ζ + w) / (ζ - w)).re * Real.log ‖f ζ‖) r =
        diskRealMean (fun ζ => (l.map (fun p => T p ζ)).sum +
          ((ζ + w) / (ζ - w)).re * Real.log ‖g ζ‖) r := by
      unfold diskRealMean
      congr 1
      apply intervalIntegral.integral_congr
      intro θ _
      dsimp only
      rw [hlogcircle θ, mul_add, ← List.sum_map_mul_left]
      congr 1
      apply congrArg List.sum
      apply List.map_congr_left
      intro p _
      dsimp only [T]
      ring
    rw [hcircleEq, diskRealMean_add
      (f := fun ζ => (l.map (fun p => T p ζ)).sum)
      (g := fun ζ => ((ζ + w) / (ζ - w)).re * Real.log ‖g ζ‖) hsumi hgi, hsummean,
      diskRealMean_poisson_log_norm_of_zero_free hr hrρ (hg.mono hρsub) hgn hw]
    congr 1
    apply congrArg List.sum
    apply List.map_congr_left
    intro p _
    exact diskRealMean_const_mul _ _ _
  rw [hlogw, heq]
  apply add_le_add_right
  apply List.sum_le_sum
  intro p hp
  exact mul_le_mul_of_nonneg_left
    (log_linearFactor_le_diskRealMean_poisson hr (hrootr p hp) hw (hwfacts.1 p hp)) (by positivity)

/-- Jensen's lower bound, obtained by evaluating the proved logarithmic Poisson
inequality at the center. -/
theorem jensen_diskRealMean_log_norm {f : ℂ → ℂ} {r R : ℝ}
    (hr : 0 < r) (hrR : r < R)
    (hf : DifferentiableOn ℂ f (ball (0 : ℂ) R)) (hf0 : f 0 ≠ 0)
    (hfn : ∀ θ : ℝ, f (circleMap 0 r θ) ≠ 0) :
    Real.log ‖f 0‖ ≤ diskRealMean (fun ζ => Real.log ‖f ζ‖) r := by
  have h := log_norm_le_diskRealMean_poisson hr hrR hf (mem_ball_self hr) hf0 hfn
  have heq : diskRealMean (fun ζ => ((ζ + 0) / (ζ - 0)).re * Real.log ‖f ζ‖) r =
      diskRealMean (fun ζ => Real.log ‖f ζ‖) r := by
    unfold diskRealMean
    congr 1
    apply intervalIntegral.integral_congr
    intro θ _
    have hn : circleMap 0 r θ ≠ 0 := by
      apply norm_ne_zero_iff.mp
      rw [norm_circleMap_zero, abs_of_pos hr]
      exact hr.ne'
    simp [hn]
  rw [heq] at h
  exact h

private theorem disk_continuous_posLog_norm {X : Type*} [TopologicalSpace X]
    {f : X → ℂ} (hf : Continuous f) : Continuous (fun z => Real.posLog ‖f z‖) := by
  have heq : ∀ z : ℂ, Real.posLog ‖z‖ = Real.log (max 1 ‖z‖) := by
    intro z
    by_cases hz : ‖z‖ ≤ 1
    · rw [max_eq_left hz, Real.log_one]
      exact (Real.posLog_eq_zero_iff _).mpr (by simpa only [abs_norm] using hz)
    · rw [max_eq_right (le_of_not_ge hz)]
      exact Real.posLog_eq_log (by simpa only [abs_norm] using le_of_not_ge hz)
  simp_rw [heq]
  exact (continuous_const.max hf.norm).log fun z =>
    ne_of_gt (lt_of_lt_of_le zero_lt_one (le_max_left _ _))

private theorem disk_poissonKernel_nonneg {r : ℝ} {ζ w : ℂ}
    (hζ : ‖ζ‖ = r) (hw : ‖w‖ ≤ r) : 0 ≤ ((ζ + w) / (ζ - w)).re := by
  have hnum : (ζ + w).re * (ζ - w).re + (ζ + w).im * (ζ - w).im =
      Complex.normSq ζ - Complex.normSq w := by
    simp only [Complex.add_re, Complex.sub_re, Complex.add_im, Complex.sub_im,
      Complex.normSq_apply]
    ring
  rw [Complex.div_re, ← add_div, hnum]
  apply div_nonneg _ (Complex.normSq_nonneg _)
  rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq, hζ]
  nlinarith [norm_nonneg w]

private theorem disk_poissonKernel_le_three {r : ℝ} (hr : 0 < r) {ζ w : ℂ}
    (hζ : ‖ζ‖ = r) (hw : 2 * ‖w‖ ≤ r) : ((ζ + w) / (ζ - w)).re ≤ 3 := by
  apply (Complex.re_le_norm _).trans
  have hsub := norm_sub_norm_le ζ w
  rw [hζ] at hsub
  have hdenpos : 0 < ‖ζ - w‖ := by linarith [norm_nonneg w]
  rw [norm_div]
  apply (div_le_iff₀ hdenpos).mpr
  have hnum := norm_add_le ζ w
  rw [hζ] at hnum
  linarith

private theorem diskRealMean_mono {f g : ℂ → ℝ} {r : ℝ}
    (hf : IntervalIntegrable (fun θ => f (circleMap 0 r θ)) volume 0 (2 * Real.pi))
    (hg : IntervalIntegrable (fun θ => g (circleMap 0 r θ)) volume 0 (2 * Real.pi))
    (hle : ∀ θ, f (circleMap 0 r θ) ≤ g (circleMap 0 r θ)) :
    diskRealMean f r ≤ diskRealMean g r := by
  unfold diskRealMean
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact intervalIntegral.integral_mono (by positivity) hf hg hle

private theorem diskRealMean_nonneg {f : ℂ → ℝ} {r : ℝ}
    (hf : ∀ θ, 0 ≤ f (circleMap 0 r θ)) : 0 ≤ diskRealMean f r := by
  unfold diskRealMean
  apply mul_nonneg (by positivity)
  exact intervalIntegral.integral_nonneg (by positivity) (fun θ _ => hf θ)

/-- The actual positive-log Poisson inequality, uniform with constant three
when the integration radius is at least twice the evaluation radius. Boundary
zeros are avoided by choosing a zero-free radius; interior zeros are allowed. -/
theorem posLog_norm_le_three_diskRealMean {f : ℂ → ℂ} {r R : ℝ}
    (hr : 0 < r) (hrR : r < R)
    (hf : DifferentiableOn ℂ f (ball (0 : ℂ) R)) {w : ℂ}
    (hw : 2 * ‖w‖ ≤ r)
    (hfn : ∀ θ : ℝ, f (circleMap 0 r θ) ≠ 0) :
    Real.posLog ‖f w‖ ≤ 3 * diskRealMean (fun ζ => Real.posLog ‖f ζ‖) r := by
  have hwr : ‖w‖ < r := by linarith [norm_nonneg w]
  have hwmem : w ∈ ball (0 : ℂ) r := by simpa only [mem_ball, dist_zero_right] using hwr
  have hmeanpos : 0 ≤ diskRealMean (fun ζ => Real.posLog ‖f ζ‖) r :=
    diskRealMean_nonneg (fun _ => Real.posLog_nonneg)
  by_cases hfw : f w = 0
  · simp only [hfw, norm_zero, Real.posLog_def, Real.log_zero, max_self]
    positivity
  · have hlog := log_norm_le_diskRealMean_poisson hr hrR hf hwmem hfw hfn
    have hker := circle_poissonKernel_continuous hr hwr
    have hfθ : Continuous (fun θ => f (circleMap 0 r θ)) := by
      apply continuous_iff_continuousOn_univ.mpr
      exact hf.continuousOn.comp (continuous_circleMap 0 r).continuousOn
        (fun θ _ => closedBall_subset_ball hrR (circle_mem_closedBall hr.le θ))
    have hlogi := (hker.mul (hfθ.norm.log (fun θ => norm_ne_zero_iff.mpr (hfn θ)))).intervalIntegrable
      (μ := volume) (0 : ℝ) (2 * Real.pi)
    have hposi := (disk_continuous_posLog_norm hfθ).intervalIntegrable
      (μ := volume) (0 : ℝ) (2 * Real.pi)
    have hposkeri := (hker.mul (disk_continuous_posLog_norm hfθ)).intervalIntegrable
      (μ := volume) (0 : ℝ) (2 * Real.pi)
    have hlogpos : diskRealMean (fun ζ => ((ζ + w) / (ζ - w)).re * Real.log ‖f ζ‖) r ≤
        diskRealMean (fun ζ => ((ζ + w) / (ζ - w)).re * Real.posLog ‖f ζ‖) r := by
      apply diskRealMean_mono (f := fun ζ => ((ζ + w) / (ζ - w)).re * Real.log ‖f ζ‖)
        (g := fun ζ => ((ζ + w) / (ζ - w)).re * Real.posLog ‖f ζ‖) hlogi hposkeri
      intro θ
      exact mul_le_mul_of_nonneg_left (le_max_right _ _)
        (disk_poissonKernel_nonneg (by rw [norm_circleMap_zero, abs_of_pos hr]) hwr.le)
    have hker3 : diskRealMean (fun ζ => ((ζ + w) / (ζ - w)).re * Real.posLog ‖f ζ‖) r ≤
        3 * diskRealMean (fun ζ => Real.posLog ‖f ζ‖) r := by
      rw [← diskRealMean_const_mul]
      apply diskRealMean_mono (f := fun ζ => ((ζ + w) / (ζ - w)).re * Real.posLog ‖f ζ‖)
        (g := fun ζ => 3 * Real.posLog ‖f ζ‖) hposkeri (hposi.const_mul 3)
      intro θ
      exact mul_le_mul_of_nonneg_right
        (disk_poissonKernel_le_three hr (by rw [norm_circleMap_zero, abs_of_pos hr]) hw) Real.posLog_nonneg
    exact max_le (by positivity) ((hlog.trans hlogpos).trans hker3)

end RieszEuclidean.CompleteMinimal
