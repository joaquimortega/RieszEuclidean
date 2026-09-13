import RieszEuclidean.SchwartzDensity
noncomputable section
set_option maxHeartbeats 800000
open scoped ContDiff
open MeasureTheory
namespace RieszEuclidean
/-- A nonnegative smooth bump supported in any prescribed positive-radius ball. -/
theorem exists_schwartz_bump {d : ℕ} {r : ℝ} (hr : 0 < r) :
    ∃ b : SchwartzMap (Euclidean d) ℂ,
      HasCompactSupport b ∧ b 0 = 1 ∧
      (∀ x, (b x).im = 0 ∧ 0 ≤ (b x).re) ∧
      (∀ x, r ≤ ‖x‖ → b x = 0) := by
  let φ : ContDiffBump (0 : Euclidean d) := ⟨r / 2, r, by positivity, by linarith⟩
  have hs : HasCompactSupport (fun x => (φ x : ℂ)) :=
    φ.hasCompactSupport.comp_left Complex.ofReal_zero
  have hd : ContDiff ℝ ∞ (fun x => (φ x : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp φ.contDiff
  let b := compactSchwartz (fun x => (φ x : ℂ)) hd hs
  refine ⟨b, hs, ?_, ?_, ?_⟩
  · change (φ 0 : ℂ) = 1
    rw [φ.one_of_mem_closedBall (by simp only [Metric.mem_closedBall, dist_self]; exact φ.rIn_pos.le)]
    rfl
  · intro x
    exact ⟨Complex.ofReal_im _, φ.nonneg⟩
  · intro x hx
    change (φ x : ℂ) = 0
    rw [φ.zero_of_le_dist (by simpa [φ] using hx)]
    rfl
/-- The bump is a nonzero vector of Euclidean L². -/
theorem bump_toLp_ne_zero {d : ℕ} (b : SchwartzMap (Euclidean d) ℂ)
    (hb : b 0 = 1) : b.toLp 2 volume ≠ 0 := by
  intro h
  have he : b = 0 := SchwartzMap.injective_toLp 2 volume (by
    simpa only [map_zero] using h)
  have hz := congrArg (fun f : SchwartzMap (Euclidean d) ℂ => f 0) he
  simp [hb] at hz
/-- Normalize a nonnegative compact bump in Euclidean L². -/
theorem exists_normalized_schwartz_bump {d : ℕ} {r : ℝ} (hr : 0 < r) :
    ∃ b : SchwartzMap (Euclidean d) ℂ,
      HasCompactSupport b ∧ ‖b.toLp 2 volume‖ = 1 ∧
      (∀ x, (b x).im = 0 ∧ 0 ≤ (b x).re) ∧
      (∀ x, r ≤ ‖x‖ → b x = 0) ∧ 0 < (b 0).re := by
  obtain ⟨b, hs, hb, hp, hz⟩ := exists_schwartz_bump (d := d) hr
  let N := ‖b.toLp 2 volume‖
  have hN : 0 < N := norm_pos_iff.mpr (bump_toLp_ne_zero b hb)
  refine ⟨N⁻¹ • b, ?_, ?_, ?_, ?_, ?_⟩
  · exact hs.smul_left
  · change ‖(SchwartzMap.toLpCLM ℝ ℂ 2 volume) (N⁻¹ • b)‖ = 1
    rw [map_smul, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hN)]
    exact inv_mul_cancel₀ hN.ne'
  · intro x
    change (N⁻¹ • b x).im = 0 ∧ 0 ≤ (N⁻¹ • b x).re
    simp only [Complex.real_smul, Complex.mul_im, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero, sub_zero]
    exact ⟨by rw [(hp x).1, mul_zero], mul_nonneg (inv_nonneg.mpr hN.le) (hp x).2⟩
  · intro x hx
    change N⁻¹ • b x = 0
    rw [hz x hx, smul_zero]
  · change (N⁻¹ • b 0).re > 0
    rw [hb]
    simpa using inv_pos.mpr hN
end RieszEuclidean
