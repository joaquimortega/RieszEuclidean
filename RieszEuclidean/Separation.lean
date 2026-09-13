import RieszEuclidean.Basic
import Mathlib.Analysis.SpecialFunctions.Exp

/-! Uniform separation of the frequencies of an exponential Riesz basis. -/

noncomputable section
open MeasureTheory
namespace RieszEuclidean
/-- Invertible synthesis uniformly separates distinct coordinate columns. -/
theorem synthesis_columns_separated {ι H : Type} [DecidableEq ι] [NormedAddCommGroup H] [NormedSpace ℂ H]
    (S : SeqL2 ι ≃L[ℂ] H) :
    ∃ c : ℝ, 0 < c ∧ ∀ i j : ι, i ≠ j →
      c ≤ ‖S (lp.single 2 i 1) - S (lp.single 2 j 1)‖ := by
  classical
  let K := ‖S.symm.toContinuousLinearMap‖ + 1
  have hK : 0 < K := by dsimp [K]; positivity
  refine ⟨1 / K, one_div_pos.mpr hK, ?_⟩
  intro i j hij
  have hc : 1 ≤ ‖lp.single (E := fun _ : ι => ℂ) 2 i 1 - lp.single 2 j 1‖ := by
    have h := lp.norm_apply_le_norm (by norm_num : (2 : ENNReal) ≠ 0)
      (lp.single (E := fun _ : ι => ℂ) 2 i 1 - lp.single 2 j 1) i
    simpa [lp.single_apply, hij, hij.symm] using h
  have hb := S.symm.toContinuousLinearMap.le_opNorm
    (S (lp.single 2 i 1) - S (lp.single 2 j 1))
  have heq : S.symm (S (lp.single 2 i 1) - S (lp.single 2 j 1)) =
      lp.single 2 i 1 - lp.single 2 j 1 := by simp
  change ‖S.symm (S (lp.single 2 i 1) - S (lp.single 2 j 1))‖ ≤ _ at hb
  rw [heq] at hb
  apply (div_le_iff₀ hK).mpr
  have hnonneg := norm_nonneg (S (lp.single 2 i 1) - S (lp.single 2 j 1))
  dsimp [K]
  nlinarith
/-- A real phase difference has the same norm after multiplication by i. -/
theorem imaginary_phase_sub_norm (a b : ℝ) :
    ‖(a : ℂ) * Complex.I - (b : ℂ) * Complex.I‖ = |a - b| := by
  rw [← sub_mul, norm_mul, Complex.norm_I, mul_one, ← Complex.ofReal_sub]
  exact Complex.norm_real (a - b)
/-- A uniform local estimate for complex exponentials of real phases. -/
theorem phase_exp_sub_le {a b : ℝ} (h : |a - b| < 1) :
    ‖Complex.exp ((a : ℂ) * Complex.I) - Complex.exp ((b : ℂ) * Complex.I)‖ ≤
      2 * |a - b| := by
  have hb : ‖Complex.exp ((b : ℂ) * Complex.I)‖ = 1 := by simp [Complex.norm_exp]
  have hd : ‖(a : ℂ) * Complex.I - (b : ℂ) * Complex.I‖ < 1 := by
    rwa [imaginary_phase_sub_norm]
  have he := Complex.locally_lipschitz_exp (r := 1) zero_le_one le_rfl
    ((b : ℂ) * Complex.I) ((a : ℂ) * Complex.I) hd
  simpa only [hb, imaginary_phase_sub_norm, one_add_one_eq_two, mul_one] using he
/-- Rewrite the paper's exponential as the exponential of a real phase times i. -/
theorem exponential_eq_phase {d : ℕ} (ξ x : Euclidean d) :
    exponential ξ x = Complex.exp ((2 * Real.pi * inner (𝕜 := ℝ) ξ x : ℝ) * Complex.I) := by
  unfold exponential
  congr 1
  push_cast
  ring
/-- Quantitative uniform continuity of exponential columns on a bounded domain. -/
theorem exponential_sub_le_on_ball {d : ℕ} (ξ η x : Euclidean d) {R : ℝ}
    (hx : ‖x‖ ≤ R) (hsmall : 2 * Real.pi * ‖ξ - η‖ * R < 1) :
    ‖exponential ξ x - exponential η x‖ ≤ 4 * Real.pi * R * ‖ξ - η‖ := by
  have hphase : |2 * Real.pi * inner (𝕜 := ℝ) ξ x - 2 * Real.pi * inner (𝕜 := ℝ) η x| ≤
      2 * Real.pi * ‖ξ - η‖ * R := by
    calc
      _ = 2 * Real.pi * |inner (𝕜 := ℝ) (ξ - η) x| := by
        rw [← mul_sub, ← inner_sub_left, abs_mul, abs_of_nonneg (by positivity : 0 ≤ 2 * Real.pi)]
      _ ≤ 2 * Real.pi * (‖ξ - η‖ * ‖x‖) :=
        mul_le_mul_of_nonneg_left (abs_real_inner_le_norm _ _) (by positivity)
      _ ≤ 2 * Real.pi * ‖ξ - η‖ * R := by
        rw [← mul_assoc]
        exact mul_le_mul_of_nonneg_left hx (by positivity)
  rw [exponential_eq_phase, exponential_eq_phase]
  calc
    _ ≤ 2 * |2 * Real.pi * inner (𝕜 := ℝ) ξ x - 2 * Real.pi * inner (𝕜 := ℝ) η x| :=
      phase_exp_sub_le (hphase.trans_lt hsmall)
    _ ≤ 2 * (2 * Real.pi * ‖ξ - η‖ * R) := mul_le_mul_of_nonneg_left hphase (by norm_num)
    _ = _ := by ring
/-- Every exponential Riesz basis on a bounded measurable domain has separated frequencies. -/
theorem riesz_frequencies_separated {d : ℕ} {Ω Λ : Set (Euclidean d)}
    (hΩ : MeasurableSet Ω) (hb : Bornology.IsBounded Ω)
    (hB : HasExponentialRieszBasis Ω Λ) : ∃ δ : ℝ, 0 < δ ∧ Separated δ Λ := by
  classical
  obtain ⟨S, hS⟩ := hB
  obtain ⟨c, hc, hcols⟩ := synthesis_columns_separated S
  obtain ⟨R, hR, hbound⟩ := hb.exists_pos_norm_le
  haveI : IsFiniteMeasure (volume.restrict Ω) := ⟨by simpa using hb.measure_lt_top (μ := volume)⟩
  let M : ℝ := (measureUnivNNReal (volume.restrict Ω) : ℝ) ^ (2 : ENNReal).toReal⁻¹
  let K : ℝ := M * (4 * Real.pi * R)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  let A : ℝ := 2 * Real.pi * R
  have hA : 0 ≤ A := by dsimp [A]; positivity
  let δ := min (1 / (A + 1)) (c / (K + 1))
  have hδ : 0 < δ := lt_min (one_div_pos.mpr (by linarith)) (div_pos hc (by linarith))
  refine ⟨δ, hδ, ?_⟩
  intro ξ hξ η hη hne
  by_contra! hdist
  have hdist' : ‖ξ - η‖ < δ := by simpa only [dist_eq_norm] using hdist
  have hn := norm_nonneg (ξ - η)
  have hsmall : 2 * Real.pi * ‖ξ - η‖ * R < 1 := by
    have h := (lt_div_iff₀ (show 0 < A + 1 by linarith)).mp
      (hdist'.trans_le (min_le_left _ _))
    dsimp [A] at h
    nlinarith
  let i : Λ := ⟨ξ, hξ⟩
  let j : Λ := ⟨η, hη⟩
  have hij : i ≠ j := fun h => hne (congrArg Subtype.val h)
  have hlower := hcols i j hij
  have hae : ∀ᵐ x ∂volume.restrict Ω,
      ‖((S (lp.single 2 i 1) - S (lp.single 2 j 1) : DomainL2 Ω) : Euclidean d → ℂ) x‖ ≤
        4 * Real.pi * R * ‖ξ - η‖ := by
    filter_upwards [Lp.coeFn_sub (S (lp.single 2 i 1)) (S (lp.single 2 j 1)),
      hS i, hS j, ae_restrict_mem hΩ] with x hsub hi hj hx
    simp only [hsub, Pi.sub_apply, hi, hj]
    exact exponential_sub_le_on_ball ξ η x (hbound x hx) hsmall
  have hupper := Lp.norm_le_of_ae_bound (by positivity : 0 ≤ 4 * Real.pi * R * ‖ξ - η‖) hae
  change ‖S (lp.single 2 i 1) - S (lp.single 2 j 1)‖ ≤ M * (4 * Real.pi * R * ‖ξ - η‖) at hupper
  have h := (lt_div_iff₀ (show 0 < K + 1 by linarith)).mp
    (hdist'.trans_le (min_le_right _ _))
  dsimp [K] at h
  nlinarith
end RieszEuclidean
