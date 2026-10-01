import RieszEuclidean.CompleteMinimalConvolutionSupport
import Mathlib.Analysis.Calculus.MeanValue

noncomputable section
open MeasureTheory SchwartzMap Set Filter Topology
open scoped SchwartzMap ContDiff

namespace RieszEuclidean.CompleteMinimal

variable {d : ℕ}

private theorem translateDifference_seminorm_bound (φ : 𝓢(Euclidean d, ℂ))
    (h : Euclidean d) (hh : ‖h‖ ≤ 1) (k j : ℕ) :
    SchwartzMap.seminorm ℂ k j (schwartzTranslateCLM h φ - φ) ≤
      4 ^ k * (Finset.Iic (k, j + 1)).sup
        (fun m => SchwartzMap.seminorm ℂ m.1 m.2) φ * ‖h‖ := by
  let F : Euclidean d → ContinuousMultilinearMap ℝ (fun _ : Fin j => Euclidean d) ℂ :=
    iteratedFDeriv ℝ j (φ : Euclidean d → ℂ)
  let S := (Finset.Iic (k, j + 1)).sup
    (fun m => SchwartzMap.seminorm ℂ m.1 m.2) φ
  apply SchwartzMap.seminorm_le_bound ℂ k j (schwartzTranslateCLM h φ - φ) (by positivity)
  intro x
  have hiter : iteratedFDeriv ℝ j (schwartzTranslateCLM h φ - φ : Euclidean d → ℂ) x =
      F (x + h) - F x := by
    have hfun : (schwartzTranslateCLM h φ - φ : Euclidean d → ℂ) =
        fun y => φ (h + y) - φ y := by
      ext y
      simp [schwartzTranslateCLM_apply]
    rw [hfun]
    change iteratedFDeriv ℝ j
      ((fun y => φ (h + y)) + (fun y => -(φ y))) x = _
    rw [iteratedFDeriv_add_apply]
    · have hneg : (fun y : Euclidean d => -φ y) = -(fun y => (φ : Euclidean d → ℂ) y) := rfl
      rw [hneg, iteratedFDeriv_neg_apply (𝕜 := ℝ) (f := (φ : Euclidean d → ℂ)),
        iteratedFDeriv_comp_add_left]
      change iteratedFDeriv ℝ j (φ : Euclidean d → ℂ) (h + x) +
        -iteratedFDeriv ℝ j (φ : Euclidean d → ℂ) x = _
      simp [F, sub_eq_add_neg, add_comm]
    · have hadd : ContDiff ℝ ∞ (fun y : Euclidean d => h + y) :=
        (contDiff_const : ContDiff ℝ ∞ (fun _ : Euclidean d => h)).add contDiff_id
      have hs := φ.smooth'.comp hadd
      exact (hs.of_le (by exact_mod_cast (le_top : (j : ℕ∞) ≤ ⊤))).contDiffAt
    · have hs := φ.smooth'.neg
      exact (hs.of_le (by exact_mod_cast (le_top : (j : ℕ∞) ≤ ⊤))).contDiffAt
  have hco : (schwartzTranslateCLM h φ - φ : 𝓢(Euclidean d, ℂ)) =
      (schwartzTranslateCLM h φ : Euclidean d → ℂ) - (φ : Euclidean d → ℂ) := by
    ext y
    rfl
  change ‖x‖ ^ k * ‖iteratedFDeriv ℝ j
    (schwartzTranslateCLM h φ - φ : 𝓢(Euclidean d, ℂ)) x‖ ≤ _
  rw [hco, hiter]
  have hFdiff : ∀ z ∈ Metric.closedBall x 1, DifferentiableAt ℝ F z := by
    intro z hz
    exact ((φ.smooth'.iteratedFDeriv_right (m := 1) (i := j)
      (by exact_mod_cast (le_top : ((1 + j : ℕ) : ℕ∞) ≤ ⊤))).differentiable le_rfl) z
  have hFbound : ∀ z ∈ Metric.closedBall x 1,
      ‖fderiv ℝ F z‖ ≤ (4 ^ k * S) / (1 + ‖x‖) ^ k := by
    intro z hz
    have hdist : dist z x ≤ 1 := Metric.mem_closedBall.mp hz
    have hnormxz : ‖x‖ ≤ ‖z‖ + 1 := by
      calc
        ‖x‖ = ‖(x - z) + z‖ := by congr 1; abel
        _ ≤ ‖x - z‖ + ‖z‖ := norm_add_le _ _
        _ = dist z x + ‖z‖ := by rw [dist_eq_norm]; simp [norm_sub_rev]
        _ ≤ _ := by linarith
    have hweight : (1 + ‖x‖) ^ k ≤ 2 ^ k * (1 + ‖z‖) ^ k := by
      have hbase : 1 + ‖x‖ ≤ 2 * (1 + ‖z‖) := by
        nlinarith [norm_nonneg z]
      calc
        _ ≤ (2 * (1 + ‖z‖)) ^ k := by gcongr
        _ = _ := by rw [mul_pow]
    have hseminorm := one_add_le_sup_seminorm_apply (𝕜 := ℂ) (E := Euclidean d) (F := ℂ)
      (m := (k, j + 1))
      (k := k) (n := j + 1) le_rfl le_rfl φ z
    have hderiv := norm_fderiv_iteratedFDeriv (𝕜 := ℝ) (f := (φ : Euclidean d → ℂ))
      (n := j) (x := z)
    have hweighted : ‖fderiv ℝ F z‖ * (1 + ‖x‖) ^ k ≤ 4 ^ k * S := by
      rw [hderiv]
      calc
        ‖iteratedFDeriv ℝ (j + 1) (φ : Euclidean d → ℂ) z‖ * (1 + ‖x‖) ^ k
            ≤ ‖iteratedFDeriv ℝ (j + 1) (φ : Euclidean d → ℂ) z‖ *
                (2 ^ k * (1 + ‖z‖) ^ k) :=
              mul_le_mul_of_nonneg_left hweight (norm_nonneg _)
        _ = 2 ^ k * ((1 + ‖z‖) ^ k *
              ‖iteratedFDeriv ℝ (j + 1) (φ : Euclidean d → ℂ) z‖) := by ring
        _ ≤ 2 ^ k * (2 ^ k * S) := by
              gcongr
        _ = 4 ^ k * S := by
          have hp : (2 : ℝ) ^ k * (2 : ℝ) ^ k = (4 : ℝ) ^ k := by
            rw [← mul_pow]
            norm_num
          calc
            2 ^ k * (2 ^ k * S) = (2 ^ k * 2 ^ k) * S := by ring
            _ = 4 ^ k * S := by rw [hp]
    have hpos : 0 < (1 + ‖x‖) ^ k := by positivity
    exact (le_div_iff₀ hpos).2 (by simpa [mul_comm] using hweighted)
  have hxball : x ∈ Metric.closedBall x 1 := by simp
  have hxhball : x + h ∈ Metric.closedBall x 1 := by
    rw [Metric.mem_closedBall, dist_eq_norm]
    simpa only [add_sub_cancel_left] using hh
  have hmvt := (convex_closedBall x (1 : ℝ)).norm_image_sub_le_of_norm_fderiv_le
    (f := F) (C := (4 ^ k * S) / (1 + ‖x‖) ^ k) hFdiff hFbound hxball hxhball
  have hweight_le : ‖x‖ ^ k ≤ (1 + ‖x‖) ^ k := by gcongr; linarith [norm_nonneg x]
  calc
    ‖x‖ ^ k * ‖F (x + h) - F x‖ ≤
        ‖x‖ ^ k * (((4 ^ k * S) / (1 + ‖x‖) ^ k) * ‖h‖) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      simpa only [show x + h - x = h by abel] using hmvt
    _ ≤ 4 ^ k * S * ‖h‖ := by
      have hp : 0 < (1 + ‖x‖) ^ k := by positivity
      have hcancel : ‖x‖ ^ k * ((4 ^ k * S) / (1 + ‖x‖) ^ k) ≤ 4 ^ k * S := by
        have hD : 0 ≤ 4 ^ k * S := by positivity
        rw [← mul_div_assoc]
        apply (div_le_iff₀ hp).2
        simpa [mul_comm] using mul_le_mul_of_nonneg_right hweight_le hD
      calc
        _ = (‖x‖ ^ k * ((4 ^ k * S) / (1 + ‖x‖) ^ k)) * ‖h‖ := by ring
        _ ≤ (4 ^ k * S) * ‖h‖ := mul_le_mul_of_nonneg_right hcancel (norm_nonneg _)

/-- Translation of a fixed Schwartz function depends continuously on the translation vector. -/
theorem continuous_schwartzTranslateCLM_apply (φ : 𝓢(Euclidean d, ℂ)) :
    Continuous (fun x : Euclidean d => schwartzTranslateCLM x φ) := by
  have hzero : ∀ ψ : 𝓢(Euclidean d, ℂ),
      Filter.Tendsto (fun h : Euclidean d => schwartzTranslateCLM h ψ)
        (𝓝 (0 : Euclidean d)) (𝓝 ψ) := by
    intro ψ
    apply ((schwartz_withSeminorms ℂ (Euclidean d) ℂ).tendsto_nhds
      (fun h : Euclidean d => schwartzTranslateCLM h ψ) ψ).mpr
    intro i ε hε
    let C := 4 ^ i.1 * (Finset.Iic (i.1, i.2 + 1)).sup
      (fun m => SchwartzMap.seminorm ℂ m.1 m.2) ψ
    have hC : 0 ≤ C := by positivity
    let δ := min 1 (ε / (C + 1))
    have hδ : 0 < δ := by positivity
    filter_upwards [Metric.ball_mem_nhds 0 hδ] with h hh
    have hnorm : ‖h‖ < δ := by simpa [Metric.mem_ball] using hh
    have hh1 : ‖h‖ ≤ 1 := (hnorm.trans_le (min_le_left _ _)).le
    have hb := translateDifference_seminorm_bound ψ h hh1 i.1 i.2
    change SchwartzMap.seminorm ℂ i.1 i.2 (schwartzTranslateCLM h ψ - ψ) < ε
    calc
      SchwartzMap.seminorm ℂ i.1 i.2 (schwartzTranslateCLM h ψ - ψ) ≤ C * ‖h‖ := hb
      _ < ε := by
        have hsmall : ‖h‖ < ε / (C + 1) := hnorm.trans_le (min_le_right _ _)
        have hε' : C * (ε / (C + 1)) < ε := by
          calc
            C * (ε / (C + 1)) < (C + 1) * (ε / (C + 1)) :=
              mul_lt_mul_of_pos_right (by linarith) (by positivity)
            _ = ε := by field_simp
        exact (mul_le_mul_of_nonneg_left hsmall.le hC).trans_lt hε'
  have hzero_eq : ∀ ψ : 𝓢(Euclidean d, ℂ), schwartzTranslateCLM (0 : Euclidean d) ψ = ψ := by
    intro ψ
    ext y
    simp [schwartzTranslateCLM_apply]
  apply continuous_iff_continuousAt.mpr
  intro x
  have harg : ContinuousAt (fun y : Euclidean d => y - x) x := by
    simpa using (continuousAt_id.sub continuousAt_const :
      ContinuousAt (fun y : Euclidean d => y - (x : Euclidean d)) x)
  have hcont0x : ContinuousAt
      (fun h : Euclidean d => schwartzTranslateCLM h (schwartzTranslateCLM x φ))
      (0 : Euclidean d) := by
    simpa [ContinuousAt, hzero_eq (schwartzTranslateCLM x φ)] using
      hzero (schwartzTranslateCLM x φ)
  have hcont0x' : ContinuousAt
      (fun h : Euclidean d => schwartzTranslateCLM h (schwartzTranslateCLM x φ)) (x - x) := by
    convert hcont0x using 1
    simp
  have hshiftComp : ContinuousAt
      ((fun t : Euclidean d => schwartzTranslateCLM t (schwartzTranslateCLM x φ)) ∘
        fun y : Euclidean d => y - x) x :=
    hcont0x'.comp (f := fun y : Euclidean d => y - x) harg
  have heq : (fun y : Euclidean d =>
      schwartzTranslateCLM (y - x) (schwartzTranslateCLM x φ)) =
      fun y => schwartzTranslateCLM y φ := by
    funext y
    ext z
    simp only [schwartzTranslateCLM_apply]
    congr 1
    abel
  exact heq ▸ hshiftComp

end RieszEuclidean.CompleteMinimal
