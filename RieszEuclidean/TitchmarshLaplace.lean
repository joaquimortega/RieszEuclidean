import RieszEuclidean.CompleteMinimalEntireFourier
import Mathlib.Analysis.Complex.Liouville

/-! Analytic core of the directional Laplace support argument. -/

noncomputable section

namespace RieszEuclidean.CompleteMinimal

/-- The Liouville step in the self-convolution support argument. A bound on
the square of the full transform controls the full transform itself. -/
theorem laplace_low_part_eq_zero
    (F G H : ℂ → ℂ) (hG : Differentiable ℂ G)
    (hdecomp : ∀ z, F z = G z + H z)
    {C D E : ℝ} (hC : 0 ≤ C)
    (hFsq : ∀ z, 0 ≤ z.re → ‖F z‖ ^ 2 ≤ C ^ 2)
    (hH : ∀ z, 0 ≤ z.re → ‖H z‖ ≤ D)
    (hGleft : ∀ z, z.re ≤ 0 → ‖G z‖ ≤ E)
    (hvanish : Filter.Tendsto (fun t : ℝ => G (-(t : ℂ)))
      Filter.atTop (nhds 0)) :
    G = 0 := by
  have hbound : ∀ z, ‖G z‖ ≤ max E (C + D) := by
    intro z
    by_cases hz : 0 ≤ z.re
    · have hFn : ‖F z‖ ≤ C := by
        have := hFsq z hz
        nlinarith [norm_nonneg (F z)]
      have hEq : G z = F z - H z := by rw [hdecomp z]; abel
      calc
        ‖G z‖ = ‖F z - H z‖ := by rw [hEq]
        _ ≤ ‖F z‖ + ‖H z‖ := norm_sub_le _ _
        _ ≤ C + D := add_le_add hFn (hH z hz)
        _ ≤ max E (C + D) := le_max_right _ _
    · exact (hGleft z (le_of_lt (lt_of_not_ge hz))).trans (le_max_left _ _)
  have hb : Bornology.IsBounded (Set.range G) := by
    apply isBounded_iff_forall_norm_le.mpr
    refine ⟨max E (C + D), ?_⟩
    rintro y ⟨z, rfl⟩
    exact hbound z
  have hconst : ∀ z, G z = G 0 := fun z => hG.apply_eq_apply_of_bounded hb z 0
  have hzero : G 0 = 0 := by
    have hc : Filter.Tendsto (fun _ : ℝ => G 0) Filter.atTop (nhds (G 0)) :=
      tendsto_const_nhds
    have heq : (fun t : ℝ => G (-(t : ℂ))) = fun _ => G 0 := by
      funext t
      exact hconst _
    exact tendsto_nhds_unique (heq ▸ hvanish) hc |>.symm
  funext z
  simpa [hzero] using hconst z

end RieszEuclidean.CompleteMinimal
