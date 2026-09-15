import RieszEuclidean.SupportingDerivative
import Mathlib.Topology.Order.Compact

noncomputable section
open Filter Topology
namespace RieszEuclidean

/-- A bounded nonempty open convex domain has a contact point with a containing
ball centered at any chosen interior point. -/
theorem exists_convex_contact_point {n : ℕ} (hn : 0 < n)
    {Ω : Set (Euclidean n)} (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    {c : Euclidean n} (hc : c ∈ Ω) :
    ∃ p ∈ frontier Ω, p ≠ c ∧ ∀ z ∈ closure Ω, ‖z-c‖ ≤ ‖p-c‖ := by
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  obtain ⟨p, hpK, hfar⟩ := hb.isCompact_closure.exists_isMaxOn
    ⟨c, subset_closure hc⟩ (f := fun x => ‖x-c‖)
    (continuous_id.sub continuous_const).norm.continuousOn
  have hpc : p ≠ c := by
    intro he
    have hsub : Ω ⊆ {c} := by
      intro z hz
      have hh : ‖z-c‖ ≤ ‖p-c‖ := hfar (subset_closure hz)
      rw [he, _root_.sub_self, norm_zero] at hh
      exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm hh (norm_nonneg _)))
    exact (infinite_of_mem_nhds c (hΩ.mem_nhds hc)) (Set.finite_singleton c |>.subset hsub)
  have hJ : innerSL ℝ (p-c) ≠ 0 := by
    intro he
    have hh := DFunLike.congr_fun he (p-c)
    have hn0 : ‖p-c‖ ^ 2 = 0 := by
      simpa only [innerSL_apply, real_inner_self_eq_norm_sq, ContinuousLinearMap.zero_apply] using hh
    exact hpc (sub_eq_zero.mp (norm_eq_zero.mp (pow_eq_zero hn0)))
  have hs : FunctionalSupportsAt (closure Ω) p (innerSL ℝ (p-c)) :=
    (farthest_point_support hfar).1
  have hpS : p ∈ frontier Ω := by
    rw [hΩ.frontier_eq]
    refine ⟨hpK, ?_⟩
    intro hpΩ
    have hh := supporting_functional_strict_interior hΩ hpΩ hJ hs
    simp at hh
  exact ⟨p, hpS, hpc, hfar⟩

end RieszEuclidean
