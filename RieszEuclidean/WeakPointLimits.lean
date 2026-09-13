import RieszEuclidean.SeparatedConfigurations
open Filter Metric Set
namespace RieszEuclidean
/-- A convergent sequence of configuration points belongs to the closed weak limit. -/
theorem WeaklyConverges.mem_of_tendsto {d : ℕ} {Γ : ℕ → Set (Euclidean d)}
    {Γ₀ : Set (Euclidean d)} (h : WeaklyConverges Γ Γ₀) (hc : IsClosed Γ₀)
    {x : ℕ → Euclidean d} {x₀ : Euclidean d}
    (hx : ∀ j, x j ∈ Γ j) (ht : Tendsto x atTop (nhds x₀)) : x₀ ∈ Γ₀ := by
  apply hc.closure_subset
  rw [Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨N, hN⟩ := h (‖x₀‖ + 1) (by positivity) (ε / 2) (by positivity)
  obtain ⟨M, hM⟩ := Metric.tendsto_atTop.mp ht (min 1 (ε / 2)) (by positivity)
  let j := max N M
  have hd := hM j (le_max_right _ _)
  have hd1 : dist (x j) x₀ < 1 := hd.trans_le (min_le_left _ _)
  have hdε : dist (x j) x₀ < ε / 2 := hd.trans_le (min_le_right _ _)
  have hr : ‖x j‖ < ‖x₀‖ + 1 := by
    have hn := norm_sub_norm_le (x j) x₀
    rw [← dist_eq_norm] at hn
    linarith
  obtain ⟨y, hy, hxy⟩ := (hN j (le_max_left _ _)).1 (x j) (hx j) hr
  refine ⟨y, hy, ?_⟩
  have htri := dist_triangle x₀ (x j) y
  rw [dist_comm x₀ (x j)] at htri
  linarith
end RieszEuclidean
