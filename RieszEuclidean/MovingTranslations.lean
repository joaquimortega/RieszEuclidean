import RieszEuclidean.WeakLimits
open Filter
namespace RieszEuclidean
/-- Local matching is preserved when the translation vectors also converge. -/
theorem WeaklyConverges.moving_translate {d : ℕ} {Γ : ℕ → Set (Euclidean d)}
    {Γ₀ : Set (Euclidean d)} (h : WeaklyConverges Γ Γ₀)
    {z : ℕ → Euclidean d} {z₀ : Euclidean d} (hz : Tendsto z atTop (nhds z₀)) :
    WeaklyConverges (fun j => RieszEuclidean.translate (z j) (Γ j)) (RieszEuclidean.translate z₀ Γ₀) := by
  intro R hR ε hε
  obtain ⟨N, hN⟩ := h (R + ‖z₀‖ + 1) (by positivity) (ε / 2) (by positivity)
  have hz' := (Metric.tendsto_atTop.mp hz) (min 1 (ε / 2)) (by positivity)
  obtain ⟨M, hM⟩ := hz'
  refine ⟨max N M, fun j hj => ⟨?_, ?_⟩⟩
  · intro x hx hxR
    have hd := hM j ((le_max_right N M).trans hj)
    have hdist : dist (z j) z₀ < 1 := hd.trans_le (min_le_left _ _)
    have hze : dist (z j) z₀ < ε / 2 := hd.trans_le (min_le_right _ _)
    have hnorm : ‖z j‖ < ‖z₀‖ + 1 := by
      have ht := norm_sub_norm_le (z j) z₀
      rw [← dist_eq_norm] at ht
      linarith
    have hxr : ‖x + z j‖ < R + ‖z₀‖ + 1 := (norm_add_le _ _).trans_lt (by linarith)
    obtain ⟨y, hy, hxy⟩ := (hN j ((le_max_left N M).trans hj)).1 (x + z j) hx hxr
    refine ⟨y - z₀, by simpa [RieszEuclidean.translate] using hy, ?_⟩
    have ht' := dist_triangle (x + z₀) (x + z j) y
    have heq : dist x (y - z₀) = dist (x + z₀) y := by
      simp only [dist_eq_norm]; congr 1; abel
    rw [heq]
    rw [dist_add_left, dist_comm z₀ (z j)] at ht'
    linarith
  · intro y hy hyR
    have hd := hM j ((le_max_right N M).trans hj)
    have hze : dist (z j) z₀ < ε / 2 := hd.trans_le (min_le_right _ _)
    have hyr : ‖y + z₀‖ < R + ‖z₀‖ + 1 := (norm_add_le _ _).trans_lt (by linarith)
    obtain ⟨x, hx, hxy⟩ := (hN j ((le_max_left N M).trans hj)).2 (y + z₀) hy hyr
    refine ⟨x - z j, by simpa [RieszEuclidean.translate] using hx, ?_⟩
    have ht := dist_triangle x (y + z₀) (y + z j)
    have heq : dist (x - z j) y = dist x (y + z j) := by
      simp only [dist_eq_norm]; congr 1; abel
    rw [heq]
    rw [dist_add_left, dist_comm z₀ (z j)] at ht
    linarith
end RieszEuclidean
