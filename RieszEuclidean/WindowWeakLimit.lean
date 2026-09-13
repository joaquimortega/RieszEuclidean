import RieszEuclidean.WindowCompatibility
open Filter TopologicalSpace Metric Set
namespace RieszEuclidean
/-- The ambient configuration assembled from the limits on compact windows. -/
def windowLimitSet {d : ℕ}
    (C : ∀ k : ℕ, Closeds (Metric.closedBall (0 : Euclidean d) (k + 1 : ℝ))) :
    Set (Euclidean d) :=
  {y | ∃ k, ∃ x ∈ C k, (x : Euclidean d) = y}
/-- Simultaneous compact-window convergence implies Beurling weak convergence. -/
theorem weaklyConverges_of_window_limits {d : ℕ}
    {Γ : ℕ → Set (Euclidean d)} (hΓ : ∀ n, IsClosed (Γ n))
    {C : ∀ k : ℕ, Closeds (Metric.closedBall (0 : Euclidean d) (k + 1 : ℝ))}
    (hC : ∀ k : ℕ, Tendsto (fun n => compactRestriction (Metric.closedBall 0 (k + 1 : ℝ))
      (Γ n) (hΓ n)) atTop (nhds (C k))) :
    WeaklyConverges Γ (windowLimitSet C) := by
  intro R _ ε hε
  obtain ⟨k, hk⟩ := exists_nat_gt R
  have hRk : R < (k + 1 : ℝ) := by linarith
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hausdorff_eventually_matching (hC k) hε)
  refine ⟨N, fun n hn => ⟨?_, ?_⟩⟩
  · intro x hx hnorm
    have hxK : x ∈ Metric.closedBall (0 : Euclidean d) (k + 1 : ℝ) := by
      simpa using (le_of_lt (hnorm.trans hRk))
    obtain ⟨y, hy, hxy⟩ := (hN n hn).1 ⟨x, hxK⟩ hx
    exact ⟨y, ⟨k, y, hy, rfl⟩, hxy⟩
  · intro y hy hnorm
    obtain ⟨j, x, hx, rfl⟩ := hy
    have hxK : (x : Euclidean d) ∈ Metric.closedBall 0 (k + 1 : ℝ) := by
      simpa using (le_of_lt (hnorm.trans hRk))
    have hr : 0 < (k + 1 : ℝ) - ‖(x : Euclidean d)‖ := by linarith
    have hb : Metric.ball (x : Euclidean d) ((k + 1 : ℝ) - ‖(x : Euclidean d)‖) ⊆
        Metric.closedBall 0 (k + 1 : ℝ) := by
      intro z hz
      have ht := norm_sub_norm_le z (x : Euclidean d)
      rw [← dist_eq_norm] at ht
      have hz' := Metric.mem_ball.mp hz
      have hnz : ‖z‖ ≤ (k + 1 : ℝ) := by linarith
      simpa using hnz
    have hxC := compactRestriction_limit_interior hΓ (hC k) (hC j) x hx hxK hr hb
    obtain ⟨a, ha, hxa⟩ := (hN n hn).2 ⟨x, hxK⟩ hxC
    refine ⟨a, ha, ?_⟩
    change dist (a : Euclidean d) (x : Euclidean d) < ε
    rw [dist_comm]
    exact hxa
/-- Every sequence with a common positive separation constant has a Beurling weakly
convergent subsequence with the same separation constant. -/
theorem separated_weak_subsequence {d : ℕ} {δ : ℝ} (hδ : 0 < δ)
    (Γ : ℕ → Set (Euclidean d)) (hs : ∀ n, Separated δ (Γ n)) :
    ∃ Γ₀ : Set (Euclidean d), Separated δ Γ₀ ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ WeaklyConverges (fun n => Γ (φ n)) Γ₀ := by
  have hc : ∀ n, IsClosed (Γ n) := fun n => (hs n).isClosed hδ
  obtain ⟨C, φ, hφ, hC⟩ := compactRestrictions_diagonal Γ hc
  have hw := weaklyConverges_of_window_limits (fun n => hc (φ n)) hC
  exact ⟨windowLimitSet C, hw.separated (fun n => hs (φ n)), φ, hφ, hw⟩
end RieszEuclidean
