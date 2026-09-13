import RieszEuclidean.BumpKernel
import RieszEuclidean.SeparatedConfigurations

open Filter Topology

namespace RieszEuclidean

/-- Near any first coordinate, the concrete kernel is one fixed finite sum. -/
theorem bumpKernel_locally_finite_sum {d : ℕ} {δ r : ℝ} {Γ : Set (Euclidean d)}
    (hΓ : Separated δ Γ) (hδ : 0 < δ) (b : Euclidean d → ℂ)
    (hs : ∀ x, r ≤ ‖x‖ → b x = 0) (v₀ : Euclidean d) :
    ∃ s : Finset Γ, ∀ v, dist v v₀ < 1 → ∀ w,
      bumpKernel Γ b v w = ∑ i ∈ s, b (v - i) * star (b (w - i)) := by
  classical
  have hf := (hΓ.finite_inter_compact hδ (isCompact_closedBall v₀ (r + 1))).preimage
    (f := fun i : Γ => (i : Euclidean d)) Subtype.val_injective.injOn
  let s := hf.toFinset
  refine ⟨s, ?_⟩
  intro v hv w
  apply tsum_eq_sum
  intro i hi
  have hfar : ¬dist (i : Euclidean d) v₀ ≤ r + 1 := by
    intro hnear
    apply hi
    exact hf.mem_toFinset.mpr ⟨i.property, hnear⟩
  have hb : b (v - i) = 0 := by
    apply hs
    have ht := dist_triangle (i : Euclidean d) v v₀
    rw [dist_comm (i : Euclidean d) v, dist_eq_norm v (i : Euclidean d)] at ht
    push_neg at hfar
    linarith
  rw [hb, zero_mul]

/-- For a fixed separated configuration, a continuous supported bump gives a jointly continuous kernel. -/
theorem continuous_bumpKernel {d : ℕ} {δ r : ℝ} {Γ : Set (Euclidean d)}
    (hΓ : Separated δ Γ) (hδ : 0 < δ) (b : Euclidean d → ℂ)
    (hb : Continuous b) (hs : ∀ x, r ≤ ‖x‖ → b x = 0) :
    Continuous (fun p : Euclidean d × Euclidean d => bumpKernel Γ b p.1 p.2) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  obtain ⟨s, hs'⟩ := bumpKernel_locally_finite_sum hΓ hδ b hs p.1
  have hc : Continuous (fun q : Euclidean d × Euclidean d =>
      ∑ i ∈ s, b (q.1 - i) * star (b (q.2 - i))) := by
    apply continuous_finset_sum
    intro i _
    exact (hb.comp (continuous_fst.sub continuous_const)).mul
      ((hb.comp (continuous_snd.sub continuous_const)).star)
  apply hc.continuousAt.congr_of_eventuallyEq
  have he : ∀ᶠ q : Euclidean d × Euclidean d in 𝓝 p, dist q.1 p.1 < 1 :=
    continuous_fst.continuousAt (Metric.ball_mem_nhds p.1 zero_lt_one)
  filter_upwards [he] with q hq
  exact hs' q.1 hq q.2

/-- Compact support supplies the radius needed for fixed-configuration joint continuity. -/
theorem continuous_bumpKernel_of_hasCompactSupport {d : ℕ} {δ : ℝ}
    {Γ : Set (Euclidean d)} (hΓ : Separated δ Γ) (hδ : 0 < δ)
    (b : Euclidean d → ℂ) (hb : Continuous b) (hs : HasCompactSupport b) :
    Continuous (fun p : Euclidean d × Euclidean d => bumpKernel Γ b p.1 p.2) := by
  obtain ⟨r, _, hr⟩ := hs.isBounded.subset_ball_lt 0 (0 : Euclidean d)
  apply continuous_bumpKernel hΓ hδ b hb
  intro x hx
  by_contra hbx
  have hh := hr (subset_closure hbx)
  have hn : ‖x‖ < r := by simpa using hh
  exact (not_lt_of_ge hx) hn

end RieszEuclidean
