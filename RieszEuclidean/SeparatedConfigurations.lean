import Mathlib.Data.Set.Card
import RieszEuclidean.WeakLimits
import Mathlib.Topology.MetricSpace.Bounded
open Set Metric
namespace RieszEuclidean
/-- Uniformly separated configurations have finitely many points in each compact region. -/
theorem Separated.finite_inter_compact {d : ℕ} {δ : ℝ} {Γ K : Set (Euclidean d)}
    (h : Separated δ Γ) (hδ : 0 < δ) (hK : IsCompact K) : (Γ ∩ K).Finite := by
  classical
  obtain ⟨t, ht, hcover⟩ := Metric.totallyBounded_iff.mp hK.totallyBounded (δ / 3) (by positivity)
  have hc : ∀ x : ↥(Γ ∩ K), ∃ y : t, dist (x : Euclidean d) y < δ / 3 := by
    intro x
    obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.mp (hcover x.property.2)
    exact ⟨⟨y, hy⟩, hxy⟩
  choose f hf using hc
  have hinj : Function.Injective f := by
    intro x y hxy
    by_contra hne
    have hne' : (x : Euclidean d) ≠ y := fun he => hne (Subtype.ext he)
    have hs := h x.property.1 y.property.1 hne'
    have h1 := hf x
    have h2 := hf y
    rw [hxy] at h1
    have htri := dist_triangle (x : Euclidean d) (f y) (y : Euclidean d)
    rw [dist_comm (f y : Euclidean d) (y : Euclidean d)] at htri
    linarith
  letI := ht.fintype
  haveI : Finite ↥(Γ ∩ K) := Finite.of_injective f hinj
  exact Set.toFinite _
/-- A uniformly separated Euclidean configuration is countable. -/
theorem Separated.countable {d : ℕ} {δ : ℝ} {Γ : Set (Euclidean d)}
    (h : Separated δ Γ) (hδ : 0 < δ) : Γ.Countable := by
  have hc : (⋃ n : ℕ, Γ ∩ Metric.closedBall 0 (n : ℝ)).Countable :=
    Set.countable_iUnion (fun n => (h.finite_inter_compact hδ (isCompact_closedBall 0 (n : ℝ))).countable)
  apply hc.mono
  intro x hx
  obtain ⟨n, hn⟩ := exists_nat_ge ‖x‖
  exact Set.mem_iUnion.mpr ⟨n, hx, by simpa using hn⟩
/-- A configuration with a positive uniform separation constant is closed. -/
theorem Separated.isClosed {d : ℕ} {δ : ℝ} {Γ : Set (Euclidean d)}
    (h : Separated δ Γ) (hδ : 0 < δ) : IsClosed Γ := by
  apply isClosed_of_closure_subset
  intro x hx
  obtain ⟨y, hy, hxy⟩ := Metric.mem_closure_iff.mp hx (δ / 3) (by positivity)
  by_cases he : x = y
  · simpa only [he] using hy
  have hd : 0 < dist x y := dist_pos.mpr he
  obtain ⟨z, hz, hxz⟩ := Metric.mem_closure_iff.mp hx
    (min (dist x y / 2) (δ / 3)) (by positivity)
  have hz1 : dist x z < dist x y / 2 := hxz.trans_le (min_le_left _ _)
  have hne : y ≠ z := by
    intro heq
    rw [← heq] at hz1
    linarith
  have hs := h hy hz hne
  have ht := dist_triangle y x z
  rw [dist_comm y x] at ht
  linarith
/-- Separation gives one compact-region counting bound uniform over all configurations. -/
theorem compact_uniform_separated_count {d : ℕ} {δ : ℝ} (hδ : 0 < δ)
    {K : Set (Euclidean d)} (hK : IsCompact K) :
    ∃ N : ℕ, ∀ Γ : Set (Euclidean d), Separated δ Γ → (Γ ∩ K).ncard ≤ N := by
  classical
  obtain ⟨t, ht, hcover⟩ := Metric.totallyBounded_iff.mp hK.totallyBounded (δ / 3) (by positivity)
  refine ⟨t.ncard, ?_⟩
  intro Γ h
  have hc : ∀ x : ↥(Γ ∩ K), ∃ y : t, dist (x : Euclidean d) y < δ / 3 := by
    intro x
    obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.mp (hcover x.property.2)
    exact ⟨⟨y, hy⟩, hxy⟩
  choose f hf using hc
  have hinj : Function.Injective f := by
    intro x y hxy
    by_contra hne
    have hne' : (x : Euclidean d) ≠ y := fun he => hne (Subtype.ext he)
    have hs := h x.property.1 y.property.1 hne'
    have h1 := hf x
    have h2 := hf y
    rw [hxy] at h1
    have htri := dist_triangle (x : Euclidean d) (f y) (y : Euclidean d)
    rw [dist_comm (f y : Euclidean d) (y : Euclidean d)] at htri
    linarith
  letI := ht.fintype
  haveI : Finite ↥(Γ ∩ K) := Finite.of_injective f hinj
  simpa only [Nat.card_coe_set_eq] using Nat.card_le_card_of_injective f hinj
end RieszEuclidean
