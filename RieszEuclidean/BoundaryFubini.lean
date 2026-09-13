import RieszEuclidean.GoodParameters
import Mathlib.Topology.Sequences
open MeasureTheory Filter Topology
namespace RieszEuclidean
/-- Fubini reverses null translated overlaps, excluding the unavoidable zero frequency. -/
theorem boundary_exceptional_mass_ae_zero {d : ℕ}
    (σ ν : Measure (Euclidean d)) [SFinite σ] [SFinite ν]
    {S : Set (Euclidean d)} (hS : MeasurableSet S)
    (hoverlap : ∀ θ : Euclidean d, θ ≠ 0 → ν {t | t + θ ∈ S} = 0) :
    ∀ᵐ t ∂ν, σ {θ | θ ≠ 0 ∧ t + θ ∈ S} = 0 := by
  have hm : MeasurableSet {p : Euclidean d × Euclidean d |
      p.2 ≠ 0 ∧ p.1 + p.2 ∈ S} :=
    ((measurableSet_singleton (0 : Euclidean d)).preimage measurable_snd).compl.inter
      (hS.preimage (measurable_fst.add measurable_snd))
  have h : ∀ᵐ θ ∂σ, ∀ᵐ t ∂ν, ¬(θ ≠ 0 ∧ t + θ ∈ S) := by
    apply Filter.Eventually.of_forall
    intro θ
    by_cases hθ : θ = 0
    · exact Filter.Eventually.of_forall (by simp [hθ])
    · rw [ae_iff]
      simpa [hθ] using hoverlap θ hθ
  have hh := (Measure.ae_ae_comm (μ := ν) (ν := σ) hm.compl).mpr h
  filter_upwards [hh] with t ht
  simpa only [ae_iff, not_not] using ht
/-- A nonzero boundary measure supplies one point clean for the entire control measure. -/
theorem exists_clean_boundary_point {d : ℕ}
    (σ ν : Measure (Euclidean d)) [SFinite σ] [SFinite ν]
    {S : Set (Euclidean d)} (hS : MeasurableSet S) (hpos : ν S ≠ 0)
    (hoverlap : ∀ θ : Euclidean d, θ ≠ 0 → ν {t | t + θ ∈ S} = 0) :
    ∃ t ∈ S, σ {θ | θ ≠ 0 ∧ t + θ ∈ S} = 0 := by
  have h := boundary_exceptional_mass_ae_zero σ ν hS hoverlap
  by_contra he
  push_neg at he
  apply hpos
  apply measure_mono_null _ (ae_iff.mp h)
  exact fun t ht => he t ht
/-- The overlap hypothesis can be stated literally on the boundary intersection. -/
theorem exists_clean_boundary_point_of_overlap {d : ℕ}
    (σ ν : Measure (Euclidean d)) [SFinite σ] [SFinite ν]
    {S : Set (Euclidean d)} (hS : MeasurableSet S) (hpos : ν S ≠ 0)
    (hoverlap : ∀ θ : Euclidean d, θ ≠ 0 → ν (S ∩ translate θ S) = 0) :
    ∃ t ∈ S, σ {θ | θ ≠ 0 ∧ t + θ ∈ S} = 0 := by
  apply exists_clean_boundary_point σ (ν.restrict S) hS
  · simpa only [Measure.restrict_apply hS, Set.inter_self] using hpos
  · intro θ hθ
    have hm : MeasurableSet {t : Euclidean d | t + θ ∈ S} :=
      hS.preimage (measurable_id.add_const θ)
    rw [Measure.restrict_apply hm]
    simpa only [translate, Set.inter_comm] using hoverlap θ hθ
/-- A conull set approaches every point of the closure of an open set from within it. -/
theorem exists_conull_sequence_in_open {d : ℕ} {G O : Set (Euclidean d)}
    (hG : volume Gᶜ = 0) (hO : IsOpen O) {x : Euclidean d} (hx : x ∈ closure O) :
    ∃ t : ℕ → Euclidean d, (∀ n, t n ∈ G ∩ O) ∧ Tendsto t atTop (𝓝 x) := by
  have hd : Dense G := Measure.dense_of_ae (μ := volume) hG
  apply mem_closure_iff_seq_limit.mp
  simpa only [closure_closure, Set.inter_comm] using
    closure_mono (hd.open_subset_closure_inter hO) hx
/-- Good parameters can approach from both ambient open sides, with no ray assumption. -/
theorem exists_conull_sequences_two_sides {d : ℕ} {G Ω : Set (Euclidean d)}
    (hG : volume Gᶜ = 0) (hΩ : IsOpen Ω) {x : Euclidean d}
    (hin : x ∈ closure Ω) (hout : x ∈ closure (closure Ω)ᶜ) :
    (∃ t : ℕ → Euclidean d, (∀ n, t n ∈ G ∩ Ω) ∧ Tendsto t atTop (𝓝 x)) ∧
    (∃ t : ℕ → Euclidean d, (∀ n, t n ∈ G ∩ (closure Ω)ᶜ) ∧
      Tendsto t atTop (𝓝 x)) :=
  ⟨exists_conull_sequence_in_open hG hΩ hin,
    exists_conull_sequence_in_open hG isClosed_closure.isOpen_compl hout⟩
end RieszEuclidean
