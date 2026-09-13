import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.Topology.EMetricSpace.Paracompact
import RieszEuclidean.SeparatedConfigurations
import Mathlib.MeasureTheory.Measure.Count
namespace RieszEuclidean
open MeasureTheory
/-- The counting measure of a Euclidean configuration, with one unit mass per point. -/
noncomputable def configurationMeasure {d : ℕ} (Γ : Set (Euclidean d)) : Measure (Euclidean d) :=
  Measure.map (fun x : Γ => (x : Euclidean d)) Measure.count
/-- Counting a measurable region counts exactly its configuration preimage. -/
theorem configurationMeasure_apply {d : ℕ} (Γ : Set (Euclidean d))
    {K : Set (Euclidean d)} (hK : MeasurableSet K) :
    configurationMeasure Γ K = Measure.count {x : Γ | (x : Euclidean d) ∈ K} := by
  exact Measure.map_apply measurable_subtype_coe hK
/-- The counting measure of a separated configuration is finite on compact regions. -/
theorem configurationMeasure_compact_lt_top {d : ℕ} {δ : ℝ} {Γ K : Set (Euclidean d)}
    (h : Separated δ Γ) (hδ : 0 < δ) (hK : IsCompact K) : configurationMeasure Γ K < ⊤ := by
  letI : T0Space (Euclidean d) := MetricSpace.instT0Space
  rw [configurationMeasure_apply Γ hK.measurableSet, Measure.count_apply_lt_top]
  have hf := (h.finite_inter_compact hδ hK).preimage (f := fun x : Γ => (x : Euclidean d)) Subtype.val_injective.injOn
  simpa only [Set.preimage_inter, Subtype.coe_preimage_self, Set.univ_inter] using hf
/-- Separated configurations define measures finite on all compact sets. -/
theorem configurationMeasure_finiteOnCompacts {d : ℕ} {δ : ℝ} {Γ : Set (Euclidean d)}
    (h : Separated δ Γ) (hδ : 0 < δ) : IsFiniteMeasureOnCompacts (configurationMeasure Γ) :=
  ⟨fun _ hK => configurationMeasure_compact_lt_top h hδ hK⟩
/-- Configuration measure agrees with the extended cardinality of the intersection. -/
theorem configurationMeasure_eq_encard {d : ℕ} (Γ : Set (Euclidean d))
    {K : Set (Euclidean d)} (hK : MeasurableSet K) :
    configurationMeasure Γ K = ((Γ ∩ K).encard : ENNReal) := by
  rw [configurationMeasure_apply Γ hK]
  have hm : MeasurableSet {x : Γ | (x : Euclidean d) ∈ K} := measurable_subtype_coe hK
  rw [Measure.count_apply hm]
  have him : (fun x : Γ => (x : Euclidean d)) '' {x : Γ | (x : Euclidean d) ∈ K} = Γ ∩ K := by
    ext x
    simp only [Set.mem_image, Set.mem_setOf_eq, Set.mem_inter_iff]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.property, hy⟩
    · rintro ⟨hx, hk⟩
      exact ⟨⟨x, hx⟩, hk, rfl⟩
  have he := (Subtype.val_injective : Function.Injective (fun x : Γ => (x : Euclidean d))).encard_image
    {x : Γ | (x : Euclidean d) ∈ K}
  rw [him] at he
  exact congrArg (fun n : ENat => (n : ENNReal)) he.symm
/-- For a finite intersection the measure is its ordinary counting cardinality. -/
theorem configurationMeasure_eq_ncard {d : ℕ} (Γ : Set (Euclidean d))
    {K : Set (Euclidean d)} (hK : MeasurableSet K) (hf : (Γ ∩ K).Finite) :
    configurationMeasure Γ K = ((Γ ∩ K).ncard : ENNReal) := by
  rw [configurationMeasure_eq_encard Γ hK, hf.encard_eq_coe]
  rfl
/-- A common separation constant bounds the counting measures uniformly on each compact set. -/
theorem configurationMeasure_uniform_compact_bound {d : ℕ} {δ : ℝ} (hδ : 0 < δ)
    {K : Set (Euclidean d)} (hK : IsCompact K) :
    ∃ N : ℕ, ∀ Γ : Set (Euclidean d), Separated δ Γ → configurationMeasure Γ K ≤ N := by
  obtain ⟨N, hN⟩ := compact_uniform_separated_count hδ hK
  refine ⟨N, fun Γ hΓ => ?_⟩
  rw [configurationMeasure_eq_ncard Γ hK.measurableSet (hΓ.finite_inter_compact hδ hK)]
  exact_mod_cast hN Γ hΓ
end RieszEuclidean
