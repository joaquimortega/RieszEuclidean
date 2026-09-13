import RieszEuclidean.InvariantProbability
import RieszEuclidean.TranslationHull
open MeasureTheory TopologicalSpace
namespace RieszEuclidean.SeparatedConfiguration
/-- The paper's compact translation hull carries a translation-invariant Borel
probability measure obtained from continuous Euclidean box averages. -/
theorem exists_hull_invariant_probability {d : ℕ} {δ : ℝ} (hδ : 0 < δ)
    (Γ : SeparatedConfiguration d δ)
    [MeasurableSpace (hull Γ)] [BorelSpace (hull Γ)] :
    ∃ μ : Measure (hull Γ), IsProbabilityMeasure μ ∧
      ∀ z : Euclidean d, MeasurePreserving (hullTranslate hδ Γ z) μ μ := by
  letI : CompactSpace (hull Γ) := isCompact_iff_compactSpace.mp (isCompact_hull hδ Γ)
  letI := metrizableSpaceMetric (hull Γ)
  let T : Euclidean d → C(hull Γ, hull Γ) := fun z =>
    ⟨hullTranslate hδ Γ z,
      (continuous_hullTranslate hδ Γ).comp (continuous_const.prodMk continuous_id)⟩
  apply exists_invariant_probability_euclidean_action T (continuous_hullTranslate hδ Γ)
  · intro z y x
    apply Subtype.ext
    change translate z (translate y (x : SeparatedConfiguration d δ)) =
      translate (y + z) (x : SeparatedConfiguration d δ)
    rw [translate_add, add_comm z y]
  · exact ⟨Γ, mem_hull Γ⟩
end RieszEuclidean.SeparatedConfiguration
