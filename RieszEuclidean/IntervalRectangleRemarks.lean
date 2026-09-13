import RieszEuclidean.EdgeGeometry

noncomputable section

open MeasureTheory Set

namespace RieszEuclidean

/-- The boundary of a nondegenerate real interval has positive counting mass in
its overlap with a nonzero translate: translating by the interval length sends
the left endpoint to the right endpoint. -/
theorem interval_boundary_positive_translated_overlap (a b : ℝ) (hab : a < b) :
    b - a ≠ 0 ∧
      0 < (Measure.dirac a + Measure.dirac b)
        (frontier (Ioo a b) ∩
          (fun x : ℝ => x + (b - a)) ⁻¹' frontier (Ioo a b)) := by
  constructor
  · linarith
  · rw [frontier_Ioo hab]
    have ha : a ∈ ({a, b} : Set ℝ) ∩
        (fun x : ℝ => x + (b - a)) ⁻¹' ({a, b} : Set ℝ) := by
      constructor
      · simp
      · simp only [mem_preimage, mem_insert_iff, mem_singleton_iff]
        exact Or.inr (by ring)
    have hdirac : Measure.dirac a
        (({a, b} : Set ℝ) ∩
          (fun x : ℝ => x + (b - a)) ⁻¹' ({a, b} : Set ℝ)) = 1 := by
      rw [Measure.dirac_apply_of_mem ha]
    rw [Measure.add_apply, hdirac]
    simp

/-- Two distinct parallel edges related by a perpendicular translation have
their full positive edge length in translated overlap, as happens for opposite
sides of a nondegenerate rectangle. -/
theorem opposite_rectangle_edges_positive_translated_overlap
    (a b θ : Euclidean 2) (hab : a ≠ b) (hθ : θ ≠ 0)
    (hperp : inner (𝕜 := ℝ) θ (b - a) = 0) :
    θ ≠ 0 ∧ inner (𝕜 := ℝ) θ (b - a) = 0 ∧
      0 < edgeLengthMeasure a b
        (openSegment ℝ a b ∩ translate θ (openSegment ℝ (θ + a) (θ + b))) := by
  refine ⟨hθ, hperp, ?_⟩
  have htranslate :
      translate θ (openSegment ℝ (θ + a) (θ + b)) = openSegment ℝ a b := by
    simpa only [translate, add_comm] using openSegment_translate_preimage ℝ θ a b
  rw [htranslate, inter_self, edgeLengthMeasure,
    Measure.restrict_apply (measurableSet_openEdge a b hab), inter_self,
    hausdorffMeasure_openEdge]
  exact edist_pos.mpr hab

end RieszEuclidean
