import RieszEuclidean.Basic
import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.MeasureTheory.Constructions.Polish.Basic

noncomputable section
open MeasureTheory
namespace RieszEuclidean

/-- Literal length measure on the relative interior of a Euclidean edge. -/
def edgeLengthMeasure {d : ℕ} (a b : Euclidean d) : Measure (Euclidean d) :=
  (Measure.hausdorffMeasure 1).restrict (openSegment ℝ a b)

/-- The relative interior of a nondegenerate edge is Borel. -/
theorem measurableSet_openEdge {d : ℕ} (a b : Euclidean d) (hab : a ≠ b) :
    MeasurableSet (openSegment ℝ a b) := by
  rw [openSegment_eq_image_lineMap]
  apply measurableSet_Ioo.image_of_continuousOn_injOn
  · exact (by
      change Continuous (fun t : ℝ => t • (b - a) + a)
      fun_prop : Continuous (AffineMap.lineMap a b)).continuousOn
  · exact (AffineMap.lineMap_injective ℝ hab).injOn

/-- One-dimensional Hausdorff measure of the open edge equals its Euclidean length. -/
theorem hausdorffMeasure_openEdge {d : ℕ} (a b : Euclidean d) :
    Measure.hausdorffMeasure 1 (openSegment ℝ a b) = edist a b := by
  rw [openSegment_eq_image_lineMap, hausdorffMeasure_lineMap_image,
    hausdorffMeasure_real, Real.volume_Ioo]
  simp only [sub_zero, ENNReal.ofReal_one]
  rw [← Algebra.algebraMap_eq_smul_one]
  exact (edist_nndist a b).symm

/-- Edge length has finite total mass, with no ambient area measure substituted. -/
theorem edgeLengthMeasure_finite {d : ℕ} (a b : Euclidean d) :
    IsFiniteMeasure (edgeLengthMeasure a b) := by
  constructor
  rw [edgeLengthMeasure, Measure.restrict_apply_univ, hausdorffMeasure_openEdge]
  exact edist_lt_top a b

/-- A nondegenerate open edge has strictly positive total length. -/
theorem edgeLengthMeasure_univ_pos {d : ℕ} (a b : Euclidean d) (hab : a ≠ b) :
    0 < edgeLengthMeasure a b Set.univ := by
  rw [edgeLengthMeasure, Measure.restrict_apply_univ, hausdorffMeasure_openEdge]
  exact edist_pos.mpr hab

/-- Length measure is concentrated on the relative interior used to define it. -/
theorem edgeLengthMeasure_ae_edge {d : ℕ} (a b : Euclidean d) (hab : a ≠ b) :
    ∀ᵐ x ∂edgeLengthMeasure a b, x ∈ openSegment ℝ a b :=
  ae_restrict_mem (measurableSet_openEdge a b hab)

/-- A line segment meets a transverse translated hyperplane in at most one point. -/
theorem openEdge_inter_translate_hyperplane_subsingleton {d : ℕ}
    (a b n θ : Euclidean d) (c : ℝ)
    (htrans : inner (𝕜 := ℝ) (b - a) n ≠ 0) :
    (openSegment ℝ a b ∩ translate θ {x | inner (𝕜 := ℝ) x n = c}).Subsingleton := by
  rintro x ⟨hx, hxH⟩ y ⟨hy, hyH⟩
  rw [openSegment_eq_image_lineMap] at hx hy
  obtain ⟨s, _, rfl⟩ := hx
  obtain ⟨t, _, rfl⟩ := hy
  have heq : s = t := by
    simp only [mem_translate, Set.mem_setOf_eq, AffineMap.lineMap_apply_module',
      inner_add_left, inner_smul_left, RCLike.conj_to_real] at hxH hyH
    exact mul_right_cancel₀ htrans (by linarith : s * inner (𝕜 := ℝ) (b - a) n =
      t * inner (𝕜 := ℝ) (b - a) n)
  rw [heq]

/-- Every translated transverse supporting hyperplane is null for literal edge length. -/
theorem edgeLengthMeasure_translate_hyperplane {d : ℕ}
    (a b n θ : Euclidean d) (c : ℝ)
    (htrans : inner (𝕜 := ℝ) (b - a) n ≠ 0) :
    edgeLengthMeasure a b (translate θ {x | inner (𝕜 := ℝ) x n = c}) = 0 := by
  haveI := Measure.noAtoms_hausdorff (Euclidean d) (show (0 : ℝ) < 1 by norm_num)
  have hm : MeasurableSet (translate θ {x | inner (𝕜 := ℝ) x n = c}) :=
    (isClosed_eq (by fun_prop) continuous_const).measurableSet
  rw [edgeLengthMeasure, Measure.restrict_apply hm, Set.inter_comm]
  exact (openEdge_inter_translate_hyperplane_subsingleton a b n θ c htrans).measure_zero _

/-- If an edge is in a supporting hyperplane, translations between its points
have zero normal component. -/
theorem inner_translation_eq_zero_of_same_hyperplane {d : ℕ}
    (x θ n : Euclidean d) (c : ℝ)
    (hx : inner (𝕜 := ℝ) x n = c)
    (hxθ : inner (𝕜 := ℝ) (x + θ) n = c) :
    inner (𝕜 := ℝ) θ n = 0 := by
  rw [inner_add_left, hx] at hxθ
  linarith

/-- Translation preserves a supporting hyperplane exactly when its normal component is zero. -/
theorem translate_hyperplane_eq_self_iff {d : ℕ} (n θ : Euclidean d) (c : ℝ)
    (hne : ({x : Euclidean d | inner (𝕜 := ℝ) x n = c}).Nonempty) :
    translate θ {x | inner (𝕜 := ℝ) x n = c} = {x | inner (𝕜 := ℝ) x n = c} ↔
      inner (𝕜 := ℝ) θ n = 0 := by
  constructor
  · intro h
    obtain ⟨x, hx⟩ := hne
    have hxθ : x ∈ translate θ {x | inner (𝕜 := ℝ) x n = c} := by rw [h]; exact hx
    exact inner_translation_eq_zero_of_same_hyperplane x θ n c hx hxθ
  · intro h
    ext x
    simp only [mem_translate, Set.mem_setOf_eq, inner_add_left, h, add_zero]

/-- Every translated set contained in a transverse supporting hyperplane is null. -/
theorem edgeLengthMeasure_translate_null_of_subset_hyperplane {d : ℕ}
    (a b n θ : Euclidean d) (c : ℝ) (F : Set (Euclidean d))
    (hF : F ⊆ {x | inner (𝕜 := ℝ) x n = c})
    (htrans : inner (𝕜 := ℝ) (b - a) n ≠ 0) :
    edgeLengthMeasure a b (translate θ F) = 0 := by
  apply measure_mono_null (show translate θ F ⊆
    translate θ {x | inner (𝕜 := ℝ) x n = c} from fun _ hx => hF hx)
  exact edgeLengthMeasure_translate_hyperplane a b n θ c htrans

/-- A planar normal obtained by rotating an edge direction through a right angle. -/
def planarEdgeNormal (v : Euclidean 2) : Euclidean 2 :=
  (WithLp.equiv 2 (Fin 2 → ℝ)).symm ![-v 1, v 0]

/-- The normal pairing is the determinant of the two planar directions. -/
theorem inner_planarEdgeNormal (u v : Euclidean 2) :
    inner (𝕜 := ℝ) u (planarEdgeNormal v) = u 1 * v 0 - u 0 * v 1 := by
  simp [PiLp.inner_apply, Fin.sum_univ_two, planarEdgeNormal, real_inner_comm]
  ring

/-- A closed planar edge lies in the hyperplane determined by its perpendicular normal. -/
theorem segment_subset_planar_support (c e : Euclidean 2) :
    segment ℝ c e ⊆ {x | inner (𝕜 := ℝ) x (planarEdgeNormal (e - c)) =
      inner (𝕜 := ℝ) c (planarEdgeNormal (e - c))} := by
  intro x hx
  rw [segment_eq_image_lineMap] at hx
  obtain ⟨t, _, rfl⟩ := hx
  have hz : inner (𝕜 := ℝ) (e - c) (planarEdgeNormal (e - c)) = 0 := by
    rw [inner_planarEdgeNormal]
    ring
  change inner (𝕜 := ℝ) (t • (e - c) + c) (planarEdgeNormal (e - c)) = _
  rw [inner_add_left, inner_smul_left, hz, mul_zero, zero_add]

/-- Nonparallel closed planar edges have null translated overlap for literal open-edge length.
Nonparallelism is expressed by the nonzero determinant of their directions. -/
theorem edgeLengthMeasure_translate_nonparallel_segment (a b c e θ : Euclidean 2)
    (htrans : (b - a) 1 * (e - c) 0 - (b - a) 0 * (e - c) 1 ≠ 0) :
    edgeLengthMeasure a b (translate θ (segment ℝ c e)) = 0 := by
  apply edgeLengthMeasure_translate_null_of_subset_hyperplane
    a b (planarEdgeNormal (e - c)) θ
    (inner (𝕜 := ℝ) c (planarEdgeNormal (e - c))) (segment ℝ c e)
    (segment_subset_planar_support c e)
  rwa [inner_planarEdgeNormal]

/-- Endpoint sets remain null after every translation. -/
theorem edgeLengthMeasure_translate_finite {d : ℕ} (a b θ : Euclidean d)
    (V : Set (Euclidean d)) (hV : V.Finite) :
    edgeLengthMeasure a b (translate θ V) = 0 := by
  haveI := Measure.noAtoms_hausdorff (Euclidean d) (show (0 : ℝ) < 1 by norm_num)
  apply le_antisymm _ (zero_le _)
  calc
    _ ≤ Measure.hausdorffMeasure 1 (translate θ V) := Measure.restrict_apply_le _ _
    _ = 0 := (hV.preimage (add_left_injective θ).injOn).measure_zero _

/-- A finite family of nonparallel planar edges, together with finitely many vertices,
has zero translated overlap with the distinguished open edge. -/
theorem edgeLengthMeasure_translate_polygon_remainder {ι : Type*} [Fintype ι]
    (a b θ : Euclidean 2) (c e : ι → Euclidean 2) (V F : Set (Euclidean 2))
    (hV : V.Finite) (hF : F ⊆ V ∪ ⋃ i, segment ℝ (c i) (e i))
    (htrans : ∀ i, (b - a) 1 * (e i - c i) 0 - (b - a) 0 * (e i - c i) 1 ≠ 0) :
    edgeLengthMeasure a b (translate θ F) = 0 := by
  have hsub : translate θ F ⊆ translate θ V ∪ ⋃ i, translate θ (segment ℝ (c i) (e i)) := by
    intro x hx
    rcases hF hx with hv | he
    · exact Or.inl hv
    · obtain ⟨i, hi⟩ := Set.mem_iUnion.mp he
      exact Or.inr (Set.mem_iUnion.mpr ⟨i, hi⟩)
  apply measure_mono_null hsub
  apply measure_union_null
  · exact edgeLengthMeasure_translate_finite a b θ V hV
  · exact measure_iUnion_null fun i =>
      edgeLengthMeasure_translate_nonparallel_segment a b (c i) (e i) θ (htrans i)

end RieszEuclidean
