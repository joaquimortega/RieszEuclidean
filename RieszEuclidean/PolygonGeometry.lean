import RieszEuclidean.EdgeGeometry
import RieszEuclidean.TriangleCrossing
import RieszEuclidean.BoundaryFubini
import Mathlib.Analysis.Convex.Measure

noncomputable section
open MeasureTheory Filter Topology
namespace RieszEuclidean

/-- The relatively open supporting face: one active constraint and all others strict. -/
def strictSupportingFace {d : ℕ} {ι : Type*}
    (normal : ι → Euclidean d) (offset : ι → ℝ) (j : ι) : Set (Euclidean d) :=
  {x | inner (𝕜 := ℝ) x (normal j) = offset j ∧
    ∀ i, i ≠ j → offset i < inner (𝕜 := ℝ) x (normal i)}

/-- Finite strict halfspace intersections are open in the ambient Euclidean space. -/
theorem strictHalfspaceIntersection_isOpen {d : ℕ} {ι : Type*} [Fintype ι]
    (normal : ι → Euclidean d) (offset : ι → ℝ) :
    IsOpen (strictHalfspaceIntersection normal offset) := by
  have h : IsOpen (⋂ i, {x : Euclidean d | offset i < inner (𝕜 := ℝ) x (normal i)}) :=
    isOpen_iInter_of_finite fun i => isOpen_lt continuous_const (by fun_prop)
  simpa only [strictHalfspaceIntersection, Set.iInter_setOf] using h

/-- The relatively open face is measurable for ambient Borel measures. -/
theorem measurableSet_strictSupportingFace {d : ℕ} {ι : Type*} [Fintype ι]
    (normal : ι → Euclidean d) (offset : ι → ℝ) (j : ι) :
    MeasurableSet (strictSupportingFace normal offset j) := by
  have h : MeasurableSet (⋂ i : {i : ι // i ≠ j},
      {x : Euclidean d | offset i < inner (𝕜 := ℝ) x (normal i)}) :=
    MeasurableSet.iInter fun i => (isOpen_lt continuous_const (by fun_prop)).measurableSet
  convert (isClosed_eq (by fun_prop : Continuous fun x : Euclidean d =>
    inner (𝕜 := ℝ) x (normal j)) (continuous_const (y := offset j))).measurableSet.inter h using 1
  ext x
  simp only [strictSupportingFace, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter,
    Subtype.forall]

/-- Every closure point satisfies each weak supporting inequality. -/
theorem strictHalfspaceIntersection_closure_le {d : ℕ} {ι : Type*}
    (normal : ι → Euclidean d) (offset : ι → ℝ) {x : Euclidean d}
    (hx : x ∈ closure (strictHalfspaceIntersection normal offset)) (i : ι) :
    offset i ≤ inner (𝕜 := ℝ) x (normal i) := by
  exact closure_minimal (fun y hy => (hy i).le)
    (isClosed_le continuous_const (by fun_prop)) hx

/-- Away from one relatively open face, the actual frontier lies in the other supports.
This includes the vertices automatically. -/
theorem strictHalfspaceIntersection_remainder_subset_supports {d : ℕ} {ι : Type*}
    [Fintype ι] (normal : ι → Euclidean d) (offset : ι → ℝ) (j : ι) :
    frontier (strictHalfspaceIntersection normal offset) \
      strictSupportingFace normal offset j ⊆
      ⋃ i : {i : ι // i ≠ j}, {x | inner (𝕜 := ℝ) x (normal i) = offset i} := by
  rintro x ⟨hx, hface⟩
  by_contra hout
  have hother : ∀ i, i ≠ j → offset i < inner (𝕜 := ℝ) x (normal i) := by
    intro i hij
    have hne : inner (𝕜 := ℝ) x (normal i) ≠ offset i := by
      intro he
      exact hout (Set.mem_iUnion.mpr ⟨⟨i, hij⟩, he⟩)
    exact lt_of_le_of_ne (strictHalfspaceIntersection_closure_le normal offset
      (frontier_subset_closure hx) i) hne.symm
  have hactive : inner (𝕜 := ℝ) x (normal j) = offset j := by
    by_contra hn
    have hin : x ∈ strictHalfspaceIntersection normal offset := by
      intro i
      by_cases hij : i = j
      · subst i
        exact lt_of_le_of_ne (strictHalfspaceIntersection_closure_le normal offset
          (frontier_subset_closure hx) j) (Ne.symm hn)
      · exact hother i hij
    exact ((strictHalfspaceIntersection_isOpen normal offset).frontier_eq ▸ hx).2 hin
  exact hface ⟨hactive, hother⟩

/-- Segments joining relatively open face points remain in that same face. -/
theorem strictSupportingFace_segment_subset {d : ℕ} {ι : Type*}
    (normal : ι → Euclidean d) (offset : ι → ℝ) (j : ι)
    {a b : Euclidean d} (ha : a ∈ strictSupportingFace normal offset j)
    (hb : b ∈ strictSupportingFace normal offset j) :
    segment ℝ a b ⊆ strictSupportingFace normal offset j := by
  rintro x ⟨r, s, hr, hs, hrs, rfl⟩
  simp only [strictSupportingFace, Set.mem_setOf_eq, inner_add_left,
    inner_smul_left, RCLike.conj_to_real]
  constructor
  · rw [ha.1, hb.1, ← add_mul, hrs, one_mul]
  · intro i hij
    have har := ha.2 i hij
    have hbr := hb.2 i hij
    have hzero : 0 < r ∨ 0 < s := by by_contra hn; push_neg at hn; linarith
    have heq : r * offset i + s * offset i = offset i := by
      rw [← add_mul, hrs, one_mul]
    rcases hzero with hrp | hsp
    · nlinarith [mul_pos hrp (sub_pos.mpr har), mul_nonneg hs (sub_nonneg.mpr hbr.le)]
    · nlinarith [mul_nonneg hr (sub_nonneg.mpr har.le), mul_pos hsp (sub_pos.mpr hbr)]

/-- An unpaired supporting face has zero edge-length overlap with every translate
of the rest of the actual polygon frontier. -/
theorem strictSupportingFace_remainder_edgeLength_null {d : ℕ} {ι : Type*} [Fintype ι]
    (normal : ι → Euclidean d) (offset : ι → ℝ) (j : ι) (a b θ : Euclidean d)
    (htrans : ∀ i, i ≠ j → inner (𝕜 := ℝ) (b - a) (normal i) ≠ 0) :
    edgeLengthMeasure a b (translate θ
      (frontier (strictHalfspaceIntersection normal offset) \
        strictSupportingFace normal offset j)) = 0 := by
  apply measure_mono_null (show translate θ
      (frontier (strictHalfspaceIntersection normal offset) \
        strictSupportingFace normal offset j) ⊆
      ⋃ i : {i : ι // i ≠ j}, translate θ
        {x | inner (𝕜 := ℝ) x (normal i) = offset i} from by
    intro x hx
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp
      (strictHalfspaceIntersection_remainder_subset_supports normal offset j hx)
    exact Set.mem_iUnion.mpr ⟨i, hi⟩)
  exact measure_iUnion_null fun i =>
    edgeLengthMeasure_translate_hyperplane a b (normal i) θ (offset i) (htrans i i.2)

/-- Tonelli produces a clean point on an actual supporting face. The geometric inputs
are two distinct face points and transversality to the other finite supporting lines. -/
theorem exists_clean_strictSupportingFace_point {d : ℕ} {ι : Type*} [Fintype ι]
    (normal : ι → Euclidean d) (offset : ι → ℝ) (j : ι) (a b : Euclidean d)
    (hab : a ≠ b) (ha : a ∈ strictSupportingFace normal offset j)
    (hb : b ∈ strictSupportingFace normal offset j)
    (htrans : ∀ i, i ≠ j → inner (𝕜 := ℝ) (b - a) (normal i) ≠ 0)
    (σ : Measure (Euclidean d)) [SFinite σ] :
    ∃ t ∈ strictSupportingFace normal offset j,
      σ {θ | t + θ ∈ frontier (strictHalfspaceIntersection normal offset) \
        strictSupportingFace normal offset j} = 0 := by
  let ν := edgeLengthMeasure a b
  haveI : IsFiniteMeasure ν := edgeLengthMeasure_finite _ _
  haveI : NeZero ν := ⟨fun h => (edgeLengthMeasure_univ_pos a b hab).ne'
    (by change ν Set.univ = 0; rw [h]; rfl)⟩
  have hF : MeasurableSet (frontier (strictHalfspaceIntersection normal offset) \
      strictSupportingFace normal offset j) :=
    isClosed_frontier.measurableSet.diff (measurableSet_strictSupportingFace normal offset j)
  have hm : MeasurableSet {p : Euclidean d × Euclidean d |
      p.1 + p.2 ∉ frontier (strictHalfspaceIntersection normal offset) \
        strictSupportingFace normal offset j} :=
    (hF.preimage (measurable_fst.add measurable_snd)).compl
  have hsections : ∀ᵐ θ ∂σ, ∀ᵐ t ∂ν,
      t + θ ∉ frontier (strictHalfspaceIntersection normal offset) \
        strictSupportingFace normal offset j := by
    apply Eventually.of_forall
    intro θ
    exact compl_mem_ae_iff.mpr
      (strictSupportingFace_remainder_edgeLength_null normal offset j a b θ htrans)
  have hswap := (Measure.ae_ae_comm (μ := ν) (ν := σ) hm).mpr hsections
  have hedge : ∀ᵐ t ∂ν, t ∈ strictSupportingFace normal offset j :=
    (edgeLengthMeasure_ae_edge a b hab).mono fun _ ht =>
      strictSupportingFace_segment_subset normal offset j ha hb (openSegment_subset_segment ℝ a b ht)
  exact (hswap.and hedge).exists.imp fun t ht => ⟨ht.2, compl_mem_ae_iff.mp ht.1⟩

/-- Distinct irredundant supporting faces cannot have positively proportional normals.
The witnesses express genuine relative face interiors, rather than a combinatorial assumption. -/
theorem strictSupportingFace_not_pos_parallel {d : ℕ} {ι : Type*}
    (normal : ι → Euclidean d) (offset : ι → ℝ) {i j : ι} (hij : i ≠ j)
    (hi : (strictSupportingFace normal offset i).Nonempty)
    (hj : (strictSupportingFace normal offset j).Nonempty)
    {r : ℝ} (hr : 0 < r) : normal j ≠ r • normal i := by
  obtain ⟨x, hx, hxother⟩ := hi
  obtain ⟨y, hy, hyother⟩ := hj
  intro heq
  have hxi := hxother j hij.symm
  have hyi := hyother i hij
  rw [heq, inner_smul_right, hx] at hxi
  rw [heq, inner_smul_right] at hy
  nlinarith [mul_pos hr (sub_pos.mpr hyi)]

end RieszEuclidean
