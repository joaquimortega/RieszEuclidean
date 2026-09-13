import RieszEuclidean.PolygonAnalyticAssembly
import Mathlib.Analysis.Convex.Topology

noncomputable section
open MeasureTheory Filter Topology
namespace RieszEuclidean

/-- The weak halfspace body belonging to the given open polygon. -/
def weakHalfspaceIntersection {ι : Type*} (normal : ι → Euclidean 2) (offset : ι → ℝ) :
    Set (Euclidean 2) := {x | ∀ i, offset i ≤ inner (𝕜 := ℝ) x (normal i)}

/-- The entire closed supporting face, including its endpoints. -/
def closedSupportingFace {ι : Type*} (normal : ι → Euclidean 2) (offset : ι → ℝ)
    (j : ι) : Set (Euclidean 2) :=
  {x | x ∈ weakHalfspaceIntersection normal offset ∧ inner (𝕜 := ℝ) x (normal j) = offset j}

theorem weakHalfspaceIntersection_isClosed {ι : Type*}
    (normal : ι → Euclidean 2) (offset : ι → ℝ) :
    IsClosed (weakHalfspaceIntersection normal offset) := by
  have h : IsClosed (⋂ i, {x : Euclidean 2 | offset i ≤ inner (𝕜 := ℝ) x (normal i)}) :=
    isClosed_iInter fun i => isClosed_le continuous_const (by fun_prop)
  simpa only [weakHalfspaceIntersection, Set.iInter_setOf] using h

theorem weakHalfspaceIntersection_convex {ι : Type*}
    (normal : ι → Euclidean 2) (offset : ι → ℝ) :
    Convex ℝ (weakHalfspaceIntersection normal offset) := by
  have h : Convex ℝ (⋂ i, {x : Euclidean 2 | offset i ≤ inner (𝕜 := ℝ) x (normal i)}) :=
    convex_iInter fun i => convex_halfSpace_ge
      { map_add := fun x y => inner_add_left x y (normal i)
        map_smul := fun r x => by simp only [inner_smul_left, RCLike.conj_to_real, smul_eq_mul] }
      (offset i)
  simpa only [weakHalfspaceIntersection, Set.iInter_setOf] using h

/-- With a strict feasible point, the weak body is exactly the closure of the open polygon. -/
theorem strictHalfspaceIntersection_closure_eq_weak {ι : Type*}
    (normal : ι → Euclidean 2) (offset : ι → ℝ)
    (hne : (strictHalfspaceIntersection normal offset).Nonempty) :
    closure (strictHalfspaceIntersection normal offset) = weakHalfspaceIntersection normal offset := by
  apply Set.Subset.antisymm
  · exact fun x hx i => strictHalfspaceIntersection_closure_le normal offset hx i
  · obtain ⟨p, hp⟩ := hne
    intro x hx
    have hseg : openSegment ℝ p x ⊆ strictHalfspaceIntersection normal offset := by
      rintro y ⟨r, s, hr, hs, hrs, rfl⟩ i
      simp only [inner_add_left, inner_smul_left, RCLike.conj_to_real]
      have heq : r * offset i + s * offset i = offset i := by rw [← add_mul, hrs, one_mul]
      nlinarith [mul_pos hr (sub_pos.mpr (hp i)), mul_nonneg hs.le (sub_nonneg.mpr (hx i))]
    exact closure_mono hseg (segment_subset_closure_openSegment (right_mem_segment ℝ p x))

theorem strictSupportingFace_subset_closed {ι : Type*}
    (normal : ι → Euclidean 2) (offset : ι → ℝ) (j : ι) :
    strictSupportingFace normal offset j ⊆ closedSupportingFace normal offset j := by
  intro x hx
  refine ⟨fun i => ?_, hx.1⟩
  by_cases hij : i = j
  · subst i; exact hx.1.ge
  · exact (hx.2 i hij).le

theorem closedSupportingFace_isClosed {ι : Type*}
    (normal : ι → Euclidean 2) (offset : ι → ℝ) (j : ι) :
    IsClosed (closedSupportingFace normal offset j) :=
  (weakHalfspaceIntersection_isClosed normal offset).inter
    (isClosed_eq (by fun_prop) continuous_const)

theorem closedSupportingFace_convex {ι : Type*}
    (normal : ι → Euclidean 2) (offset : ι → ℝ) (j : ι) :
    Convex ℝ (closedSupportingFace normal offset j) := by
  apply (weakHalfspaceIntersection_convex normal offset).inter
  exact convex_hyperplane
    { map_add := fun x y => inner_add_left x y (normal j)
      map_smul := fun r x => by simp only [inner_smul_left, RCLike.conj_to_real, smul_eq_mul] }
    (offset j)

/-- Closing the strict supporting face gives the whole weak supporting face. -/
theorem strictSupportingFace_closure_eq {ι : Type*}
    (normal : ι → Euclidean 2) (offset : ι → ℝ) (j : ι)
    (hne : (strictSupportingFace normal offset j).Nonempty) :
    closure (strictSupportingFace normal offset j) = closedSupportingFace normal offset j := by
  apply Set.Subset.antisymm
  · exact closure_minimal (strictSupportingFace_subset_closed normal offset j)
      (closedSupportingFace_isClosed normal offset j)
  · obtain ⟨p, hp⟩ := hne
    intro x hx
    have hseg : openSegment ℝ p x ⊆ strictSupportingFace normal offset j := by
      rintro y ⟨r, s, hr, hs, hrs, rfl⟩
      simp only [strictSupportingFace, Set.mem_setOf_eq, inner_add_left, inner_smul_left,
        RCLike.conj_to_real]
      constructor
      · rw [hp.1, hx.2, ← add_mul, hrs, one_mul]
      · intro i hij
        have heq : r * offset i + s * offset i = offset i := by rw [← add_mul, hrs, one_mul]
        nlinarith [mul_pos hr (sub_pos.mpr (hp.2 i hij)),
          mul_nonneg hs.le (sub_nonneg.mpr (hx.1 i))]
    exact closure_mono hseg (segment_subset_closure_openSegment (right_mem_segment ℝ p x))

/-- A genuine face with nonzero normal guarantees a nonempty open polygon. -/
theorem strictHalfspaceIntersection_nonempty_of_face {ι : Type*} [Fintype ι]
    (normal : ι → Euclidean 2) (offset : ι → ℝ) (j : ι) (hn : normal j ≠ 0)
    (hface : (strictSupportingFace normal offset j).Nonempty) :
    (strictHalfspaceIntersection normal offset).Nonempty := by
  obtain ⟨t, ht⟩ := hface
  exact Set.Nonempty.of_closure
    ⟨t, (strictSupportingFace_two_sided_closure normal offset j t ht hn).1⟩

/-- The closed supporting face is part of the actual frontier. -/
theorem closedSupportingFace_subset_frontier {ι : Type*} [Fintype ι]
    (normal : ι → Euclidean 2) (offset : ι → ℝ) (j : ι)
    (hne : (strictHalfspaceIntersection normal offset).Nonempty) :
    closedSupportingFace normal offset j ⊆ frontier (strictHalfspaceIntersection normal offset) := by
  intro x hx
  rw [(strictHalfspaceIntersection_isOpen normal offset).frontier_eq,
    strictHalfspaceIntersection_closure_eq_weak normal offset hne]
  refine ⟨hx.1, fun h => ?_⟩
  exact (ne_of_gt (h j)) hx.2

/-- The closed supporting face is compact when the polygon is bounded. -/
theorem closedSupportingFace_isCompact {ι : Type*}
    (normal : ι → Euclidean 2) (offset : ι → ℝ) (j : ι)
    (hne : (strictHalfspaceIntersection normal offset).Nonempty)
    (hbounded : Bornology.IsBounded (strictHalfspaceIntersection normal offset)) :
    IsCompact (closedSupportingFace normal offset j) := by
  apply hbounded.isCompact_closure.of_isClosed_subset
    (closedSupportingFace_isClosed normal offset j)
  rw [strictHalfspaceIntersection_closure_eq_weak normal offset hne]
  exact fun _ hx => hx.1

/-- A nondegenerate compact convex subset of a planar line is literally a closed segment. -/
theorem compact_convex_planar_support_eq_segment (S : Set (Euclidean 2))
    (hcompact : IsCompact S) (hconvex : Convex ℝ S) (n : Euclidean 2) (hn : n ≠ 0) (c : ℝ)
    (hsupport : ∀ x ∈ S, inner (𝕜 := ℝ) x n = c)
    (hnondeg : ∃ x ∈ S, ∃ y ∈ S, x ≠ y) :
    ∃ a b : Euclidean 2, a ≠ b ∧ S = segment ℝ a b := by
  obtain ⟨x, hx, y, hy, hxy⟩ := hnondeg
  obtain ⟨⟨a, b⟩, ⟨ha, hb⟩, hmax⟩ := (hcompact.prod hcompact).exists_isMaxOn
    ⟨(x, y), hx, hy⟩ (by fun_prop : ContinuousOn (fun p : Euclidean 2 × Euclidean 2 =>
      dist p.1 p.2) (S ×ˢ S))
  have hab : a ≠ b := by
    intro he
    have h := hmax (show (x, y) ∈ S ×ˢ S from ⟨hx, hy⟩)
    change dist x y ≤ dist a b at h
    rw [he, dist_self] at h
    exact (not_le_of_gt (dist_pos.mpr hxy)) h
  refine ⟨a, b, hab, Set.Subset.antisymm ?_ (hconvex.segment_subset ha hb)⟩
  intro z hz
  have hzn : inner (𝕜 := ℝ) n (z - a) = 0 := by
    rw [real_inner_comm, inner_sub_left, hsupport z hz, hsupport a ha, _root_.sub_self]
  have hbn : inner (𝕜 := ℝ) n (b - a) = 0 := by
    rw [real_inner_comm, inner_sub_left, hsupport b hb, hsupport a ha, _root_.sub_self]
  have hscalar : ∃ r : ℝ, z - a = r • (b - a) := by
    apply Classical.byContradiction
    intro hnot
    have hh : ∀ r : ℝ, z - a ≠ r • (b - a) := not_exists.mp hnot
    exact planar_inner_ne_zero_of_not_parallel n (b - a) (z - a) hn
      (sub_ne_zero.mpr hab.symm) hbn hh hzn
  obtain ⟨r, hr⟩ := hscalar
  have hzexpr : z = r • (b - a) + a := by rw [← hr]; abel
  have hpos : 0 < ‖b - a‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hab.symm)
  have h₀ : |r| ≤ 1 := by
    have h := hmax (show (z, a) ∈ S ×ˢ S from ⟨hz, ha⟩)
    change dist z a ≤ dist a b at h
    rw [dist_eq_norm, hr, norm_smul, Real.norm_eq_abs, dist_comm a b, dist_eq_norm] at h
    exact (mul_le_mul_right hpos).mp (by simpa only [one_mul] using h)
  have hzsub : z - b = (r - 1) • (b - a) := by rw [hzexpr]; module
  have h₁ : |r - 1| ≤ 1 := by
    have h := hmax (show (z, b) ∈ S ×ˢ S from ⟨hz, hb⟩)
    change dist z b ≤ dist a b at h
    rw [dist_eq_norm, hzsub, norm_smul, Real.norm_eq_abs, dist_comm a b, dist_eq_norm] at h
    exact (mul_le_mul_right hpos).mp (by simpa only [one_mul] using h)
  rw [segment_eq_image_lineMap]
  refine ⟨r, ⟨?_, (abs_le.mp h₀).2⟩, ?_⟩
  · linarith [(abs_le.mp h₁).1]
  · exact hzexpr.symm

/-- Each irredundant supporting face of a bounded polygon is a nondegenerate closed segment. -/
theorem closedSupportingFace_eq_segment {ι : Type*} [Fintype ι]
    (normal : ι → Euclidean 2) (offset : ι → ℝ) (j : ι) (hn : normal j ≠ 0)
    (hface : (strictSupportingFace normal offset j).Nonempty)
    (hbounded : Bornology.IsBounded (strictHalfspaceIntersection normal offset)) :
    ∃ a b : Euclidean 2, a ≠ b ∧ closedSupportingFace normal offset j = segment ℝ a b := by
  obtain ⟨x, y, hxy, hx, hy⟩ := strictSupportingFace_exists_distinct_points normal offset j hn hface
  exact compact_convex_planar_support_eq_segment _
    (closedSupportingFace_isCompact normal offset j
      (strictHalfspaceIntersection_nonempty_of_face normal offset j hn hface) hbounded)
    (closedSupportingFace_convex normal offset j) (normal j) hn (offset j)
    (fun _ ht => ht.2) ⟨x, strictSupportingFace_subset_closed normal offset j hx,
      y, strictSupportingFace_subset_closed normal offset j hy, hxy⟩

/-- A maximal polygon side is a literal nondegenerate boundary segment, maximal under inclusion
among boundary segments. This definition makes no reference to the halfspace presentation. -/
def IsMaximalBoundarySegment (Ω S : Set (Euclidean 2)) : Prop :=
  (∃ a b : Euclidean 2, a ≠ b ∧ S = segment ℝ a b) ∧ S ⊆ frontier Ω ∧
    ∀ T : Set (Euclidean 2),
      (∃ a b : Euclidean 2, a ≠ b ∧ T = segment ℝ a b) →
      T ⊆ frontier Ω → S ⊆ T → T ⊆ S

/-- Any straight boundary segment lies in a single supporting face: an active midpoint
constraint forces the same constraint to be active at both endpoints. -/
theorem boundary_segment_subset_closedSupportingFace {ι : Type*} [Fintype ι]
    (normal : ι → Euclidean 2) (offset : ι → ℝ) (a b : Euclidean 2)
    (hseg : segment ℝ a b ⊆ frontier (strictHalfspaceIntersection normal offset)) :
    ∃ j, segment ℝ a b ⊆ closedSupportingFace normal offset j := by
  classical
  let m := (1 / 2 : ℝ) • a + (1 / 2 : ℝ) • b
  have hm : m ∈ segment ℝ a b := ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, rfl⟩
  have hmf := hseg hm
  have hnot : m ∉ strictHalfspaceIntersection normal offset :=
    ((strictHalfspaceIntersection_isOpen normal offset).frontier_eq ▸ hmf).2
  obtain ⟨j, hj⟩ := not_forall.mp hnot
  have ha : ∀ i, offset i ≤ inner (𝕜 := ℝ) a (normal i) :=
    fun i => strictHalfspaceIntersection_closure_le normal offset
      (frontier_subset_closure (hseg (left_mem_segment ℝ a b))) i
  have hb : ∀ i, offset i ≤ inner (𝕜 := ℝ) b (normal i) :=
    fun i => strictHalfspaceIntersection_closure_le normal offset
      (frontier_subset_closure (hseg (right_mem_segment ℝ a b))) i
  have hmj : inner (𝕜 := ℝ) m (normal j) = offset j :=
    le_antisymm (le_of_not_gt hj)
      (strictHalfspaceIntersection_closure_le normal offset (frontier_subset_closure hmf) j)
  change inner (𝕜 := ℝ) ((1 / 2 : ℝ) • a + (1 / 2 : ℝ) • b) (normal j) = offset j at hmj
  simp only [inner_add_left, inner_smul_left, RCLike.conj_to_real] at hmj
  have haj : inner (𝕜 := ℝ) a (normal j) = offset j := by linarith [ha j, hb j]
  have hbj : inner (𝕜 := ℝ) b (normal j) = offset j := by linarith [ha j, hb j]
  exact ⟨j, (closedSupportingFace_convex normal offset j).segment_subset ⟨ha, haj⟩ ⟨hb, hbj⟩⟩

/-- A strict face point cannot belong to any other closed supporting face. -/
theorem strictSupportingFace_index_eq_of_mem_closed {ι : Type*}
    (normal : ι → Euclidean 2) (offset : ι → ℝ) {i j : ι} {x : Euclidean 2}
    (hi : x ∈ strictSupportingFace normal offset i)
    (hj : x ∈ closedSupportingFace normal offset j) : j = i := by
  by_contra hji
  exact (ne_of_gt (hi.2 j hji)) hj.2

/-- Distinct irredundant constraints give distinct geometric closed sides. -/
theorem closedSupportingFace_injective {ι : Type*}
    (normal : ι → Euclidean 2) (offset : ι → ℝ)
    (hface : ∀ i, (strictSupportingFace normal offset i).Nonempty) :
    Function.Injective (closedSupportingFace normal offset) := by
  intro i j heq
  obtain ⟨x, hx⟩ := hface i
  have hj : x ∈ closedSupportingFace normal offset j :=
    heq ▸ strictSupportingFace_subset_closed normal offset i hx
  exact (strictSupportingFace_index_eq_of_mem_closed normal offset hx hj).symm

/-- Every genuine closed supporting face of a bounded polygon is a maximal boundary segment. -/
theorem closedSupportingFace_isMaximalBoundarySegment {ι : Type*} [Fintype ι]
    (normal : ι → Euclidean 2) (offset : ι → ℝ) (j : ι) (hn : normal j ≠ 0)
    (hface : (strictSupportingFace normal offset j).Nonempty)
    (hbounded : Bornology.IsBounded (strictHalfspaceIntersection normal offset)) :
    IsMaximalBoundarySegment (strictHalfspaceIntersection normal offset)
      (closedSupportingFace normal offset j) := by
  refine ⟨closedSupportingFace_eq_segment normal offset j hn hface hbounded,
    closedSupportingFace_subset_frontier normal offset j
      (strictHalfspaceIntersection_nonempty_of_face normal offset j hn hface), ?_⟩
  rintro T ⟨a, b, _, rfl⟩ hT hsub
  obtain ⟨i, hi⟩ := boundary_segment_subset_closedSupportingFace normal offset a b hT
  obtain ⟨x, hx⟩ := hface
  have hij : i = j := strictSupportingFace_index_eq_of_mem_closed normal offset hx
    (hi (hsub (strictSupportingFace_subset_closed normal offset j hx)))
  simpa only [hij] using hi

/-- The maximal boundary segments are exactly the indexed closed supporting faces. -/
theorem isMaximalBoundarySegment_iff_closedSupportingFace {ι : Type*} [Fintype ι]
    (normal : ι → Euclidean 2) (offset : ι → ℝ)
    (hn : ∀ i, normal i ≠ 0)
    (hface : ∀ i, (strictSupportingFace normal offset i).Nonempty)
    (hbounded : Bornology.IsBounded (strictHalfspaceIntersection normal offset))
    (S : Set (Euclidean 2)) :
    IsMaximalBoundarySegment (strictHalfspaceIntersection normal offset) S ↔
      ∃ i, S = closedSupportingFace normal offset i := by
  constructor
  · rintro ⟨⟨a, b, hab, rfl⟩, hseg, hmax⟩
    obtain ⟨i, hi⟩ := boundary_segment_subset_closedSupportingFace normal offset a b hseg
    have hmaxface := closedSupportingFace_isMaximalBoundarySegment normal offset i
      (hn i) (hface i) hbounded
    exact ⟨i, Set.Subset.antisymm hi (hmax _ hmaxface.1 hmaxface.2.1 hi)⟩
  · rintro ⟨i, rfl⟩
    exact closedSupportingFace_isMaximalBoundarySegment normal offset i (hn i) (hface i) hbounded

/-- The halfspace indices are in bijection with the polygon's maximal geometric sides. -/
def supportingFaceEquivMaximalBoundarySegments {ι : Type*} [Fintype ι]
    (normal : ι → Euclidean 2) (offset : ι → ℝ)
    (hn : ∀ i, normal i ≠ 0)
    (hface : ∀ i, (strictSupportingFace normal offset i).Nonempty)
    (hbounded : Bornology.IsBounded (strictHalfspaceIntersection normal offset)) :
    ι ≃ {S : Set (Euclidean 2) //
      IsMaximalBoundarySegment (strictHalfspaceIntersection normal offset) S} :=
  Equiv.ofBijective (fun i => ⟨closedSupportingFace normal offset i,
    closedSupportingFace_isMaximalBoundarySegment normal offset i (hn i) (hface i) hbounded⟩)
    ⟨fun i j h => closedSupportingFace_injective normal offset hface (congrArg Subtype.val h),
      fun ⟨S, hS⟩ => by
        obtain ⟨i, hi⟩ := (isMaximalBoundarySegment_iff_closedSupportingFace normal offset hn
          hface hbounded S).mp hS
        exact ⟨i, Subtype.ext hi.symm⟩⟩

/-- Side counts in the irredundant halfspace and maximal-segment presentations agree. -/
theorem maximalBoundarySegments_card {ι : Type*} [Fintype ι]
    (normal : ι → Euclidean 2) (offset : ι → ℝ)
    (hn : ∀ i, normal i ≠ 0)
    (hface : ∀ i, (strictSupportingFace normal offset i).Nonempty)
    (hbounded : Bornology.IsBounded (strictHalfspaceIntersection normal offset)) :
    Nat.card {S : Set (Euclidean 2) //
      IsMaximalBoundarySegment (strictHalfspaceIntersection normal offset) S} = Fintype.card ι := by
  rw [← Nat.card_congr (supportingFaceEquivMaximalBoundarySegments normal offset hn hface hbounded)]
  exact Nat.card_eq_fintype_card

/-- An endpoint of a closed face segment is not in its relatively open supporting face:
a tangential extension would otherwise contradict the endpoint property. -/
theorem leftEndpoint_not_mem_strictSupportingFace {ι : Type*} [Fintype ι]
    (normal : ι → Euclidean 2) (offset : ι → ℝ) (j : ι) (a b : Euclidean 2)
    (hab : a ≠ b) (hseg : closedSupportingFace normal offset j = segment ℝ a b) :
    a ∉ strictSupportingFace normal offset j := by
  intro ha
  have hb : b ∈ closedSupportingFace normal offset j := hseg ▸ right_mem_segment ℝ a b
  have horth : inner (𝕜 := ℝ) (a - b) (normal j) = 0 := by
    rw [inner_sub_left, ha.1, hb.2, _root_.sub_self]
  have hlim : Tendsto (fun k : ℕ => a + (1 / ((k : ℝ) + 1)) • (a - b)) atTop (nhds a) := by
    simpa only [zero_smul, add_zero] using
      tendsto_const_nhds.add (tendsto_one_div_add_atTop_nhds_zero_nat.smul_const (a - b))
  obtain ⟨k, hk⟩ := (hlim.eventually
    (strictSupportingFace_eventually_other normal offset j a ha)).exists
  have hz : a + (1 / ((k : ℝ) + 1)) • (a - b) ∈ closedSupportingFace normal offset j := by
    apply strictSupportingFace_subset_closed normal offset j
    refine ⟨?_, hk⟩
    rw [inner_add_left, inner_smul_left, horth, mul_zero, add_zero, ha.1]
  rw [hseg, segment_eq_image_lineMap] at hz
  obtain ⟨r, hr, heq⟩ := hz
  have hzline : a + (1 / ((k : ℝ) + 1)) • (a - b) =
      AffineMap.lineMap a b (-(1 / ((k : ℝ) + 1))) := by
    rw [AffineMap.lineMap_apply_module']
    module
  rw [hzline] at heq
  have hcoeff := AffineMap.lineMap_injective ℝ hab heq
  have hpos : 0 < (1 : ℝ) / ((k : ℝ) + 1) := by positivity
  linarith [hr.1]

/-- The selected strict supporting face is literally the relative interior of its maximal side. -/
theorem strictSupportingFace_eq_openSegment {ι : Type*} [Fintype ι]
    (normal : ι → Euclidean 2) (offset : ι → ℝ) (j : ι)
    (hface : (strictSupportingFace normal offset j).Nonempty)
    (a b : Euclidean 2) (hab : a ≠ b)
    (hseg : closedSupportingFace normal offset j = segment ℝ a b) :
    strictSupportingFace normal offset j = openSegment ℝ a b := by
  have ha : a ∈ closedSupportingFace normal offset j := hseg ▸ left_mem_segment ℝ a b
  have hb : b ∈ closedSupportingFace normal offset j := hseg ▸ right_mem_segment ℝ a b
  apply Set.Subset.antisymm
  · intro x hx
    have hxa : a ≠ x := fun h => leftEndpoint_not_mem_strictSupportingFace normal offset j a b hab hseg (h ▸ hx)
    have hxb : b ≠ x := fun h => leftEndpoint_not_mem_strictSupportingFace normal offset j b a hab.symm
      (hseg.trans (segment_symm ℝ a b)) (h ▸ hx)
    exact mem_openSegment_of_ne_left_right hxa hxb
      (hseg ▸ strictSupportingFace_subset_closed normal offset j hx)
  · rintro x ⟨r, s, hr, hs, hrs, rfl⟩
    refine ⟨?_, fun i hij => ?_⟩
    · simp only [inner_add_left, inner_smul_left, RCLike.conj_to_real, ha.2, hb.2,
        ← add_mul, hrs, one_mul]
    · have hweak := (closedSupportingFace_convex normal offset j).segment_subset ha hb
        (show r • a + s • b ∈ segment ℝ a b from ⟨r, s, hr.le, hs.le, hrs, rfl⟩)
      apply lt_of_le_of_ne (hweak.1 i)
      intro heq
      simp only [inner_add_left, inner_smul_left, RCLike.conj_to_real] at heq
      have hweight : r * offset i + s * offset i = offset i := by rw [← add_mul, hrs, one_mul]
      have hai : inner (𝕜 := ℝ) a (normal i) = offset i := by
        have hh : r * (inner (𝕜 := ℝ) a (normal i) - offset i) = 0 := by
          nlinarith [mul_nonneg hr.le (sub_nonneg.mpr (ha.1 i)),
            mul_nonneg hs.le (sub_nonneg.mpr (hb.1 i))]
        exact sub_eq_zero.mp ((mul_eq_zero.mp hh).resolve_left hr.ne')
      have hbi : inner (𝕜 := ℝ) b (normal i) = offset i := by
        have hh : s * (inner (𝕜 := ℝ) b (normal i) - offset i) = 0 := by
          nlinarith [mul_nonneg hr.le (sub_nonneg.mpr (ha.1 i)),
            mul_nonneg hs.le (sub_nonneg.mpr (hb.1 i))]
        exact sub_eq_zero.mp ((mul_eq_zero.mp hh).resolve_left hs.ne')
      obtain ⟨p, hp⟩ := hface
      have hpseg := hseg ▸ strictSupportingFace_subset_closed normal offset j hp
      obtain ⟨u, v, _, _, huv, hpexpr⟩ := hpseg
      have hpi : inner (𝕜 := ℝ) p (normal i) = offset i := by
        rw [← hpexpr, inner_add_left, inner_smul_left, inner_smul_left, hai, hbi]
        simp only [RCLike.conj_to_real, ← add_mul, huv, one_mul]
      exact (ne_of_gt (hp.2 i hij)) hpi

/-- Each actual maximal side is represented once, with its literal relative interior. -/
theorem maximalBoundarySegment_exists_unique_face {ι : Type*} [Fintype ι]
    (normal : ι → Euclidean 2) (offset : ι → ℝ)
    (hn : ∀ i, normal i ≠ 0)
    (hface : ∀ i, (strictSupportingFace normal offset i).Nonempty)
    (hbounded : Bornology.IsBounded (strictHalfspaceIntersection normal offset))
    (S : Set (Euclidean 2))
    (hS : IsMaximalBoundarySegment (strictHalfspaceIntersection normal offset) S) :
    ∃! i, ∃ a b : Euclidean 2, a ≠ b ∧ S = segment ℝ a b ∧
      closedSupportingFace normal offset i = S ∧
      strictSupportingFace normal offset i = openSegment ℝ a b := by
  obtain ⟨i, hi⟩ := (isMaximalBoundarySegment_iff_closedSupportingFace normal offset hn hface hbounded S).mp hS
  obtain ⟨a, b, hab, habseg⟩ := closedSupportingFace_eq_segment normal offset i (hn i) (hface i) hbounded
  refine ⟨i, ⟨a, b, hab, hi.trans habseg, hi.symm,
    strictSupportingFace_eq_openSegment normal offset i (hface i) a b hab habseg⟩, ?_⟩
  rintro j ⟨_, _, _, _, hj, _⟩
  exact closedSupportingFace_injective normal offset hface (hj.trans hi)

/-- Oddness of the number of maximal geometric sides implies the polygon obstruction.
The side count here is independent of the halfspace indexing. -/
theorem SeparatedConfiguration.oddMaximalSides_no_exponentialRieszBasis_of_hull_representations
    {ι : Type*} [Fintype ι] (normal : ι → Euclidean 2) (offset : ι → ℝ)
    (hunit : ∀ i, ‖normal i‖ = 1)
    (hface : ∀ i, (strictSupportingFace normal offset i).Nonempty)
    (hbounded : Bornology.IsBounded (strictHalfspaceIntersection normal offset))
    (hodd : Odd (Nat.card {S : Set (Euclidean 2) //
      IsMaximalBoundarySegment (strictHalfspaceIntersection normal offset) S}))
    (hrep : ∀ {δ : ℝ} (hδ : 0 < δ) (Γ : SeparatedConfiguration 2 δ)
      [MeasurableSpace (hull Γ)] [BorelSpace (hull Γ)]
      (μ : Measure (hull Γ)) [IsProbabilityMeasure μ]
      (hμ : ∀ z : Euclidean 2, MeasurePreserving (hullTranslate hδ Γ z) μ μ),
      ∃ σ : Lp ℂ 2 μ → Measure (Euclidean 2),
        ∀ f, RepresentsCorrelation
          (unitaryCorrelation (hullKoopmanUnitary hδ Γ μ hμ) f) (σ f))
    (Λ : Set (Euclidean 2)) :
    ¬ HasExponentialRieszBasis (strictHalfspaceIntersection normal offset) Λ := by
  have hn : ∀ i, normal i ≠ 0 :=
    fun i h => by simpa only [h, norm_zero, zero_ne_one] using hunit i
  rw [maximalBoundarySegments_card normal offset hn hface hbounded] at hodd
  exact oddSupportingPolygon_no_exponentialRieszBasis_of_hull_representations
    normal offset hunit hface hodd hbounded hrep Λ

/-- The polygon frontier is exactly the union of its full closed supporting sides. -/
theorem strictHalfspaceIntersection_frontier_eq_faces {ι : Type*} [Fintype ι]
    (normal : ι → Euclidean 2) (offset : ι → ℝ)
    (hne : (strictHalfspaceIntersection normal offset).Nonempty) :
    frontier (strictHalfspaceIntersection normal offset) = ⋃ i, closedSupportingFace normal offset i := by
  classical
  apply Set.Subset.antisymm
  · intro x hx
    have hnot := ((strictHalfspaceIntersection_isOpen normal offset).frontier_eq ▸ hx).2
    obtain ⟨i, hi⟩ := not_forall.mp hnot
    have hweak : ∀ j, offset j ≤ inner (𝕜 := ℝ) x (normal j) :=
      fun j => strictHalfspaceIntersection_closure_le normal offset (frontier_subset_closure hx) j
    exact Set.mem_iUnion.mpr ⟨i, hweak, le_antisymm (le_of_not_gt hi) (hweak i)⟩
  · exact Set.iUnion_subset fun i => closedSupportingFace_subset_frontier normal offset i hne

/-- Geometric parallelism of two nondegenerate segments, defined from their endpoint directions. -/
def BoundarySegmentsParallel (S T : Set (Euclidean 2)) : Prop :=
  ∃ a b c d : Euclidean 2, a ≠ b ∧ c ≠ d ∧ S = segment ℝ a b ∧ T = segment ℝ c d ∧
    ∃ r : ℝ, d - c = r • (b - a)

/-- For literal planar supporting segments, parallel normals and parallel side directions agree. -/
theorem supporting_segments_parallel_iff {ι : Type*}
    (normal : ι → Euclidean 2) (offset : ι → ℝ) (i j : ι)
    (hni : normal i ≠ 0) (hnj : normal j ≠ 0) (a b c d : Euclidean 2)
    (hab : a ≠ b) (hcd : c ≠ d)
    (hseg : closedSupportingFace normal offset i = segment ℝ a b)
    (hseg' : closedSupportingFace normal offset j = segment ℝ c d) :
    (∃ r : ℝ, normal j = r • normal i) ↔ ∃ r : ℝ, d - c = r • (b - a) := by
  have ha : a ∈ closedSupportingFace normal offset i := hseg ▸ left_mem_segment ℝ a b
  have hb : b ∈ closedSupportingFace normal offset i := hseg ▸ right_mem_segment ℝ a b
  have hc : c ∈ closedSupportingFace normal offset j := hseg' ▸ left_mem_segment ℝ c d
  have hd : d ∈ closedSupportingFace normal offset j := hseg' ▸ right_mem_segment ℝ c d
  have hvi : inner (𝕜 := ℝ) (b - a) (normal i) = 0 := by
    rw [inner_sub_left, ha.2, hb.2, _root_.sub_self]
  have hwj : inner (𝕜 := ℝ) (d - c) (normal j) = 0 := by
    rw [inner_sub_left, hc.2, hd.2, _root_.sub_self]
  constructor
  · rintro ⟨r, hr⟩
    have hrzero : r ≠ 0 := fun h => hnj (by simpa only [h, zero_smul] using hr)
    have hwi : inner (𝕜 := ℝ) (d - c) (normal i) = 0 := by
      rw [hr, inner_smul_right] at hwj
      exact (mul_eq_zero.mp hwj).resolve_left hrzero
    apply Classical.byContradiction
    intro hnot
    exact planar_inner_ne_zero_of_not_parallel (normal i) (b - a) (d - c) hni
      (sub_ne_zero.mpr hab.symm) (by rwa [real_inner_comm]) (not_exists.mp hnot)
      (by rwa [real_inner_comm])
  · rintro ⟨r, hr⟩
    have hrzero : r ≠ 0 := fun h => (sub_ne_zero.mpr hcd.symm)
      (by simpa only [h, zero_smul] using hr)
    have hvj : inner (𝕜 := ℝ) (b - a) (normal j) = 0 := by
      rw [hr, inner_smul_left, RCLike.conj_to_real] at hwj
      exact (mul_eq_zero.mp hwj).resolve_left hrzero
    apply Classical.byContradiction
    intro hnot
    exact planar_inner_ne_zero_of_not_parallel (b - a) (normal i) (normal j)
      (sub_ne_zero.mpr hab.symm) hni hvi (not_exists.mp hnot) hvj

/-- Parallelism is preserved by the geometric-side identification, independently of endpoint choices. -/
theorem closedSupportingFaces_parallel_iff {ι : Type*} [Fintype ι]
    (normal : ι → Euclidean 2) (offset : ι → ℝ)
    (hn : ∀ i, normal i ≠ 0)
    (hface : ∀ i, (strictSupportingFace normal offset i).Nonempty)
    (hbounded : Bornology.IsBounded (strictHalfspaceIntersection normal offset)) (i j : ι) :
    BoundarySegmentsParallel (closedSupportingFace normal offset i) (closedSupportingFace normal offset j) ↔
      ∃ r : ℝ, normal j = r • normal i := by
  constructor
  · rintro ⟨a, b, c, d, hab, hcd, hseg, hseg', hr⟩
    exact (supporting_segments_parallel_iff normal offset i j (hn i) (hn j)
      a b c d hab hcd hseg hseg').mpr hr
  · intro h
    obtain ⟨a, b, hab, hseg⟩ := closedSupportingFace_eq_segment normal offset i (hn i) (hface i) hbounded
    obtain ⟨c, d, hcd, hseg'⟩ := closedSupportingFace_eq_segment normal offset j (hn j) (hface j) hbounded
    exact ⟨a, b, c, d, hab, hcd, hseg, hseg',
      (supporting_segments_parallel_iff normal offset i j (hn i) (hn j)
        a b c d hab hcd hseg hseg').mp h⟩

/-- The unpaired-edge hypothesis expressed using maximal geometric boundary segments
implies the unpaired-normal condition used by the analytic proof. -/
theorem exists_unpaired_normal_of_maximal_side {ι : Type*} [Fintype ι]
    (normal : ι → Euclidean 2) (offset : ι → ℝ)
    (hn : ∀ i, normal i ≠ 0)
    (hface : ∀ i, (strictSupportingFace normal offset i).Nonempty)
    (hbounded : Bornology.IsBounded (strictHalfspaceIntersection normal offset))
    (S : Set (Euclidean 2))
    (hS : IsMaximalBoundarySegment (strictHalfspaceIntersection normal offset) S)
    (hunpaired : ∀ T : Set (Euclidean 2),
      IsMaximalBoundarySegment (strictHalfspaceIntersection normal offset) T →
      T ≠ S → ¬ BoundarySegmentsParallel S T) :
    ∃ i, ∀ j, j ≠ i → ∀ r : ℝ, normal j ≠ r • normal i := by
  obtain ⟨i, hi⟩ := (isMaximalBoundarySegment_iff_closedSupportingFace normal offset hn hface hbounded S).mp hS
  refine ⟨i, fun j hji r hr => ?_⟩
  apply hunpaired (closedSupportingFace normal offset j)
    (closedSupportingFace_isMaximalBoundarySegment normal offset j (hn j) (hface j) hbounded)
  · intro heq
    exact hji (closedSupportingFace_injective normal offset hface (heq.trans hi))
  · rw [hi]
    exact (closedSupportingFaces_parallel_iff normal offset hn hface hbounded i j).mpr ⟨r, hr⟩

/-- A bounded irredundant planar halfspace polygon with a geometrically unpaired maximal side
has no exponential Riesz basis, given the stationary hull representations. -/
theorem SeparatedConfiguration.unpairedMaximalSide_no_exponentialRieszBasis_of_hull_representations
    {ι : Type*} [Fintype ι] (normal : ι → Euclidean 2) (offset : ι → ℝ)
    (hn : ∀ i, normal i ≠ 0)
    (hface : ∀ i, (strictSupportingFace normal offset i).Nonempty)
    (hbounded : Bornology.IsBounded (strictHalfspaceIntersection normal offset))
    (S : Set (Euclidean 2))
    (hS : IsMaximalBoundarySegment (strictHalfspaceIntersection normal offset) S)
    (hunpaired : ∀ T : Set (Euclidean 2),
      IsMaximalBoundarySegment (strictHalfspaceIntersection normal offset) T →
      T ≠ S → ¬ BoundarySegmentsParallel S T)
    (hrep : ∀ {δ : ℝ} (hδ : 0 < δ) (Γ : SeparatedConfiguration 2 δ)
      [MeasurableSpace (hull Γ)] [BorelSpace (hull Γ)]
      (μ : Measure (hull Γ)) [IsProbabilityMeasure μ]
      (hμ : ∀ z : Euclidean 2, MeasurePreserving (hullTranslate hδ Γ z) μ μ),
      ∃ σ : Lp ℂ 2 μ → Measure (Euclidean 2),
        ∀ f, RepresentsCorrelation
          (unitaryCorrelation (hullKoopmanUnitary hδ Γ μ hμ) f) (σ f))
    (Λ : Set (Euclidean 2)) :
    ¬ HasExponentialRieszBasis (strictHalfspaceIntersection normal offset) Λ := by
  obtain ⟨i, hi⟩ := exists_unpaired_normal_of_maximal_side normal offset hn hface hbounded S hS hunpaired
  exact unpairedSupportingFace_no_exponentialRieszBasis_of_hull_representations
    normal offset i (hn i) (hface i) hi hbounded hrep Λ

/-- Unit inward normals obtained by positive rescaling of nonzero supporting normals. -/
def normalizedSupportNormal {ι : Type*} (normal : ι → Euclidean 2) (i : ι) : Euclidean 2 :=
  ‖normal i‖⁻¹ • normal i

/-- The matching offsets under the same positive rescaling. -/
def normalizedSupportOffset {ι : Type*} (normal : ι → Euclidean 2) (offset : ι → ℝ)
    (i : ι) : ℝ := ‖normal i‖⁻¹ * offset i

/-- Normalization gives literal unit normals. -/
theorem normalizedSupportNormal_norm {ι : Type*} (normal : ι → Euclidean 2)
    (hn : ∀ i, normal i ≠ 0) (i : ι) : ‖normalizedSupportNormal normal i‖ = 1 := by
  rw [normalizedSupportNormal, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _))]
  exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr (hn i))

/-- Positive support normalization preserves the actual open polygon. -/
theorem strictHalfspaceIntersection_normalize {ι : Type*}
    (normal : ι → Euclidean 2) (offset : ι → ℝ) (hn : ∀ i, normal i ≠ 0) :
    strictHalfspaceIntersection (normalizedSupportNormal normal) (normalizedSupportOffset normal offset) =
      strictHalfspaceIntersection normal offset := by
  ext x
  simp only [strictHalfspaceIntersection, Set.mem_setOf_eq, normalizedSupportNormal,
    normalizedSupportOffset, inner_smul_right]
  exact forall_congr' fun i => mul_lt_mul_left (inv_pos.mpr (norm_pos_iff.mpr (hn i)))

/-- Normalization preserves each relatively open side, hence also irredundancy. -/
theorem strictSupportingFace_normalize {ι : Type*}
    (normal : ι → Euclidean 2) (offset : ι → ℝ) (hn : ∀ i, normal i ≠ 0) (j : ι) :
    strictSupportingFace (normalizedSupportNormal normal) (normalizedSupportOffset normal offset) j =
      strictSupportingFace normal offset j := by
  ext x
  simp only [strictSupportingFace, Set.mem_setOf_eq, normalizedSupportNormal,
    normalizedSupportOffset, inner_smul_right]
  apply and_congr
  · exact mul_right_inj' (inv_ne_zero (norm_ne_zero_iff.mpr (hn j)))
  · exact forall_congr' fun i => imp_congr_right fun _ =>
      mul_lt_mul_left (inv_pos.mpr (norm_pos_iff.mpr (hn i)))

/-- The maximal-side odd polygon theorem requires no normalization assumption: arbitrary
nonzero irredundant inward normals are normalized without changing the polygon or its sides. -/
theorem SeparatedConfiguration.oddMaximalSides_no_exponentialRieszBasis_of_nonzero_normals_and_hull_representations
    {ι : Type*} [Fintype ι] (normal : ι → Euclidean 2) (offset : ι → ℝ)
    (hn : ∀ i, normal i ≠ 0)
    (hface : ∀ i, (strictSupportingFace normal offset i).Nonempty)
    (hbounded : Bornology.IsBounded (strictHalfspaceIntersection normal offset))
    (hodd : Odd (Nat.card {S : Set (Euclidean 2) //
      IsMaximalBoundarySegment (strictHalfspaceIntersection normal offset) S}))
    (hrep : ∀ {δ : ℝ} (hδ : 0 < δ) (Γ : SeparatedConfiguration 2 δ)
      [MeasurableSpace (hull Γ)] [BorelSpace (hull Γ)]
      (μ : Measure (hull Γ)) [IsProbabilityMeasure μ]
      (hμ : ∀ z : Euclidean 2, MeasurePreserving (hullTranslate hδ Γ z) μ μ),
      ∃ σ : Lp ℂ 2 μ → Measure (Euclidean 2),
        ∀ f, RepresentsCorrelation
          (unitaryCorrelation (hullKoopmanUnitary hδ Γ μ hμ) f) (σ f))
    (Λ : Set (Euclidean 2)) :
    ¬ HasExponentialRieszBasis (strictHalfspaceIntersection normal offset) Λ := by
  have heq := strictHalfspaceIntersection_normalize normal offset hn
  have hf : ∀ i, (strictSupportingFace (normalizedSupportNormal normal)
      (normalizedSupportOffset normal offset) i).Nonempty := by
    intro i
    rw [strictSupportingFace_normalize normal offset hn]
    exact hface i
  have h := oddMaximalSides_no_exponentialRieszBasis_of_hull_representations
    (normalizedSupportNormal normal) (normalizedSupportOffset normal offset)
    (normalizedSupportNormal_norm normal hn) hf
    (by rwa [heq]) (by rwa [heq]) hrep Λ
  rwa [heq] at h

end RieszEuclidean
