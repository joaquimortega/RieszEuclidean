import RieszEuclidean.PolygonParity

noncomputable section
open MeasureTheory Filter Topology
namespace RieszEuclidean

/-- Small perturbations of a relatively open face point preserve every inactive constraint. -/
theorem strictSupportingFace_eventually_other {d : ℕ} {ι : Type*} [Fintype ι]
    (normal : ι → Euclidean d) (offset : ι → ℝ) (j : ι) (t : Euclidean d)
    (ht : t ∈ strictSupportingFace normal offset j) :
    ∀ᶠ u in nhds t, ∀ i, i ≠ j → offset i < inner (𝕜 := ℝ) u (normal i) := by
  apply eventually_all.mpr
  intro i
  by_cases hij : i = j
  · exact Eventually.of_forall fun _ h => (h hij).elim
  · have h : ∀ᶠ u in nhds t, offset i < inner (𝕜 := ℝ) u (normal i) :=
      (isOpen_lt continuous_const (by fun_prop)).mem_nhds (ht.2 i hij)
    exact h.mono fun _ hh _ => hh

/-- A nonzero inward normal gives approaches from the interior and the strict exterior
at each relatively open face point, in the ordinary ambient topology. -/
theorem strictSupportingFace_two_sided_closure {d : ℕ} {ι : Type*} [Fintype ι]
    (normal : ι → Euclidean d) (offset : ι → ℝ) (j : ι) (t : Euclidean d)
    (ht : t ∈ strictSupportingFace normal offset j) (hn : normal j ≠ 0) :
    t ∈ closure (strictHalfspaceIntersection normal offset) ∧
      t ∈ closure (closure (strictHalfspaceIntersection normal offset))ᶜ := by
  have hlim (v : Euclidean d) : Tendsto
      (fun k : ℕ => t + (1 / ((k : ℝ) + 1)) • v) atTop (nhds t) := by
    simpa only [zero_smul, add_zero] using
      tendsto_const_nhds.add (tendsto_one_div_add_atTop_nhds_zero_nat.smul_const v)
  have hpos (k : ℕ) : 0 < (1 : ℝ) / ((k : ℝ) + 1) := by positivity
  have hnn : 0 < inner (𝕜 := ℝ) (normal j) (normal j) := real_inner_self_pos.mpr hn
  constructor
  · apply mem_closure_of_tendsto (hlim (normal j))
    filter_upwards [(hlim (normal j)).eventually
      (strictSupportingFace_eventually_other normal offset j t ht)] with k hk
    intro i
    by_cases hij : i = j
    · subst i
      rw [inner_add_left, inner_smul_left, ht.1]
      exact lt_add_of_pos_right _ (mul_pos (hpos k) hnn)
    · exact hk i hij
  · apply mem_closure_of_tendsto (hlim (-normal j))
    apply Eventually.of_forall
    intro k hk
    have hle := strictHalfspaceIntersection_closure_le normal offset hk j
    rw [inner_add_left, inner_smul_left, inner_neg_left, ht.1, RCLike.conj_to_real] at hle
    nlinarith [mul_pos (hpos k) hnn]

/-- The designated relatively open supporting face is contained in the actual frontier. -/
theorem strictSupportingFace_subset_frontier {d : ℕ} {ι : Type*} [Fintype ι]
    (normal : ι → Euclidean d) (offset : ι → ℝ) (j : ι) (hn : normal j ≠ 0) :
    strictSupportingFace normal offset j ⊆ frontier (strictHalfspaceIntersection normal offset) := by
  intro t ht
  rw [(strictHalfspaceIntersection_isOpen normal offset).frontier_eq]
  refine ⟨(strictSupportingFace_two_sided_closure normal offset j t ht hn).1, ?_⟩
  intro hh
  have := hh j
  rw [ht.1] at this
  exact lt_irrefl _ this

/-- Every conull set supplies ordinary Euclidean sequences on both sides of a face. -/
theorem exists_conull_sequences_strictSupportingFace_two_sides {d : ℕ} {ι : Type*}
    [Fintype ι] (normal : ι → Euclidean d) (offset : ι → ℝ) (j : ι)
    {G : Set (Euclidean d)} (hG : volume Gᶜ = 0)
    (t : Euclidean d) (ht : t ∈ strictSupportingFace normal offset j) (hn : normal j ≠ 0) :
    (∃ ts : ℕ → Euclidean d,
      (∀ k, ts k ∈ G ∩ strictHalfspaceIntersection normal offset) ∧
      Tendsto ts atTop (nhds t)) ∧
    (∃ ts : ℕ → Euclidean d,
      (∀ k, ts k ∈ G ∩ (closure (strictHalfspaceIntersection normal offset))ᶜ) ∧
      Tendsto ts atTop (nhds t)) := by
  have h := strictSupportingFace_two_sided_closure normal offset j t ht hn
  exact exists_conull_sequences_two_sides hG (strictHalfspaceIntersection_isOpen normal offset) h.1 h.2

/-- A genuine relatively open planar face with a nonzero normal contains two distinct points.
The proof constructs tangential perturbations, so nondegeneracy is not assumed separately. -/
theorem strictSupportingFace_exists_distinct_points {ι : Type*} [Fintype ι]
    (normal : ι → Euclidean 2) (offset : ι → ℝ) (j : ι)
    (hn : normal j ≠ 0) (hface : (strictSupportingFace normal offset j).Nonempty) :
    ∃ a b : Euclidean 2, a ≠ b ∧
      a ∈ strictSupportingFace normal offset j ∧ b ∈ strictSupportingFace normal offset j := by
  obtain ⟨t, ht⟩ := hface
  let v := planarEdgeNormal (normal j)
  have hv : v ≠ 0 := by
    intro hz
    apply hn
    apply PiLp.ext
    intro i
    fin_cases i
    · have h := congrArg (fun x : Euclidean 2 => x 1) hz
      exact h
    · have h := congrArg (fun x : Euclidean 2 => x 0) hz
      change -(normal j) 1 = 0 at h
      exact neg_eq_zero.mp h
  have horth : inner (𝕜 := ℝ) v (normal j) = 0 := by
    rw [real_inner_comm, inner_planarEdgeNormal]
    ring
  have hlim : Tendsto (fun k : ℕ => t + (1 / ((k : ℝ) + 1)) • v) atTop (nhds t) := by
    simpa only [zero_smul, add_zero] using
      tendsto_const_nhds.add (tendsto_one_div_add_atTop_nhds_zero_nat.smul_const v)
  obtain ⟨k, hk⟩ := (hlim.eventually
    (strictSupportingFace_eventually_other normal offset j t ht)).exists
  refine ⟨t, t + (1 / ((k : ℝ) + 1)) • v, ?_, ht, ?_⟩
  · intro he
    have hezero : (1 / ((k : ℝ) + 1)) • v = 0 := by
      exact add_left_cancel (by simpa only [add_zero] using he.symm)
    exact hv ((smul_eq_zero.mp hezero).resolve_left (by positivity))
  · refine ⟨?_, hk⟩
    rw [inner_add_left, inner_smul_left, horth, mul_zero, add_zero, ht.1]

/-- Odd irredundant planar halfspace presentations have a clean unpaired face point
for every sigma-finite frequency measure. All boundary and counting conclusions are derived. -/
theorem odd_strictSupportingFaces_exists_clean_point {ι : Type*} [Fintype ι]
    (normal : ι → Euclidean 2) (offset : ι → ℝ)
    (hunit : ∀ i, ‖normal i‖ = 1)
    (hface : ∀ i, (strictSupportingFace normal offset i).Nonempty)
    (hodd : Odd (Fintype.card ι)) (σ : Measure (Euclidean 2)) [SFinite σ] :
    ∃ i, ∃ t ∈ strictSupportingFace normal offset i,
      σ {θ | t + θ ∈ frontier (strictHalfspaceIntersection normal offset) \
        strictSupportingFace normal offset i} = 0 := by
  obtain ⟨i, hi⟩ := odd_strictSupportingFaces_exists_transverse normal offset hunit hface hodd
  obtain ⟨a, b, hab, ha, hb⟩ := strictSupportingFace_exists_distinct_points normal offset i
    (fun h => by simpa only [h, norm_zero, zero_ne_one] using hunit i) (hface i)
  exact ⟨i, exists_clean_strictSupportingFace_point normal offset i a b hab ha hb
    (hi a b hab ha hb) σ⟩

/-- A supporting-halfspace presentation defines a convex Euclidean domain. -/
theorem strictHalfspaceIntersection_convex {d : ℕ} {ι : Type*}
    (normal : ι → Euclidean d) (offset : ι → ℝ) :
    Convex ℝ (strictHalfspaceIntersection normal offset) := by
  have h : Convex ℝ (⋂ i, {x : Euclidean d | offset i < inner (𝕜 := ℝ) x (normal i)}) :=
    convex_iInter fun i => convex_halfSpace_gt
      { map_add := fun x y => inner_add_left x y (normal i)
        map_smul := fun r x => by simp only [inner_smul_left, RCLike.conj_to_real, smul_eq_mul] } (offset i)
  simpa only [strictHalfspaceIntersection, Set.iInter_setOf] using h

/-- The ordinary frontier of every such convex domain is Lebesgue-null. -/
theorem strictHalfspaceIntersection_volume_frontier {d : ℕ} {ι : Type*}
    (normal : ι → Euclidean d) (offset : ι → ℝ) :
    volume (frontier (strictHalfspaceIntersection normal offset)) = 0 :=
  (strictHalfspaceIntersection_convex normal offset).addHaar_frontier volume

/-- Surviving translated face points have identical eventual crossing signs. -/
theorem strictSupportingFace_same_direction {d : ℕ} {ι : Type*} [Fintype ι]
    (normal : ι → Euclidean d) (offset : ι → ℝ) (j : ι) (t θ : Euclidean d)
    (ht : t ∈ strictSupportingFace normal offset j)
    (htθ : t + θ ∈ strictSupportingFace normal offset j)
    (ts : ℕ → Euclidean d) (hts : Tendsto ts atTop (nhds t)) :
    ∀ᶠ k in atTop, ts k + θ ∈ strictHalfspaceIntersection normal offset ↔
      ts k ∈ strictHalfspaceIntersection normal offset :=
  hts.eventually (strictHalfspaceIntersection_same_direction normal offset j t θ
    ht.1 htθ.1 ht.2 htθ.2)

end RieszEuclidean
