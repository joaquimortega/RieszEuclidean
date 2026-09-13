import RieszEuclidean.PolygonGeometry
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

noncomputable section
open MeasureTheory
namespace RieszEuclidean

/-- A finite odd family of distinct nonzero vectors contains one with no opposite partner. -/
theorem exists_no_opposite_of_odd_card {d : ℕ} {ι : Type*} [Fintype ι]
    (v : ι → Euclidean d) (hv : Function.Injective v) (hzero : ∀ i, v i ≠ 0)
    (hodd : Odd (Fintype.card ι)) : ∃ i, ∀ j, v j ≠ -v i := by
  classical
  by_contra hn
  push_neg at hn
  let G : SimpleGraph ι :=
    { Adj := fun i j => v j = -v i
      symm := by intro i j h; simp only [h, neg_neg]
      loopless := by
        intro i h
        apply hzero i
        have hz : (2 : ℝ) • v i = 0 := by
          rw [two_smul]
          calc v i + v i = v i + -v i := congrArg (fun w => v i + w) h
            _ = 0 := add_neg_cancel (v i)
        exact (smul_eq_zero.mp hz).resolve_left (by norm_num) }
  have hdeg : ∀ i, G.degree i = 1 := by
    intro i
    obtain ⟨j, hj⟩ := hn i
    rw [← G.card_neighborFinset_eq_degree]
    apply Finset.card_eq_one.mpr
    refine ⟨j, ?_⟩
    ext k
    simp only [SimpleGraph.mem_neighborFinset, Finset.mem_singleton]
    change v k = -v i ↔ k = j
    exact ⟨fun h => hv (h.trans hj.symm), fun h => h ▸ hj⟩
  have heven := G.even_card_odd_degree_vertices
  simp only [hdeg, Nat.odd_iff, Nat.reduceMod, Finset.filter_True, Finset.card_univ] at heven
  exact (Nat.not_even_iff_odd.mpr hodd) heven

/-- Irredundancy makes the inward normal assignment injective. -/
theorem strictSupportingFace_normal_injective {d : ℕ} {ι : Type*}
    (normal : ι → Euclidean d) (offset : ι → ℝ)
    (hface : ∀ i, (strictSupportingFace normal offset i).Nonempty) :
    Function.Injective normal := by
  intro i j heq
  by_contra hij
  exact strictSupportingFace_not_pos_parallel normal offset hij (hface i) (hface j)
    (show (0 : ℝ) < 1 by norm_num) (by simpa only [one_smul] using heq.symm)

/-- An odd irredundant finite supporting-halfspace presentation with unit inward normals
has a face with no parallel partner, expressed without an assumed pairing function. -/
theorem odd_strictSupportingFaces_exists_unpaired {d : ℕ} {ι : Type*} [Fintype ι]
    (normal : ι → Euclidean d) (offset : ι → ℝ)
    (hunit : ∀ i, ‖normal i‖ = 1)
    (hface : ∀ i, (strictSupportingFace normal offset i).Nonempty)
    (hodd : Odd (Fintype.card ι)) :
    ∃ i, ∀ j, j ≠ i → ∀ r : ℝ, normal j ≠ r • normal i := by
  obtain ⟨i, hi⟩ := exists_no_opposite_of_odd_card normal
    (strictSupportingFace_normal_injective normal offset hface)
    (fun i h => by simpa only [h, norm_zero, zero_ne_one] using hunit i) hodd
  refine ⟨i, fun j hji r hr => ?_⟩
  have habs : |r| = 1 := by
    have hh := congrArg norm hr
    simpa only [hunit, norm_smul, Real.norm_eq_abs, mul_one] using hh.symm
  rcases (abs_eq (show (0 : ℝ) ≤ 1 by norm_num)).mp habs with hp | hm
  · exact strictSupportingFace_not_pos_parallel normal offset hji.symm (hface i) (hface j)
      (show (0 : ℝ) < r by linarith) hr
  · exact hi j (by simpa only [hm, neg_one_smul] using hr)

/-- In the plane, a nonzero direction cannot be orthogonal to two nonparallel normals. -/
theorem planar_inner_ne_zero_of_not_parallel (v n m : Euclidean 2)
    (hv : v ≠ 0) (hn : n ≠ 0) (hvnormal : inner (𝕜 := ℝ) v n = 0)
    (hparallel : ∀ r : ℝ, m ≠ r • n) : inner (𝕜 := ℝ) v m ≠ 0 := by
  intro hm
  have hni : v 0 * n 0 + v 1 * n 1 = 0 := by
    simpa only [PiLp.inner_apply, Fin.sum_univ_two, RCLike.inner_apply,
      RCLike.conj_to_real, mul_comm] using hvnormal
  have hmi : v 0 * m 0 + v 1 * m 1 = 0 := by
    simpa only [PiLp.inner_apply, Fin.sum_univ_two, RCLike.inner_apply,
      RCLike.conj_to_real, mul_comm] using hm
  have coord_ne {w : Euclidean 2} (hw : w ≠ 0) : w 0 ≠ 0 ∨ w 1 ≠ 0 := by
    by_contra hh
    push_neg at hh
    apply hw
    apply PiLp.ext
    intro i
    fin_cases i
    · exact hh.1
    · exact hh.2
  by_cases hn₀ : n 0 = 0
  · have hn₁ : n 1 ≠ 0 := (coord_ne hn).resolve_left (not_not.mpr hn₀)
    have hv₁ : v 1 = 0 := by
      rw [hn₀, mul_zero, zero_add] at hni
      exact (mul_eq_zero.mp hni).resolve_right hn₁
    have hv₀ : v 0 ≠ 0 := (coord_ne hv).resolve_right (not_not.mpr hv₁)
    have hm₀ : m 0 = 0 := by
      rw [hv₁, zero_mul, add_zero] at hmi
      exact (mul_eq_zero.mp hmi).resolve_left hv₀
    apply hparallel (m 1 / n 1)
    apply PiLp.ext
    intro i
    fin_cases i
    · change m 0 = m 1 / n 1 * n 0
      rw [hn₀, hm₀, mul_zero]
    · change m 1 = m 1 / n 1 * n 1
      field_simp
  · have hv₁ : v 1 ≠ 0 := by
      intro he
      have hv₀ : v 0 = 0 := by
        rw [he, zero_mul, add_zero] at hni
        exact (mul_eq_zero.mp hni).resolve_right hn₀
      exact (coord_ne hv).elim (fun h => h hv₀) (fun h => h he)
    have hdet : m 1 * n 0 = m 0 * n 1 := by
      apply mul_left_cancel₀ hv₁
      nlinarith [congrArg (fun z : ℝ => z * m 0) hni,
        congrArg (fun z : ℝ => z * n 0) hmi]
    apply hparallel (m 0 / n 0)
    apply PiLp.ext
    intro i
    fin_cases i
    · change m 0 = m 0 / n 0 * n 0
      field_simp
    · change m 1 = m 0 / n 0 * n 1
      field_simp
      exact hdet

/-- The odd-side argument supplies the literal transversality needed by edge-length Tonelli.
No parity or pairing conclusion is assumed in the geometric hypotheses. -/
theorem odd_strictSupportingFaces_exists_transverse {ι : Type*} [Fintype ι]
    (normal : ι → Euclidean 2) (offset : ι → ℝ)
    (hunit : ∀ i, ‖normal i‖ = 1)
    (hface : ∀ i, (strictSupportingFace normal offset i).Nonempty)
    (hodd : Odd (Fintype.card ι)) :
    ∃ i, ∀ a b : Euclidean 2, a ≠ b →
      a ∈ strictSupportingFace normal offset i →
      b ∈ strictSupportingFace normal offset i →
      ∀ j, j ≠ i → inner (𝕜 := ℝ) (b - a) (normal j) ≠ 0 := by
  obtain ⟨i, hi⟩ := odd_strictSupportingFaces_exists_unpaired normal offset hunit hface hodd
  refine ⟨i, fun a b hab ha hb j hji => ?_⟩
  apply planar_inner_ne_zero_of_not_parallel (b - a) (normal i) (normal j)
    (sub_ne_zero.mpr hab.symm)
    (fun h => by simpa only [h, norm_zero, zero_ne_one] using hunit i)
  · rw [inner_sub_left, ha.1, hb.1, _root_.sub_self]
  · exact hi j hji

/-- With unit inward normals, a distinct parallel irredundant face has exactly the opposite normal. -/
theorem strictSupportingFace_parallel_eq_neg {d : ℕ} {ι : Type*}
    (normal : ι → Euclidean d) (offset : ι → ℝ)
    (hunit : ∀ i, ‖normal i‖ = 1)
    (hface : ∀ i, (strictSupportingFace normal offset i).Nonempty)
    {i j : ι} (hji : j ≠ i) {r : ℝ} (hr : normal j = r • normal i) :
    normal j = -normal i := by
  have habs : |r| = 1 := by
    have hh := congrArg norm hr
    simpa only [hunit, norm_smul, Real.norm_eq_abs, mul_one] using hh.symm
  rcases (abs_eq (show (0 : ℝ) ≤ 1 by norm_num)).mp habs with hp | hm
  · exact (strictSupportingFace_not_pos_parallel normal offset hji.symm (hface i) (hface j)
      (show (0 : ℝ) < r by linarith) hr).elim
  · simpa only [hm, neg_one_smul] using hr

/-- At most two irredundant supporting faces have a given unoriented normal direction.
Thus the geometric restriction used in the odd-side counting argument is proved explicitly. -/
theorem strictSupportingFaces_parallel_card_le_two {d : ℕ} {ι : Type*} [Fintype ι]
    (normal : ι → Euclidean d) (offset : ι → ℝ)
    (hunit : ∀ i, ‖normal i‖ = 1)
    (hface : ∀ i, (strictSupportingFace normal offset i).Nonempty) (i : ι) :
    Set.ncard {j | ∃ r : ℝ, normal j = r • normal i} ≤ 2 := by
  classical
  have hinj := strictSupportingFace_normal_injective normal offset hface
  by_cases hex : ∃ j, j ≠ i ∧ ∃ r : ℝ, normal j = r • normal i
  · obtain ⟨j, hji, r, hr⟩ := hex
    have hjneg := strictSupportingFace_parallel_eq_neg normal offset hunit hface hji hr
    have hsub : {k | ∃ r : ℝ, normal k = r • normal i} ⊆ {i, j} := by
      rintro k ⟨s, hs⟩
      by_cases hki : k = i
      · exact Or.inl hki
      · exact Or.inr (hinj ((strictSupportingFace_parallel_eq_neg normal offset hunit hface
          hki hs).trans hjneg.symm))
    exact (Set.ncard_le_ncard hsub).trans (by rw [Set.ncard_pair hji.symm])
  · have hsub : {k | ∃ r : ℝ, normal k = r • normal i} ⊆ {i} := by
      intro k hk
      change k = i
      by_contra hki
      exact hex ⟨k, hki, hk⟩
    exact (Set.ncard_le_ncard hsub).trans (by simp)

end RieszEuclidean
