import RieszEuclidean.EdgeGeometry
import RieszEuclidean.TriangleCrossing
import RieszEuclidean.BoundaryFubini
import Mathlib.Analysis.Convex.Measure
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Normed.Operator.Banach

noncomputable section
open MeasureTheory Filter Topology
namespace RieszEuclidean

/-- The closed triangle defined by its three weak supporting inequalities. -/
def closedStandardTriangle (s : ℝ) : Set (Euclidean 2) :=
  {x | 0 ≤ x 0 ∧ 0 ≤ x 1 ∧ x 0 + x 1 ≤ s}

/-- A point on the horizontal coordinate axis. -/
def standardHorizontalPoint (a : ℝ) : Euclidean 2 :=
  (WithLp.equiv 2 (Fin 2 → ℝ)).symm ![a, 0]

theorem standardTriangle_isOpen (s : ℝ) : IsOpen (standardTriangle s) := by
  have hc (i : Fin 2) : Continuous (fun x : Euclidean 2 => x i) :=
    (continuous_apply i).comp (PiLp.continuous_equiv 2 (fun _ : Fin 2 => ℝ))
  exact (isOpen_lt continuous_const (hc 0)).inter
    ((isOpen_lt continuous_const (hc 1)).inter (isOpen_lt ((hc 0).add (hc 1)) continuous_const))

theorem closedStandardTriangle_isClosed (s : ℝ) : IsClosed (closedStandardTriangle s) := by
  have hc (i : Fin 2) : Continuous (fun x : Euclidean 2 => x i) :=
    (continuous_apply i).comp (PiLp.continuous_equiv 2 (fun _ : Fin 2 => ℝ))
  exact (isClosed_le continuous_const (hc 0)).inter
    ((isClosed_le continuous_const (hc 1)).inter (isClosed_le ((hc 0).add (hc 1)) continuous_const))

theorem standardTriangle_subset_closedStandardTriangle (s : ℝ) :
    standardTriangle s ⊆ closedStandardTriangle s :=
  fun _ hx => ⟨hx.1.le, hx.2.1.le, hx.2.2.le⟩

theorem closedStandardTriangle_interior (s : ℝ) :
    interior (closedStandardTriangle s) = standardTriangle s := by
  let p (i : Fin 2) : Euclidean 2 →L[ℝ] ℝ := PiLp.proj 2 (fun _ : Fin 2 => ℝ) i
  have hp (i : Fin 2) : Function.Surjective (p i) := by
    intro a
    refine ⟨(WithLp.equiv 2 (Fin 2 → ℝ)).symm (fun _ => a), rfl⟩
  have hsum : Function.Surjective (p 0 + p 1) := by
    intro a
    refine ⟨standardHorizontalPoint a, ?_⟩
    simp [p, PiLp.proj, standardHorizontalPoint]
  change interior ((p 0 ⁻¹' Set.Ici 0) ∩
    ((p 1 ⁻¹' Set.Ici 0) ∩ ((p 0 + p 1) ⁻¹' Set.Iic s))) = _
  rw [interior_inter, interior_inter, (p 0).interior_preimage (hp 0),
    (p 1).interior_preimage (hp 1), (p 0 + p 1).interior_preimage hsum,
    interior_Ici, interior_Iic]
  rfl

theorem closedStandardTriangle_convex (s : ℝ) : Convex ℝ (closedStandardTriangle s) := by
  intro x hx y hy a b ha hb hab
  change 0 ≤ a * x 0 + b * y 0 ∧ 0 ≤ a * x 1 + b * y 1 ∧
    (a * x 0 + b * y 0) + (a * x 1 + b * y 1) ≤ s
  refine ⟨add_nonneg (mul_nonneg ha hx.1) (mul_nonneg hb hy.1),
    add_nonneg (mul_nonneg ha hx.2.1) (mul_nonneg hb hy.2.1), ?_⟩
  calc
    a * x 0 + b * y 0 + (a * x 1 + b * y 1) =
        a * (x 0 + x 1) + b * (y 0 + y 1) := by ring
    _ ≤ a * s + b * s := add_le_add
      (mul_le_mul_of_nonneg_left hx.2.2 ha) (mul_le_mul_of_nonneg_left hy.2.2 hb)
    _ = s := by rw [← add_mul, hab, one_mul]

theorem standardTriangle_nonempty (s : ℝ) (hs : 0 < s) : (standardTriangle s).Nonempty := by
  refine ⟨(WithLp.equiv 2 (Fin 2 → ℝ)).symm ![s / 3, s / 3], ?_⟩
  change 0 < s / 3 ∧ 0 < s / 3 ∧ s / 3 + s / 3 < s
  constructor
  · positivity
  constructor
  · positivity
  · linarith

theorem standardTriangle_closure (s : ℝ) (hs : 0 < s) :
    closure (standardTriangle s) = closedStandardTriangle s := by
  have h := (closedStandardTriangle_convex s).closure_interior_eq_closure_of_nonempty_interior
    (by rw [closedStandardTriangle_interior]; exact standardTriangle_nonempty s hs)
  simpa only [closedStandardTriangle_interior, (closedStandardTriangle_isClosed s).closure_eq] using h

theorem closedStandardTriangle_norm_le (s : ℝ) (hs : 0 ≤ s)
    {x : Euclidean 2} (hx : x ∈ closedStandardTriangle s) : ‖x‖ ≤ s := by
  have hsq : ‖x‖ ^ 2 = (x 0) ^ 2 + (x 1) ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2, Fin.sum_univ_two]
    simp only [Real.norm_eq_abs, sq_abs]
  have hprod := mul_nonneg hx.1 hx.2.1
  have hsum := add_nonneg hx.1 hx.2.1
  nlinarith [hx.2.2, norm_nonneg x]

theorem closedStandardTriangle_isCompact (s : ℝ) (hs : 0 ≤ s) :
    IsCompact (closedStandardTriangle s) := by
  apply (isCompact_closedBall (0 : Euclidean 2) s).of_isClosed_subset
    (closedStandardTriangle_isClosed s)
  intro x hx
  simpa only [Metric.mem_closedBall, dist_zero_right] using closedStandardTriangle_norm_le s hs hx


/-- The standard triangle is bounded in the ambient Euclidean plane. -/
theorem standardTriangle_isBounded (s : ℝ) (hs : 0 ≤ s) :
    Bornology.IsBounded (standardTriangle s) :=
  (closedStandardTriangle_isCompact s hs).isBounded.subset
    (standardTriangle_subset_closedStandardTriangle s)

/-- Its ordinary frontier is its closed triangle minus its open interior. -/
theorem standardTriangle_frontier (s : ℝ) (hs : 0 < s) :
    frontier (standardTriangle s) = closedStandardTriangle s \ standardTriangle s := by
  rw [frontier, standardTriangle_closure s hs, (standardTriangle_isOpen s).interior_eq]

/-- Convexity gives Lebesgue-null boundary for the actual Euclidean triangle. -/
theorem standardTriangle_volume_frontier (s : ℝ) :
    volume (frontier (standardTriangle s)) = 0 := by
  have hc : Convex ℝ (standardTriangle s) := by
    rw [← closedStandardTriangle_interior]
    exact (closedStandardTriangle_convex s).interior
  exact hc.addHaar_frontier volume

/-- The bottom-edge coordinate description is literally the nondegenerate open segment. -/
theorem standardTriangleEdge_eq_openSegment (s : ℝ) (hs : 0 < s) :
    standardTriangleEdge s = openSegment ℝ (0 : Euclidean 2) (standardHorizontalPoint s) := by
  rw [openSegment_eq_image_lineMap]
  ext x
  constructor
  · intro hx
    refine ⟨x 0 / s, ⟨div_pos hx.1 hs, (div_lt_one hs).mpr hx.2.2⟩, ?_⟩
    rw [AffineMap.lineMap_apply_module]
    apply PiLp.ext
    intro i
    fin_cases i
    · change (1 - x 0 / s) * 0 + x 0 / s * s = x 0
      field_simp
    · change (1 - x 0 / s) * 0 + x 0 / s * 0 = x 1
      simp only [mul_zero, add_zero, hx.2.1]
  · rintro ⟨t, ht, rfl⟩
    rw [AffineMap.lineMap_apply_module]
    change 0 < (1 - t) * 0 + t * s ∧ (1 - t) * 0 + t * 0 = 0 ∧
      (1 - t) * 0 + t * s < s
    simp only [mul_zero, zero_add, add_zero]
    exact ⟨mul_pos ht.1 hs, trivial, by nlinarith [ht.2]⟩

/-- Every point of the selected bottom edge is on the actual frontier. -/
theorem standardTriangleEdge_subset_frontier (s : ℝ) (hs : 0 < s) :
    standardTriangleEdge s ⊆ frontier (standardTriangle s) := by
  rw [standardTriangle_frontier s hs]
  intro x hx
  refine ⟨⟨hx.1.le, by simp only [hx.2.1]; rfl, ?_⟩, ?_⟩
  · simpa only [hx.2.1, add_zero] using hx.2.2.le
  · intro h
    simpa only [hx.2.1, lt_self_iff_false] using h.2.1

/-- Removing the open bottom edge leaves just the vertical and diagonal supports,
including all three vertices. -/
theorem standardTriangle_remainder_subset_supports (s : ℝ) (hs : 0 < s) :
    frontier (standardTriangle s) \ standardTriangleEdge s ⊆
      {x : Euclidean 2 | x 0 = 0} ∪ {x | x 0 + x 1 = s} := by
  rw [standardTriangle_frontier s hs]
  rintro x ⟨⟨hx, hout⟩, hedge⟩
  by_contra hn
  have h₀ : x 0 ≠ 0 := fun h => hn (Or.inl h)
  have hsum : x 0 + x 1 ≠ s := fun h => hn (Or.inr h)
  have hx₀ : 0 < x 0 := lt_of_le_of_ne hx.1 (Ne.symm h₀)
  have hxsum : x 0 + x 1 < s := lt_of_le_of_ne hx.2.2 hsum
  have hx₁ : x 1 = 0 := by
    by_contra hn₁
    exact hout ⟨hx₀, lt_of_le_of_ne hx.2.1 (Ne.symm hn₁), hxsum⟩
  exact hedge ⟨hx₀, hx₁, by simpa only [hx₁, add_zero] using hxsum⟩

/-- A point on the vertical coordinate axis. -/
def standardVerticalPoint (a : ℝ) : Euclidean 2 :=
  (WithLp.equiv 2 (Fin 2 → ℝ)).symm ![0, a]

/-- Pairing with the horizontal unit vector extracts the first coordinate. -/
theorem inner_standardHorizontalPoint_one (x : Euclidean 2) :
    inner (𝕜 := ℝ) x (standardHorizontalPoint 1) = x 0 := by
  simp [PiLp.inner_apply, Fin.sum_univ_two, standardHorizontalPoint]

/-- Pairing with the vertical unit vector extracts the second coordinate. -/
theorem inner_standardVerticalPoint_one (x : Euclidean 2) :
    inner (𝕜 := ℝ) x (standardVerticalPoint 1) = x 1 := by
  simp [PiLp.inner_apply, Fin.sum_univ_two, standardVerticalPoint]

/-- The two endpoints determining bottom-edge length are distinct. -/
theorem standardHorizontalPoint_ne_zero (s : ℝ) (hs : 0 < s) :
    standardHorizontalPoint s ≠ 0 := by
  intro h
  have h₀ := congrArg (fun x : Euclidean 2 => x 0) h
  exact hs.ne' h₀

/-- Every translate of the other two edges is null, including the zero translation. -/
theorem standardTriangle_edgeLength_remainder_null (s : ℝ) (hs : 0 < s)
    (θ : Euclidean 2) :
    edgeLengthMeasure 0 (standardHorizontalPoint s)
      (translate θ (frontier (standardTriangle s) \ standardTriangleEdge s)) = 0 := by
  have hsub : translate θ (frontier (standardTriangle s) \ standardTriangleEdge s) ⊆
      translate θ {x : Euclidean 2 | x 0 = 0} ∪
        translate θ {x : Euclidean 2 | x 0 + x 1 = s} :=
    fun _ hx => standardTriangle_remainder_subset_supports s hs hx
  apply measure_mono_null hsub
  apply measure_union_null
  · have h := edgeLengthMeasure_translate_hyperplane 0 (standardHorizontalPoint s)
      (standardHorizontalPoint 1) θ 0
      (by simpa only [sub_zero, inner_standardHorizontalPoint_one] using hs.ne')
    simpa only [inner_standardHorizontalPoint_one] using h
  · have h := edgeLengthMeasure_translate_hyperplane 0 (standardHorizontalPoint s)
      (standardHorizontalPoint 1 + standardVerticalPoint 1) θ s
      (by
        rw [sub_zero, inner_add_right, inner_standardHorizontalPoint_one,
          inner_standardVerticalPoint_one]
        change s + 0 ≠ 0
        simpa only [add_zero] using hs.ne')
    simpa only [inner_add_right, inner_standardHorizontalPoint_one,
      inner_standardVerticalPoint_one] using h

/-- Tonelli discards exactly the translated boundary remainder, preserving the whole
bottom-edge jump, including all tangential frequencies. -/
theorem exists_clean_standardTriangle_edge_point (s : ℝ) (hs : 0 < s)
    (σ : Measure (Euclidean 2)) [SFinite σ] :
    ∃ t ∈ standardTriangleEdge s,
      σ {θ | t + θ ∈ frontier (standardTriangle s) \ standardTriangleEdge s} = 0 := by
  let ν := edgeLengthMeasure 0 (standardHorizontalPoint s)
  haveI : IsFiniteMeasure ν := edgeLengthMeasure_finite _ _
  have hab : (0 : Euclidean 2) ≠ standardHorizontalPoint s :=
    (standardHorizontalPoint_ne_zero s hs).symm
  haveI : NeZero ν := ⟨fun h =>
    (edgeLengthMeasure_univ_pos 0 (standardHorizontalPoint s) hab).ne'
      (by change ν Set.univ = 0; rw [h]; rfl)⟩
  have hE : MeasurableSet (standardTriangleEdge s) := by
    rw [standardTriangleEdge_eq_openSegment s hs]
    exact measurableSet_openEdge _ _ hab
  have hF : MeasurableSet (frontier (standardTriangle s) \ standardTriangleEdge s) :=
    isClosed_frontier.measurableSet.diff hE
  have hm : MeasurableSet {p : Euclidean 2 × Euclidean 2 |
      p.1 + p.2 ∉ frontier (standardTriangle s) \ standardTriangleEdge s} :=
    (hF.preimage (measurable_fst.add measurable_snd)).compl
  have hsections : ∀ᵐ θ ∂σ, ∀ᵐ t ∂ν,
      t + θ ∉ frontier (standardTriangle s) \ standardTriangleEdge s := by
    apply Eventually.of_forall
    intro θ
    exact compl_mem_ae_iff.mpr (standardTriangle_edgeLength_remainder_null s hs θ)
  have hswap := (Measure.ae_ae_comm (μ := ν) (ν := σ) hm).mpr hsections
  have hedge : ∀ᵐ t ∂ν, t ∈ standardTriangleEdge s := by
    rw [standardTriangleEdge_eq_openSegment s hs]
    exact edgeLengthMeasure_ae_edge _ _ hab
  have hgood : ∀ᵐ t ∂ν, t ∈ standardTriangleEdge s ∧
      σ {θ | t + θ ∈ frontier (standardTriangle s) \ standardTriangleEdge s} = 0 := by
    filter_upwards [hswap, hedge] with t ht he
    exact ⟨he, compl_mem_ae_iff.mp ht⟩
  exact hgood.exists

/-- Bottom-edge points are approached from both ambient open sides of the triangle. -/
theorem standardTriangleEdge_two_sided_closure (s : ℝ) (hs : 0 < s)
    (t : Euclidean 2) (ht : t ∈ standardTriangleEdge s) :
    t ∈ closure (standardTriangle s) ∧ t ∈ closure (closure (standardTriangle s))ᶜ := by
  have hf := standardTriangleEdge_subset_frontier s hs ht
  refine ⟨frontier_subset_closure hf, ?_⟩
  rw [closure_compl, standardTriangle_closure s hs, closedStandardTriangle_interior]
  rw [(standardTriangle_isOpen s).frontier_eq] at hf
  exact hf.2

/-- Any Lebesgue-conull parameter set approaches the selected edge from inside and
from the strict exterior in the ambient plane. -/
theorem exists_conull_sequences_standardTriangle_two_sides (s : ℝ) (hs : 0 < s)
    {G : Set (Euclidean 2)} (hG : volume Gᶜ = 0)
    (t : Euclidean 2) (ht : t ∈ standardTriangleEdge s) :
    (∃ ts : ℕ → Euclidean 2, (∀ j, ts j ∈ G ∩ standardTriangle s) ∧
      Tendsto ts atTop (nhds t)) ∧
    (∃ ts : ℕ → Euclidean 2, (∀ j, ts j ∈ G ∩ (closure (standardTriangle s))ᶜ) ∧
      Tendsto ts atTop (nhds t)) := by
  have h := standardTriangleEdge_two_sided_closure s hs t ht
  exact exists_conull_sequences_two_sides hG (standardTriangle_isOpen s) h.1 h.2

end RieszEuclidean
