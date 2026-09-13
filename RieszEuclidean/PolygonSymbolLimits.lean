import RieszEuclidean.PolygonLocalGeometry
import RieszEuclidean.BoundarySymbols

noncomputable section
open MeasureTheory Filter Topology
namespace RieszEuclidean

variable {ι : Type*}

/-- The full surviving selected-face jump, retaining tangential translations. -/
def supportingFaceJump (normal : ι → Euclidean 2) (offset : ι → ℝ) (j : ι) (t : Euclidean 2) : Set (Euclidean 2) :=
  {θ | t + θ ∈ strictSupportingFace normal offset j}

/-- The full edge jump is a measurable frequency set. -/
theorem supportingFaceJump_measurableSet [Fintype ι] (normal : ι → Euclidean 2) (offset : ι → ℝ) (j : ι) (t : Euclidean 2) :
    MeasurableSet (supportingFaceJump normal offset j t) := by
  exact (measurableSet_strictSupportingFace normal offset j).preimage
    (measurable_const.add measurable_id)

/-- The invariant zero frequency always belongs to the edge jump. -/
theorem zero_mem_supportingFaceJump (normal : ι → Euclidean 2) (offset : ι → ℝ) (j : ι) (t : Euclidean 2)
    (ht : t ∈ strictSupportingFace normal offset j) : 0 ∈ supportingFaceJump normal offset j t := by
  simpa only [supportingFaceJump, Set.mem_setOf_eq, add_zero] using ht

/-- Every retained jump frequency is tangent to the chosen supporting face. -/
theorem supportingFaceJump_normal_zero
    (normal : ι → Euclidean 2) (offset : ι → ℝ) (j : ι) (t : Euclidean 2)
    (ht : t ∈ strictSupportingFace normal offset j) {θ : Euclidean 2}
    (hθ : θ ∈ supportingFaceJump normal offset j t) :
    inner (𝕜 := ℝ) θ (normal j) = 0 :=
  inner_translation_eq_zero_of_same_hyperplane t θ (normal j) (offset j) ht.1 hθ.1

/-- Jump frequencies lie outside the original open-domain symbol. -/
theorem supportingFaceJump_not_mem (normal : ι → Euclidean 2) (offset : ι → ℝ) (j : ι) (t : Euclidean 2)
    {θ : Euclidean 2} (hθ : θ ∈ supportingFaceJump normal offset j t) :
    t + θ ∉ strictHalfspaceIntersection normal offset := by
  intro h
  exact (ne_of_gt (h j)) hθ.1

/-- Arbitrary interior approaches eventually turn on each retained jump frequency. -/
theorem supportingFaceJump_interior_eventually [Fintype ι] (normal : ι → Euclidean 2) (offset : ι → ℝ) (j : ι) (t θ : Euclidean 2)
    (ht : t ∈ strictSupportingFace normal offset j) (hθ : θ ∈ supportingFaceJump normal offset j t)
    {ts : ℕ → Euclidean 2} (hts : Tendsto ts atTop (nhds t))
    (hin : ∀ n, ts n ∈ strictHalfspaceIntersection normal offset) :
    ∀ᶠ n in atTop, cutoffSymbol (strictHalfspaceIntersection normal offset) (ts n) θ = 1 := by
  filter_upwards [strictSupportingFace_same_direction normal offset j t θ ht hθ ts hts] with n hn
  exact Set.indicator_of_mem (hn.mpr (hin n)) _

/-- Arbitrary strict exterior approaches eventually turn off each retained frequency. -/
theorem supportingFaceJump_exterior_eventually [Fintype ι] (normal : ι → Euclidean 2) (offset : ι → ℝ) (j : ι) (t θ : Euclidean 2)
    (ht : t ∈ strictSupportingFace normal offset j) (hθ : θ ∈ supportingFaceJump normal offset j t)
    {ts : ℕ → Euclidean 2} (hts : Tendsto ts atTop (nhds t))
    (hout : ∀ n, ts n ∉ closure (strictHalfspaceIntersection normal offset)) :
    ∀ᶠ n in atTop, cutoffSymbol (strictHalfspaceIntersection normal offset) (ts n) θ = 0 := by
  filter_upwards [strictSupportingFace_same_direction normal offset j t θ ht hθ ts hts] with n hn
  exact Set.indicator_of_not_mem (fun h => hout n (subset_closure (hn.mp h))) _

/-- At a clean face point the interior symbol gains the entire edge jump. -/
theorem polygonFace_cutoffSymbol_interior_ae_tendsto [Fintype ι] (normal : ι → Euclidean 2) (offset : ι → ℝ) (j : ι)
    (t : Euclidean 2) (ht : t ∈ strictSupportingFace normal offset j)
    (σ : Measure (Euclidean 2))
    (hclean : σ {θ | t + θ ∈ frontier (strictHalfspaceIntersection normal offset) \ strictSupportingFace normal offset j} = 0)
    {ts : ℕ → Euclidean 2} (hts : Tendsto ts atTop (nhds t))
    (hin : ∀ n, ts n ∈ strictHalfspaceIntersection normal offset) :
    ∀ᵐ θ ∂σ, Tendsto (fun n => cutoffSymbol (strictHalfspaceIntersection normal offset) (ts n) θ) atTop
      (nhds (cutoffSymbol (strictHalfspaceIntersection normal offset) t θ +
        (supportingFaceJump normal offset j t).indicator (fun _ => (1 : ℂ)) θ)) := by
  have hae : ∀ᵐ θ ∂σ,
      t + θ ∉ frontier (strictHalfspaceIntersection normal offset) \ strictSupportingFace normal offset j :=
    compl_mem_ae_iff.mpr hclean
  filter_upwards [hae] with θ hθ
  by_cases hj : θ ∈ supportingFaceJump normal offset j t
  · have hn := supportingFaceJump_not_mem normal offset j t hj
    simpa only [cutoffSymbol, Set.indicator_of_not_mem hn, Set.indicator_of_mem hj,
      zero_add] using
      tendsto_const_nhds.congr' ((supportingFaceJump_interior_eventually normal offset j t θ ht hj hts hin).mono (fun _ h => h.symm))
  · have hoff : t + θ ∉ frontier (strictHalfspaceIntersection normal offset) := fun h => hθ ⟨h, hj⟩
    simpa only [Set.indicator_of_not_mem hj, add_zero] using
      tendsto_cutoffSymbol_off_frontier hts hoff

/-- At the same clean point the exterior symbol keeps the original open-domain value. -/
theorem polygonFace_cutoffSymbol_exterior_ae_tendsto [Fintype ι] (normal : ι → Euclidean 2) (offset : ι → ℝ) (j : ι)
    (t : Euclidean 2) (ht : t ∈ strictSupportingFace normal offset j)
    (σ : Measure (Euclidean 2))
    (hclean : σ {θ | t + θ ∈ frontier (strictHalfspaceIntersection normal offset) \ strictSupportingFace normal offset j} = 0)
    {ts : ℕ → Euclidean 2} (hts : Tendsto ts atTop (nhds t))
    (hout : ∀ n, ts n ∉ closure (strictHalfspaceIntersection normal offset)) :
    ∀ᵐ θ ∂σ, Tendsto (fun n => cutoffSymbol (strictHalfspaceIntersection normal offset) (ts n) θ) atTop
      (nhds (cutoffSymbol (strictHalfspaceIntersection normal offset) t θ)) := by
  have hae : ∀ᵐ θ ∂σ,
      t + θ ∉ frontier (strictHalfspaceIntersection normal offset) \ strictSupportingFace normal offset j :=
    compl_mem_ae_iff.mpr hclean
  filter_upwards [hae] with θ hθ
  by_cases hj : θ ∈ supportingFaceJump normal offset j t
  · have hn := supportingFaceJump_not_mem normal offset j t hj
    simpa only [cutoffSymbol, Set.indicator_of_not_mem hn] using
      tendsto_const_nhds.congr' ((supportingFaceJump_exterior_eventually normal offset j t θ ht hj hts hout).mono (fun _ h => h.symm))
  · exact tendsto_cutoffSymbol_off_frontier hts (fun h => hθ ⟨h, hj⟩)

/-- A nonempty unpaired planar supporting face supplies a point clean for any frequency measure. -/
theorem exists_clean_unpairedSupportingFace_point [Fintype ι]
    (normal : ι → Euclidean 2) (offset : ι → ℝ) (j : ι)
    (hn : normal j ≠ 0) (hface : (strictSupportingFace normal offset j).Nonempty)
    (hparallel : ∀ i, i ≠ j → ∀ r : ℝ, normal i ≠ r • normal j)
    (σ : Measure (Euclidean 2)) [SFinite σ] :
    ∃ t ∈ strictSupportingFace normal offset j,
      σ {θ | t + θ ∈ frontier (strictHalfspaceIntersection normal offset) \
        strictSupportingFace normal offset j} = 0 := by
  obtain ⟨a, b, hab, ha, hb⟩ :=
    strictSupportingFace_exists_distinct_points normal offset j hn hface
  apply exists_clean_strictSupportingFace_point normal offset j a b hab ha hb
  intro i hij
  apply planar_inner_ne_zero_of_not_parallel (b - a) (normal j) (normal i)
    (sub_ne_zero.mpr hab.symm) hn
  · rw [inner_sub_left, ha.1, hb.1, _root_.sub_self]
  · exact hparallel i hij

/-- Every ambient conull set supplies both boundary approaches at a common clean point,
with the actual full-face shifted-indicator limits. -/
theorem exists_unpairedSupportingFace_boundary_symbol_limits [Fintype ι]
    (normal : ι → Euclidean 2) (offset : ι → ℝ) (j : ι)
    (hn : normal j ≠ 0) (hface : (strictSupportingFace normal offset j).Nonempty)
    (hparallel : ∀ i, i ≠ j → ∀ r : ℝ, normal i ≠ r • normal j)
    (σ : Measure (Euclidean 2)) [SFinite σ]
    {G : Set (Euclidean 2)} (hG : volume Gᶜ = 0) :
    ∃ t ∈ strictSupportingFace normal offset j,
      σ {θ | t + θ ∈ frontier (strictHalfspaceIntersection normal offset) \
        strictSupportingFace normal offset j} = 0 ∧
      (∃ ts : ℕ → Euclidean 2,
        (∀ n, ts n ∈ G ∩ strictHalfspaceIntersection normal offset) ∧
        Tendsto ts atTop (nhds t) ∧
        ∀ᵐ θ ∂σ, Tendsto (fun n => cutoffSymbol (strictHalfspaceIntersection normal offset) (ts n) θ)
          atTop (nhds (cutoffSymbol (strictHalfspaceIntersection normal offset) t θ +
            (supportingFaceJump normal offset j t).indicator (fun _ => (1 : ℂ)) θ))) ∧
      (∃ ts : ℕ → Euclidean 2,
        (∀ n, ts n ∈ G ∩ (closure (strictHalfspaceIntersection normal offset))ᶜ) ∧
        Tendsto ts atTop (nhds t) ∧
        ∀ᵐ θ ∂σ, Tendsto (fun n => cutoffSymbol (strictHalfspaceIntersection normal offset) (ts n) θ)
          atTop (nhds (cutoffSymbol (strictHalfspaceIntersection normal offset) t θ))) := by
  obtain ⟨t, ht, hc⟩ := exists_clean_unpairedSupportingFace_point normal offset j hn hface hparallel σ
  obtain ⟨⟨tin, hin, htin⟩, ⟨tout, hout, htout⟩⟩ :=
    exists_conull_sequences_strictSupportingFace_two_sides normal offset j hG t ht hn
  exact ⟨t, ht, hc,
    ⟨tin, hin, htin, polygonFace_cutoffSymbol_interior_ae_tendsto normal offset j t ht σ hc htin
      (fun n => (hin n).2)⟩,
    ⟨tout, hout, htout, polygonFace_cutoffSymbol_exterior_ae_tendsto normal offset j t ht σ hc htout
      (fun n => (hout n).2)⟩⟩

end RieszEuclidean
