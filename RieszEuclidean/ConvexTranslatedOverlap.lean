import RieszEuclidean.ConvexDefiningFunctions
import RieszEuclidean.TransverseLinearAlgebra
import RieszEuclidean.RegularLevelNullity

noncomputable section
open MeasureTheory Filter Topology
namespace RieszEuclidean

/-- On a C² convex boundary, a patch of singleton supporting faces meets every
nontrivial translated boundary in a surface-null set. The proof derives the
transverse regular levels from the defining functions; transversality is not an
additional nullity assumption. -/
theorem c2_patch_translated_overlap_null {n : ℕ} (hn : 2 ≤ n)
    {Ω U : Set (Euclidean n)} (hΩ : IsOpen Ω) (hc : Convex ℝ Ω)
    (hC : HasC2Boundary Ω) (hU : U ⊆ frontier Ω)
    (hface : ∀ x ∈ U, ∀ L : Euclidean n →L[ℝ] ℝ, L ≠ 0 →
      FunctionalSupportsAt (closure Ω) x L → FunctionalSingletonFace (closure Ω) x L)
    {θ : Euclidean n} (hθ : θ ≠ 0) :
    (Measure.hausdorffMeasure ((n - 1 : ℕ) : ℝ))
      (U ∩ translate θ (frontier Ω)) = 0 := by
  classical
  let μ : Measure (Euclidean n) := Measure.hausdorffMeasure ((n - 1 : ℕ) : ℝ)
  haveI : NoAtoms μ := Measure.noAtoms_hausdorff _ (by exact_mod_cast (show 0 < n - 1 by omega))
  by_cases hopp : ∃ x ∈ U, ∃ (L M : Euclidean n →L[ℝ] ℝ) (c : ℝ),
      L ≠ 0 ∧ FunctionalSupportsAt (closure Ω) x L ∧
      FunctionalSupportsAt (closure Ω) (x + θ) M ∧ M = c • L ∧ c < 0
  · obtain ⟨x, hx, L, M, c, hL0, hL, hM, he, hc⟩ := hopp
    have hs := functional_opposite_inter_subset_singleton hL hM
      (hface x hx L hL0 hL) he hc
    change μ (U ∩ translate θ (frontier Ω)) = 0
    apply measure_mono_null (t := {x}) _ (measure_singleton x)
    intro z hz
    exact hs ⟨frontier_subset_closure (hU hz.1), frontier_subset_closure hz.2⟩
  · apply regular_levels_hausdorff_null (F := ℝ × ℝ)
    intro x hx
    obtain ⟨f, L, hf, hL0, hf0, hL, hSf⟩ :=
      exists_supporting_defining_function hΩ hc hC (hU hx.1)
    obtain ⟨g, M, hg, hM0, hg0, hM, hSg⟩ :=
      exists_supporting_defining_function hΩ hc hC hx.2
    have hnonprop : ∀ c : ℝ, M ≠ c • L := by
      intro c he
      have hc0 : c ≠ 0 := by
        intro hz
        apply hM0
        simp [hz] at he
        exact he
      rcases lt_or_gt_of_ne hc0 with hcneg | hcpos
      · exact hopp ⟨x, hx.1, L, M, c, hL0, hL, hM, he, hcneg⟩
      · have hy := functional_support_points_eq
          (frontier_subset_closure (hU hx.1)) (frontier_subset_closure hx.2)
          hL hM (hface x hx.1 L hL0 hL) he hcpos
        exact hθ (add_left_cancel (hy.trans (add_zero x).symm))
    have hsurj := prod_functionals_surjective L M hL0 hnonprop
    have hdim := prod_functionals_kernel_dim L M hsurj
    have hgshift : HasStrictFDerivAt (fun z => g (z + θ)) M x := by
      simpa using hg.comp x ((hasStrictFDerivAt_id x).add_const θ)
    refine ⟨fun z => (f z, g (z + θ)), L.prod M, hf.prodMk hgshift,
      LinearMap.range_eq_top.mpr hsurj, by omega, ?_⟩
    have hSg' : ∀ᶠ z in nhds x, z + θ ∈ frontier Ω ↔ g (z + θ) = 0 :=
      ((continuous_id.add continuous_const).tendsto x).eventually hSg
    filter_upwards [hSf, hSg'] with z hz₁ hz₂
    intro hz
    apply Prod.ext
    · exact ((hz₁.mp (hU hz.1)).trans hf0.symm)
    · exact ((hz₂.mp hz.2).trans hg0.symm)

end RieszEuclidean
