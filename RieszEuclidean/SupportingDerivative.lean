import RieszEuclidean.ConvexDefiningFunctions
import RieszEuclidean.TransverseLinearAlgebra
import RieszEuclidean.RegularLevelNullity

noncomputable section
open MeasureTheory Filter Topology
namespace RieszEuclidean

/-- A nonzero real continuous functional is onto. -/
theorem functional_range_eq_top {n : ℕ} {L : Euclidean n →L[ℝ] ℝ} (hL : L ≠ 0) :
    LinearMap.range L = ⊤ := by
  apply Module.Dual.range_eq_top_of_ne_zero
  intro hz
  apply hL
  ext x
  exact DFunLike.congr_fun hz x

/-- The derivative of a regular defining function determines every supporting
functional up to scalar multiplication. -/
theorem supporting_functional_proportional {n : ℕ} {Ω : Set (Euclidean n)}
    {p : Euclidean n} {f : Euclidean n → ℝ} {L J : Euclidean n →L[ℝ] ℝ}
    (hf : HasStrictFDerivAt f L p) (hL : L ≠ 0) (hf0 : f p = 0)
    (hlevel : ∀ᶠ x in nhds p, x ∈ frontier Ω ↔ f x = 0)
    (hJ : FunctionalSupportsAt (closure Ω) p J) : ∃ c : ℝ, J = c • L := by
  classical
  classical
  let hr := functional_range_eq_top hL
  let φ := hf.implicitFunction f L hr (f p)
  have hφ0 : φ 0 = p := hf.implicitFunction_apply_image hr
  have hφ : HasStrictFDerivAt φ (LinearMap.ker L).subtypeL 0 := hf.to_implicitFunction hr
  have hφlevel : ∀ᶠ u in nhds (0 : LinearMap.ker L), φ u ∈ frontier Ω := by
    have hm := (tendsto_const_nhds.prodMk_nhds tendsto_id).eventually
      (hf.map_implicitFunction_eq hr)
    have ht : Tendsto φ (nhds 0) (nhds p) := hφ0 ▸ hφ.continuousAt.tendsto
    have hs := ht.eventually hlevel
    filter_upwards [hm, hs] with u hu hs
    exact hs.mpr (hu.trans hf0)
  have hg : IsLocalMax (fun u => J (φ u - p)) 0 := by
    filter_upwards [hφlevel] with u hu
    rw [hφ0, _root_.sub_self, map_zero]
    exact hJ _ (frontier_subset_closure hu)
  have hd : J.comp (LinearMap.ker L).subtypeL = 0 := by
    apply hg.hasFDerivAt_eq_zero
    exact J.hasFDerivAt.comp 0 (hφ.hasFDerivAt.sub_const p)
  by_contra hn
  have hnonprop : ∀ c : ℝ, J ≠ c • L := fun c he => hn ⟨c, he⟩
  have hsurj := prod_functionals_surjective L J hL hnonprop
  obtain ⟨v, hv⟩ := hsurj (0, 1)
  have hvL : L v = 0 := congrArg Prod.fst hv
  have hvJ : J v = 1 := congrArg Prod.snd hv
  have he := DFunLike.congr_fun hd (⟨v, hvL⟩ : LinearMap.ker L)
  change J v = 0 at he
  linarith

/-- A nonzero supporting functional is strictly negative towards any interior
point. Otherwise a nonzero affine function would have a local maximum there. -/
theorem supporting_functional_strict_interior {n : ℕ} {Ω : Set (Euclidean n)}
    (hΩ : IsOpen Ω) {p c : Euclidean n} (hc : c ∈ Ω)
    {L : Euclidean n →L[ℝ] ℝ} (hL : L ≠ 0)
    (hs : FunctionalSupportsAt (closure Ω) p L) : L (c - p) < 0 := by
  have hle := hs c (subset_closure hc)
  apply lt_of_le_of_ne hle
  intro he
  have hm : IsLocalMax (fun x => L (x - p)) c := by
    filter_upwards [hΩ.mem_nhds hc] with x hx
    rw [he]
    exact hs x (subset_closure hx)
  apply hL
  have hd : HasFDerivAt (fun x => L (x - p)) L c := by
    simpa only [ContinuousLinearMap.comp_id] using
      L.hasFDerivAt.comp c ((hasFDerivAt_id c).sub_const p)
  exact IsLocalMax.hasFDerivAt_eq_zero hm hd

end RieszEuclidean
