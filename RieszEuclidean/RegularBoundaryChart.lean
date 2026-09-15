import RieszEuclidean.SmoothImplicitChart
import RieszEuclidean.SupportingDerivative

noncomputable section
open Filter Topology
namespace RieszEuclidean

/-- A regular defining function provides a C² boundary chart whose inverse is
an affine continuous projection onto the tangent kernel. -/
theorem regular_boundary_chart {n : ℕ} {Ω : Set (Euclidean n)}
    {f : Euclidean n → ℝ} {p : Euclidean n} {L : Euclidean n →L[ℝ] ℝ}
    (hf : HasStrictFDerivAt f L p) (hL : L ≠ 0) (hC : ContDiffAt ℝ 2 f p)
    (hlevel : ∀ᶠ x in nhds p, x ∈ frontier Ω ↔ f x = f p) :
    ∃ (φ : LinearMap.ker L → Euclidean n) (P : Euclidean n →L[ℝ] LinearMap.ker L),
      φ 0 = p ∧ ContDiffAt ℝ 2 φ 0 ∧
      HasStrictFDerivAt φ (LinearMap.ker L).subtypeL 0 ∧
      (∀ᶠ u in nhds 0, φ u ∈ frontier Ω ∧ P (φ u-p) = u) ∧
      (∀ᶠ x in nhds p, x ∈ frontier Ω → φ (P (x-p)) = x) := by
  classical
  let hr := functional_range_eq_top hL
  let hk := L.ker_closedComplemented_of_finiteDimensional_range
  let φ := hf.implicitFunction f L hr (f p)
  let P := Classical.choose hk
  let e := hf.implicitToPartialHomeomorph f L hr
  have hφ0 : φ 0 = p := hf.implicitFunction_apply_image hr
  have hd : HasStrictFDerivAt φ (LinearMap.ker L).subtypeL 0 := hf.to_implicitFunction hr
  have he (x : Euclidean n) : e x = (f x, P (x-p)) := rfl
  have hright : ∀ᶠ u in nhds (0 : LinearMap.ker L), e (φ u) = (f p,u) := by
    exact (tendsto_const_nhds.prodMk_nhds tendsto_id).eventually
      (e.eventually_right_inverse (hf.mem_implicitToPartialHomeomorph_target hr))
  have ht : Tendsto φ (nhds 0) (nhds p) := hφ0 ▸ hd.continuousAt.tendsto
  refine ⟨φ, P, hφ0, regular_implicit_contDiffAt hf hr hC, hd, ?_, ?_⟩
  · filter_upwards [hright, ht.eventually hlevel] with u hu hlev
    rw [he] at hu
    exact ⟨hlev.mpr (congrArg Prod.fst hu), congrArg Prod.snd hu⟩
  · filter_upwards [hf.eq_implicitFunction hr, hlevel] with x hx hlev
    intro hxS
    have hfval := hlev.mp hxS
    change hf.implicitFunction f L hr (f x) (P (x-p)) = x at hx
    rwa [hfval] at hx

end RieszEuclidean
