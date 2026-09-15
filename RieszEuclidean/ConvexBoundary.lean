import RieszEuclidean.UnconditionalGeometry
import Mathlib.Analysis.Convex.Measure

noncomputable section
open MeasureTheory Filter Topology
namespace RieszEuclidean

/-- Every neighborhood of a point in the closure of an open Euclidean set
has positive measure in that set. -/
theorem positive_neighborhood_inter_of_mem_closure {d : ℕ}
    {Ω : Set (Euclidean d)} (hΩ : IsOpen Ω) {t : Euclidean d}
    (ht : t ∈ closure Ω) {V : Set (Euclidean d)} (hV : V ∈ nhds t) :
    0 < volume (V ∩ Ω) := by
  obtain ⟨W, hWV, hW, htW⟩ := _root_.mem_nhds_iff.mp hV
  have hn := mem_closure_iff_nhds.mp ht W (hW.mem_nhds htW)
  exact ((hW.inter hΩ).measure_pos volume hn).trans_le
    (measure_mono (Set.inter_subset_inter_left Ω hWV))

/-- An open nonempty convex domain is regular open. In particular, its boundary
is approachable from the strict exterior as well as from the domain. -/
theorem convex_boundary_two_sided {d : ℕ} {Ω : Set (Euclidean d)}
    (hΩ : IsOpen Ω) (hn : Ω.Nonempty) (hc : Convex ℝ Ω)
    {t : Euclidean d} (ht : t ∈ frontier Ω) :
    ∀ V ∈ nhds t, 0 < volume (V ∩ Ω) ∧
      0 < volume (V ∩ (closure Ω)ᶜ) := by
  have hi : interior (closure Ω) = Ω := by
    rw [hc.interior_closure_eq_interior_of_nonempty_interior
      (hΩ.interior_eq.symm ▸ hn), hΩ.interior_eq]
  have he : t ∈ closure (closure Ω)ᶜ := by
    rw [closure_compl, hi]
    exact (hΩ.frontier_eq ▸ ht).2
  intro V hV
  exact ⟨positive_neighborhood_inter_of_mem_closure hΩ
    (frontier_subset_closure ht) hV,
    positive_neighborhood_inter_of_mem_closure isClosed_closure.isOpen_compl he hV⟩

/-- For convex domains, the boundary-measure criterion only needs the finite
nonzero boundary measure and its translated non-overlap property. Boundary
Lebesgue-nullity and two-sided neighborhood positivity follow from convexity. -/
theorem convex_no_exponentialRieszBasis_of_boundary_measure {d : ℕ}
    (Ω : Set (Euclidean d)) (hΩ : IsOpen Ω) (hn : Ω.Nonempty)
    (hc : Convex ℝ Ω) (hb : Bornology.IsBounded Ω)
    (ν : Measure (Euclidean d)) [IsFiniteMeasure ν] (hν : ν ≠ 0)
    (hsupport : ν (frontier Ω)ᶜ = 0)
    (hoverlap : ∀ θ : Euclidean d, θ ≠ 0 →
      ν (frontier Ω ∩ RieszEuclidean.translate θ (frontier Ω)) = 0)
    (Λ : Set (Euclidean d)) : ¬ HasExponentialRieszBasis Ω Λ := by
  apply SeparatedConfiguration.no_exponentialRieszBasis_of_general_boundary
    Ω ⟨hΩ, hn⟩ hb (hc.addHaar_frontier volume) ν hν hsupport hoverlap
  have hs : ∀ᵐ t ∂ν, t ∈ frontier Ω := by
    simpa only [compl_compl] using compl_mem_ae_iff.mpr hsupport
  filter_upwards [hs] with t ht
  exact convex_boundary_two_sided hΩ hn hc ht

/-- A finite positive measure on a boundary patch suffices; no global strict
convexity or global curvature condition enters the analytic argument. -/
theorem convex_no_exponentialRieszBasis_of_boundary_patch {d : ℕ}
    (Ω : Set (Euclidean d)) (hΩ : IsOpen Ω) (hn : Ω.Nonempty)
    (hc : Convex ℝ Ω) (hb : Bornology.IsBounded Ω)
    (μ : Measure (Euclidean d)) (U : Set (Euclidean d))
    (hUS : U ⊆ frontier Ω)
    (hpos : μ U ≠ 0) (hfin : μ U ≠ ⊤)
    (hoverlap : ∀ θ : Euclidean d, θ ≠ 0 →
      μ (U ∩ RieszEuclidean.translate θ (frontier Ω)) = 0)
    (Λ : Set (Euclidean d)) : ¬ HasExponentialRieszBasis Ω Λ := by
  let ν := μ.restrict U
  haveI : IsFiniteMeasure ν := ⟨by simpa [ν] using hfin.lt_top⟩
  have hnν : ν ≠ 0 := by
    intro hz
    have hu := congrArg (fun m : Measure (Euclidean d) => m Set.univ) hz
    simp [ν, hpos] at hu
  apply convex_no_exponentialRieszBasis_of_boundary_measure Ω hΩ hn hc hb ν hnν
  · rw [Measure.restrict_apply isClosed_frontier.measurableSet.compl]
    apply measure_mono_null (t := ∅) _ (measure_empty)
    intro x hx
    exact hx.1 (hUS hx.2)
  · intro θ hθ
    change (μ.restrict U) (frontier Ω ∩ (fun x => x + θ) ⁻¹' frontier Ω) = 0
    have hm : MeasurableSet (frontier Ω ∩ (fun x => x + θ) ⁻¹' frontier Ω) :=
      isClosed_frontier.measurableSet.inter
        (isClosed_frontier.measurableSet.preimage
          (continuous_id.add continuous_const).measurable)
    rw [Measure.restrict_apply hm]
    apply measure_mono_null _ (hoverlap θ hθ)
    intro x hx
    exact ⟨hx.2, hx.1.2⟩

end RieszEuclidean
