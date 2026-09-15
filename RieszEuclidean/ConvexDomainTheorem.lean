import RieszEuclidean.ChartSurfaceMeasure
import RieszEuclidean.ConvexTranslatedOverlap
import RieszEuclidean.ConvexBoundary

noncomputable section
open MeasureTheory Topology
namespace RieszEuclidean

/-- Corollary 8.1: no bounded nonempty open convex domain with C² boundary in
dimension at least two admits an exponential Riesz basis. All geometric and
surface-measure inputs are derived from the domain hypotheses. -/
theorem convex_C2_no_exponentialRieszBasis {n : ℕ} (hn : 2 ≤ n)
    (Ω : Set (Euclidean n)) (hΩ : IsOpen Ω) (hne : Ω.Nonempty)
    (hc : Convex ℝ Ω) (hb : Bornology.IsBounded Ω) (hC : HasC2Boundary Ω)
    (Λ : Set (Euclidean n)) : ¬ HasExponentialRieszBasis Ω Λ := by
  obtain ⟨C⟩ := exists_convex_curved_patch (by omega : 0 < n) hΩ hc hb hne hC
  obtain ⟨K, hK, hpos, hfin⟩ := C.exists_positive_finite_subpatch
  apply convex_no_exponentialRieszBasis_of_boundary_patch Ω hΩ hne hc hb
    (Measure.hausdorffMeasure ((n-1 : ℕ) : ℝ)) K (fun x hx => (hK hx).2) hpos hfin
  intro θ hθ
  apply measure_mono_null (Set.inter_subset_inter_left _ hK)
  exact c2_patch_translated_overlap_null hn hΩ hc hC (fun _ hx => hx.2)
    C.singleton_faces hθ

end RieszEuclidean
