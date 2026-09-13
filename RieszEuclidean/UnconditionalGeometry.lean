import RieszEuclidean.BochnerExistence
import RieszEuclidean.TriangleAffineAssembly
import RieszEuclidean.GeneralBoundaryAssembly
import RieszEuclidean.PolygonPresentation

noncomputable section
open MeasureTheory Filter Topology

namespace RieszEuclidean

/-- No noncollinear planar vertex triangle admits an exponential Riesz basis. -/
theorem noncollinear_triangle_no_exponentialRieszBasis
    (a b c : Euclidean 2) (h : ¬ Collinear ℝ (Set.range ![a, b, c]))
    (Λ : Set (Euclidean 2)) : ¬ HasExponentialRieszBasis (vertexTriangle a b c) Λ := by
  exact noncollinear_triangle_no_exponentialRieszBasis_of_hull_representations
    a b c h (fun hδ Γ _ _ μ _ hμ =>
      SeparatedConfiguration.exists_hull_spectralMeasures hδ Γ μ hμ) Λ

namespace SeparatedConfiguration

/-- The manuscript's general boundary-measure criterion excludes exponential
Riesz bases, with spectral-measure existence discharged. -/
theorem no_exponentialRieszBasis_of_general_boundary {d : ℕ}
    (Ω : Set (Euclidean d)) (hΩ : IsOpen Ω ∧ Ω.Nonempty)
    (hbounded : Bornology.IsBounded Ω)
    (hboundary : volume (frontier Ω) = 0)
    (ν : Measure (Euclidean d)) [IsFiniteMeasure ν] (hν : ν ≠ 0)
    (hsupport : ν (frontier Ω)ᶜ = 0)
    (hoverlap : ∀ θ : Euclidean d, θ ≠ 0 →
      ν (frontier Ω ∩ RieszEuclidean.translate θ (frontier Ω)) = 0)
    (hsep : ∀ᵐ t ∂ν, ∀ V ∈ nhds t,
      0 < volume (V ∩ Ω) ∧ 0 < volume (V ∩ (closure Ω)ᶜ))
    (Λ : Set (Euclidean d)) : ¬ HasExponentialRieszBasis Ω Λ := by
  exact no_exponentialRieszBasis_of_general_boundary_and_hull_representations
    Ω hΩ hbounded hboundary ν hν hsupport hoverlap hsep
    (fun hδ Γ _ _ μ _ hμ => exists_hull_spectralMeasures hδ Γ μ hμ) Λ

/-- Every bounded irredundant planar halfspace polygon with an odd number of
actual maximal geometric sides and nonzero supporting normals has no exponential
Riesz basis. -/
theorem oddMaximalSides_no_exponentialRieszBasis_of_nonzero_normals
    {ι : Type*} [Fintype ι] (normal : ι → Euclidean 2) (offset : ι → ℝ)
    (hn : ∀ i, normal i ≠ 0)
    (hface : ∀ i, (strictSupportingFace normal offset i).Nonempty)
    (hbounded : Bornology.IsBounded (strictHalfspaceIntersection normal offset))
    (hodd : Odd (Nat.card {S : Set (Euclidean 2) //
      IsMaximalBoundarySegment (strictHalfspaceIntersection normal offset) S}))
    (Λ : Set (Euclidean 2)) :
    ¬ HasExponentialRieszBasis (strictHalfspaceIntersection normal offset) Λ := by
  exact oddMaximalSides_no_exponentialRieszBasis_of_nonzero_normals_and_hull_representations
    normal offset hn hface hbounded hodd
    (fun hδ Γ _ _ μ _ hμ => exists_hull_spectralMeasures hδ Γ μ hμ) Λ

/-- Every bounded irredundant planar halfspace polygon with a geometrically
unpaired maximal boundary side has no exponential Riesz basis. -/
theorem unpairedMaximalSide_no_exponentialRieszBasis
    {ι : Type*} [Fintype ι] (normal : ι → Euclidean 2) (offset : ι → ℝ)
    (hn : ∀ i, normal i ≠ 0)
    (hface : ∀ i, (strictSupportingFace normal offset i).Nonempty)
    (hbounded : Bornology.IsBounded (strictHalfspaceIntersection normal offset))
    (S : Set (Euclidean 2))
    (hS : IsMaximalBoundarySegment (strictHalfspaceIntersection normal offset) S)
    (hunpaired : ∀ T : Set (Euclidean 2),
      IsMaximalBoundarySegment (strictHalfspaceIntersection normal offset) T →
      T ≠ S → ¬ BoundarySegmentsParallel S T)
    (Λ : Set (Euclidean 2)) :
    ¬ HasExponentialRieszBasis (strictHalfspaceIntersection normal offset) Λ := by
  exact unpairedMaximalSide_no_exponentialRieszBasis_of_hull_representations
    normal offset hn hface hbounded S hS hunpaired
    (fun hδ Γ _ _ μ _ hμ => exists_hull_spectralMeasures hδ Γ μ hμ) Λ

end SeparatedConfiguration
end RieszEuclidean
