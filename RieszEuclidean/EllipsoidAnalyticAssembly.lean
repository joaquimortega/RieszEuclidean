import RieszEuclidean.SphereAnalyticAssembly
import RieszEuclidean.Affine
noncomputable section
open MeasureTheory Metric
namespace RieszEuclidean.SeparatedConfiguration
/-- The paper's actual nondegenerate ellipsoid is an invertible affine image of the unit Metric.ball. -/
theorem not_hasExponentialRieszBasis_ellipsoid_of_hull_representations {d : ℕ}
    (hd : 2 ≤ d) (a : Euclidean d) (A : Euclidean d ≃L[ℝ] Euclidean d)
    (hrep : ∀ {δ : ℝ} (hδ : 0 < δ) (Γ : SeparatedConfiguration d δ)
      [MeasurableSpace (hull Γ)] [BorelSpace (hull Γ)]
      (μ : Measure (hull Γ)) [IsProbabilityMeasure μ]
      (hμ : ∀ z : Euclidean d, MeasurePreserving (hullTranslate hδ Γ z) μ μ),
      ∃ σ : Lp ℂ 2 μ → Measure (Euclidean d), ∀ f,
        RepresentsCorrelation (unitaryCorrelation (hullKoopmanUnitary hδ Γ μ hμ) f) (σ f))
    (Λ : Set (Euclidean d)) :
    ¬HasExponentialRieszBasis ((planeAffine a A) '' Metric.ball (0 : Euclidean d) 1) Λ := by
  intro hB
  exact not_hasExponentialRieszBasis_ball_of_hull_representations hd 0 zero_lt_one hrep
    ((affineFrequency A) '' Λ)
    (hasExponentialRieszBasis_affine_pullback a A (Metric.ball 0 1) Λ hB)

/-- No frequency set gives an exponential Riesz basis on a nondegenerate ellipsoid. -/
theorem not_exists_exponentialRieszBasis_ellipsoid_of_hull_representations {d : ℕ}
    (hd : 2 ≤ d) (a : Euclidean d) (A : Euclidean d ≃L[ℝ] Euclidean d)
    (hrep : ∀ {δ : ℝ} (hδ : 0 < δ) (Γ : SeparatedConfiguration d δ)
      [MeasurableSpace (hull Γ)] [BorelSpace (hull Γ)]
      (μ : Measure (hull Γ)) [IsProbabilityMeasure μ]
      (hμ : ∀ z : Euclidean d, MeasurePreserving (hullTranslate hδ Γ z) μ μ),
      ∃ σ : Lp ℂ 2 μ → Measure (Euclidean d), ∀ f,
        RepresentsCorrelation (unitaryCorrelation (hullKoopmanUnitary hδ Γ μ hμ) f) (σ f))
    : ¬∃ Λ : Set (Euclidean d),
      HasExponentialRieszBasis ((planeAffine a A) '' Metric.ball (0 : Euclidean d) 1) Λ := by
  rintro ⟨Λ, hΛ⟩
  exact not_hasExponentialRieszBasis_ellipsoid_of_hull_representations hd a A hrep Λ hΛ
end RieszEuclidean.SeparatedConfiguration
