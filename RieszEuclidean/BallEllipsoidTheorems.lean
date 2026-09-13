import RieszEuclidean.BochnerExistence
import RieszEuclidean.EllipsoidAnalyticAssembly
noncomputable section
open MeasureTheory Metric
namespace RieszEuclidean
/-- No Euclidean ball of positive radius in dimension at least two has an exponential Riesz basis. -/
theorem not_hasExponentialRieszBasis_ball {d : ℕ} (hd : 2 ≤ d)
    (a : Euclidean d) {r : ℝ} (hr : 0 < r) (Λ : Set (Euclidean d)) :
    ¬HasExponentialRieszBasis (Metric.ball a r) Λ :=
  SeparatedConfiguration.not_hasExponentialRieszBasis_ball_of_hull_representations hd a hr
    (@SeparatedConfiguration.exists_hull_spectralMeasures d) Λ
/-- A ball in dimension at least two admits no frequency set furnishing an exponential Riesz basis. -/
theorem not_exists_exponentialRieszBasis_ball {d : ℕ} (hd : 2 ≤ d)
    (a : Euclidean d) {r : ℝ} (hr : 0 < r) :
    ¬∃ Λ : Set (Euclidean d), HasExponentialRieszBasis (Metric.ball a r) Λ := by
  rintro ⟨Λ, hΛ⟩
  exact not_hasExponentialRieszBasis_ball hd a hr Λ hΛ
/-- No nondegenerate ellipsoid in dimension at least two has an exponential Riesz basis. -/
theorem not_hasExponentialRieszBasis_ellipsoid {d : ℕ} (hd : 2 ≤ d)
    (a : Euclidean d) (A : Euclidean d ≃L[ℝ] Euclidean d) (Λ : Set (Euclidean d)) :
    ¬HasExponentialRieszBasis ((planeAffine a A) '' Metric.ball (0 : Euclidean d) 1) Λ :=
  SeparatedConfiguration.not_hasExponentialRieszBasis_ellipsoid_of_hull_representations hd a A
    (@SeparatedConfiguration.exists_hull_spectralMeasures d) Λ
/-- The paper's ellipsoid corollary, with neither spectral-existence nor geometric inputs left conditional. -/
theorem not_exists_exponentialRieszBasis_ellipsoid {d : ℕ} (hd : 2 ≤ d)
    (a : Euclidean d) (A : Euclidean d ≃L[ℝ] Euclidean d) :
    ¬∃ Λ : Set (Euclidean d),
      HasExponentialRieszBasis ((planeAffine a A) '' Metric.ball (0 : Euclidean d) 1) Λ := by
  rintro ⟨Λ, hΛ⟩
  exact not_hasExponentialRieszBasis_ellipsoid hd a A Λ hΛ
end RieszEuclidean
