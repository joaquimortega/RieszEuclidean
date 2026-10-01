import RieszEuclidean.TitchmarshRegularization
import RieszEuclidean.TitchmarshTranslationContinuity

/-! Exact support control and local detection for compact distribution kernels. -/

noncomputable section
open MeasureTheory Set SchwartzMap
open scoped SchwartzMap Pointwise

namespace RieszEuclidean.CompleteMinimal

/-- A fixed smooth kernel gives a continuous family of reflected translated tests. -/
theorem continuous_regularizationTest {d : ℕ} (ρ : 𝓢(Euclidean d, ℂ)) :
    Continuous (regularizationTest ρ) :=
  (continuous_schwartzTranslateCLM_apply (schwartzReflectCLM ρ)).comp continuous_neg

/-- Regularization of a tempered distribution is a continuous function. -/
theorem continuous_distributionRegularization {d : ℕ}
    (u : TemperedDistribution d) (ρ : 𝓢(Euclidean d, ℂ)) :
    Continuous (distributionRegularization u ρ) :=
  u.continuous.comp (continuous_regularizationTest ρ)

/-- The closed support of a regularized compact distribution lies in the sum
of the exact distribution support and the compact kernel support. -/
theorem distributionRegularization_tsupport_subset {d : ℕ}
    {u : TemperedDistribution d} (hu : CompactlySupportedDistribution u)
    {ρ : 𝓢(Euclidean d, ℂ)} (hρ : HasCompactSupport (ρ : Euclidean d → ℂ)) :
    tsupport (distributionRegularization u ρ) ⊆
      distributionSupport u + tsupport (ρ : Euclidean d → ℂ) := by
  apply closure_minimal
  · intro x hx
    by_contra hn
    exact hx (distributionRegularization_eq_zero_of_not_mem_add_support ρ hn)
  · exact (hu.support_isCompact.add hρ).isClosed

/-- Regularization with a compact kernel has compact support. -/
theorem distributionRegularization_hasCompactSupport {d : ℕ}
    {u : TemperedDistribution d} (hu : CompactlySupportedDistribution u)
    {ρ : 𝓢(Euclidean d, ℂ)} (hρ : HasCompactSupport (ρ : Euclidean d → ℂ)) :
    HasCompactSupport (distributionRegularization u ρ) :=
  (hu.support_isCompact.add hρ).of_isClosed_subset isClosed_closure
    (distributionRegularization_tsupport_subset hu hρ)

/-- Each exact support point can be detected by a compact smooth kernel with
arbitrarily small support around the origin. -/
theorem distributionSupport_regularization_detect_small {d : ℕ}
    {u : TemperedDistribution d} {x : Euclidean d}
    (hx : x ∈ distributionSupport u) {ε : ℝ} (hε : 0 < ε) :
    ∃ ρ : 𝓢(Euclidean d, ℂ), HasCompactSupport (ρ : Euclidean d → ℂ) ∧
      tsupport (ρ : Euclidean d → ℂ) ⊆ Metric.closedBall 0 ε ∧
      distributionRegularization u ρ x ≠ 0 := by
  obtain ⟨ρ, hρ, hlocal, hnonzero⟩ := distributionSupport_regularization_detect
    hx (Metric.ball x ε) Metric.isOpen_ball (Metric.mem_ball_self hε)
  refine ⟨ρ, hρ, ?_, hnonzero⟩
  intro z hz
  have hdist : dist (x - z) x < ε := hlocal z hz
  have hnorm : ‖z‖ < ε := by
    simpa only [dist_eq_norm, sub_sub_cancel_left, norm_neg] using hdist
  simpa only [Metric.mem_closedBall, dist_zero_right] using hnorm.le

end RieszEuclidean.CompleteMinimal
