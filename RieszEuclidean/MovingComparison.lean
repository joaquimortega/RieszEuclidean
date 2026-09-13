import Mathlib.Analysis.Normed.Order.Lattice
import RieszEuclidean.ProjectionGap

/-!
# Passing to a moving comparison projection

This is the last analytic limit in Section 6 of the Euclidean manuscript.
The comparison projection depends on the parameter. The hypotheses specify
both limiting families; their construction is recorded in the blueprint.
-/
noncomputable section
namespace RieszEuclidean.OrthProjection

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- A common distance bound survives simultaneous strong convergence of both sides. -/
theorem gap_le_of_two_strong_limits
    (P M : ℕ → H →L[ℂ] H) (R Q : H →L[ℂ] H) (γ : ℝ)
    (hP : StronglyConverges P R) (hM : StronglyConverges M Q)
    (hgap : ∀ j, ‖P j - M j‖ ≤ γ) : ‖R - Q‖ ≤ γ := by
  have hγ : 0 ≤ γ := (norm_nonneg (P 0 - M 0)).trans (hgap 0)
  apply ContinuousLinearMap.opNorm_le_bound _ hγ
  intro x
  have hx := ((hP x).sub (hM x)).norm
  change Filter.Tendsto (fun j => ‖(P j - M j) x‖) Filter.atTop
    (nhds ‖(R - Q) x‖) at hx
  apply le_of_tendsto' hx
  intro j
  exact ((P j - M j).le_opNorm x).trans
    (mul_le_mul_of_nonneg_right (hgap j) (norm_nonneg x))

/-- Operator-norm convergence of the comparison family is more than sufficient. -/
theorem gap_le_of_moving_comparison
    (P M : ℕ → H →L[ℂ] H) (R Q : H →L[ℂ] H) (γ : ℝ)
    (hP : StronglyConverges P R)
    (hM : Filter.Tendsto M Filter.atTop (nhds Q))
    (hgap : ∀ j, ‖P j - M j‖ ≤ γ) : ‖R - Q‖ ≤ γ := by
  apply gap_le_of_two_strong_limits P M R Q γ hP _ hgap
  intro x
  exact (ContinuousLinearMap.apply ℂ H x).continuous.tendsto Q |>.comp hM

/-- The Euclidean boundary contradiction after constructing the two limits. -/
theorem moving_comparison_obstruction [CompleteSpace H]
    (Pminus Pplus Mminus Mplus : ℕ → H →L[ℂ] H)
    (Rminus Rplus Q : OrthProjection H) (γ : ℝ) (hγ : γ < 1)
    (hminus : StronglyConverges Pminus Rminus.op)
    (hplus : StronglyConverges Pplus Rplus.op)
    (hMminus : Filter.Tendsto Mminus Filter.atTop (nhds Q.op))
    (hMplus : Filter.Tendsto Mplus Filter.atTop (nhds Q.op))
    (hgapminus : ∀ j, ‖Pminus j - Mminus j‖ ≤ γ)
    (hgapplus : ∀ j, ‖Pplus j - Mplus j‖ ≤ γ)
    (hinclusion : Rminus.range < Rplus.range) : False := by
  exact nested_not_both_gap Rminus Rplus Q hinclusion
    ⟨(gap_le_of_moving_comparison Pminus Mminus Rminus.op Q.op γ
        hminus hMminus hgapminus).trans_lt hγ,
     (gap_le_of_moving_comparison Pplus Mplus Rplus.op Q.op γ
        hplus hMplus hgapplus).trans_lt hγ⟩

end RieszEuclidean.OrthProjection
