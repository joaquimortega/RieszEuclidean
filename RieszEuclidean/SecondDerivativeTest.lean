import RieszEuclidean.Basic
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.LocalExtr.Basic

noncomputable section
open Filter Topology
namespace RieszEuclidean

/-- A twice continuously differentiable real function has nonpositive second
derivative at a local maximum. -/
theorem second_derivative_nonpos_at_local_max {f : ℝ → ℝ} {a : ℝ}
    (hf : ContDiffAt ℝ 2 f a) (hm : IsLocalMax f a) :
    deriv (deriv f) a ≤ 0 := by
  have hd : ContDiffAt ℝ 1 (deriv f) a := by
    exact (hf.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).clm_apply
      contDiffAt_const
  have hdd : ContinuousAt (deriv (deriv f)) a := by
    exact ((hd.fderiv_right (by norm_num : (0 : WithTop ℕ∞) + 1 ≤ 1)).clm_apply
      contDiffAt_const).continuousAt
  by_contra! hpos
  have hp : ∀ᶠ x in nhds a, 0 < deriv (deriv f) x := hdd.eventually (lt_mem_nhds hpos)
  have he : ∀ᶠ x in nhds a,
      0 < deriv (deriv f) x ∧ ContDiffAt ℝ 2 f x ∧ f x ≤ f a :=
    hp.and ((hf.eventually (by norm_num)).and hm)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp he
  have hconv : StrictConvexOn ℝ (Metric.ball a ε) f := by
    apply strictConvexOn_of_deriv2_pos (convex_ball a ε)
    · intro x hx
      exact (hball hx).2.1.continuousAt.continuousWithinAt
    · intro x hx
      exact (hball (interior_subset hx)).1
  have hx : a - ε / 2 ∈ Metric.ball a ε := by
    rw [Metric.mem_ball, Real.dist_eq]
    have heq : a - ε / 2 - a = -(ε / 2) := by ring
    rw [heq, abs_neg, abs_of_pos (half_pos hε)]
    linarith
  have hy : a + ε / 2 ∈ Metric.ball a ε := by
    rw [Metric.mem_ball, Real.dist_eq, add_sub_cancel_left, abs_of_pos (half_pos hε)]
    linarith
  have hxy : a - ε / 2 ≠ a + ε / 2 := by linarith
  obtain ⟨_, hstrict⟩ := hconv
  have hi := hstrict hx hy hxy (a := (1 / 2 : ℝ)) (b := (1 / 2 : ℝ))
    (by norm_num) (by norm_num) (by norm_num)
  have heq : (1 / 2 : ℝ) • (a - ε / 2) + (1 / 2 : ℝ) • (a + ε / 2) = a := by
    simp only [smul_eq_mul]
    ring
  rw [heq] at hi
  simp only [smul_eq_mul] at hi
  linarith [(hball hx).2.2, (hball hy).2.2]

end RieszEuclidean
