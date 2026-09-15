import RieszEuclidean.SecondDerivativeTest
import Mathlib.Analysis.InnerProductSpace.Calculus

noncomputable section
open Filter Topology
namespace RieszEuclidean

/-- At contact with a containing ball, the radial component of the acceleration
of any C² boundary curve is bounded above by minus its squared speed. -/
theorem contact_curve_acceleration {n : ℕ} {q : ℝ → Euclidean n}
    {a : ℝ} (c : Euclidean n) (hq : ContDiffAt ℝ 2 q a)
    (hm : IsLocalMax (fun t => ‖q t - c‖ ^ 2) a) :
    inner (𝕜 := ℝ) (q a - c) (deriv (deriv q) a) ≤ -‖deriv q a‖ ^ 2 := by
  let G := fun t => ‖q t - c‖ ^ 2
  have hd : ContDiffAt ℝ 1 (deriv q) a :=
    (hq.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).clm_apply contDiffAt_const
  have hfirst : deriv G =ᶠ[nhds a] fun t =>
      2 * inner (𝕜 := ℝ) (q t - c) (deriv q t) := by
    filter_upwards [hq.eventually (by norm_num)] with t ht
    exact ((ht.differentiableAt (by norm_num)).hasDerivAt.sub_const c).norm_sq.deriv
  have hs := (((hq.differentiableAt (by norm_num)).hasDerivAt.sub_const c).inner ℝ
    (hd.differentiableAt (by norm_num)).hasDerivAt).const_mul 2
  have hsecond : HasDerivAt (deriv G)
      (2 * (inner (𝕜 := ℝ) (q a - c) (deriv (deriv q) a) + ‖deriv q a‖ ^ 2)) a := by
    apply HasDerivAt.congr_of_eventuallyEq _ hfirst
    simpa only [real_inner_self_eq_norm_sq] using hs
  have hnon := second_derivative_nonpos_at_local_max
    ((hq.sub (contDiffAt_const (c := c))).norm_sq ℝ) hm
  change deriv (deriv G) a ≤ 0 at hnon
  rw [hsecond.deriv] at hnon
  linarith

end RieszEuclidean
