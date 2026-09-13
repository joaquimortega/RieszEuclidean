import RieszEuclidean.Basic
import Mathlib.Analysis.NormedSpace.Real
import RieszEuclidean.BoundaryFubini

noncomputable section
open MeasureTheory Metric Filter Topology
namespace RieszEuclidean

/-- A positive-radius sphere point lies on the frontier and is approached from
both the open ball and its strict exterior. -/
theorem sphere_point_two_sided_closure {d : ℕ} (a : Euclidean d) {r : ℝ}
    (hr : 0 < r) {t₀ : Euclidean d} (ht₀ : t₀ ∈ sphere a r) :
    t₀ ∈ frontier (ball a r) ∧ t₀ ∈ closure (ball a r) ∧
      t₀ ∈ closure (closure (ball a r))ᶜ := by
  refine ⟨?_, ?_, ?_⟩
  · rwa [frontier_ball a hr.ne']
  · rw [closure_ball a hr.ne']
    exact sphere_subset_closedBall ht₀
  · rw [closure_ball a hr.ne', closure_compl, interior_closedBall a hr.ne']
    exact fun h => (not_lt_of_ge (mem_sphere.mp ht₀).ge) (Metric.mem_ball.mp h)

/-- Every Lebesgue-conull parameter set supplies sequences approaching a sphere
point from the ball and from the strict exterior, without restricting to a ray. -/
theorem exists_conull_sequences_sphere_two_sides {d : ℕ}
    {G : Set (Euclidean d)} (hG : volume Gᶜ = 0)
    (a : Euclidean d) {r : ℝ} (hr : 0 < r)
    {t₀ : Euclidean d} (ht₀ : t₀ ∈ sphere a r) :
    (∃ t : ℕ → Euclidean d, (∀ n, t n ∈ G ∩ ball a r) ∧
      Tendsto t atTop (𝓝 t₀)) ∧
    (∃ t : ℕ → Euclidean d, (∀ n, t n ∈ G ∩ (closedBall a r)ᶜ) ∧
      Tendsto t atTop (𝓝 t₀)) := by
  have h := sphere_point_two_sided_closure a hr ht₀
  simpa only [closure_ball a hr.ne'] using
    exists_conull_sequences_two_sides hG Metric.isOpen_ball h.2.1 h.2.2

end RieszEuclidean
