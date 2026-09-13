import RieszEuclidean.SphereGeometry
import RieszEuclidean.SphereFiniteness

noncomputable section
open MeasureTheory Metric
namespace RieszEuclidean

/-- The literal codimension-one Hausdorff measure restricted to the Euclidean sphere. -/
def sphereSurfaceMeasure {d : ℕ} (a : Euclidean d) (r : ℝ) : Measure (Euclidean d) :=
  (Measure.hausdorffMeasure ((d - 1 : ℕ) : ℝ)).restrict (sphere a r)

/-- The geometric measure statement of Lemma `lem:sphere`: the actual sphere
carries finite nonzero Hausdorff surface measure, is Lebesgue null, and each
nontrivial translated sphere has zero surface measure. -/
theorem sphere_boundary_measure_properties {d : ℕ} (hd : 2 ≤ d)
    (a : Euclidean d) {r : ℝ} (hr : 0 < r) :
    IsFiniteMeasure (sphereSurfaceMeasure a r) ∧
      0 < sphereSurfaceMeasure a r (sphere a r) ∧
      sphereSurfaceMeasure a r (sphere a r)ᶜ = 0 ∧
      volume (sphere a r) = 0 ∧
      (∀ θ : Euclidean d, θ ≠ 0 →
        sphereSurfaceMeasure a r (sphere a r ∩ translate θ (sphere a r)) = 0) ∧
      (∀ θ : Euclidean d, θ ≠ 0 →
        sphereSurfaceMeasure a r (translate θ (sphere a r)) = 0) := by
  have hd1 : 1 ≤ d := by omega
  refine ⟨?_, ?_, ?_, volume_sphere_eq_zero a hr.ne', ?_, ?_⟩
  · refine ⟨?_⟩
    change ((Measure.hausdorffMeasure ((d - 1 : ℕ) : ℝ)).restrict (sphere a r)) Set.univ < ⊤
    rw [Measure.restrict_apply_univ]
    exact hausdorffMeasure_sphere_lt_top hd1 a hr
  · change 0 < ((Measure.hausdorffMeasure ((d - 1 : ℕ) : ℝ)).restrict
      (sphere a r)) (sphere a r)
    rw [Measure.restrict_apply isClosed_sphere.measurableSet, Set.inter_self]
    exact hausdorffMeasure_sphere_pos hd1 a hr
  · change ((Measure.hausdorffMeasure ((d - 1 : ℕ) : ℝ)).restrict
      (sphere a r)) (sphere a r)ᶜ = 0
    rw [Measure.restrict_apply isClosed_sphere.measurableSet.compl]
    simp only [Set.compl_inter_self, measure_empty]
  · intro θ hθ
    exact sphere_surfaceMeasure_inter_translate hd a θ hθ r
  · intro θ hθ
    exact sphere_surfaceMeasure_translate hd a θ hθ r

end RieszEuclidean
