import RieszEuclidean.DirectionalSecondDerivative

noncomputable section
open Filter Topology
namespace RieszEuclidean

/-- Uniform negativity of a continuous bilinear form persists under a small
operator-norm perturbation. -/
theorem negative_bilinear_perturbation
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {A B : E →L[ℝ] E →L[ℝ] ℝ} {c : ℝ}
    (hA : ∀ v, A v v ≤ -c * ‖v‖ ^ 2) (hB : ‖B - A‖ < c / 2) :
    ∀ v, B v v ≤ -(c / 2) * ‖v‖ ^ 2 := by
  intro v
  have he : ‖(B - A) v v‖ ≤ ‖B - A‖ * ‖v‖ ^ 2 := by
    calc
      _ ≤ ‖(B - A) v‖ * ‖v‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ (‖B - A‖ * ‖v‖) * ‖v‖ :=
        mul_le_mul_of_nonneg_right (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _)
      _ = _ := by ring
  have hval : B v v - A v v ≤ ‖B - A‖ * ‖v‖ ^ 2 := by
    exact (le_abs_self _).trans (by simpa only [ContinuousLinearMap.sub_apply, Real.norm_eq_abs] using he)
  have hmul := mul_le_mul_of_nonneg_right hB.le (sq_nonneg ‖v‖)
  have ha := hA v
  linarith

/-- The quantitative estimate is uniform in all directions on a neighborhood. -/
theorem negative_bilinear_eventually
    {E X : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace X]
    {B : X → E →L[ℝ] E →L[ℝ] ℝ} {x : X} {c : ℝ}
    (hc : 0 < c) (hB : ContinuousAt B x)
    (hneg : ∀ v, B x v v ≤ -c * ‖v‖ ^ 2) :
    ∀ᶠ y in nhds x, ∀ v, B y v v ≤ -(c / 2) * ‖v‖ ^ 2 := by
  have he : ∀ᶠ y in nhds x, ‖B y - B x‖ < c / 2 := by
    have hh : Tendsto (fun y => ‖B y - B x‖) (nhds x) (nhds 0) := by
      have hs : ContinuousAt (fun y => B y - B x) x := hB.sub continuousAt_const
      have hc' : ContinuousAt (fun y => ‖B y - B x‖) x :=
        ContinuousAt.norm (E := E →L[ℝ] E →L[ℝ] ℝ) hs
      simpa only [_root_.sub_self, ContinuousLinearMap.opNorm_zero] using hc'.tendsto
    exact (tendsto_order.1 hh).2 _ (half_pos hc)
  exact he.mono fun _ hy => negative_bilinear_perturbation hneg hy

end RieszEuclidean
