import RieszEuclidean.LinearHeightHessian
import RieszEuclidean.HessianConcavity

noncomputable section
open Filter Topology
namespace RieszEuclidean

/-- A contact chart has a strictly concave radial height on a small ball.
The quantitative Hessian estimate records persistence of strict curvature. -/
theorem contact_chart_strictConcavity {n : ℕ}
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (φ : E → Euclidean n) (p c : Euclidean n)
    (hφ : ContDiffAt ℝ 2 φ 0) (hφ0 : φ 0 = p)
    (V : E →ₗᵢ[ℝ] Euclidean n) (hd : HasFDerivAt φ V.toContinuousLinearMap 0)
    (hball : ∀ᶠ u in nhds 0, ‖φ u-c‖ ≤ ‖p-c‖) :
    ∃ r : ℝ, 0 < r ∧
      StrictConcaveOn ℝ (Metric.ball 0 r) (fun u => inner (𝕜 := ℝ) (p-c) (φ u)) ∧
      (∀ u ∈ Metric.ball 0 r, ContDiffAt ℝ 2 φ u) ∧
      (∀ u ∈ Metric.ball 0 r, ∀ v,
        inner (𝕜 := ℝ) (p-c) (fderiv ℝ (fderiv ℝ φ) u v v) ≤ -(1/2 : ℝ) * ‖v‖ ^ 2) := by
  let H := innerSL ℝ (p-c)
  let g := fun u => H (φ u)
  have hg : ContDiffAt ℝ 2 g 0 := H.contDiff.contDiffAt.comp 0 hφ
  have hh : ContinuousAt (fderiv ℝ (fderiv ℝ g)) 0 :=
    ((hg.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).fderiv_right
      (by norm_num : (0 : WithTop ℕ∞) + 1 ≤ 1)).continuousAt
  have hneg : ∀ v, fderiv ℝ (fderiv ℝ g) 0 v v ≤ -(1 : ℝ) * ‖v‖ ^ 2 := by
    intro v
    rw [linear_height_hessian hφ H v]
    simpa only [neg_mul, one_mul, H, innerSL_apply] using
      contact_chart_second_derivative φ p c hφ hφ0 V hd hball v
  have hn := negative_bilinear_eventually (by norm_num : (0 : ℝ) < 1) hh hneg
  obtain ⟨r, hr, hsmall⟩ := Metric.mem_nhds_iff.mp (hn.and (hφ.eventually (by norm_num)))
  refine ⟨r, hr, ?_, fun u hu => (hsmall hu).2, ?_⟩
  · apply strictConcaveOn_of_hessian_neg (convex_ball 0 r)
    · intro u hu
      exact H.contDiff.contDiffAt.comp u (hsmall hu).2
    · intro u hu v hv
      have he := (hsmall hu).1 v
      exact lt_of_le_of_lt he (by nlinarith [sq_pos_of_pos (norm_pos_iff.mpr hv)])
  · intro u hu v
    have he := (hsmall hu).1 v
    rw [linear_height_hessian (hsmall hu).2 H v] at he
    exact he

end RieszEuclidean
