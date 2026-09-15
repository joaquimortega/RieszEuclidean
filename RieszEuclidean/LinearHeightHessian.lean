import RieszEuclidean.NegativeBilinear

noncomputable section
open Filter Topology
namespace RieszEuclidean

/-- Taking a fixed linear height commutes with the second derivative. -/
theorem linear_height_hessian
    {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {φ : E → F} {u : E} (hφ : ContDiffAt ℝ 2 φ u)
    (J : F →L[ℝ] ℝ) (v : E) :
    fderiv ℝ (fderiv ℝ (fun w => J (φ w))) u v v =
      J (fderiv ℝ (fderiv ℝ φ) u v v) := by
  have he : fderiv ℝ (fun w => J (φ w)) =ᶠ[nhds u]
      fun w => J.comp (fderiv ℝ φ w) := by
    filter_upwards [hφ.eventually (by norm_num)] with w hw
    exact (J.hasFDerivAt.comp w (hw.differentiableAt (by norm_num)).hasFDerivAt).fderiv
  have hd := (ContinuousLinearMap.compL ℝ E F ℝ J).hasFDerivAt.comp u
    ((hφ.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).differentiableAt
      (by norm_num)).hasFDerivAt
  have hh := (hd.congr_of_eventuallyEq he).fderiv
  exact congrArg (fun A : E →L[ℝ] E →L[ℝ] ℝ => A v v) hh

end RieszEuclidean
