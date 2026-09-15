import RieszEuclidean.ContactCurvature

noncomputable section
open Filter Topology
namespace RieszEuclidean

/-- Second derivatives along affine lines are evaluations of the second Fréchet
derivative on the direction twice. -/
theorem second_derivative_along_line
    {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → F} (u v : E) (t : ℝ)
    (hf : ContDiffAt ℝ 2 f (u + t • v)) :
    deriv (deriv (fun s : ℝ => f (u + s • v))) t =
      fderiv ℝ (fderiv ℝ f) (u + t • v) v v := by
  have hc (s : ℝ) : HasDerivAt (fun s : ℝ => u + s • v) v s := by
    simpa using (hasDerivAt_const s u).add ((hasDerivAt_id s).smul_const v)
  have he : deriv (fun s : ℝ => f (u + s • v)) =ᶠ[nhds t]
      fun s => fderiv ℝ f (u + s • v) v := by
    have hn := (hc t).continuousAt.tendsto.eventually (hf.eventually (by norm_num))
    filter_upwards [hn] with s hs
    exact ((hs.differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt s (hc s)).deriv
  have hd := ((hf.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).differentiableAt
    (by norm_num)).hasFDerivAt.comp_hasDerivAt t (hc t)
  have hd' := hd.clm_apply (hasDerivAt_const t v)
  have hsecond : HasDerivAt (deriv (fun s : ℝ => f (u + s • v)))
      (fderiv ℝ (fderiv ℝ f) (u + t • v) v v) t := by
    apply HasDerivAt.congr_of_eventuallyEq _ he
    simpa using hd'
  exact hsecond.deriv

/-- The C² chart at a contact point has negative radial second fundamental form
in every nonzero tangent direction, quantitatively in the parameter norm. -/
theorem contact_chart_second_derivative {n : ℕ}
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (φ : E → Euclidean n) (p c : Euclidean n)
    (hφ : ContDiffAt ℝ 2 φ 0) (hφ0 : φ 0 = p)
    (V : E →ₗᵢ[ℝ] Euclidean n) (hd : HasFDerivAt φ V.toContinuousLinearMap 0)
    (hball : ∀ᶠ u in nhds 0, ‖φ u - c‖ ≤ ‖p - c‖) (v : E) :
    inner (𝕜 := ℝ) (p - c) (fderiv ℝ (fderiv ℝ φ) 0 v v) ≤ -‖v‖ ^ 2 := by
  have hc : ContDiffAt ℝ 2 (fun t : ℝ => t • v) 0 :=
    contDiffAt_id.smul contDiffAt_const
  have hq : ContDiffAt ℝ 2 (fun t : ℝ => φ (t • v)) 0 := by
    simpa using (show ContDiffAt ℝ 2 φ ((0 : ℝ) • v) by simpa using hφ).comp 0 hc
  have hm : IsLocalMax (fun t : ℝ => ‖φ (t • v) - c‖ ^ 2) 0 := by
    have hn := (show Tendsto (fun t : ℝ => t • v) (nhds 0) (nhds 0) by
      simpa using hc.continuousAt.tendsto).eventually hball
    filter_upwards [hn] with t ht
    simpa [hφ0] using pow_le_pow_left₀ (norm_nonneg _) ht 2
  have ha := contact_curve_acceleration c hq hm
  have hfirst : deriv (fun t : ℝ => φ (t • v)) 0 = V v := by
    have hl : HasDerivAt (fun t : ℝ => t • v) v 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).smul_const v
    simpa using ((show HasFDerivAt φ V.toContinuousLinearMap ((0 : ℝ) • v) by
      simpa using hd).comp_hasDerivAt 0 hl).deriv
  have hsecond := second_derivative_along_line (f := φ) 0 v 0 (by simpa using hφ)
  simp only [zero_add, zero_smul] at hsecond ha
  rw [hsecond, hφ0, hfirst, V.norm_map] at ha
  exact ha

end RieszEuclidean
