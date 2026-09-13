import RieszEuclidean.FejerConcentration
import RieszEuclidean.ApproximateCutoffs
import Mathlib.MeasureTheory.Integral.Prod
/-!
# Concrete smoothed box Fejér cutoffs

The actual normalized coordinate-box kernels yield measurable cutoffs between
zero and one, converging pointwise to the domain indicator off its frontier.
-/

noncomputable section
open MeasureTheory Set Filter
namespace RieszEuclidean
/-- The actual box Fejér kernel smoothed against the domain indicator. -/
def fejerCutoff {d : ℕ} (Ω : Set (Euclidean d)) (R : ℝ) (x : Euclidean d) : ℝ :=
  smoothedIndicator (fejerKernel d R) Ω x

/-- The cutoff integral is well-defined for every measurable domain. -/
theorem integrable_fejerCutoff_integrand {d : ℕ} {Ω : Set (Euclidean d)}
    (hΩ : MeasurableSet Ω) {R : ℝ} (hR : 0 < R) (x : Euclidean d) :
    Integrable (fun y => fejerKernel d R y * Ω.indicator (fun _ => (1 : ℝ)) (x - y)) :=
  integrable_smoothedIndicator (fejerKernel_integrable_integral d hR).1 hΩ x

/-- The actual smoothed Fejér cutoffs lie between zero and one. -/
theorem fejerCutoff_mem_Icc {d : ℕ} {Ω : Set (Euclidean d)}
    (hΩ : MeasurableSet Ω) {R : ℝ} (hR : 0 < R) (x : Euclidean d) :
    fejerCutoff Ω R x ∈ Icc (0 : ℝ) 1 :=
  smoothedIndicator_mem_Icc (fejerKernel_integrable_integral d hR).1
    (fejerKernel_nonneg d R) (fejerKernel_integrable_integral d hR).2 hΩ x

/-- The smoothed box Fejér cutoffs converge to the indicator off the boundary. -/
theorem tendsto_fejerCutoff {d : ℕ} {Ω : Set (Euclidean d)}
    (hΩ : MeasurableSet Ω) {x : Euclidean d} (hx : x ∉ frontier Ω) :
    Tendsto (fun R : ℝ => fejerCutoff Ω R x) atTop
      (nhds (Ω.indicator (fun _ => (1 : ℝ)) x)) := by
  apply tendsto_smoothedIndicator
    (fun R hR => (fejerKernel_integrable_integral d hR).1)
    (fun R _ => fejerKernel_nonneg d R)
    (fun R hR => (fejerKernel_integrable_integral d hR).2) _ hΩ hx
  intro ε hε
  simpa only [Metric.closedBall, dist_zero_right, Set.compl_setOf, not_le] using
    tendsto_fejerKernel_tail d hε
/-- Each positive-side Fejér kernel is continuous. -/
theorem continuous_fejerKernel (d : ℕ) {R : ℝ} (hR : 0 < R) :
    Continuous (fejerKernel d R) := by
  have hi : Integrable ((euclideanBox d R).indicator (fun _ => (1 : ℂ))) :=
    (integrable_indicator_iff (measurableSet_euclideanBox d R)).mpr
      (integrableOn_const.mpr (Or.inr (volume_euclideanBox_pos_lt_top d hR).2))
  have hc : Continuous (Real.fourierIntegralInv
      ((euclideanBox d R).indicator (fun _ => (1 : ℂ)))) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (continuous_fst.inner continuous_snd).neg hi
  exact continuous_const.mul (hc.norm.pow 2)

/-- Smoothed Fejér cutoffs are measurable functions of the spatial parameter. -/
theorem measurable_fejerCutoff {d : ℕ} {Ω : Set (Euclidean d)}
    (hΩ : MeasurableSet Ω) {R : ℝ} (hR : 0 < R) :
    Measurable (fejerCutoff Ω R) := by
  have hm : Measurable (fun p : Euclidean d × Euclidean d =>
      fejerKernel d R p.2 * Ω.indicator (fun _ => (1 : ℝ)) (p.1 - p.2)) :=
    ((continuous_fejerKernel d hR).measurable.comp measurable_snd).mul
      ((measurable_const.indicator hΩ).comp (measurable_fst.sub measurable_snd))
  exact hm.stronglyMeasurable.integral_prod_right'.measurable

end RieszEuclidean
