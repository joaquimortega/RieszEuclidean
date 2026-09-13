import RieszEuclidean.FejerKernel
import RieszEuclidean.BoxBoundary
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
/-!
# Concentration of Euclidean box Fejér kernels

Euclidean dilation gives the exact kernel scaling. Since the unit kernel is
integrable with mass one, its mass in expanding balls tends to one; thus the
rescaled kernels concentrate at zero.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Pointwise
namespace RieszEuclidean
/-- Coordinate-box norm scales by the absolute value of the scalar. -/
theorem boxNorm_smul {d : ℕ} (R : ℝ) (x : Euclidean d) :
    boxNorm (R • x) = |R| * boxNorm x := by
  change ‖R • (EuclideanSpace.measurableEquiv (Fin d) x)‖ = _
  rw [norm_smul, Real.norm_eq_abs]
  rfl
/-- Dilating the unit coordinate box gives the box of radius `R`. -/
theorem smul_euclideanBox_one (d : ℕ) {R : ℝ} (hR : 0 < R) :
    R • euclideanBox d 1 = euclideanBox d R := by
  ext x
  rw [mem_smul_set_iff_inv_smul_mem₀ hR.ne', mem_euclideanBox_iff,
    mem_euclideanBox_iff, boxNorm_smul, abs_of_pos (inv_pos.mpr hR)]
  rw [← div_eq_inv_mul, div_le_iff₀ hR, one_mul]

/-- Scaling the positive Fourier transform of a box indicator. -/
theorem box_exponential_integral_scale (d : ℕ) {R : ℝ} (hR : 0 < R)
    (x : Euclidean d) :
    (∫ v in euclideanBox d R, exponential x v) =
      (R ^ d) • ∫ v in euclideanBox d 1, exponential (R • x) v := by
  have h := Measure.setIntegral_comp_smul_of_pos volume (exponential x)
    (euclideanBox d 1) hR
  rw [smul_euclideanBox_one d hR] at h
  have he : (fun v => exponential x (R • v)) = exponential (R • x) := by
    funext v
    simp only [exponential, inner_smul_left, inner_smul_right, conj_trivial]
  rw [he, finrank_euclideanSpace, Fintype.card_fin] at h
  rw [h, smul_smul, mul_inv_cancel₀ (pow_ne_zero _ hR.ne'), one_smul]

/-- Positive-side Fejér kernels are dilates of the unit-box kernel. -/
theorem fejerKernel_scale (d : ℕ) {R : ℝ} (hR : 0 < R) (x : Euclidean d) :
    fejerKernel d R x = R ^ d * fejerKernel d 1 (R • x) := by
  rw [fejerKernel_eq_box_integral, box_exponential_integral_scale d hR,
    fejerKernel_eq_box_integral, norm_smul, Real.norm_eq_abs,
    abs_of_pos (pow_pos hR _)]
  simp only [Measure.real, volume_euclideanBox d hR.le,
    volume_euclideanBox d zero_le_one, ENNReal.toReal_ofReal (pow_nonneg (by positivity) _)]
  rw [mul_one, mul_pow]
  field_simp
  ring
/-- Integrating a box Fejér kernel over a ball reduces to the unit kernel. -/
theorem fejerKernel_integral_closedBall_scale (d : ℕ) {R ε : ℝ}
    (hR : 0 < R) (hε : 0 ≤ ε) :
    (∫ x in Metric.closedBall 0 ε, fejerKernel d R x) =
      ∫ x in Metric.closedBall 0 (R * ε), fejerKernel d 1 x := by
  simp_rw [fejerKernel_scale d hR]
  rw [integral_const_mul, Measure.setIntegral_comp_smul_of_pos volume _ _ hR,
    finrank_euclideanSpace, Fintype.card_fin, smul_eq_mul, ← mul_assoc,
    mul_inv_cancel₀ (pow_ne_zero _ hR.ne'), one_mul,
    smul_closedBall _ _ hε]
  simp only [smul_zero, Real.norm_eq_abs, abs_of_pos hR]

/-- Fejér mass outside any fixed positive-radius ball tends to zero. -/
theorem tendsto_fejerKernel_tail (d : ℕ) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun R : ℝ => ∫ x in (Metric.closedBall 0 ε)ᶜ, fejerKernel d R x)
      atTop (nhds 0) := by
  have hi := (fejerKernel_integrable_integral d (R := 1) zero_lt_one).1
  have ht : Tendsto (fun R : ℝ => ∫ x in Metric.closedBall 0 (R * ε), fejerKernel d 1 x)
      atTop (nhds 1) := by
    have hballs := (aecover_closedBall (x := (0 : Euclidean d)) (tendsto_id.atTop_mul_const hε)).integral_tendsto_of_countably_generated hi
    simpa only [(fejerKernel_integrable_integral d (R := 1) zero_lt_one).2] using hballs
  have hz := (tendsto_const_nhds (x := (1 : ℝ))).sub ht
  have hz' : Tendsto (fun R : ℝ => 1 - ∫ x in Metric.closedBall 0 (R * ε), fejerKernel d 1 x)
      atTop (nhds 0) := by simpa using hz
  apply hz'.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
  rw [setIntegral_compl Metric.isClosed_closedBall.measurableSet
    (fejerKernel_integrable_integral d hR).1,
    (fejerKernel_integrable_integral d hR).2,
    fejerKernel_integral_closedBall_scale d hR hε.le]

end RieszEuclidean
