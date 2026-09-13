import RieszEuclidean.BoxBoundary
import RieszEuclidean.IntegralSymmDiff
import Mathlib.MeasureTheory.Group.Integral
open MeasureTheory Set Filter
open scoped symmDiff
namespace RieszEuclidean
/-- Translation preserves measurability of configurations and integration regions. -/
theorem measurableSet_translate_region {d : ℕ} {s : Set (Euclidean d)}
    (hs : MeasurableSet s) (z : Euclidean d) : MeasurableSet (translate z s) :=
  hs.preimage (measurable_id.add_const z)
/-- Lebesgue volume is invariant under real translations of regions. -/
theorem volume_translate_region {d : ℕ} {s : Set (Euclidean d)}
    (hs : MeasurableSet s) (z : Euclidean d) : volume (translate z s) = volume s :=
  (measurePreserving_add_right volume z).measure_preimage hs.nullMeasurableSet
/-- Change of variables for a translated observable on a region. -/
theorem setIntegral_add_right_region {d : ℕ} (g : Euclidean d → ℝ)
    (s : Set (Euclidean d)) (z : Euclidean d) :
    (∫ y in s, g (y + z)) = ∫ y in translate (-z) s, g y := by
  have h := (measurePreserving_add_right (volume : Measure (Euclidean d)) (-z)).setIntegral_preimage_emb
    (MeasurableEquiv.addRight (-z)).measurableEmbedding (fun y => g (y + z)) s
  simpa [translate, add_assoc] using h.symm
/-- The box probability integral is normalized by the exact coordinate-box volume. -/
theorem boxProbability_integral_eq {d : ℕ} {R : ℝ} (hR : 0 ≤ R) (g : Euclidean d → ℝ) :
    (∫ y, g y ∂boxProbabilityMeasure d R) = ((2 * R) ^ d)⁻¹ * ∫ y in euclideanBox d R, g y := by
  rw [boxProbabilityMeasure, integral_smul_measure, ENNReal.toReal_inv,
    ← measureReal_def, volume_real_euclideanBox d hR, smul_eq_mul]
/-- A globally bounded continuous observable is integrable on every finite-volume region. -/
theorem integrableOn_bounded_observable {d : ℕ} {g : Euclidean d → ℝ} (hg : Continuous g)
    {C : ℝ} (hC : ∀ x, ‖g x‖ ≤ C) {s : Set (Euclidean d)} (hs : volume s < ⊤) :
    IntegrableOn g s volume :=
  (integrableOn_const.mpr (Or.inr hs) : IntegrableOn (fun _ => C) s volume).mono'
    hg.aestronglyMeasurable (Eventually.of_forall hC)
/-- Translation error of a bounded observable is controlled by relative symmetric difference. -/
theorem norm_box_translation_error_le {d : ℕ} {g : Euclidean d → ℝ} (hg : Continuous g)
    {C : ℝ} (hC : ∀ x, ‖g x‖ ≤ C) (z : Euclidean d) {R : ℝ} (hR : 0 < R) :
    ‖(∫ y, g (y + z) ∂boxProbabilityMeasure d R) - ∫ y, g y ∂boxProbabilityMeasure d R‖ ≤
      C * (volume.real (euclideanBox d R ∆ translate (-z) (euclideanBox d R)) / (2 * R) ^ d) := by
  have hs := measurableSet_euclideanBox d R
  have ht := measurableSet_translate_region hs (-z)
  have hfs := (volume_euclideanBox_pos_lt_top d hR).2
  have hft : volume (translate (-z) (euclideanBox d R)) < ⊤ := by
    rwa [volume_translate_region hs (-z)]
  have hfd : volume (translate (-z) (euclideanBox d R) ∆ euclideanBox d R) < ⊤ :=
    (measure_mono symmDiff_subset_union).trans_lt (measure_union_lt_top hft hfs)
  have hb := norm_setIntegral_sub_le_symmDiff ht hs
    (integrableOn_bounded_observable hg hC hft) (integrableOn_bounded_observable hg hC hfs) hC hfd
  rw [symmDiff_comm] at hb
  rw [boxProbability_integral_eq hR.le, boxProbability_integral_eq hR.le,
    ← mul_sub, norm_mul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (pow_pos (by positivity) _)),
    setIntegral_add_right_region]
  calc
    _ ≤ ((2 * R) ^ d)⁻¹ *
        (C * volume.real (euclideanBox d R ∆ translate (-z) (euclideanBox d R))) :=
      mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr (pow_nonneg (by positivity) _))
    _ = _ := by ring
/-- Actual normalized continuous-box averages have vanishing error under every fixed translation. -/
theorem box_translation_error_tendsto_zero {d : ℕ} {g : Euclidean d → ℝ} (hg : Continuous g)
    {C : ℝ} (hC : ∀ x, ‖g x‖ ≤ C) (z : Euclidean d) :
    Tendsto (fun R : ℝ => (∫ y, g (y + z) ∂boxProbabilityMeasure d R) -
      ∫ y, g y ∂boxProbabilityMeasure d R) atTop (nhds 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  refine squeeze_zero' (Eventually.of_forall fun R => norm_nonneg _) ?_
    (by simpa using (box_symmDiff_ratio_tendsto_zero (-z)).const_mul C)
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
    exact norm_box_translation_error_le hg hC z hR

end RieszEuclidean
