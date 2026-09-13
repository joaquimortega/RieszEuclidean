import RieszEuclidean.EuclideanBoxes
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
open Set MeasureTheory Filter
open scoped symmDiff
namespace RieszEuclidean
/-- The coordinate supremum norm controls translation of coordinate boxes. -/
noncomputable def boxNorm {d : ℕ} (x : Euclidean d) : ℝ :=
  ‖EuclideanSpace.measurableEquiv (Fin d) x‖
/-- Membership in a coordinate cube is a bound on the coordinate supremum norm. -/
theorem mem_euclideanBox_iff {d : ℕ} (x : Euclidean d) (R : ℝ) :
    x ∈ euclideanBox d R ↔ boxNorm x ≤ R := by
  simp [euclideanBox, boxNorm, Metric.mem_closedBall, dist_zero_right]
/-- The coordinate supremum norm is nonnegative. -/
theorem boxNorm_nonneg {d : ℕ} (x : Euclidean d) : 0 ≤ boxNorm x := norm_nonneg _
/-- Triangle inequality for the coordinate supremum norm. -/
theorem boxNorm_add_le {d : ℕ} (x y : Euclidean d) :
    boxNorm (x + y) ≤ boxNorm x + boxNorm y := norm_add_le _ _
/-- Negation preserves the coordinate supremum norm. -/
@[simp] theorem boxNorm_neg {d : ℕ} (x : Euclidean d) : boxNorm (-x) = boxNorm x := norm_neg _
/-- Increasing the half-side length enlarges a coordinate cube. -/
theorem euclideanBox_mono {d : ℕ} {R S : ℝ} (h : R ≤ S) :
    euclideanBox d R ⊆ euclideanBox d S := by
  intro x hx
  exact (mem_euclideanBox_iff x S).mpr (((mem_euclideanBox_iff x R).mp hx).trans h)
/-- A smaller concentric box lies in a translated box. -/
theorem innerBox_subset_translate {d : ℕ} (R : ℝ) (z : Euclidean d) :
    euclideanBox d (R - boxNorm z) ⊆ translate z (euclideanBox d R) := by
  intro x hx
  apply (mem_euclideanBox_iff (x + z) R).mpr
  have h := (mem_euclideanBox_iff x _).mp hx
  linarith [boxNorm_add_le x z]
/-- A translated box lies in a larger concentric box. -/
theorem translateBox_subset_outer {d : ℕ} (R : ℝ) (z : Euclidean d) :
    translate z (euclideanBox d R) ⊆ euclideanBox d (R + boxNorm z) := by
  intro x hx
  apply (mem_euclideanBox_iff x _).mpr
  have h := (mem_euclideanBox_iff (x + z) R).mp hx
  have ht := boxNorm_add_le (x + z) (-z)
  simp only [add_neg_cancel_right, boxNorm_neg] at ht
  linarith
/-- The symmetric difference between a box and its translate lies in a thin box shell. -/
theorem box_symmDiff_subset_shell {d : ℕ} (R : ℝ) (z : Euclidean d) :
    euclideanBox d R ∆ translate z (euclideanBox d R) ⊆
      euclideanBox d (R + boxNorm z) \ euclideanBox d (R - boxNorm z) := by
  have hi : euclideanBox d (R - boxNorm z) ⊆ euclideanBox d R :=
    euclideanBox_mono (by linarith [boxNorm_nonneg z])
  have ho : euclideanBox d R ⊆ euclideanBox d (R + boxNorm z) :=
    euclideanBox_mono (by linarith [boxNorm_nonneg z])
  rintro x (hx | hx)
  · exact ⟨ho hx.1, fun h => hx.2 (innerBox_subset_translate R z h)⟩
  · exact ⟨translateBox_subset_outer R z hx.1, fun h => hx.2 (hi h)⟩
/-- The real-valued volume of a coordinate cube. -/
theorem volume_real_euclideanBox (d : ℕ) {R : ℝ} (hR : 0 ≤ R) :
    volume.real (euclideanBox d R) = (2 * R) ^ d := by
  rw [measureReal_def, volume_euclideanBox d hR]
  exact ENNReal.toReal_ofReal (pow_nonneg (mul_nonneg (by norm_num) hR) _)
/-- A shell-volume bound for the symmetric difference with a fixed translate. -/
theorem volume_real_box_symmDiff_le {d : ℕ} (R : ℝ) (z : Euclidean d)
    (hR : boxNorm z ≤ R) :
    volume.real (euclideanBox d R ∆ translate z (euclideanBox d R)) ≤
      (2 * (R + boxNorm z)) ^ d - (2 * (R - boxNorm z)) ^ d := by
  have ho : 0 ≤ R + boxNorm z := by linarith [boxNorm_nonneg z]
  have hi : 0 ≤ R - boxNorm z := sub_nonneg.mpr hR
  have hf : volume (euclideanBox d (R + boxNorm z)) ≠ ⊤ := by
    rw [volume_euclideanBox d ho]
    exact ENNReal.ofReal_ne_top
  have hin : euclideanBox d (R - boxNorm z) ⊆ euclideanBox d (R + boxNorm z) :=
    euclideanBox_mono (by linarith [boxNorm_nonneg z])
  calc
    _ ≤ volume.real (euclideanBox d (R + boxNorm z) \ euclideanBox d (R - boxNorm z)) :=
      measureReal_mono (box_symmDiff_subset_shell R z) (measure_ne_top_of_subset diff_subset hf)
    _ = _ := by
      rw [measureReal_diff hin (measurableSet_euclideanBox d _) hf,
        volume_real_euclideanBox d ho, volume_real_euclideanBox d hi]
/-- The relative volume of a fixed-thickness coordinate-box shell tends to zero. -/
theorem box_shell_ratio_tendsto_zero (d : ℕ) (c : ℝ) :
    Tendsto (fun R : ℝ => ((2 * (R + c)) ^ d - (2 * (R - c)) ^ d) / (2 * R) ^ d)
      atTop (nhds 0) := by
  have hc : Tendsto (fun R : ℝ => c / R) atTop (nhds 0) := tendsto_id.const_div_atTop c
  have h : Tendsto (fun R : ℝ => (1 + c / R) ^ d - (1 - c / R) ^ d) atTop (nhds 0) := by
    have h1 : Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (nhds 1) := tendsto_const_nhds
    simpa using ((h1.add hc).pow d).sub ((h1.sub hc).pow d)
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
  have hp : 1 + c / R = (R + c) / R := by field_simp
  have hm : 1 - c / R = (R - c) / R := by field_simp
  rw [hp, hm, div_pow, div_pow, ← sub_div]
  simp only [mul_pow]
  field_simp
  ring
/-- The relative symmetric-difference volume of a box and a fixed translate vanishes. -/
theorem box_symmDiff_ratio_tendsto_zero {d : ℕ} (z : Euclidean d) :
    Tendsto (fun R : ℝ => volume.real (euclideanBox d R ∆ translate z (euclideanBox d R)) /
      (2 * R) ^ d) atTop (nhds 0) := by
  apply squeeze_zero' ?_ ?_ (box_shell_ratio_tendsto_zero d (boxNorm z))
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with R hR
    exact div_nonneg ENNReal.toReal_nonneg (pow_nonneg (by positivity) _)
  · filter_upwards [eventually_ge_atTop (boxNorm z)] with R hR
    have hR0 : 0 ≤ R := (boxNorm_nonneg z).trans hR
    exact div_le_div_of_nonneg_right (volume_real_box_symmDiff_le R z hR)
      (pow_nonneg (by positivity) _)
end RieszEuclidean
