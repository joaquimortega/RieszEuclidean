import RieszEuclidean.BoxBoundary
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Function.LocallyIntegrable
open Filter Set MeasureTheory
namespace RieszEuclidean
/-- The continuous Fejér weight for the coordinate box of half-side length `R`. -/
noncomputable def fejerWeight {d : ℕ} (R : ℝ) (y : Euclidean d) : ℝ :=
  ∏ j : Fin d, max 0 (1 - |y j| / (2 * R))
/-- Fejér weights are nonnegative. -/
theorem fejerWeight_nonneg {d : ℕ} (R : ℝ) (y : Euclidean d) :
    0 ≤ fejerWeight R y := Finset.prod_nonneg fun _ _ => le_max_left _ _
/-- Positive radii give weights bounded by one. -/
theorem fejerWeight_le_one {d : ℕ} {R : ℝ} (hR : 0 < R) (y : Euclidean d) :
    fejerWeight R y ≤ 1 := by
  apply Finset.prod_le_one
  · intro j _; exact le_max_left _ _
  · intro j _
    exact max_le (by norm_num) (sub_le_self _ (div_nonneg (abs_nonneg _) (by positivity)))
/-- The weight is normalized at the origin. -/
@[simp] theorem fejerWeight_zero {d : ℕ} (R : ℝ) :
    fejerWeight R (0 : Euclidean d) = 1 := by simp [fejerWeight]
/-- The weight is even. -/
@[simp] theorem fejerWeight_neg {d : ℕ} (R : ℝ) (y : Euclidean d) :
    fejerWeight R (-y) = fejerWeight R y := by simp [fejerWeight]
/-- The weight depends continuously on the translation parameter. -/
theorem continuous_fejerWeight {d : ℕ} (R : ℝ) :
    Continuous (fejerWeight (d := d) R) := by
  unfold fejerWeight
  fun_prop
/-- A coordinate beyond twice the radius makes the weight vanish. -/
theorem fejerWeight_eq_zero_of_coordinate {d : ℕ} {R : ℝ} (hR : 0 < R)
    (y : Euclidean d) (j : Fin d) (hj : 2 * R ≤ |y j|) :
    fejerWeight R y = 0 := by
  apply Finset.prod_eq_zero (Finset.mem_univ j)
  apply max_eq_left
  have : 1 ≤ |y j| / (2 * R) := (le_div_iff₀ (by positivity)).2 (by simpa using hj)
  linarith
/-- Coordinate cubes are compact in Euclidean space. -/
theorem isCompact_euclideanBox (d : ℕ) (R : ℝ) :
    IsCompact (euclideanBox d R) := by
  let e := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)).toHomeomorph
  exact e.isCompact_preimage.mpr (isCompact_closedBall 0 R)
/-- The weight vanishes outside the box of twice the radius. -/
theorem fejerWeight_eq_zero_outside {d : ℕ} {R : ℝ} (hR : 0 < R)
    (y : Euclidean d) (hy : y ∉ euclideanBox d (2 * R)) :
    fejerWeight R y = 0 := by
  have hn : ¬ ∀ j : Fin d, |y j| ≤ 2 * R := by
    intro h
    apply hy
    apply (mem_euclideanBox_iff y _).mpr
    exact (pi_norm_le_iff_of_nonneg (by positivity)).mpr h
  obtain ⟨j, hj⟩ := not_forall.mp hn
  exact fejerWeight_eq_zero_of_coordinate hR y j (le_of_lt (lt_of_not_ge hj))
/-- Positive-radius weights have compact support. -/
theorem hasCompactSupport_fejerWeight {d : ℕ} {R : ℝ} (hR : 0 < R) :
    HasCompactSupport (fejerWeight (d := d) R) :=
  HasCompactSupport.intro (isCompact_euclideanBox d (2 * R))
    (fun y hy => fejerWeight_eq_zero_outside hR y hy)
/-- At each fixed translation the weights converge to one as the radius increases. -/
theorem tendsto_fejerWeight {d : ℕ} (y : Euclidean d) :
    Tendsto (fun R : ℝ => fejerWeight R y) atTop (nhds 1) := by
  have hj (j : Fin d) : Tendsto (fun R : ℝ => max 0 (1 - |y j| / (2 * R)))
      atTop (nhds 1) := by
    have h := (tendsto_const_nhds.div_atTop tendsto_id :
      Tendsto (fun R : ℝ => (|y j| / 2) / R) atTop (nhds 0))
    simp only [div_div] at h
    simpa using (tendsto_const_nhds (x := (0 : ℝ))).max
      ((tendsto_const_nhds (x := (1 : ℝ))).sub h)
  simpa [fejerWeight] using tendsto_finset_prod Finset.univ (fun j _ => hj j)
/-- The continuous compactly supported weights are Lebesgue integrable. -/
theorem integrable_fejerWeight {d : ℕ} {R : ℝ} (hR : 0 < R) :
    Integrable (fejerWeight (d := d) R) :=
  (continuous_fejerWeight R).integrable_of_hasCompactSupport
    (hasCompactSupport_fejerWeight hR)
/-- Multiplication by a positive-radius Fejér weight preserves integrability. -/
theorem integrable_fejerWeight_smul {d : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {f : Euclidean d → E}
    (hf : Integrable f) {R : ℝ} (hR : 0 < R) :
    Integrable (fun y => fejerWeight R y • f y) := by
  apply hf.norm.mono'
    ((continuous_fejerWeight R).aestronglyMeasurable.smul hf.aestronglyMeasurable)
  exact Filter.Eventually.of_forall fun y => by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (fejerWeight_nonneg R y)]
    exact mul_le_of_le_one_left (norm_nonneg _) (fejerWeight_le_one hR y)
/-- Fejér weights can be removed from any integrable vector-valued kernel in the limit. -/
theorem tendsto_integral_fejerWeight_smul {d : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {f : Euclidean d → E}
    (hf : Integrable f) :
    Tendsto (fun R : ℝ => ∫ y, fejerWeight R y • f y) atTop (nhds (∫ y, f y)) := by
  apply tendsto_integral_filter_of_dominated_convergence (fun y => ‖f y‖)
  · exact Filter.Eventually.of_forall fun R =>
      (continuous_fejerWeight R).aestronglyMeasurable.smul hf.aestronglyMeasurable
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
    exact Filter.Eventually.of_forall fun y => by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (fejerWeight_nonneg R y)]
      exact mul_le_of_le_one_left (norm_nonneg _) (fejerWeight_le_one hR y)
  · exact hf.norm
  · exact Filter.Eventually.of_forall fun y => by
      simpa using (tendsto_fejerWeight y).smul (tendsto_const_nhds (x := f y))
/-- Fejér truncation converges in the integral of the norm. -/
theorem tendsto_integral_norm_fejerWeight_smul_sub {d : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {f : Euclidean d → E}
    (hf : Integrable f) :
    Tendsto (fun R : ℝ => ∫ y, ‖fejerWeight R y • f y - f y‖) atTop (nhds 0) := by
  have h := tendsto_integral_fejerWeight_smul hf.norm
  have he : ∀ᶠ R : ℝ in atTop,
      (∫ y, ‖fejerWeight R y • f y - f y‖) =
        (∫ y, ‖f y‖) - ∫ y, fejerWeight R y • ‖f y‖ := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
    rw [← integral_sub hf.norm (integrable_fejerWeight_smul hf.norm hR)]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun y => by
      have heq : fejerWeight R y • f y - f y = (fejerWeight R y - 1) • f y := by
        rw [sub_smul, one_smul]
      change ‖fejerWeight R y • f y - f y‖ = ‖f y‖ - fejerWeight R y • ‖f y‖
      rw [heq, norm_smul, Real.norm_eq_abs,
        abs_of_nonpos (sub_nonpos.mpr (fejerWeight_le_one hR y))]
      simp only [smul_eq_mul]
      ring
  apply Filter.Tendsto.congr' (he.mono fun _ hR => hR.symm)
  simpa using (tendsto_const_nhds (x := ∫ y, ‖f y‖)).sub h
end RieszEuclidean
