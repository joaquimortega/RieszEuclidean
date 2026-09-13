import RieszEuclidean.Basic
import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.Analysis.Calculus.ContDiff.RCLike
open MeasureTheory Metric Set
open scoped ENNReal
namespace RieszEuclidean
/-- A smooth map sends a compact ball to a set of finite intrinsic-dimensional Hausdorff measure. -/
theorem hausdorffMeasure_contDiff_image_closedBall_lt_top
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F]
    {f : E → F} (hf : ContDiff ℝ 1 f) (r : ℝ) :
    Measure.hausdorffMeasure (Module.finrank ℝ E : ℝ) (f '' closedBall 0 r) < ⊤ := by
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : E) r).exists_bound_of_continuousOn
    (hf.continuous_fderiv le_rfl).continuousOn
  have hl : LipschitzOnWith ⟨max C 0, le_max_right _ _⟩ f (closedBall 0 r) :=
    Convex.lipschitzOnWith_of_nnnorm_fderiv_le (fun x _ => hf.differentiable le_rfl x)
      (fun x hx => by exact (hC x hx).trans (le_max_left _ _)) (convex_closedBall _ _)
  exact lt_of_le_of_lt (hl.hausdorffMeasure_image_le (by positivity))
    (ENNReal.mul_lt_top (by simp) (isCompact_closedBall (0 : E) r).measure_lt_top)
/-- Stereographic coordinates of the opposite closed hemisphere lie in the radius-two ball. -/
theorem stereoToFun_norm_le_two {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {v x : E} (hx : ‖x‖ = 1)
    (h : inner (𝕜 := ℝ) v x ≤ 0) : ‖stereoToFun v x‖ ≤ 2 := by
  simp only [stereoToFun_apply, norm_smul, Real.norm_eq_abs, innerSL_apply]
  rw [
    abs_of_nonneg (div_nonneg (by norm_num) (by linarith))]
  have hp : ‖(ℝ ∙ v)ᗮ.orthogonalProjection x‖ ≤ 1 := by
    calc
      _ ≤ ‖(ℝ ∙ v)ᗮ.orthogonalProjection‖ * ‖x‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ 1 := by rw [hx, mul_one]; exact Submodule.orthogonalProjection_norm_le _
  have hc : 2 / (1 - inner (𝕜 := ℝ) v x) ≤ 2 := (div_le_iff₀ (by linarith)).2 (by linarith)
  calc
    _ ≤ (2 / (1 - inner (𝕜 := ℝ) v x)) * 1 := mul_le_mul_of_nonneg_left hp (div_nonneg (by norm_num) (by linarith))
    _ ≤ 2 := by simpa using hc
/-- Each closed hemisphere is a smooth image of a bounded tangent ball. -/
theorem hausdorffMeasure_hemisphere_lt_top {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] {v : E} (hv : ‖v‖ = 1) :
    Measure.hausdorffMeasure (Module.finrank ℝ (ℝ ∙ v)ᗮ : ℝ)
      (sphere (0 : E) 1 ∩ {x | inner (𝕜 := ℝ) v x ≤ 0}) < ⊤ := by
  letI : MeasurableSpace (ℝ ∙ v)ᗮ := borel _
  letI : BorelSpace (ℝ ∙ v)ᗮ := ⟨rfl⟩
  let f : (ℝ ∙ v)ᗮ → E := stereoInvFunAux v ∘ Subtype.val
  have hf : ContDiff ℝ 1 f := (contDiff_stereoInvFunAux (v := v)).comp
    (ℝ ∙ v)ᗮ.subtypeL.contDiff
  apply lt_of_le_of_lt (measure_mono (t := f '' Metric.closedBall 0 2) ?_)
    (hausdorffMeasure_contDiff_image_closedBall_lt_top hf 2)
  rintro x ⟨hx, hinner⟩
  have hxn : ‖x‖ = 1 := by simpa using hx
  refine ⟨stereoToFun v x, ?_, ?_⟩
  · simpa using stereoToFun_norm_le_two hxn hinner
  · have hne : x ≠ v := by
      intro heq
      subst x
      have hh : inner (𝕜 := ℝ) v v = 1 := by rw [real_inner_self_eq_norm_sq, hv]; norm_num
      change inner (𝕜 := ℝ) v v ≤ 0 at hinner
      rw [hh] at hinner
      norm_num at hinner
    exact congrArg Subtype.val (stereo_left_inv hv (x := ⟨x, hx⟩) hne)
/-- Two bounded stereographic charts give finite codimension-one measure of the unit sphere. -/
theorem hausdorffMeasure_unit_sphere_lt_top {d : ℕ} (hd : 1 ≤ d) :
    Measure.hausdorffMeasure ((d - 1 : ℕ) : ℝ) (sphere (0 : Euclidean d) 1) < ⊤ := by
  haveI : Nontrivial (Euclidean d) := Module.nontrivial_of_finrank_pos (R := ℝ)
    (by simpa only [finrank_euclideanSpace_fin] using hd)
  obtain ⟨v, hv⟩ := exists_norm_eq (Euclidean d) (show (0 : ℝ) ≤ 1 by norm_num)
  have hdim (w : Euclidean d) (hw : ‖w‖ = 1) :
      Module.finrank ℝ (ℝ ∙ w)ᗮ = d - 1 := by
    have hwne : w ≠ 0 := by intro h; simp [h] at hw
    have h := (ℝ ∙ w).finrank_add_finrank_orthogonal
    rw [finrank_span_singleton hwne, finrank_euclideanSpace_fin] at h
    omega
  have hpos := hausdorffMeasure_hemisphere_lt_top hv
  have hvneg : ‖-v‖ = 1 := by simpa using hv
  have hneg := hausdorffMeasure_hemisphere_lt_top hvneg
  rw [hdim v hv] at hpos
  rw [hdim (-v) hvneg] at hneg
  have hcover : sphere (0 : Euclidean d) 1 ⊆
      (sphere 0 1 ∩ {x | inner (𝕜 := ℝ) v x ≤ 0}) ∪
      (sphere 0 1 ∩ {x | inner (𝕜 := ℝ) (-v) x ≤ 0}) := by
    intro x hx
    rcases le_total (inner (𝕜 := ℝ) v x) 0 with h | h
    · exact Or.inl ⟨hx, h⟩
    · exact Or.inr ⟨hx, by simpa using neg_nonpos.mpr h⟩
  exact lt_of_le_of_lt (measure_mono hcover) ((measure_union_le _ _).trans_lt
    (ENNReal.add_lt_top.mpr ⟨hpos, hneg⟩))
/-- Every Euclidean sphere of positive radius has finite codimension-one Hausdorff measure. -/
theorem hausdorffMeasure_sphere_lt_top {d : ℕ} (hd : 1 ≤ d)
    (a : Euclidean d) {r : ℝ} (hr : 0 < r) :
    Measure.hausdorffMeasure ((d - 1 : ℕ) : ℝ) (sphere a r) < ⊤ := by
  let f : Euclidean d → Euclidean d := fun x => a + r • x
  have hf : LipschitzWith ‖r‖₊ f := by
    intro x y
    simpa [f, edist_add_left] using (lipschitzWith_smul r :
      LipschitzWith ‖r‖₊ (fun x : Euclidean d => r • x)) x y
  have hs : sphere a r ⊆ f '' sphere 0 1 := by
    intro x hx
    have hxnorm : ‖x - a‖ = r := by simpa [mem_sphere, dist_eq_norm] using hx
    refine ⟨r⁻¹ • (x - a), ?_, ?_⟩
    · simp [mem_sphere, dist_eq_norm, norm_smul, hxnorm, abs_of_pos hr, hr.ne']
    · simp [f, smul_smul, hr.ne']
  exact lt_of_le_of_lt ((measure_mono hs).trans (hf.hausdorffMeasure_image_le
    (by positivity) _)) (ENNReal.mul_lt_top (by simp)
      (hausdorffMeasure_unit_sphere_lt_top hd))
end RieszEuclidean
