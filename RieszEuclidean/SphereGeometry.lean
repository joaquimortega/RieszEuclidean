import RieszEuclidean.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Hausdorff

noncomputable section
open MeasureTheory Metric
namespace RieszEuclidean

/-- The literal Euclidean sphere has zero Lebesgue measure at every nonzero radius. -/
theorem volume_sphere_eq_zero {d : ℕ} (a : Euclidean d) {r : ℝ} (hr : r ≠ 0) :
    volume (sphere a r) = 0 :=
  Measure.addHaar_sphere_of_ne_zero volume a hr

/-- Two equal-radius translated spheres meet in their bisecting hyperplane. -/
theorem sphere_inter_translate_subset_hyperplane {d : ℕ} (a θ : Euclidean d) (r : ℝ) :
    sphere a r ∩ translate θ (sphere a r) ⊆
      {x | 2 * inner (𝕜 := ℝ) (x - a) θ = -‖θ‖ ^ 2} := by
  intro x hx
  have h₁ : ‖x - a‖ = r := by simpa only [mem_sphere, dist_eq_norm] using hx.1
  have h₂ : ‖x - a + θ‖ = r := by
    simpa only [mem_translate, mem_sphere, dist_eq_norm, sub_add_eq_add_sub] using hx.2
  have hi := norm_add_sq_real (x - a) θ
  rw [h₁, h₂] at hi
  change 2 * inner (𝕜 := ℝ) (x - a) θ = -‖θ‖ ^ 2
  nlinarith

/-- A sphere inside a positive-dimensional linear subspace is null for the
Hausdorff measure whose exponent is that subspace's dimension, even after translation. -/
theorem hausdorffMeasure_translated_subspace_sphere {d : ℕ}
    (V : Submodule ℝ (Euclidean d)) [Nontrivial V] (a : Euclidean d) (r : ℝ) :
    Measure.hausdorffMeasure (Module.finrank ℝ V : ℝ)
      ((fun v : V => a + (v : Euclidean d)) '' sphere (0 : V) r) = 0 := by
  letI : MeasurableSpace V := borel V
  letI : BorelSpace V := ⟨rfl⟩
  have hi : Isometry (fun v : V => a + (v : Euclidean d)) := by
    intro v w
    simp only [edist_add_left]
    rfl
  rw [hi.hausdorffMeasure_image (Or.inl (by positivity))]
  exact Measure.addHaar_sphere _ _ _

/-- The translated intersection is a sphere in the orthogonal bisector subspace. -/
theorem sphere_inter_translate_subset_subspace_sphere {d : ℕ}
    (a θ : Euclidean d) (r : ℝ) :
    sphere a r ∩ translate θ (sphere a r) ⊆
      (fun v : (ℝ ∙ θ)ᗮ => (a - (1 / 2 : ℝ) • θ) + (v : Euclidean d)) ''
        sphere 0 (Real.sqrt (r ^ 2 - ‖θ‖ ^ 2 / 4)) := by
  intro x hx
  have hp := sphere_inter_translate_subset_hyperplane a θ r hx
  change 2 * inner (𝕜 := ℝ) (x - a) θ = -‖θ‖ ^ 2 at hp
  have hv : x - a + (1 / 2 : ℝ) • θ ∈ (ℝ ∙ θ)ᗮ := by
    rw [Submodule.mem_orthogonal_singleton_iff_inner_left]
    simp only [inner_add_left, inner_smul_left, RCLike.conj_to_real, real_inner_self_eq_norm_sq]
    linarith
  refine ⟨⟨x - a + (1 / 2 : ℝ) • θ, hv⟩, ?_, ?_⟩
  · have h₁ : ‖x - a‖ = r := by simpa only [mem_sphere, dist_eq_norm] using hx.1
    have hs := norm_add_sq_real (x - a) ((1 / 2 : ℝ) • θ)
    simp only [inner_smul_right, norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num :
      (0 : ℝ) < 1 / 2), h₁] at hs
    have hsq : ‖x - a + (1 / 2 : ℝ) • θ‖ ^ 2 = r ^ 2 - ‖θ‖ ^ 2 / 4 := by
      nlinarith
    simp only [mem_sphere, dist_zero_right, Submodule.norm_coe]
    rw [← hsq, Real.sqrt_sq (norm_nonneg _)]
    rfl
  · dsimp
    module

/-- Nontrivial translates of a sphere have null intersection for the literal
codimension-one Hausdorff measure in dimensions at least two. -/
theorem hausdorffMeasure_sphere_inter_translate {d : ℕ} (hd : 2 ≤ d)
    (a θ : Euclidean d) (hθ : θ ≠ 0) (r : ℝ) :
    Measure.hausdorffMeasure ((d - 1 : ℕ) : ℝ)
      (sphere a r ∩ translate θ (sphere a r)) = 0 := by
  let V := (ℝ ∙ θ)ᗮ
  have hdim : Module.finrank ℝ V = d - 1 := by
    have h := (ℝ ∙ θ).finrank_add_finrank_orthogonal
    rw [finrank_span_singleton hθ] at h
    have he : Module.finrank ℝ (Euclidean d) = d := finrank_euclideanSpace_fin
    rw [he] at h
    change Module.finrank ℝ (ℝ ∙ θ)ᗮ = d - 1
    omega
  haveI : Nontrivial V := Module.nontrivial_of_finrank_pos (R := ℝ) (by omega)
  apply measure_mono_null (sphere_inter_translate_subset_subspace_sphere a θ r)
  rw [← hdim]
  exact hausdorffMeasure_translated_subspace_sphere V _ _

/-- Restricting the literal surface Hausdorff measure to the sphere preserves the
null translated-intersection conclusion used in the boundary Fubini argument. -/
theorem sphere_surfaceMeasure_inter_translate {d : ℕ} (hd : 2 ≤ d)
    (a θ : Euclidean d) (hθ : θ ≠ 0) (r : ℝ) :
    ((Measure.hausdorffMeasure ((d - 1 : ℕ) : ℝ)).restrict (sphere a r))
      (sphere a r ∩ translate θ (sphere a r)) = 0 := by
  apply le_antisymm _ (zero_le _)
  calc
    _ ≤ Measure.hausdorffMeasure ((d - 1 : ℕ) : ℝ)
        (sphere a r ∩ translate θ (sphere a r)) := Measure.restrict_apply_le _ _
    _ = 0 := hausdorffMeasure_sphere_inter_translate hd a θ hθ r

/-- Orthogonal projection of the sphere contains the tangent subspace's open ball. -/
theorem ball_subset_projection_sphere {d : ℕ} (e : Euclidean d) (he : ‖e‖ = 1)
    {r : ℝ} (hr : 0 < r) :
    ball (0 : (ℝ ∙ e)ᗮ) r ⊆
      (ℝ ∙ e)ᗮ.orthogonalProjection '' sphere (0 : Euclidean d) r := by
  intro v hv
  have hvnorm : ‖(v : Euclidean d)‖ < r := by simpa only [Metric.mem_ball, dist_zero_right] using hv
  have hi : inner (𝕜 := ℝ) (v : Euclidean d) e = 0 :=
    Submodule.mem_orthogonal_singleton_iff_inner_left.mp v.property
  refine ⟨(v : Euclidean d) + Real.sqrt (r ^ 2 - ‖(v : Euclidean d)‖ ^ 2) • e, ?_, ?_⟩
  · have hnonneg : 0 ≤ r ^ 2 - ‖(v : Euclidean d)‖ ^ 2 := by
      nlinarith [norm_nonneg (v : Euclidean d)]
    have hs := norm_add_sq_real (v : Euclidean d)
      (Real.sqrt (r ^ 2 - ‖(v : Euclidean d)‖ ^ 2) • e)
    simp only [inner_smul_right, hi, mul_zero, add_zero, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), he, mul_one, Real.sq_sqrt hnonneg] at hs
    rw [mem_sphere, dist_zero_right]
    nlinarith [norm_nonneg ((v : Euclidean d) + Real.sqrt (r ^ 2 - ‖(v : Euclidean d)‖ ^ 2) • e)]
  · rw [map_add, map_smul, Submodule.orthogonalProjection_mem_subspace_eq_self,
      Submodule.orthogonalProjection_orthogonalComplement_singleton_eq_zero, smul_zero, add_zero]

/-- A unit normal yields a strictly positive codimension-one sphere measure via
its orthogonal projection onto the tangent ball. -/
theorem hausdorffMeasure_sphere_zero_pos_of_unit {d : ℕ}
    (e : Euclidean d) (he : ‖e‖ = 1) {r : ℝ} (hr : 0 < r) :
    0 < Measure.hausdorffMeasure (Module.finrank ℝ (ℝ ∙ e)ᗮ : ℝ)
      (sphere (0 : Euclidean d) r) := by
  let V := (ℝ ∙ e)ᗮ
  letI : MeasurableSpace V := borel V
  letI : BorelSpace V := ⟨rfl⟩
  have hball : 0 < Measure.hausdorffMeasure (Module.finrank ℝ V : ℝ) (ball (0 : V) r) :=
    Metric.isOpen_ball.measure_pos _ (nonempty_ball.mpr hr)
  have hle := V.orthogonalProjection.lipschitz.hausdorffMeasure_image_le
    (d := (Module.finrank ℝ V : ℝ)) (by positivity) (sphere (0 : Euclidean d) r)
  have hpos := lt_of_lt_of_le hball (measure_mono (ball_subset_projection_sphere e he hr))
  apply pos_iff_ne_zero.mpr
  intro hzero
  rw [hzero, mul_zero] at hle
  exact (not_lt_of_ge hle) hpos

/-- The literal codimension-one Hausdorff measure of every positive-radius Euclidean
sphere is nonzero in positive dimension. -/
theorem hausdorffMeasure_sphere_pos {d : ℕ} (hd : 1 ≤ d)
    (a : Euclidean d) {r : ℝ} (hr : 0 < r) :
    0 < Measure.hausdorffMeasure ((d - 1 : ℕ) : ℝ) (sphere a r) := by
  haveI : Nontrivial (Euclidean d) := Module.nontrivial_of_finrank_pos (R := ℝ)
    (by simpa only [finrank_euclideanSpace_fin] using hd)
  obtain ⟨e, he⟩ := exists_norm_eq (Euclidean d) (show (0 : ℝ) ≤ 1 by norm_num)
  have hene : e ≠ 0 := by intro h; simp [h] at he
  have hdim : Module.finrank ℝ (ℝ ∙ e)ᗮ = d - 1 := by
    have h := (ℝ ∙ e).finrank_add_finrank_orthogonal
    rw [finrank_span_singleton hene, finrank_euclideanSpace_fin] at h
    omega
  have hp := hausdorffMeasure_sphere_zero_pos_of_unit e he hr
  rw [hdim] at hp
  have hi : Isometry (fun x : Euclidean d => a + x) := by
    intro x y
    simp only [edist_add_left]
  have himage : (fun x : Euclidean d => a + x) '' sphere 0 r = sphere a r := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa only [mem_sphere, dist_eq_norm, add_sub_cancel_left, sub_zero] using hy
    · intro hx
      refine ⟨x - a, ?_, by module⟩
      simpa only [mem_sphere, dist_eq_norm, sub_zero] using hx
  rw [← himage, hi.hausdorffMeasure_image (Or.inl (by positivity))]
  exact hp

/-- The sphere-restricted literal surface measure has positive total mass. -/
theorem sphere_surfaceMeasure_univ_pos {d : ℕ} (hd : 1 ≤ d)
    (a : Euclidean d) {r : ℝ} (hr : 0 < r) :
    0 < ((Measure.hausdorffMeasure ((d - 1 : ℕ) : ℝ)).restrict (sphere a r)) Set.univ := by
  rw [Measure.restrict_apply_univ]
  exact hausdorffMeasure_sphere_pos hd a hr

/-- The sphere-restricted surface measure assigns zero mass to each nontrivial
translate of the sphere, in the form used directly by Tonelli. -/
theorem sphere_surfaceMeasure_translate {d : ℕ} (hd : 2 ≤ d)
    (a θ : Euclidean d) (hθ : θ ≠ 0) (r : ℝ) :
    ((Measure.hausdorffMeasure ((d - 1 : ℕ) : ℝ)).restrict (sphere a r))
      (translate θ (sphere a r)) = 0 := by
  have hm : MeasurableSet (translate θ (sphere a r)) :=
    isClosed_sphere.measurableSet.preimage (continuous_id.add continuous_const).measurable
  rw [Measure.restrict_apply hm, Set.inter_comm]
  exact hausdorffMeasure_sphere_inter_translate hd a θ hθ r

end RieszEuclidean
