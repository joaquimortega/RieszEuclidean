import RieszEuclidean.Affine
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.LinearAlgebra.Matrix.SchurComplement

/-!
# Closed ellipsoids and the John maximality predicate

A full-dimensional ellipsoid is the image of the closed unit ball by an actual
invertible affine map. `IsJohnEllipsoid` asks only for containment and maximal
Lebesgue volume. In particular, neither existence nor uniqueness is part of its
definition.
-/

noncomputable section

open MeasureTheory Metric
open scoped ENNReal

namespace RieszEuclidean.CompleteMinimal

variable {d : ℕ}

/-- The closed, full-dimensional ellipsoid with center `a` and invertible shape `A`. -/
def closedEllipsoid (a : Euclidean d) (A : Euclidean d ≃L[ℝ] Euclidean d) :
    Set (Euclidean d) :=
  (planeAffine a A) '' closedBall (0 : Euclidean d) 1

/-- Full-dimensional closed ellipsoids, with no singular shapes admitted. -/
def IsEllipsoid (E : Set (Euclidean d)) : Prop :=
  ∃ a : Euclidean d, ∃ A : Euclidean d ≃L[ℝ] Euclidean d, E = closedEllipsoid a A

/-- A John ellipsoid is a contained full-dimensional ellipsoid of maximal volume
among every contained full-dimensional ellipsoid. -/
def IsJohnEllipsoid (K E : Set (Euclidean d)) : Prop :=
  IsEllipsoid E ∧ E ⊆ K ∧
    ∀ F : Set (Euclidean d), IsEllipsoid F → F ⊆ K → volume F ≤ volume E

/-- The topological realization of the already defined affine coordinate map. -/
def affineHomeomorph (a : Euclidean d) (A : Euclidean d ≃L[ℝ] Euclidean d) :
    Euclidean d ≃ₜ Euclidean d :=
  A.toHomeomorph.trans (Homeomorph.addLeft a)

@[simp] theorem affineHomeomorph_apply (a x : Euclidean d)
    (A : Euclidean d ≃L[ℝ] Euclidean d) :
    affineHomeomorph a A x = planeAffine a A x := rfl

/-- The absolute determinant multiplying volume under affine image. -/
def volumeFactor (A : Euclidean d ≃L[ℝ] Euclidean d) : ℝ≥0∞ :=
  ENNReal.ofReal |LinearMap.det A.toLinearEquiv.toLinearMap|

theorem volumeFactor_ne_zero (A : Euclidean d ≃L[ℝ] Euclidean d) :
    volumeFactor A ≠ 0 := by
  apply ENNReal.ofReal_ne_zero_iff.mpr
  exact abs_pos.mpr A.toLinearEquiv.isUnit_det'.ne_zero

theorem volumeFactor_ne_top (A : Euclidean d ≃L[ℝ] Euclidean d) :
    volumeFactor A ≠ ∞ := ENNReal.ofReal_ne_top

/-- Affine change of volume, valid for arbitrary sets. -/
theorem volume_affine_image (a : Euclidean d)
    (A : Euclidean d ≃L[ℝ] Euclidean d) (S : Set (Euclidean d)) :
    volume ((planeAffine a A) '' S) = volumeFactor A * volume S := by
  have htrans : (fun x : Euclidean d => a + x) '' (A '' S) =
      (fun x : Euclidean d => -a + x) ⁻¹' (A '' S) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa using hy
    · intro hx
      exact ⟨-a + x, hx, by simp⟩
  change volume (((fun x : Euclidean d => a + x) ∘ A) '' S) = _
  rw [Set.image_comp, htrans, measure_preimage_add,
    volume.addHaar_image_continuousLinearEquiv]
  rfl

@[simp] theorem isEllipsoid_closedEllipsoid (a : Euclidean d)
    (A : Euclidean d ≃L[ℝ] Euclidean d) : IsEllipsoid (closedEllipsoid a A) :=
  ⟨a, A, rfl⟩

theorem closedEllipsoid_isCompact (a : Euclidean d)
    (A : Euclidean d ≃L[ℝ] Euclidean d) : IsCompact (closedEllipsoid a A) :=
  (isCompact_closedBall (0 : Euclidean d) 1).image
    (continuous_const.add A.continuous)

theorem closedEllipsoid_isClosed (a : Euclidean d)
    (A : Euclidean d ≃L[ℝ] Euclidean d) : IsClosed (closedEllipsoid a A) :=
  (closedEllipsoid_isCompact a A).isClosed

theorem closedEllipsoid_measurableSet (a : Euclidean d)
    (A : Euclidean d ≃L[ℝ] Euclidean d) : MeasurableSet (closedEllipsoid a A) :=
  (closedEllipsoid_isClosed a A).measurableSet

theorem closedEllipsoid_convex (a : Euclidean d)
    (A : Euclidean d ≃L[ℝ] Euclidean d) : Convex ℝ (closedEllipsoid a A) := by
  have h := ((convex_closedBall (0 : Euclidean d) 1).linear_image
    A.toLinearEquiv.toLinearMap).translate a
  simpa only [closedEllipsoid, Set.image_image, Function.comp_def] using h

theorem center_mem_closedEllipsoid (a : Euclidean d)
    (A : Euclidean d ≃L[ℝ] Euclidean d) : a ∈ closedEllipsoid a A := by
  exact ⟨0, by simp, by simp [planeAffine]⟩

theorem center_mem_interior_closedEllipsoid (a : Euclidean d)
    (A : Euclidean d ≃L[ℝ] Euclidean d) : a ∈ interior (closedEllipsoid a A) := by
  have h : (0 : Euclidean d) ∈ interior (closedBall (0 : Euclidean d) 1) :=
    ball_subset_interior_closedBall (by simp)
  have him : affineHomeomorph a A '' interior (closedBall (0 : Euclidean d) 1) =
      interior (closedEllipsoid a A) :=
    (affineHomeomorph a A).image_interior _
  rw [← him]
  exact ⟨0, h, by simp [affineHomeomorph, planeAffine]⟩

@[simp] theorem volume_closedEllipsoid (a : Euclidean d)
    (A : Euclidean d ≃L[ℝ] Euclidean d) :
    volume (closedEllipsoid a A) =
      volumeFactor A * volume (closedBall (0 : Euclidean d) 1) :=
  volume_affine_image a A _

theorem volume_closedEllipsoid_pos (a : Euclidean d)
    (A : Euclidean d ≃L[ℝ] Euclidean d) : 0 < volume (closedEllipsoid a A) := by
  rw [volume_closedEllipsoid]
  exact ENNReal.mul_pos (volumeFactor_ne_zero A)
    (measure_closedBall_pos volume (0 : Euclidean d) zero_lt_one).ne'

theorem volume_closedEllipsoid_ne_top (a : Euclidean d)
    (A : Euclidean d ≃L[ℝ] Euclidean d) : volume (closedEllipsoid a A) ≠ ∞ :=
  (closedEllipsoid_isCompact a A).measure_lt_top.ne

theorem IsEllipsoid.isCompact {E : Set (Euclidean d)} (hE : IsEllipsoid E) :
    IsCompact E := by
  obtain ⟨a, A, rfl⟩ := hE
  exact closedEllipsoid_isCompact a A

theorem IsEllipsoid.convex {E : Set (Euclidean d)} (hE : IsEllipsoid E) :
    Convex ℝ E := by
  obtain ⟨a, A, rfl⟩ := hE
  exact closedEllipsoid_convex a A

theorem IsEllipsoid.interior_nonempty {E : Set (Euclidean d)} (hE : IsEllipsoid E) :
    (interior E).Nonempty := by
  obtain ⟨a, A, rfl⟩ := hE
  exact ⟨a, center_mem_interior_closedEllipsoid a A⟩

theorem IsEllipsoid.volume_pos {E : Set (Euclidean d)} (hE : IsEllipsoid E) :
    0 < volume E := by
  obtain ⟨a, A, rfl⟩ := hE
  exact volume_closedEllipsoid_pos a A

theorem IsEllipsoid.volume_ne_top {E : Set (Euclidean d)} (hE : IsEllipsoid E) :
    volume E ≠ ∞ := hE.isCompact.measure_lt_top.ne

/-- Composition of affine maps stays within the same concrete class of ellipsoids. -/
theorem affine_image_closedEllipsoid (b a : Euclidean d)
    (B A : Euclidean d ≃L[ℝ] Euclidean d) :
    (planeAffine b B) '' closedEllipsoid a A =
      closedEllipsoid (b + B a) (A.trans B) := by
  simp only [closedEllipsoid, Set.image_image]
  apply congrArg (fun f : Euclidean d → Euclidean d => f '' closedBall (0 : Euclidean d) 1)
  funext x
  change b + B (a + A x) = (b + B a) + B (A x)
  rw [map_add, add_assoc]

theorem IsEllipsoid.affine_image {E : Set (Euclidean d)} (hE : IsEllipsoid E)
    (a : Euclidean d) (A : Euclidean d ≃L[ℝ] Euclidean d) :
    IsEllipsoid ((planeAffine a A) '' E) := by
  obtain ⟨b, B, rfl⟩ := hE
  exact ⟨a + A b, B.trans A, affine_image_closedEllipsoid a b A B⟩

/-- Interior nonemptiness already ensures the admissible family is nonempty.
This does not assert that the supremal volume is attained. -/
theorem exists_contained_ellipsoid {K : Set (Euclidean d)}
    (hK : (interior K).Nonempty) : ∃ E : Set (Euclidean d), IsEllipsoid E ∧ E ⊆ K := by
  obtain ⟨a, ha⟩ := hK
  obtain ⟨r, hr, hsub⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (mem_interior_iff_mem_nhds.mp ha)
  let A : Euclidean d ≃L[ℝ] Euclidean d :=
    (LinearEquiv.smulOfNeZero ℝ (Euclidean d) r hr.ne').toContinuousLinearEquiv
  refine ⟨closedEllipsoid a A, isEllipsoid_closedEllipsoid a A, ?_⟩
  rintro x ⟨y, hy, rfl⟩
  apply hsub
  change dist (a + r • y) a ≤ r
  rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hr]
  have hy' : ‖y‖ ≤ 1 := by simpa only [mem_closedBall, dist_zero_right] using hy
  simpa using mul_le_mul_of_nonneg_left hy' hr.le

/-- Every ellipsoid is itself a body for which a John ellipsoid exists. -/
theorem IsEllipsoid.isJohnEllipsoid_self {E : Set (Euclidean d)} (hE : IsEllipsoid E) :
    IsJohnEllipsoid E E :=
  ⟨hE, Set.Subset.refl E, fun _ _ hF => measure_mono hF⟩

theorem IsJohnEllipsoid.isEllipsoid {K E : Set (Euclidean d)}
    (h : IsJohnEllipsoid K E) : IsEllipsoid E := h.1

theorem IsJohnEllipsoid.subset {K E : Set (Euclidean d)}
    (h : IsJohnEllipsoid K E) : E ⊆ K := h.2.1

theorem IsJohnEllipsoid.volume_max {K E F : Set (Euclidean d)}
    (h : IsJohnEllipsoid K E) (hF : IsEllipsoid F) (hFK : F ⊆ K) :
    volume F ≤ volume E := h.2.2 F hF hFK

/-- All maximizers have the same volume; equality of their sets is a separate
geometric statement, not a consequence inserted into the definition. -/
theorem IsJohnEllipsoid.volume_eq {K E F : Set (Euclidean d)}
    (hE : IsJohnEllipsoid K E) (hF : IsJohnEllipsoid K F) : volume E = volume F :=
  le_antisymm (hF.volume_max hE.isEllipsoid hE.subset)
    (hE.volume_max hF.isEllipsoid hF.subset)

/-- An equal-volume contained ellipsoid is another maximizer. -/
theorem IsJohnEllipsoid.of_volume_eq {K E F : Set (Euclidean d)}
    (hE : IsJohnEllipsoid K E) (hF : IsEllipsoid F) (hFK : F ⊆ K)
    (hvol : volume F = volume E) : IsJohnEllipsoid K F := by
  refine ⟨hF, hFK, ?_⟩
  intro G hG hGK
  rw [hvol]
  exact hE.volume_max hG hGK

/-- John maximality is preserved by every invertible affine change of coordinates. -/
theorem IsJohnEllipsoid.affine_image {K E : Set (Euclidean d)}
    (hE : IsJohnEllipsoid K E) (a : Euclidean d)
    (A : Euclidean d ≃L[ℝ] Euclidean d) :
    IsJohnEllipsoid ((planeAffine a A) '' K) ((planeAffine a A) '' E) := by
  refine ⟨hE.isEllipsoid.affine_image a A, Set.image_mono hE.subset, ?_⟩
  intro F hF hFK
  let G := (planeAffine (-A.symm a) A.symm) '' F
  have hG : IsEllipsoid G := hF.affine_image _ _
  have hGK : G ⊆ K := by
    rintro x ⟨y, hy, rfl⟩
    obtain ⟨z, hz, rfl⟩ := hFK hy
    simpa only [planeAffine_inverse, MeasurableEquiv.symm_apply_apply] using hz
  have hFG : (planeAffine a A) '' G = F := by
    rw [show G = (planeAffine (-A.symm a) A.symm) '' F from rfl,
      planeAffine_inverse, Set.image_image]
    simp only [Function.comp_def, MeasurableEquiv.apply_symm_apply, Set.image_id']
  rw [← hFG, volume_affine_image a A G, volume_affine_image a A E]
  exact mul_le_mul_left' (hE.volume_max hG hGK) _

/-- The same invariance in both directions. -/
theorem isJohnEllipsoid_affine_image_iff (K E : Set (Euclidean d))
    (a : Euclidean d) (A : Euclidean d ≃L[ℝ] Euclidean d) :
    IsJohnEllipsoid ((planeAffine a A) '' K) ((planeAffine a A) '' E) ↔
      IsJohnEllipsoid K E := by
  constructor
  · intro h
    have h' := h.affine_image (-A.symm a) A.symm
    simpa only [planeAffine_inverse, Set.image_image, Function.comp_def,
      MeasurableEquiv.symm_apply_apply, Set.image_id'] using h'
  · exact fun h => h.affine_image a A

/-- The rank-one determinant formula in the concrete Euclidean space. -/
theorem det_id_add_smulRight (f : Euclidean d →ₗ[ℝ] ℝ) (v : Euclidean d) :
    LinearMap.det (LinearMap.id + f.smulRight v) = 1 + f v := by
  classical
  let b := (EuclideanSpace.basisFun (Fin d) ℝ).toBasis
  rw [← LinearMap.det_toMatrix b]
  have hm : LinearMap.toMatrix b b (LinearMap.id + f.smulRight v) =
      1 + Matrix.replicateCol Unit (fun i => b.repr v i) *
        Matrix.replicateRow Unit (fun i => f (b i)) := by
    rw [map_add, LinearMap.toMatrix_id]
    congr 1
    ext i j
    simp [LinearMap.toMatrix_apply, LinearMap.smulRight_apply,
      Matrix.mul_apply, Matrix.replicateCol, Matrix.replicateRow, mul_comm]
  rw [hm, Matrix.det_one_add_replicateCol_mul_replicateRow]
  congr 1
  rw [← b.sum_repr v]
  simp [dotProduct, map_sum, map_smul, mul_comm]

/-- Two distinct translated unit balls in a convex body admit a strictly larger
inscribed ellipsoid, obtained by a rank-one stretch along the translation. -/
theorem exists_larger_ellipsoid_of_translated_unitBall_subset
    {K : Set (Euclidean d)} (hK : Convex ℝ K)
    (hB : closedBall (0 : Euclidean d) 1 ⊆ K)
    {t : Euclidean d} (ht : t ≠ 0)
    (hBt : (fun x : Euclidean d => t + x) '' closedBall (0 : Euclidean d) 1 ⊆ K) :
    ∃ E : Set (Euclidean d), IsEllipsoid E ∧ E ⊆ K ∧
      volume (closedBall (0 : Euclidean d) 1) < volume E := by
  let e : Euclidean d := ‖t‖⁻¹ • t
  have he : ‖e‖ = 1 := norm_smul_inv_norm (𝕜 := ℝ) ht
  have hnorm : 0 < ‖t‖ := norm_pos_iff.mpr ht
  have heinner : inner (𝕜 := ℝ) e t = ‖t‖ := by
    dsimp only [e]
    rw [real_inner_smul_left, real_inner_self_eq_norm_sq]
    field_simp
    ring
  let f : Euclidean d →L[ℝ] ℝ := innerSL ℝ e
  let L : Euclidean d →L[ℝ] Euclidean d :=
    ContinuousLinearMap.id ℝ (Euclidean d) + f.smulRight ((1 / 2 : ℝ) • t)
  have hLdet : L.det = 1 + ‖t‖ / 2 := by
    change LinearMap.det (LinearMap.id + f.toLinearMap.smulRight ((1 / 2 : ℝ) • t)) = _
    rw [det_id_add_smulRight]
    change 1 + inner (𝕜 := ℝ) e ((1 / 2 : ℝ) • t) = _
    rw [real_inner_smul_right, heinner]
    ring
  have hdetpos : 0 < L.det := by rw [hLdet]; positivity
  let A : Euclidean d ≃L[ℝ] Euclidean d :=
    (L.toLinearMap.equivOfDetNeZero hdetpos.ne').toContinuousLinearEquiv
  have hA : A.toContinuousLinearMap = L := by ext x; rfl
  have hfac : 1 < volumeFactor A := by
    change 1 < ENNReal.ofReal |A.toContinuousLinearMap.det|
    rw [hA, abs_of_pos hdetpos, ← ENNReal.ofReal_one]
    apply (ENNReal.ofReal_lt_ofReal_iff hdetpos).mpr
    rw [hLdet]
    linarith
  refine ⟨closedEllipsoid ((1 / 2 : ℝ) • t) A,
    isEllipsoid_closedEllipsoid _ _, ?_, ?_⟩
  · rintro z ⟨x, hx, rfl⟩
    have hxnorm : ‖x‖ ≤ 1 := by simpa only [mem_closedBall, dist_zero_right] using hx
    have habs : |inner (𝕜 := ℝ) e x| ≤ 1 :=
      (abs_real_inner_le_norm e x).trans (by simpa [he] using hxnorm)
    have hcoef : (1 + inner (𝕜 := ℝ) e x) / 2 ∈ Set.Icc (0 : ℝ) 1 := by
      rcases abs_le.mp habs with ⟨hlo, hhi⟩
      constructor <;> linarith
    have htx : x + t ∈ K := by
      rw [add_comm]
      exact hBt ⟨x, hx, rfl⟩
    have hconv := hK.add_smul_mem (hB hx) htx hcoef
    have hAx : A x = x + inner (𝕜 := ℝ) e x • ((1 / 2 : ℝ) • t) := by
      change A.toContinuousLinearMap x = _
      rw [hA]
      rfl
    change (1 / 2 : ℝ) • t + A x ∈ K
    rw [hAx]
    convert hconv using 1
    rw [smul_smul]
    have hscalar : (1 + inner (𝕜 := ℝ) e x) / 2 =
        (1 / 2 : ℝ) + inner (𝕜 := ℝ) e x * (1 / 2 : ℝ) := by ring
    rw [hscalar, add_smul]
    abel
  · rw [volume_closedEllipsoid]
    have hvolpos := (measure_closedBall_pos volume (0 : Euclidean d) zero_lt_one).ne'
    have hvolfin : volume (closedBall (0 : Euclidean d) 1) ≠ ∞ :=
      measure_closedBall_lt_top.ne
    simpa only [one_mul] using (ENNReal.mul_lt_mul_right hvolpos hvolfin).mpr hfac

/-- In John-normalized coordinates, no nonzero translate of the closed unit ball
is contained in the convex body. The proof uses maximality, not a uniqueness assumption. -/
theorem IsJohnEllipsoid.eq_zero_of_translated_unitBall_subset
    {K : Set (Euclidean d)} (hJ : IsJohnEllipsoid K (closedBall (0 : Euclidean d) 1))
    (hK : Convex ℝ K) {t : Euclidean d}
    (hBt : (fun x : Euclidean d => t + x) '' closedBall (0 : Euclidean d) 1 ⊆ K) : t = 0 := by
  by_contra ht
  obtain ⟨E, hE, hEK, hvol⟩ :=
    exists_larger_ellipsoid_of_translated_unitBall_subset hK hJ.subset ht hBt
  exact (not_lt_of_ge (hJ.volume_max hE hEK)) hvol

@[simp] theorem closedEllipsoid_zero_refl :
    closedEllipsoid (0 : Euclidean d) (ContinuousLinearEquiv.refl ℝ (Euclidean d)) =
      closedBall (0 : Euclidean d) 1 := by
  ext x
  simp [closedEllipsoid, planeAffine]

/-- An affine image of a convex body is convex. -/
theorem convex_affine_image {K : Set (Euclidean d)} (hK : Convex ℝ K)
    (a : Euclidean d) (A : Euclidean d ≃L[ℝ] Euclidean d) :
    Convex ℝ ((planeAffine a A) '' K) := by
  simpa only [Set.image_image, Function.comp_def] using
    (hK.linear_image A.toLinearEquiv.toLinearMap).translate a

/-- Taking the inverse affine coordinates sends a given John ellipsoid to the unit ball. -/
theorem IsJohnEllipsoid.normalize {K : Set (Euclidean d)}
    {a : Euclidean d} {A : Euclidean d ≃L[ℝ] Euclidean d}
    (hJ : IsJohnEllipsoid K (closedEllipsoid a A)) :
    IsJohnEllipsoid ((planeAffine (-A.symm a) A.symm) '' K)
      (closedBall (0 : Euclidean d) 1) := by
  have h := hJ.affine_image (-A.symm a) A.symm
  have he : (planeAffine (-A.symm a) A.symm) '' closedEllipsoid a A =
      closedBall (0 : Euclidean d) 1 := by
    rw [closedEllipsoid, planeAffine_inverse, Set.image_image]
    simp only [Function.comp_def, MeasurableEquiv.symm_apply_apply, Set.image_id']
  rw [he] at h
  exact h

/-- For any John ellipsoid of a convex body, a contained translate has zero shift. -/
theorem IsJohnEllipsoid.eq_zero_of_translated_subset
    {K E : Set (Euclidean d)} (hJ : IsJohnEllipsoid K E) (hK : Convex ℝ K)
    {t : Euclidean d} (hEt : (fun x : Euclidean d => t + x) '' E ⊆ K) : t = 0 := by
  obtain ⟨a, A, rfl⟩ := hJ.isEllipsoid
  have hnorm := hJ.normalize
  have hconv := convex_affine_image hK (-A.symm a) A.symm
  have htrans : (fun x : Euclidean d => A.symm t + x) ''
      closedBall (0 : Euclidean d) 1 ⊆ (planeAffine (-A.symm a) A.symm) '' K := by
    rintro z ⟨x, hx, rfl⟩
    refine ⟨t + (a + A x), hEt ⟨a + A x, ⟨x, hx, rfl⟩, rfl⟩, ?_⟩
    change -A.symm a + A.symm (t + (a + A x)) = A.symm t + x
    simp only [map_add, ContinuousLinearEquiv.symm_apply_apply]
    abel
  have ht : A.symm t = 0 := hnorm.eq_zero_of_translated_unitBall_subset hconv htrans
  exact A.symm.injective (by simpa using ht)

/-- The closed parameter family allows singular shapes during compact optimization. -/
def admissibleParameters (K : Set (Euclidean d)) :
    Set (Euclidean d × (Euclidean d →L[ℝ] Euclidean d)) :=
  {p | ∀ x : closedBall (0 : Euclidean d) 1, p.1 + p.2 x ∈ K}

theorem admissibleParameters_isClosed {K : Set (Euclidean d)} (hK : IsClosed K) :
    IsClosed (admissibleParameters K) := by
  have heq : admissibleParameters K =
      ⋂ x : closedBall (0 : Euclidean d) 1,
        (fun p : Euclidean d × (Euclidean d →L[ℝ] Euclidean d) => p.1 + p.2 x) ⁻¹' K := by
    ext p
    simp only [admissibleParameters, Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage]
  rw [heq]
  exact isClosed_iInter fun x => hK.preimage
    (continuous_fst.add (continuous_snd.clm_apply continuous_const))

theorem admissibleParameters_isBounded {K : Set (Euclidean d)}
    (hK : Bornology.IsBounded K) : Bornology.IsBounded (admissibleParameters K) := by
  obtain ⟨R, hR, hKR⟩ := hK.exists_pos_norm_le
  apply isBounded_iff_forall_norm_le.mpr
  refine ⟨2 * R, ?_⟩
  intro p hp
  have ha : ‖p.1‖ ≤ R := by
    have hzero := hp ⟨0, by simp⟩
    simp only [ContinuousLinearMap.map_zero, add_zero] at hzero
    exact hKR _ hzero
  apply norm_prod_le_iff.mpr
  refine ⟨by linarith, ?_⟩
  apply ContinuousLinearMap.opNorm_le_of_unit_norm (by positivity)
  intro x hx
  have hax : ‖p.1 + p.2 x‖ ≤ R := hKR _ (hp ⟨x, by simp [mem_closedBall, hx]⟩)
  calc
    ‖p.2 x‖ = ‖(p.1 + p.2 x) - p.1‖ := by rw [add_sub_cancel_left]
    _ ≤ ‖p.1 + p.2 x‖ + ‖p.1‖ := norm_sub_le _ _
    _ ≤ 2 * R := by linarith

/-- Including singular shapes makes the feasible parameter family closed and compact. -/
theorem admissibleParameters_isCompact {K : Set (Euclidean d)} (hK : IsCompact K) :
    IsCompact (admissibleParameters K) :=
  isCompact_iff_isClosed_bounded.mpr
    ⟨admissibleParameters_isClosed hK.isClosed, admissibleParameters_isBounded hK.isBounded⟩

/-- A compact set with nonempty interior has a maximal-volume inscribed
full-dimensional ellipsoid. Convexity is not needed for existence. -/
theorem exists_isJohnEllipsoid {K : Set (Euclidean d)} (hK : IsCompact K)
    (hKi : (interior K).Nonempty) : ∃ E : Set (Euclidean d), IsJohnEllipsoid K E := by
  obtain ⟨E₀, ⟨a₀, A₀, rfl⟩, hE₀K⟩ := exists_contained_ellipsoid hKi
  have h₀ : (a₀, A₀.toContinuousLinearMap) ∈ admissibleParameters K := by
    intro x
    exact hE₀K ⟨x, x.property, rfl⟩
  obtain ⟨p, hp, hmax⟩ := (admissibleParameters_isCompact hK).exists_isMaxOn
    ⟨(a₀, A₀.toContinuousLinearMap), h₀⟩
    ((ContinuousLinearMap.continuous_det.comp continuous_snd).abs.continuousOn)
  have hdetpos : 0 < |p.2.det| :=
    (abs_pos.mpr A₀.toLinearEquiv.isUnit_det'.ne_zero).trans_le (hmax h₀)
  have hdet : LinearMap.det p.2.toLinearMap ≠ 0 := abs_pos.mp hdetpos
  let A := (p.2.toLinearMap.equivOfDetNeZero hdet).toContinuousLinearEquiv
  have hA : A.toContinuousLinearMap = p.2 := by
    ext x
    rfl
  refine ⟨closedEllipsoid p.1 A, isEllipsoid_closedEllipsoid p.1 A, ?_, ?_⟩
  · rintro x ⟨y, hy, rfl⟩
    change p.1 + A y ∈ K
    have he : A y = p.2 y := congrArg (fun f : Euclidean d →L[ℝ] Euclidean d => f y) hA
    rw [he]
    exact hp ⟨y, hy⟩
  · intro F hF hFK
    obtain ⟨b, B, rfl⟩ := hF
    have hB : (b, B.toContinuousLinearMap) ∈ admissibleParameters K := by
      intro x
      exact hFK ⟨x, x.property, rfl⟩
    rw [volume_closedEllipsoid, volume_closedEllipsoid]
    apply mul_le_mul_right'
    apply ENNReal.ofReal_le_ofReal
    change |B.toContinuousLinearMap.det| ≤ |A.toContinuousLinearMap.det|
    rw [hA]
    exact hmax hB

end RieszEuclidean.CompleteMinimal
