import RieszEuclidean.L2Transport
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Tactic.Abel
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! Invertible affine changes of domain and the transpose change of frequencies. -/

noncomputable section
open MeasureTheory MeasureTheory.Measure Filter Topology
open scoped ENNReal

namespace RieszEuclidean

variable {d : ℕ}

/-- An invertible affine coordinate map in the current Euclidean dimension. -/
def planeAffine (a : (Euclidean d)) (A : (Euclidean d) ≃L[ℝ] (Euclidean d)) : (Euclidean d) ≃ᵐ (Euclidean d) where
  toFun x := a + A x
  invFun x := A.symm (x - a)
  left_inv x := by simp
  right_inv x := by simp
  measurable_toFun := measurable_const.add A.continuous.measurable
  measurable_invFun := A.symm.continuous.measurable.comp (measurable_id.sub measurable_const)

/-- The inverse absolute determinant, which is the Jacobian for pushforward. -/
def affineJacobian (A : (Euclidean d) ≃L[ℝ] (Euclidean d)) : ℝ≥0∞ :=
  ENNReal.ofReal |(LinearMap.det A.toLinearEquiv.toLinearMap)⁻¹|

theorem affineJacobian_ne_zero (A : (Euclidean d) ≃L[ℝ] (Euclidean d)) : affineJacobian A ≠ 0 := by
  apply ENNReal.ofReal_ne_zero_iff.mpr
  exact abs_pos.mpr (inv_ne_zero (A.toLinearEquiv.isUnit_det'.ne_zero))

theorem affineJacobian_ne_top (A : (Euclidean d) ≃L[ℝ] (Euclidean d)) : affineJacobian A ≠ ∞ :=
  ENNReal.ofReal_ne_top

/-- The full change-of-variables formula, including translation and arbitrary determinant. -/
theorem planeAffine_map (a : (Euclidean d)) (A : (Euclidean d) ≃L[ℝ] (Euclidean d)) (D : Set (Euclidean d)) :
    Measure.map (planeAffine a A) (volume.restrict D) =
      affineJacobian A • volume.restrict ((planeAffine a A) '' D) := by
  have hm : Measure.map (planeAffine a A) volume =
      affineJacobian A • (volume : Measure (Euclidean d)) := by
    change Measure.map ((fun x : (Euclidean d) => a + x) ∘ A) volume = _
    have hma : Measurable (fun x : (Euclidean d) => a + x) := measurable_const.add measurable_id
    rw [← Measure.map_map hma A.continuous.measurable]
    have hA : Measure.map A (volume : Measure (Euclidean d)) = affineJacobian A • volume :=
      map_linearMap_addHaar_eq_smul_addHaar volume A.toLinearEquiv.isUnit_det'.ne_zero
    rw [hA, Measure.map_smul, map_add_left_eq_self]
  have hpre : (planeAffine a A) ⁻¹' ((planeAffine a A) '' D) = D :=
    Set.preimage_image_eq D (planeAffine a A).injective
  calc
    _ = Measure.map (planeAffine a A)
        (volume.restrict ((planeAffine a A) ⁻¹' ((planeAffine a A) '' D))) := by rw [hpre]
    _ = _ := by rw [← (planeAffine a A).restrict_map, hm, Measure.restrict_smul]

/-- The transpose (real adjoint) is the frequency map for affine pullback. -/
def affineFrequency (A : (Euclidean d) ≃L[ℝ] (Euclidean d)) : (Euclidean d) →L[ℝ] (Euclidean d) :=
  ContinuousLinearMap.adjoint A.toContinuousLinearMap

theorem affineFrequency_inner (A : (Euclidean d) ≃L[ℝ] (Euclidean d)) (ξ x : (Euclidean d)) :
    inner (𝕜 := ℝ) (affineFrequency A ξ) x = inner (𝕜 := ℝ) ξ (A x) :=
  ContinuousLinearMap.adjoint_inner_left A.toContinuousLinearMap x ξ

theorem affineFrequency_injective (A : (Euclidean d) ≃L[ℝ] (Euclidean d)) :
    Function.Injective (affineFrequency A) := by
  intro ξ η h
  apply ext_inner_right ℝ
  intro x
  obtain ⟨y, rfl⟩ := A.surjective x
  rw [← affineFrequency_inner, ← affineFrequency_inner, h]

theorem exponential_planeAffine (a ξ x : (Euclidean d)) (A : (Euclidean d) ≃L[ℝ] (Euclidean d)) :
    exponential ξ (planeAffine a A x) = exponential ξ a * exponential (affineFrequency A ξ) x := by
  unfold exponential
  change Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (inner (𝕜 := ℝ) ξ (a + A x) : ℂ)) = _
  rw [inner_add_right, Complex.ofReal_add, mul_add, Complex.exp_add, affineFrequency_inner]

theorem exponential_norm (ξ x : Euclidean d) : ‖exponential ξ x‖ = 1 := by
  simp [exponential, Complex.norm_exp, Complex.mul_re]

/--  BAFFINE-01: Pullback by an invertible affine map preserves actual exponential Riesz bases,
with the precise transpose image of the frequency set. -/
theorem hasExponentialRieszBasis_affine_pullback (a : (Euclidean d)) (A : (Euclidean d) ≃L[ℝ] (Euclidean d))
    (D Λ : Set (Euclidean d)) (hΛ : HasExponentialRieszBasis ((planeAffine a A) '' D) Λ) :
    HasExponentialRieszBasis D ((affineFrequency A) '' Λ) := by
  classical
  obtain ⟨S, hS⟩ := hΛ
  let e := Equiv.Set.image (affineFrequency A) Λ (affineFrequency_injective A)
  let w : Λ → ℂ := fun ξ => (exponential ξ.val a)⁻¹
  have hw : ∀ ξ, ‖w ξ‖ = 1 := by intro ξ; simp [w, exponential_norm]
  let U := weightedReindex e w hw
  let B := scaledL2Equiv (planeAffine a A) (planeAffine_map a A D)
    (affineJacobian_ne_zero A) (affineJacobian_ne_top A)
  have hq : QuasiMeasurePreserving (planeAffine a A)
      (volume.restrict D) (volume.restrict ((planeAffine a A) '' D)) :=
    ⟨(planeAffine a A).measurable, by rw [planeAffine_map]; exact smul_absolutelyContinuous⟩
  refine ⟨U.toContinuousLinearEquiv.trans (S.trans B), ?_⟩
  intro η
  obtain ⟨ξ, rfl⟩ := e.surjective η
  change (B (S (weightedReindex e w hw (lp.single 2 (e ξ) 1))) : (Euclidean d) → ℂ) =ᵐ[_] _
  rw [weightedReindex_single, map_smul]
  filter_upwards [scaledL2Equiv_ae (planeAffine a A) (planeAffine_map a A D)
      (affineJacobian_ne_zero A) (affineJacobian_ne_top A) (w ξ • S (lp.single 2 ξ 1)),
    hq.ae (Lp.coeFn_smul (w ξ) (S (lp.single 2 ξ 1))), hq.ae (hS ξ)] with x hx hy hz
  change _ = exponential (affineFrequency A ξ.val) x
  rw [hx]
  change (w ξ • S (lp.single 2 ξ 1)) (planeAffine a A x) = _
  rw [hy]
  change w ξ * S (lp.single 2 ξ 1) (planeAffine a A x) = _
  rw [hz]
  change (exponential ξ.val a)⁻¹ * exponential ξ.val (planeAffine a A x) = _
  rw [exponential_planeAffine, ← mul_assoc, inv_mul_cancel₀, one_mul]
  exact Complex.exp_ne_zero _

/-- The affine inverse is again an affine map. -/
theorem planeAffine_inverse (a : (Euclidean d)) (A : (Euclidean d) ≃L[ℝ] (Euclidean d)) :
    planeAffine (-A.symm a) A.symm = (planeAffine a A).symm := by
  apply MeasurableEquiv.ext
  funext x
  change -A.symm a + A.symm x = A.symm (x - a)
  rw [map_sub]
  abel

/-- Existence of an exponential Riesz basis is invariant under every invertible
real affine coordinate change. -/
theorem exists_exponentialRieszBasis_affine_iff (a : (Euclidean d)) (A : (Euclidean d) ≃L[ℝ] (Euclidean d))
    (D : Set (Euclidean d)) :
    (∃ Λ, HasExponentialRieszBasis ((planeAffine a A) '' D) Λ) ↔
      ∃ Λ, HasExponentialRieszBasis D Λ := by
  constructor
  · rintro ⟨Λ, hΛ⟩
    exact ⟨_, hasExponentialRieszBasis_affine_pullback a A D Λ hΛ⟩
  · rintro ⟨Λ, hΛ⟩
    have hD : (planeAffine (-A.symm a) A.symm) '' ((planeAffine a A) '' D) = D := by
      rw [planeAffine_inverse, Set.image_image]
      simp only [Function.comp_def, MeasurableEquiv.symm_apply_apply, Set.image_id']
    have h := hasExponentialRieszBasis_affine_pullback (-A.symm a) A.symm
      ((planeAffine a A) '' D) Λ (hD.symm ▸ hΛ)
    exact ⟨_, h⟩

end RieszEuclidean
