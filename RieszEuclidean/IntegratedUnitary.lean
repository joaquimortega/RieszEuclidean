import RieszEuclidean.Correlations
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
open MeasureTheory
namespace RieszEuclidean
variable {d : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
/-- An integrable scalar kernel can be integrated against a strongly continuous unitary orbit. -/
theorem integrable_unitary_smul (U : Euclidean d → H ≃ₗᵢ[ℂ] H)
    (hU : ∀ f, Continuous (fun y => U y f)) {a : Euclidean d → ℂ}
    (ha : Integrable a) (f : H) : Integrable (fun y => a y • U y f) := by
  apply (ha.norm.mul_const ‖f‖).mono'
    (ha.aestronglyMeasurable.smul (hU f).aestronglyMeasurable)
  filter_upwards [] with y
  simp [norm_smul]
/-- The integrated unitary action associated with a scalar kernel. -/
noncomputable def integratedUnitary (U : Euclidean d → H ≃ₗᵢ[ℂ] H)
    (a : Euclidean d → ℂ) (f : H) : H := ∫ y, a y • U y f
/-- The integrated action has the expected L¹ bound. -/
theorem norm_integratedUnitary_le (U : Euclidean d → H ≃ₗᵢ[ℂ] H)
    (a : Euclidean d → ℂ) (f : H) :
    ‖integratedUnitary U a f‖ ≤ (∫ y, ‖a y‖) * ‖f‖ := by
  calc
    ‖integratedUnitary U a f‖ ≤ ∫ y, ‖a y • U y f‖ := norm_integral_le_integral_norm _
    _ = (∫ y, ‖a y‖) * ‖f‖ := by simp [norm_smul, integral_mul_const]
/-- Integration is linear in the Hilbert-space vector. -/
noncomputable def integratedUnitaryLinear (U : Euclidean d → H ≃ₗᵢ[ℂ] H)
    (hU : ∀ f, Continuous (fun y => U y f)) {a : Euclidean d → ℂ}
    (ha : Integrable a) : H →ₗ[ℂ] H where
  toFun := integratedUnitary U a
  map_add' f g := by
    simp only [integratedUnitary, map_add, smul_add]
    exact integral_add (integrable_unitary_smul U hU ha f)
      (integrable_unitary_smul U hU ha g)
  map_smul' c f := by
    simp only [integratedUnitary, map_smul, RingHom.id_apply]
    simp_rw [smul_comm (a _) c]
    exact integral_smul c _
/-- The L¹ norm bounds the continuous integrated operator. -/
noncomputable def integratedUnitaryCLM (U : Euclidean d → H ≃ₗᵢ[ℂ] H)
    (hU : ∀ f, Continuous (fun y => U y f)) {a : Euclidean d → ℂ}
    (ha : Integrable a) : H →L[ℂ] H :=
  (integratedUnitaryLinear U hU ha).mkContinuous (∫ y, ‖a y‖)
    (norm_integratedUnitary_le U a)
/-- The continuous operator evaluates to the orbit integral. -/
theorem integratedUnitaryCLM_apply (U : Euclidean d → H ≃ₗᵢ[ℂ] H)
    (hU : ∀ f, Continuous (fun y => U y f)) {a : Euclidean d → ℂ}
    (ha : Integrable a) (f : H) :
    integratedUnitaryCLM U hU ha f = ∫ y, a y • U y f := rfl
/-- The integrated operator norm is at most the scalar kernel's L¹ norm. -/
theorem norm_integratedUnitaryCLM_le (U : Euclidean d → H ≃ₗᵢ[ℂ] H)
    (hU : ∀ f, Continuous (fun y => U y f)) {a : Euclidean d → ℂ}
    (ha : Integrable a) : ‖integratedUnitaryCLM U hU ha‖ ≤ ∫ y, ‖a y‖ := by
  apply (integratedUnitaryCLM U hU ha).opNorm_le_bound (integral_nonneg (fun _ => norm_nonneg _))
  exact norm_integratedUnitary_le U a
/-- Changing a kernel on a null set does not change its integrated action. -/
theorem integratedUnitary_congr_ae (U : Euclidean d → H ≃ₗᵢ[ℂ] H)
    {a b : Euclidean d → ℂ} (hab : a =ᵐ[volume] b) (f : H) :
    integratedUnitary U a f = integratedUnitary U b f := by
  apply integral_congr_ae
  filter_upwards [hab] with y hy
  rw [hy]
/-- The squared orbit integral is the double integral of its Gram kernel. -/
theorem integratedUnitary_norm_sq [CompleteSpace H]
    (U : Euclidean d → H ≃ₗᵢ[ℂ] H)
    (hU : ∀ f, Continuous (fun y => U y f))
    (hadd : ∀ z y f, U z (U y f) = U (z + y) f)
    {a : Euclidean d → ℂ} (ha : Integrable a) (f : H) :
    (‖integratedUnitary U a f‖ : ℂ) ^ 2 =
      ∫ y, ∫ w, star (a w) * a y * unitaryCorrelation U f (y - w) := by
  have hi := integrable_unitary_smul U hU ha f
  trans inner (𝕜 := ℂ) (integratedUnitary U a f) (integratedUnitary U a f)
  · exact (inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (integratedUnitary U a f)).symm
  change inner (𝕜 := ℂ) (integratedUnitary U a f) (∫ y, a y • U y f) = _
  rw [← integral_inner hi]
  apply integral_congr_ae
  filter_upwards [] with y
  have hl : inner (𝕜 := ℂ) (integratedUnitary U a f) (a y • U y f) =
      ∫ w, inner (𝕜 := ℂ) (a w • U w f) (a y • U y f) := by
    rw [← inner_conj_symm, integratedUnitary, ← integral_inner hi, ← integral_conj]
    apply integral_congr_ae
    filter_upwards [] with w
    exact inner_conj_symm _ _
  rw [hl]
  apply integral_congr_ae
  filter_upwards [] with w
  rw [unitaryCorrelation_sub U hadd]
  simp only [inner_smul_left, inner_smul_right, starRingEnd_apply]
  ring
end RieszEuclidean
