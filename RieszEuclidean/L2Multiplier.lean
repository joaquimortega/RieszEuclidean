import RieszEuclidean.CutoffProjection
open MeasureTheory
noncomputable section
namespace RieszEuclidean
/-- Multiplication by an essentially bounded measurable scalar function on L². -/
def l2Multiplier {α : Type} [MeasurableSpace α] {μ : Measure α}
    (m : α → ℂ) (hm : AEStronglyMeasurable m μ) {C : ℝ}
    (hC : ∀ᵐ x ∂μ, ‖m x‖ ≤ C) (f : Lp ℂ 2 μ) : Lp ℂ 2 μ :=
  ((Lp.memLp f).of_le_mul (hm.mul (Lp.memLp f).aestronglyMeasurable)
    (by filter_upwards [hC] with x hx; simpa only [Pi.mul_apply, norm_mul] using mul_le_mul_of_nonneg_right hx (norm_nonneg (f x)))).toLp _
/-- Representative formula for bounded multiplication. -/
theorem l2Multiplier_coe {α : Type} [MeasurableSpace α] {μ : Measure α}
    (m : α → ℂ) (hm : AEStronglyMeasurable m μ) {C : ℝ}
    (hC : ∀ᵐ x ∂μ, ‖m x‖ ≤ C) (f : Lp ℂ 2 μ) :
    (l2Multiplier m hm hC f : α → ℂ) =ᵐ[μ] fun x => m x * f x :=
  MemLp.coeFn_toLp _
/-- The multiplier norm is controlled by its pointwise bound. -/
theorem l2Multiplier_norm_le {α : Type} [MeasurableSpace α] {μ : Measure α}
    (m : α → ℂ) (hm : AEStronglyMeasurable m μ) {C : ℝ}
    (hC : ∀ᵐ x ∂μ, ‖m x‖ ≤ C) (f : Lp ℂ 2 μ) :
    ‖l2Multiplier m hm hC f‖ ≤ C * ‖f‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [l2Multiplier_coe m hm hC f, hC] with x hx hb
  rw [hx, norm_mul]
  exact mul_le_mul_of_nonneg_right hb (norm_nonneg _)
/-- Bounded multiplication as a complex linear map. -/
def l2MultiplierLM {α : Type} [MeasurableSpace α] {μ : Measure α}
    (m : α → ℂ) (hm : AEStronglyMeasurable m μ) {C : ℝ}
    (hC : ∀ᵐ x ∂μ, ‖m x‖ ≤ C) : Lp ℂ 2 μ →ₗ[ℂ] Lp ℂ 2 μ where
  toFun := l2Multiplier m hm hC
  map_add' f g := by
    apply Lp.ext
    filter_upwards [l2Multiplier_coe m hm hC (f + g), l2Multiplier_coe m hm hC f,
      l2Multiplier_coe m hm hC g, Lp.coeFn_add f g,
      Lp.coeFn_add (l2Multiplier m hm hC f) (l2Multiplier m hm hC g)] with x h1 h2 h3 h4 h5
    simp only [h1, h5, Pi.add_apply, h2, h3, h4, mul_add]
  map_smul' c f := by
    apply Lp.ext
    filter_upwards [l2Multiplier_coe m hm hC (c • f), l2Multiplier_coe m hm hC f,
      Lp.coeFn_smul c f, Lp.coeFn_smul c (l2Multiplier m hm hC f)] with x h1 h2 h3 h4
    simp only [h1, h4, Pi.smul_apply, h2, h3, smul_eq_mul, RingHom.id_apply]
    ring
/-- Bounded multiplication as a continuous linear operator. -/
def l2MultiplierCLM {α : Type} [MeasurableSpace α] {μ : Measure α}
    (m : α → ℂ) (hm : AEStronglyMeasurable m μ) {C : ℝ}
    (hC : ∀ᵐ x ∂μ, ‖m x‖ ≤ C) : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ :=
  (l2MultiplierLM m hm hC).mkContinuous C (l2Multiplier_norm_le m hm hC)
/-- Reciprocal multiplication reverses multiplication by a nonzero function. -/
theorem l2Multiplier_inv_mul {α : Type} [MeasurableSpace α] {μ : Measure α}
    (m : α → ℂ) (hm : AEStronglyMeasurable m μ) {C D : ℝ}
    (hC : ∀ᵐ x ∂μ, ‖m x‖ ≤ C) (hD : ∀ᵐ x ∂μ, ‖(m x)⁻¹‖ ≤ D)
    (hz : ∀ᵐ x ∂μ, m x ≠ 0) (f : Lp ℂ 2 μ) :
    l2Multiplier (fun x => (m x)⁻¹) hm.aemeasurable.inv.aestronglyMeasurable hD (l2Multiplier m hm hC f) = f := by
  apply Lp.ext
  filter_upwards [l2Multiplier_coe (fun x => (m x)⁻¹) hm.aemeasurable.inv.aestronglyMeasurable hD (l2Multiplier m hm hC f),
    l2Multiplier_coe m hm hC f, hz] with x h1 h2 h3
  rw [h1, h2, ← mul_assoc, inv_mul_cancel₀ h3, one_mul]
/-- A bounded multiplier bounded away from zero is a continuous linear equivalence. -/
def l2MultiplierEquiv {α : Type} [MeasurableSpace α] {μ : Measure α}
    (m : α → ℂ) (hm : AEStronglyMeasurable m μ) {C c : ℝ}
    (hC : ∀ᵐ x ∂μ, ‖m x‖ ≤ C) (hc : 0 < c)
    (hl : ∀ᵐ x ∂μ, c ≤ ‖m x‖) : Lp ℂ 2 μ ≃L[ℂ] Lp ℂ 2 μ := by
  have hi : AEStronglyMeasurable (fun x => (m x)⁻¹) μ :=
    hm.aemeasurable.inv.aestronglyMeasurable
  have hz : ∀ᵐ x ∂μ, m x ≠ 0 := hl.mono (fun x hx => norm_pos_iff.mp (hc.trans_le hx))
  have hD : ∀ᵐ x ∂μ, ‖(m x)⁻¹‖ ≤ c⁻¹ := by
    filter_upwards [hl] with x hx
    rw [norm_inv]
    exact inv_anti₀ hc hx
  refine
    { toLinearEquiv :=
        { toLinearMap := l2MultiplierLM m hm hC
          invFun := l2Multiplier (fun x => (m x)⁻¹) hi hD
          left_inv := l2Multiplier_inv_mul m hm hC hD hz
          right_inv := ?_ }
      continuous_toFun := (l2MultiplierCLM m hm hC).continuous
      continuous_invFun := (l2MultiplierCLM (fun x => (m x)⁻¹) hi hD).continuous }
  intro f
  apply Lp.ext
  filter_upwards [l2Multiplier_coe m hm hC (l2Multiplier (fun x => (m x)⁻¹) hi hD f),
    l2Multiplier_coe (fun x => (m x)⁻¹) hi hD f, hz] with x h1 h2 h3
  change (l2Multiplier m hm hC (l2Multiplier (fun x => (m x)⁻¹) hi hD f) : α → ℂ) x = f x
  rw [h1, h2, ← mul_assoc, mul_inv_cancel₀ h3, one_mul]
/-- The multiplier equivalence retains the prescribed pointwise multiplication formula. -/
theorem l2MultiplierEquiv_coe {α : Type} [MeasurableSpace α] {μ : Measure α}
    (m : α → ℂ) (hm : AEStronglyMeasurable m μ) {C c : ℝ}
    (hC : ∀ᵐ x ∂μ, ‖m x‖ ≤ C) (hc : 0 < c)
    (hl : ∀ᵐ x ∂μ, c ≤ ‖m x‖) (f : Lp ℂ 2 μ) :
    (l2MultiplierEquiv m hm hC hc hl f : α → ℂ) =ᵐ[μ] fun x => m x * f x :=
  l2Multiplier_coe m hm hC f
end RieszEuclidean
