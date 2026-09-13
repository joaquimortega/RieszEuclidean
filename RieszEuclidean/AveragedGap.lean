import RieszEuclidean.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
open MeasureTheory Filter Topology
namespace RieszEuclidean
/-- Scalar Cauchy–Schwarz with the exact averaged test energies. -/
theorem integral_product_le_of_squared_energies {X : Type*} [MeasurableSpace X]
    (μ : Measure X) {u v : X → ℝ} (hu : MemLp u 2 μ) (hv : MemLp v 2 μ)
    (hupos : 0 ≤ᵐ[μ] u) (hvpos : 0 ≤ᵐ[μ] v)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (heu : (∫ x, u x ^ 2 ∂μ) = a ^ 2) (hev : (∫ x, v x ^ 2 ∂μ) = b ^ 2) :
    (∫ x, u x * v x ∂μ) ≤ a * b := by
  have hu' : MemLp u (ENNReal.ofReal (2 : ℝ)) μ := by simpa using hu
  have hv' : MemLp v (ENNReal.ofReal (2 : ℝ)) μ := by simpa using hv
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two hupos hvpos hu' hv'
  simpa only [Real.rpow_two, heu, hev, ← Real.sqrt_eq_rpow, Real.sqrt_sq ha, Real.sqrt_sq hb] using h
/-- Pointwise gap control and averaged energies bound the actual scalar integral. -/
theorem norm_averaged_scalar_le {X : Type*} [MeasurableSpace X]
    (μ : Measure X) {u v : X → ℝ} (hu : MemLp u 2 μ) (hv : MemLp v 2 μ)
    (hupos : 0 ≤ᵐ[μ] u) (hvpos : 0 ≤ᵐ[μ] v)
    {a b γ : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hγ : 0 ≤ γ)
    (heu : (∫ x, u x ^ 2 ∂μ) = a ^ 2) (hev : (∫ x, v x ^ 2 ∂μ) = b ^ 2)
    {F : X → ℂ} (hF : AEStronglyMeasurable F μ)
    (hbound : ∀ᵐ x ∂μ, ‖F x‖ ≤ γ * (u x * v x)) :
    Integrable F μ ∧ ‖∫ x, F x ∂μ‖ ≤ γ * (a * b) := by
  have huv : Integrable (fun x => u x * v x) μ := hu.integrable_mul hv
  have hi : Integrable F μ := (huv.const_mul γ).mono' hF hbound
  refine ⟨hi, ?_⟩
  calc
    ‖∫ x, F x ∂μ‖ ≤ ∫ x, ‖F x‖ ∂μ := norm_integral_le_integral_norm _
    _ ≤ ∫ x, γ * (u x * v x) ∂μ := integral_mono_ae hi.norm (huv.const_mul γ) hbound
    _ = γ * ∫ x, u x * v x ∂μ := integral_const_mul _ _
    _ ≤ γ * (a * b) := mul_le_mul_of_nonneg_left
      (integral_product_le_of_squared_energies μ hu hv hupos hvpos ha hb heu hev) hγ
/-- Uniform scalar pairing bounds control an actual continuous linear operator. -/
theorem norm_operator_le_of_pairing_bound {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (A : H →L[ℂ] H) {γ : ℝ} (hγ : 0 ≤ γ)
    (h : ∀ f g, ‖inner (𝕜 := ℂ) g (A f)‖ ≤ γ * (‖g‖ * ‖f‖)) : ‖A‖ ≤ γ := by
  apply A.opNorm_le_bound hγ
  intro f
  have hh := h f (A f)
  have he : ‖inner (𝕜 := ℂ) (A f) (A f)‖ = ‖A f‖ ^ 2 := by
    simp [inner_self_eq_norm_sq_to_K]
  rw [he] at hh
  by_cases hz : ‖A f‖ = 0
  · rw [hz]; positivity
  · have hp : 0 < ‖A f‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
    nlinarith
/-- The averaged scalar argument transfers the same gap constant. -/
theorem norm_operator_le_of_averaged_scalar_pairings {H X : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [MeasurableSpace X]
    (μ : Measure X) (A : H →L[ℂ] H) (j : H → X → ℝ)
    (hj : ∀ f, MemLp (j f) 2 μ) (hpos : ∀ f, 0 ≤ᵐ[μ] j f)
    (henergy : ∀ f, (∫ x, j f x ^ 2 ∂μ) = ‖f‖ ^ 2)
    (F : H → H → X → ℂ) (hF : ∀ f g, AEStronglyMeasurable (F f g) μ)
    (hpair : ∀ f g, inner (𝕜 := ℂ) g (A f) = ∫ x, F f g x ∂μ)
    {γ : ℝ} (hγ : 0 ≤ γ)
    (hbound : ∀ f g, ∀ᵐ x ∂μ, ‖F f g x‖ ≤ γ * (j g x * j f x)) : ‖A‖ ≤ γ := by
  apply norm_operator_le_of_pairing_bound A hγ
  intro f g
  rw [hpair]
  exact (norm_averaged_scalar_le μ (hj g) (hj f) (hpos g) (hpos f)
    (norm_nonneg g) (norm_nonneg f) hγ (henergy g) (henergy f) (hF f g) (hbound f g)).2
/-- An eventual uniform operator gap passes to two strong limits along the same filter. -/
theorem norm_sub_le_of_strong_filter_limits {ι H : Type*}
    [NormedAddCommGroup H] [NormedSpace ℂ H] {l : Filter ι} [NeBot l]
    (A B : ι → H →L[ℂ] H) (P Q : H →L[ℂ] H) {γ : ℝ} (hγ : 0 ≤ γ)
    (hA : ∀ f, Tendsto (fun i => A i f) l (𝓝 (P f)))
    (hB : ∀ f, Tendsto (fun i => B i f) l (𝓝 (Q f)))
    (hgap : ∀ᶠ i in l, ‖A i - B i‖ ≤ γ) : ‖P - Q‖ ≤ γ := by
  apply (P - Q).opNorm_le_bound hγ
  intro f
  have ht := ((hA f).sub (hB f)).norm
  change Tendsto (fun i => ‖(A i - B i) f‖) l (𝓝 ‖(P - Q) f‖) at ht
  apply le_of_tendsto ht
  filter_upwards [hgap] with i hi
  exact ((A i - B i).le_opNorm f).trans
    (mul_le_mul_of_nonneg_right hi (norm_nonneg f))
end RieszEuclidean
