import RieszEuclidean.Koopman
import Mathlib.Analysis.InnerProductSpace.LinearMap
open scoped BigOperators
namespace RieszEuclidean
variable {d : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
/-- The paper uses an inner product linear in its first argument; this order
translates its correlation to Mathlib's conjugate-linear-first convention. -/
noncomputable def unitaryCorrelation (U : Euclidean d → H ≃ₗᵢ[ℂ] H) (f : H)
    (z : Euclidean d) : ℂ := inner (𝕜 := ℂ) f (U z f)
/-- Strong continuity gives continuous scalar correlations. -/
theorem continuous_unitaryCorrelation (U : Euclidean d → H ≃ₗᵢ[ℂ] H)
    (hU : ∀ f, Continuous (fun z => U z f)) (f : H) :
    Continuous (unitaryCorrelation U f) := continuous_const.inner (hU f)
/-- Scalar correlations are uniformly bounded by the squared vector norm. -/
theorem norm_unitaryCorrelation_le (U : Euclidean d → H ≃ₗᵢ[ℂ] H) (f : H)
    (z : Euclidean d) : ‖unitaryCorrelation U f z‖ ≤ ‖f‖ ^ 2 := by
  simpa [unitaryCorrelation, pow_two] using norm_inner_le_norm (𝕜 := ℂ) f (U z f)
/-- The correlation at zero records the total spectral mass. -/
theorem unitaryCorrelation_zero (U : Euclidean d → H ≃ₗᵢ[ℂ] H)
    (h0 : ∀ f, U 0 f = f) (f : H) : unitaryCorrelation U f 0 = (‖f‖ : ℂ) ^ 2 := by
  rw [unitaryCorrelation, h0]
  exact inner_self_eq_norm_sq_to_K (𝕜 := ℂ) f
/-- Translation differences give the Gram kernel of a unitary orbit. -/
theorem unitaryCorrelation_sub (U : Euclidean d → H ≃ₗᵢ[ℂ] H)
    (hadd : ∀ z y f, U z (U y f) = U (z + y) f) (f : H) (x y : Euclidean d) :
    unitaryCorrelation U f (y - x) = inner (𝕜 := ℂ) (U x f) (U y f) := by
  rw [unitaryCorrelation, ← (U x).inner_map_map, hadd]
  rw [show x + (y - x) = y by abel]
/-- Positive definiteness of the scalar unitary correlation, with the precise
finite quadratic-form convention needed by Bochner's theorem. -/
theorem unitaryCorrelation_positiveDefinite (U : Euclidean d → H ≃ₗᵢ[ℂ] H)
    (hadd : ∀ z y f, U z (U y f) = U (z + y) f)
    (f : H) {ι : Type*} [Fintype ι] (x : ι → Euclidean d) (c : ι → ℂ) :
    (∑ i, ∑ j, star (c i) * c j * unitaryCorrelation U f (x j - x i)).im = 0 ∧
      0 ≤ (∑ i, ∑ j, star (c i) * c j * unitaryCorrelation U f (x j - x i)).re := by
  have he : (∑ i, ∑ j, star (c i) * c j * unitaryCorrelation U f (x j - x i)) =
      inner (𝕜 := ℂ) (∑ i, c i • U (x i) f) (∑ j, c j • U (x j) f) := by
    simp_rw [unitaryCorrelation_sub U hadd]
    symm
    rw [sum_inner]
    apply Finset.sum_congr rfl
    intro i hi
    rw [inner_sum]
    apply Finset.sum_congr rfl
    intro j hj
    simp only [inner_smul_left, inner_smul_right, mul_assoc]
    simp only [starRingEnd_apply]
    ring

  rw [he]
  constructor
  · exact inner_self_im (𝕜 := ℂ) (∑ i, c i • U (x i) f)
  · simpa using (inner_self_nonneg (𝕜 := ℂ) (x := ∑ i, c i • U (x i) f))
/-- The parallelogram identity holds already at the correlation level. -/
theorem unitaryCorrelation_parallelogram (U : Euclidean d → H ≃ₗᵢ[ℂ] H)
    (f g : H) (z : Euclidean d) :
    unitaryCorrelation U (f + g) z + unitaryCorrelation U (f - g) z =
      2 * (unitaryCorrelation U f z + unitaryCorrelation U g z) := by
  simp only [unitaryCorrelation, map_add, map_sub, inner_add_left, inner_add_right,
    inner_sub_left, inner_sub_right]
  ring
/-- Scaling a vector multiplies its correlation by the squared scalar modulus. -/
theorem unitaryCorrelation_smul (U : Euclidean d → H ≃ₗᵢ[ℂ] H)
    (c : ℂ) (f : H) (z : Euclidean d) :
    unitaryCorrelation U (c • f) z = (‖c‖ : ℂ) ^ 2 * unitaryCorrelation U f z := by
  simp only [unitaryCorrelation, map_smul, inner_smul_left, inner_smul_right]
  rw [← mul_assoc, RCLike.mul_conj]
  rfl
namespace SeparatedConfiguration
open MeasureTheory
/-- Scalar correlations for the actual stationary hull and the paper's U_z. -/
noncomputable def hullCorrelation {d : ℕ} {δ : ℝ} (hδ : 0 < δ)
    (Γ : SeparatedConfiguration d δ) [MeasurableSpace (hull Γ)]
    (μ : Measure (hull Γ))
    (hμ : ∀ z : Euclidean d, MeasurePreserving (hullTranslate hδ Γ z) μ μ)
    (f : Lp ℂ 2 μ) : Euclidean d → ℂ :=
  unitaryCorrelation (hullKoopmanUnitary hδ Γ μ hμ) f
/-- The actual hull correlations are continuous. -/
theorem continuous_hullCorrelation {d : ℕ} {δ : ℝ} (hδ : 0 < δ)
    (Γ : SeparatedConfiguration d δ)
    [MeasurableSpace (hull Γ)] [BorelSpace (hull Γ)]
    (μ : Measure (hull Γ)) [IsProbabilityMeasure μ]
    (hμ : ∀ z : Euclidean d, MeasurePreserving (hullTranslate hδ Γ z) μ μ)
    (f : Lp ℂ 2 μ) : Continuous (hullCorrelation hδ Γ μ hμ f) :=
  continuous_unitaryCorrelation _ (strongContinuous_hullKoopmanUnitary hδ Γ μ hμ) f
/-- The actual hull correlations have real, nonnegative finite quadratic forms. -/
theorem hullCorrelation_positiveDefinite {d : ℕ} {δ : ℝ} (hδ : 0 < δ)
    (Γ : SeparatedConfiguration d δ) [MeasurableSpace (hull Γ)]
    (μ : Measure (hull Γ))
    (hμ : ∀ z : Euclidean d, MeasurePreserving (hullTranslate hδ Γ z) μ μ)
    (f : Lp ℂ 2 μ) {ι : Type*} [Fintype ι] (x : ι → Euclidean d) (c : ι → ℂ) :
    (∑ i, ∑ j, star (c i) * c j * hullCorrelation hδ Γ μ hμ f (x j - x i)).im = 0 ∧
      0 ≤ (∑ i, ∑ j, star (c i) * c j * hullCorrelation hδ Γ μ hμ f (x j - x i)).re :=
  unitaryCorrelation_positiveDefinite _ (hullKoopmanUnitary_add hδ Γ μ hμ) f x c
/-- The invariant unit constant has correlation identically equal to one. -/
theorem hullCorrelation_one {d : ℕ} {δ : ℝ} (hδ : 0 < δ)
    (Γ : SeparatedConfiguration d δ) [MeasurableSpace (hull Γ)]
    (μ : Measure (hull Γ)) [IsProbabilityMeasure μ]
    (hμ : ∀ z : Euclidean d, MeasurePreserving (hullTranslate hδ Γ z) μ μ)
    (z : Euclidean d) : hullCorrelation hδ Γ μ hμ (Lp.const 2 μ (1 : ℂ)) z = 1 := by
  rw [hullCorrelation, unitaryCorrelation, hullKoopmanUnitary_const,
    inner_self_eq_norm_sq_to_K, norm_stationary_one]
  norm_num
end SeparatedConfiguration
end RieszEuclidean
