import RieszEuclidean.StationaryComparison
import RieszEuclidean.ContinuousMultiplierIntegral
import RieszEuclidean.BumpKernelProjection
noncomputable section
open MeasureTheory
namespace RieszEuclidean
/-- The covariant coefficient product reproduces the stationary coefficient after integration. -/
theorem integral_stationaryKernel_product {d : ℕ} {δ r : ℝ}
    (Δ : SeparatedConfiguration d δ) (hr : 2 * r ≤ δ)
    (b : Euclidean d → ℂ) (hs : ∀ x, r ≤ ‖x‖ → b x = 0)
    (hn : (∫ x, ‖b x‖ ^ 2) = 1) (v : Euclidean d) :
    (∫ y, stationaryKernel b y Δ *
      stationaryKernel b (v - y) (SeparatedConfiguration.translate (-y) Δ)) =
      stationaryKernel b v Δ := by
  have he (y : Euclidean d) : stationaryKernel b y Δ *
      stationaryKernel b (v - y) (SeparatedConfiguration.translate (-y) Δ) =
      bumpKernel Δ.carrier b 0 (-y) * bumpKernel Δ.carrier b (-y) (-v) := by
    rw [stationaryKernel_translate]
    simp [stationaryKernel]
  simp_rw [he]
  rw [integral_neg_eq_self (fun y => bumpKernel Δ.carrier b 0 y * bumpKernel Δ.carrier b y (-v)) volume,
    integral_bumpKernel_product Δ.separated hr b hs hn]
  rfl

namespace SeparatedConfiguration
/-- Composition of the actual shifted multipliers has the covariant kernel-product representative. -/
theorem comparisonIntegrand_comp_coe {d : ℕ} {δ r M : ℝ} (hδ : 0 < δ)
    (Γ : SeparatedConfiguration d δ) [MeasurableSpace (hull Γ)] [BorelSpace (hull Γ)]
    (μ : Measure (hull Γ))
    (hμ : ∀ z : Euclidean d, MeasurePreserving (hullTranslate hδ Γ z) μ μ)
    (hr : 2 * r ≤ δ) (b : Euclidean d → ℂ)
    (hbc : Continuous b) (hcompact : HasCompactSupport b)
    (hs : ∀ x, r ≤ ‖x‖ → b x = 0) (hM : 0 ≤ M) (hb : ∀ x, ‖b x‖ ≤ M)
    (y u : Euclidean d) (f : Lp ℂ 2 μ) :
    (comparisonIntegrand hδ Γ μ hμ hr b hbc hcompact hs hM hb y
      (comparisonIntegrand hδ Γ μ hμ hr b hbc hcompact hs hM hb u f) : hull Γ → ℂ) =ᵐ[μ]
      fun Δ => stationaryKernel b y Δ.val *
        stationaryKernel b u (translate (-y) Δ.val) * f (hullTranslate hδ Γ (-(y + u)) Δ) := by
  have hy := stationaryKernelOperator_coe hδ Γ μ hμ hr b hs hM hb y
    (stationaryCoefficient hδ Γ b hbc hcompact y).continuous.aestronglyMeasurable
    (comparisonIntegrand hδ Γ μ hμ hr b hbc hcompact hs hM hb u f)
  have hu := stationaryKernelOperator_coe hδ Γ μ hμ hr b hs hM hb u
    (stationaryCoefficient hδ Γ b hbc hcompact u).continuous.aestronglyMeasurable f
  filter_upwards [hy, (hμ (-y)).quasiMeasurePreserving.ae hu] with Δ hyΔ huΔ
  have he : hullTranslate hδ Γ (-u) (hullTranslate hδ Γ (-y) Δ) =
      hullTranslate hδ Γ (-(y + u)) Δ := by
    apply Subtype.ext
    change translate (-u) (translate (-y) Δ.val) = translate (-(y + u)) Δ.val
    rw [translate_add, neg_add, add_comm (-u) (-y)]
  change (stationaryKernelOperator hδ Γ μ hμ hr b hs hM hb y
    (stationaryCoefficient hδ Γ b hbc hcompact y).continuous.aestronglyMeasurable
    (comparisonIntegrand hδ Γ μ hμ hr b hbc hcompact hs hM hb u f)) Δ = _
  rw [hyΔ]
  change stationaryKernel b y Δ.val *
    (stationaryKernelOperator hδ Γ μ hμ hr b hs hM hb u
      (stationaryCoefficient hδ Γ b hbc hcompact u).continuous.aestronglyMeasurable f)
      (hullTranslate hδ Γ (-y) Δ) = _
  rw [huΔ, he, ← mul_assoc]
  rfl
section Projection
variable {d : ℕ} {δ r M : ℝ} (hδ : 0 < δ)
    (Γ : SeparatedConfiguration d δ) [MeasurableSpace (hull Γ)] [BorelSpace (hull Γ)]
    [CompactSpace (hull Γ)] (μ : Measure (hull Γ)) [IsProbabilityMeasure μ]
    (hμ : ∀ z : Euclidean d, MeasurePreserving (hullTranslate hδ Γ z) μ μ)
    (hr : 2 * r ≤ δ) (b : Euclidean d → ℂ)
    (hbc : Continuous b) (hcompact : HasCompactSupport b)
    (hs : ∀ x, r ≤ ‖x‖ → b x = 0) (hM : 0 ≤ M) (hb : ∀ x, ‖b x‖ ≤ M)

/-- The actual covariant operator integrand is jointly continuous in displacement and vector. -/
theorem continuous_comparisonIntegrand_uncurry :
    Continuous (fun p : Euclidean d × Lp ℂ 2 μ =>
      comparisonIntegrand hδ Γ μ hμ hr b hbc hcompact hs hM hb p.1 p.2) := by
  have hU := (continuous_hull_pullback hδ Γ μ hμ).comp
    (continuous_fst.neg.prodMk continuous_snd)
  have hc := (((continuous_continuousL2Multiplier μ).comp
    (continuous_stationaryCoefficient hδ Γ b hbc hcompact)).comp continuous_fst).clm_apply hU
  convert hc using 1

/-- The double operator product is a continuous vector-valued function. -/
theorem continuous_comparisonIntegrand_product (f : Lp ℂ 2 μ) :
    Continuous (fun p : Euclidean d × Euclidean d =>
      comparisonIntegrand hδ Γ μ hμ hr b hbc hcompact hs hM hb p.1
        (comparisonIntegrand hδ Γ μ hμ hr b hbc hcompact hs hM hb p.2 f)) := by
  let A := comparisonIntegrand hδ Γ μ hμ hr b hbc hcompact hs hM hb
  have hpair : Continuous (fun p : Euclidean d × Euclidean d => (p.1, A p.2 f)) :=
    continuous_fst.prodMk ((continuous_comparisonIntegrand_apply hδ Γ μ hμ hr b hbc hcompact hs hM hb f).comp continuous_snd)
  have hA : Continuous (fun p : Euclidean d × Lp ℂ 2 μ => A p.1 p.2) :=
    continuous_comparisonIntegrand_uncurry hδ Γ μ hμ hr b hbc hcompact hs hM hb
  have hh := hA.comp hpair
  exact hh

/-- Compact operator envelopes justify Fubini for the actual double operator product. -/
theorem integrable_comparisonIntegrand_product (f : Lp ℂ 2 μ) :
    Integrable (fun p : Euclidean d × Euclidean d =>
      comparisonIntegrand hδ Γ μ hμ hr b hbc hcompact hs hM hb p.1
        (comparisonIntegrand hδ Γ μ hμ hr b hbc hcompact hs hM hb p.2 f))
      (volume.prod volume) := by
  let A := comparisonIntegrand hδ Γ μ hμ hr b hbc hcompact hs hM hb
  let C := stationaryEnvelope (d := d) r M
  have hC := integrable_stationaryEnvelope d r M
  have hprod : Integrable (fun p : Euclidean d × Euclidean d => C p.1 * C p.2 * ‖f‖)
      (volume.prod volume) := (hC.mul_prod hC).mul_const ‖f‖
  apply hprod.mono' (continuous_comparisonIntegrand_product hδ Γ μ hμ hr b hbc hcompact hs hM hb f).aestronglyMeasurable
  filter_upwards [] with p
  have hb1 := norm_comparisonIntegrand_le hδ Γ μ hμ hr b hbc hcompact hs hM hb p.1
  have hb2 := norm_comparisonIntegrand_le hδ Γ μ hμ hr b hbc hcompact hs hM hb p.2
  have hp1 : 0 ≤ C p.1 := (norm_nonneg (A p.1)).trans hb1
  calc
    ‖A p.1 (A p.2 f)‖ ≤ ‖A p.1‖ * ‖A p.2 f‖ := (A p.1).le_opNorm _
    _ ≤ C p.1 * (C p.2 * ‖f‖) :=
      mul_le_mul hb1 ((A p.2).le_opNorm f |>.trans
        (mul_le_mul_of_nonneg_right hb2 (norm_nonneg f))) (norm_nonneg _) hp1
    _ = _ := (mul_assoc _ _ _).symm
/-- Modulation preserves integrability of the double operator product. -/
theorem integrable_modulated_comparison_product (t : Euclidean d) (f : Lp ℂ 2 μ) :
    Integrable (fun p : Euclidean d × Euclidean d => exponential t (p.1 + p.2) •
      comparisonIntegrand hδ Γ μ hμ hr b hbc hcompact hs hM hb p.1
        (comparisonIntegrand hδ Γ μ hμ hr b hbc hcompact hs hM hb p.2 f))
      (volume.prod volume) := by
  have hi := integrable_comparisonIntegrand_product hδ Γ μ hμ hr b hbc hcompact hs hM hb f
  have hc : Continuous (fun p : Euclidean d × Euclidean d => exponential t (p.1 + p.2)) := by
    unfold exponential
    fun_prop
  apply hi.norm.mono' (hc.aestronglyMeasurable.smul hi.aestronglyMeasurable)
  filter_upwards [] with p
  simp only [norm_smul, exponential_norm, one_mul, le_refl]

/-- Squaring the actual comparison integral gives the concrete iterated kernel integral. -/
theorem stationaryComparison_sq_apply (t : Euclidean d) (f : Lp ℂ 2 μ) :
    stationaryComparison hδ Γ μ hμ hr b hbc hcompact hs hM hb t
      (stationaryComparison hδ Γ μ hμ hr b hbc hcompact hs hM hb t f) =
      ∫ y, ∫ u, exponential t (y + u) •
        comparisonIntegrand hδ Γ μ hμ hr b hbc hcompact hs hM hb y
          (comparisonIntegrand hδ Γ μ hμ hr b hbc hcompact hs hM hb u f) := by
  let A := comparisonIntegrand hδ Γ μ hμ hr b hbc hcompact hs hM hb
  have hi : Integrable (fun y => exponential t y • A y f) :=
    integrable_modulatedOperator A
      (fun f => (continuous_comparisonIntegrand_apply hδ Γ μ hμ hr b hbc hcompact hs hM hb f).aestronglyMeasurable)
      (integrable_stationaryEnvelope d r M)
      (norm_comparisonIntegrand_le hδ Γ μ hμ hr b hbc hcompact hs hM hb) t f
  change (∫ y, exponential t y • A y (∫ u, exponential t u • A u f)) = _
  apply integral_congr_ae
  filter_upwards [] with y
  rw [← (A y).integral_comp_comm hi, ← integral_smul]
  apply integral_congr_ae
  filter_upwards [] with u
  rw [map_smul, smul_smul]
  congr 1
  unfold exponential
  rw [inner_add_right, Complex.ofReal_add, mul_add, Complex.exp_add]
/-- The convolution-coordinate double integrand is integrable. -/
theorem integrable_comparison_convolution (t : Euclidean d) (f : Lp ℂ 2 μ) :
    Integrable (fun p : Euclidean d × Euclidean d => exponential t p.1 •
      comparisonIntegrand hδ Γ μ hμ hr b hbc hcompact hs hM hb p.2
        (comparisonIntegrand hδ Γ μ hμ hr b hbc hcompact hs hM hb (p.1 - p.2) f))
      (volume.prod volume) := by
  let A := comparisonIntegrand hδ Γ μ hμ hr b hbc hcompact hs hM hb
  let C := stationaryEnvelope (d := d) r M
  have hC := integrable_stationaryEnvelope d r M
  have hprod : Integrable (fun p : Euclidean d × Euclidean d => C p.2 * C (p.1 - p.2) * ‖f‖)
      (volume.prod volume) := (hC.convolution_integrand (ContinuousLinearMap.mul ℝ ℝ) hC).mul_const ‖f‖
  have hcont := (continuous_comparisonIntegrand_product hδ Γ μ hμ hr b hbc hcompact hs hM hb f).comp
    (continuous_snd.prodMk (continuous_fst.sub continuous_snd))
  have hexp : Continuous (fun p : Euclidean d × Euclidean d => exponential t p.1) := by
    unfold exponential
    fun_prop
  apply hprod.mono' (hexp.smul hcont).aestronglyMeasurable
  filter_upwards [] with p
  rw [norm_smul, exponential_norm, one_mul]
  have hb1 := norm_comparisonIntegrand_le hδ Γ μ hμ hr b hbc hcompact hs hM hb p.2
  have hb2 := norm_comparisonIntegrand_le hδ Γ μ hμ hr b hbc hcompact hs hM hb (p.1 - p.2)
  have hp1 : 0 ≤ C p.2 := (norm_nonneg (A p.2)).trans hb1
  calc
    ‖A p.2 (A (p.1 - p.2) f)‖ ≤ ‖A p.2‖ * ‖A (p.1 - p.2) f‖ := (A p.2).le_opNorm _
    _ ≤ C p.2 * (C (p.1 - p.2) * ‖f‖) :=
      mul_le_mul hb1 ((A (p.1 - p.2)).le_opNorm f |>.trans
        (mul_le_mul_of_nonneg_right hb2 (norm_nonneg f))) (norm_nonneg _) hp1
    _ = _ := (mul_assoc _ _ _).symm

/-- Fubini and translation convert the actual square to the reproducing-kernel coordinates. -/
theorem stationaryComparison_sq_convolution (t : Euclidean d) (f : Lp ℂ 2 μ) :
    stationaryComparison hδ Γ μ hμ hr b hbc hcompact hs hM hb t
      (stationaryComparison hδ Γ μ hμ hr b hbc hcompact hs hM hb t f) =
      ∫ v, exponential t v • ∫ y,
        comparisonIntegrand hδ Γ μ hμ hr b hbc hcompact hs hM hb y
          (comparisonIntegrand hδ Γ μ hμ hr b hbc hcompact hs hM hb (v - y) f) := by
  rw [stationaryComparison_sq_apply]
  let A := comparisonIntegrand hδ Γ μ hμ hr b hbc hcompact hs hM hb
  calc
    (∫ y, ∫ u, exponential t (y + u) • A y (A u f)) =
        ∫ y, ∫ v, exponential t v • A y (A (v - y) f) := by
      apply integral_congr_ae
      filter_upwards [] with y
      simpa only [add_sub_cancel_left] using integral_add_left_eq_self
        (fun v => exponential t v • A y (A (v - y) f)) y
    _ = ∫ v, ∫ y, exponential t v • A y (A (v - y) f) :=
      (integral_integral_swap (integrable_comparison_convolution hδ Γ μ hμ hr b hbc hcompact hs hM hb t f)).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with v
      exact integral_smul (exponential t v) _
/-- The continuous coefficient of the convolution product on the compact hull. -/
def comparisonProductCoefficient (v y : Euclidean d) : C(hull Γ, ℂ) :=
  ⟨fun Δ => bumpKernel Δ.val.carrier b 0 (-y) * bumpKernel Δ.val.carrier b (-y) (-v),
    ((continuous_configuration_bumpKernel hδ b hbc hcompact 0 (-y)).comp continuous_subtype_val).mul
      ((continuous_configuration_bumpKernel hδ b hbc hcompact (-y) (-v)).comp continuous_subtype_val)⟩

omit [MeasurableSpace (hull Γ)] [BorelSpace (hull Γ)] [CompactSpace (hull Γ)] in
/-- Joint kernel continuity gives uniform continuity in the coefficient parameter. -/
theorem continuous_comparisonProductCoefficient (v : Euclidean d) :
    Continuous (comparisonProductCoefficient hδ Γ b hbc hcompact v) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  exact ((continuous_configuration_bumpKernel_joint hδ b hbc hcompact).comp
    ((continuous_subtype_val.comp continuous_snd).prodMk (continuous_const.prodMk continuous_fst.neg))).mul
    ((continuous_configuration_bumpKernel_joint hδ b hbc hcompact).comp
    ((continuous_subtype_val.comp continuous_snd).prodMk (continuous_fst.neg.prodMk continuous_const)))

include hs in
omit [MeasurableSpace (hull Γ)] [BorelSpace (hull Γ)] [CompactSpace (hull Γ)] in
/-- The coefficient vanishes outside the bump interaction ball. -/
theorem comparisonProductCoefficient_eq_zero (v y : Euclidean d) (hy : 2 * r < ‖y‖) :
    comparisonProductCoefficient hδ Γ b hbc hcompact v y = 0 := by
  ext Δ
  change stationaryKernel b y Δ.val * bumpKernel Δ.val.carrier b (-y) (-v) = 0
  rw [stationaryKernel_eq_zero b hs hy, zero_mul]

include hs in
omit [MeasurableSpace (hull Γ)] [BorelSpace (hull Γ)] in
/-- The continuous coefficient family has compact support, so its vector integral is absolute. -/
theorem integrable_comparisonProductCoefficient (v : Euclidean d) :
    Integrable (comparisonProductCoefficient hδ Γ b hbc hcompact v) := by
  apply (continuous_comparisonProductCoefficient hδ Γ b hbc hcompact v).integrable_of_hasCompactSupport
  apply (isCompact_closedBall (0 : Euclidean d) (2 * r)).of_isClosed_subset isClosed_closure
  apply closure_minimal _ Metric.isClosed_closedBall
  intro y hy
  by_contra hn
  have hyr : 2 * r < ‖y‖ := by
    simpa only [Metric.mem_closedBall, dist_zero_right, not_le] using hn
  exact hy (comparisonProductCoefficient_eq_zero hδ Γ b hbc hcompact hs v y hyr)

include hr hs in
omit [MeasurableSpace (hull Γ)] [BorelSpace (hull Γ)] in
/-- The integrated coefficient is exactly the original stationary coefficient. -/
theorem integral_comparisonProductCoefficient (hn : (∫ x, ‖b x‖ ^ 2) = 1) (v : Euclidean d) :
    (∫ y, comparisonProductCoefficient hδ Γ b hbc hcompact v y) =
      stationaryCoefficient hδ Γ b hbc hcompact v := by
  ext Δ
  rw [ContinuousMap.integral_apply (integrable_comparisonProductCoefficient hδ Γ b hbc hcompact hs v)]
  change (∫ y, bumpKernel Δ.val.carrier b 0 (-y) * bumpKernel Δ.val.carrier b (-y) (-v)) = _
  rw [integral_neg_eq_self (fun y => bumpKernel Δ.val.carrier b 0 y * bumpKernel Δ.val.carrier b y (-v)) volume,
    integral_bumpKernel_product Δ.val.separated hr b hs hn]
  rfl
omit [IsProbabilityMeasure μ] in
/-- Convolution products are multiplication of a single shifted vector by their actual coefficients. -/
theorem comparisonIntegrand_product_eq_multiplier (v y : Euclidean d) (f : Lp ℂ 2 μ) :
    comparisonIntegrand hδ Γ μ hμ hr b hbc hcompact hs hM hb y
      (comparisonIntegrand hδ Γ μ hμ hr b hbc hcompact hs hM hb (v - y) f) =
      continuousL2Multiplier μ (comparisonProductCoefficient hδ Γ b hbc hcompact v y)
        (hullKoopmanUnitary hδ Γ μ hμ v f) := by
  apply Lp.ext
  have hp := comparisonIntegrand_comp_coe hδ Γ μ hμ hr b hbc hcompact hs hM hb y (v - y) f
  have hm := continuousL2Multiplier_coe μ (comparisonProductCoefficient hδ Γ b hbc hcompact v y)
    (hullKoopmanUnitary hδ Γ μ hμ v f)
  have hu := Lp.coeFn_compMeasurePreserving f (hμ (-v))
  filter_upwards [hp, hm, hu] with Δ hpΔ hmΔ huΔ
  rw [hpΔ, hmΔ]
  change stationaryKernel b y Δ.val * stationaryKernel b (v - y) (translate (-y) Δ.val) *
    f (hullTranslate hδ Γ (-(y + (v - y))) Δ) =
    (comparisonProductCoefficient hδ Γ b hbc hcompact v y) Δ *
      Lp.compMeasurePreserving (hullTranslate hδ Γ (-v)) (hμ (-v)) f Δ
  rw [huΔ, stationaryKernel_translate]
  simp only [Function.comp_apply, comparisonProductCoefficient, ContinuousMap.coe_mk,
    stationaryKernel, neg_sub, sub_sub_cancel_left]
  congr 2
  abel_nf

omit [IsProbabilityMeasure μ] in
/-- Integration of the actual covariant operator product reproduces the single operator. -/
theorem integral_comparisonIntegrand_product (hn : (∫ x, ‖b x‖ ^ 2) = 1)
    (v : Euclidean d) (f : Lp ℂ 2 μ) :
    (∫ y, comparisonIntegrand hδ Γ μ hμ hr b hbc hcompact hs hM hb y
      (comparisonIntegrand hδ Γ μ hμ hr b hbc hcompact hs hM hb (v - y) f)) =
      comparisonIntegrand hδ Γ μ hμ hr b hbc hcompact hs hM hb v f := by
  simp_rw [comparisonIntegrand_product_eq_multiplier hδ Γ μ hμ hr b hbc hcompact hs hM hb]
  rw [integral_continuousL2Multiplier μ _
      (integrable_comparisonProductCoefficient hδ Γ b hbc hcompact hs v),
    integral_comparisonProductCoefficient hδ Γ hr b hbc hcompact hs hn v]
  rfl

/-- The actual normalized stationary comparison operator is idempotent. -/
theorem stationaryComparison_idempotent (hn : (∫ x, ‖b x‖ ^ 2) = 1) (t : Euclidean d) :
    (stationaryComparison hδ Γ μ hμ hr b hbc hcompact hs hM hb t).comp
      (stationaryComparison hδ Γ μ hμ hr b hbc hcompact hs hM hb t) =
      stationaryComparison hδ Γ μ hμ hr b hbc hcompact hs hM hb t := by
  apply ContinuousLinearMap.ext
  intro f
  change stationaryComparison hδ Γ μ hμ hr b hbc hcompact hs hM hb t
    (stationaryComparison hδ Γ μ hμ hr b hbc hcompact hs hM hb t f) = _
  rw [stationaryComparison_sq_convolution]
  simp_rw [integral_comparisonIntegrand_product hδ Γ μ hμ hr b hbc hcompact hs hM hb hn]
  rfl
end Projection
end SeparatedConfiguration
end RieszEuclidean
