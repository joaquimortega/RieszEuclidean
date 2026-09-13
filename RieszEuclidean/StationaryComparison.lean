import RieszEuclidean.StationaryKernel
import RieszEuclidean.ConfigurationKernel
import RieszEuclidean.ModulatedOperator
import Mathlib.Topology.ContinuousMap.Compact
noncomputable section
open MeasureTheory
namespace RieszEuclidean
/-- Multiplication by a continuous coefficient on a compact measured space. -/
def continuousL2Multiplier {X : Type} [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] (μ : Measure X) (m : C(X, ℂ)) :
    Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ :=
  l2MultiplierCLM m m.continuous.aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => m.norm_coe_le_norm x)

/-- Uniform convergence of coefficients implies operator norm convergence of multipliers. -/
theorem norm_continuousL2Multiplier_sub_le {X : Type} [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] (μ : Measure X) (m n : C(X, ℂ)) :
    ‖continuousL2Multiplier μ m - continuousL2Multiplier μ n‖ ≤ ‖m - n‖ := by
  refine (continuousL2Multiplier μ m - continuousL2Multiplier μ n).opNorm_le_bound
    (norm_nonneg _) ?_
  intro f
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  have hm := l2Multiplier_coe m m.continuous.aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => m.norm_coe_le_norm x) f
  have hn := l2Multiplier_coe n n.continuous.aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => n.norm_coe_le_norm x) f
  filter_upwards [hm, hn, Lp.coeFn_sub (continuousL2Multiplier μ m f)
    (continuousL2Multiplier μ n f)] with x hx hy hz
  change ‖(continuousL2Multiplier μ m f - continuousL2Multiplier μ n f) x‖ ≤ _
  change (continuousL2Multiplier μ m f) x = m x * f x at hx
  change (continuousL2Multiplier μ n f) x = n x * f x at hy
  rw [hz, Pi.sub_apply, hx, hy, ← sub_mul, norm_mul]
  exact mul_le_mul_of_nonneg_right ((m - n).norm_coe_le_norm x) (norm_nonneg _)

/-- The coefficient-to-multiplier map is continuous in the uniform norm. -/
theorem continuous_continuousL2Multiplier {X : Type} [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] (μ : Measure X) :
    Continuous (continuousL2Multiplier μ) := by
  apply LipschitzWith.continuous (K := 1)
  apply LipschitzWith.of_dist_le_mul
  intro m n
  simpa only [dist_eq_norm, NNReal.coe_one, one_mul] using norm_continuousL2Multiplier_sub_le μ m n
/-- A compactly supported uniform envelope for the stationary operator integrand. -/
def stationaryEnvelope {d : ℕ} (r M : ℝ) (y : Euclidean d) : ℝ :=
  (Metric.closedBall 0 (2 * r)).indicator (fun _ => M ^ 2) y

/-- The stationary envelope is integrable. -/
theorem integrable_stationaryEnvelope (d : ℕ) (r M : ℝ) :
    Integrable (stationaryEnvelope (d := d) r M) := by
  exact (integrable_indicator_iff Metric.isClosed_closedBall.measurableSet).mpr
    (integrableOn_const.mpr (Or.inr (isCompact_closedBall (0 : Euclidean d) (2 * r)).measure_lt_top))

/-- The compact stationary envelope has a finite first moment. -/
theorem integrable_stationaryEnvelope_moment (d : ℕ) (r M : ℝ) :
    Integrable (fun y : Euclidean d => ‖y‖ * stationaryEnvelope r M y) := by
  have hh : Integrable ((Metric.closedBall (0 : Euclidean d) (2 * r)).indicator
      (fun y => ‖y‖ * M ^ 2)) :=
    (integrable_indicator_iff Metric.isClosed_closedBall.measurableSet).mpr
      ((continuous_norm.mul continuous_const).continuousOn.integrableOn_compact
        (isCompact_closedBall _ _))
  convert hh using 1
  funext y
  by_cases hy : y ∈ Metric.closedBall (0 : Euclidean d) (2 * r) <;>
    simp [stationaryEnvelope, hy]

namespace SeparatedConfiguration
/-- The stationary coefficient as an actual continuous function on the hull. -/
def stationaryCoefficient {d : ℕ} {δ : ℝ} (hδ : 0 < δ)
    (Γ : SeparatedConfiguration d δ) (b : Euclidean d → ℂ)
    (hb : Continuous b) (hc : HasCompactSupport b) (y : Euclidean d) : C(hull Γ, ℂ) :=
  ⟨fun Δ => stationaryKernel b y Δ.val,
    (continuous_configuration_bumpKernel hδ b hb hc 0 (-y)).comp continuous_subtype_val⟩

/-- Compactness of the hull turns joint kernel continuity into uniform coefficient continuity. -/
theorem continuous_stationaryCoefficient {d : ℕ} {δ : ℝ} (hδ : 0 < δ)
    (Γ : SeparatedConfiguration d δ) (b : Euclidean d → ℂ)
    (hb : Continuous b) (hc : HasCompactSupport b) :
    Continuous (stationaryCoefficient hδ Γ b hb hc) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  exact (continuous_configuration_bumpKernel_joint hδ b hb hc).comp
    ((continuous_subtype_val.comp continuous_snd).prodMk
      (continuous_const.prodMk continuous_fst.neg))

/-- Strong continuity of the actual stationary operator integrand. -/
theorem continuous_stationaryKernelOperator_apply {d : ℕ} {δ r M : ℝ} (hδ : 0 < δ)
    (Γ : SeparatedConfiguration d δ) [MeasurableSpace (hull Γ)] [BorelSpace (hull Γ)]
    [CompactSpace (hull Γ)]
    (μ : Measure (hull Γ)) [IsProbabilityMeasure μ]
    (hμ : ∀ z : Euclidean d, MeasurePreserving (hullTranslate hδ Γ z) μ μ)
    (hr : 2 * r ≤ δ) (b : Euclidean d → ℂ)
    (hbc : Continuous b) (hcompact : HasCompactSupport b)
    (hs : ∀ x, r ≤ ‖x‖ → b x = 0) (hM : 0 ≤ M) (hb : ∀ x, ‖b x‖ ≤ M)
    (f : Lp ℂ 2 μ) :
    Continuous (fun y => stationaryKernelOperator hδ Γ μ hμ hr b hs hM hb y
      (stationaryCoefficient hδ Γ b hbc hcompact y).continuous.aestronglyMeasurable f) := by
  have hh := ((continuous_continuousL2Multiplier μ).comp
    (continuous_stationaryCoefficient hδ Γ b hbc hcompact)).clm_apply
    (strongContinuous_hullKoopmanUnitary hδ Γ μ hμ f)
  convert hh using 1
section Comparison
variable {d : ℕ} {δ r M : ℝ} (hδ : 0 < δ)
    (Γ : SeparatedConfiguration d δ) [MeasurableSpace (hull Γ)] [BorelSpace (hull Γ)]
    [CompactSpace (hull Γ)] (μ : Measure (hull Γ)) [IsProbabilityMeasure μ]
    (hμ : ∀ z : Euclidean d, MeasurePreserving (hullTranslate hδ Γ z) μ μ)
    (hr : 2 * r ≤ δ) (b : Euclidean d → ℂ)
    (hbc : Continuous b) (hcompact : HasCompactSupport b)
    (hs : ∀ x, r ≤ ‖x‖ → b x = 0) (hM : 0 ≤ M) (hb : ∀ x, ‖b x‖ ≤ M)

/-- The concrete covariant operator family with measurability discharged by kernel continuity. -/
def comparisonIntegrand (y : Euclidean d) : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ :=
  stationaryKernelOperator hδ Γ μ hμ hr b hs hM hb y
    (stationaryCoefficient hδ Γ b hbc hcompact y).continuous.aestronglyMeasurable

/-- The actual comparison integrand is strongly continuous on every vector. -/
theorem continuous_comparisonIntegrand_apply (f : Lp ℂ 2 μ) :
    Continuous (fun y => comparisonIntegrand hδ Γ μ hμ hr b hbc hcompact hs hM hb y f) :=
  continuous_stationaryKernelOperator_apply hδ Γ μ hμ hr b hbc hcompact hs hM hb f

omit [CompactSpace (hull Γ)] [IsProbabilityMeasure μ] in
/-- The compact envelope bounds the actual operator family everywhere. -/
theorem norm_comparisonIntegrand_le (y : Euclidean d) :
    ‖comparisonIntegrand hδ Γ μ hμ hr b hbc hcompact hs hM hb y‖ ≤
      stationaryEnvelope r M y := by
  by_cases hy : y ∈ Metric.closedBall (0 : Euclidean d) (2 * r)
  · simpa only [stationaryEnvelope, Set.indicator_of_mem hy] using
      norm_stationaryKernelOperator_le hδ Γ μ hμ hr b hs hM hb y
        (stationaryCoefficient hδ Γ b hbc hcompact y).continuous.aestronglyMeasurable
  · have hyr : 2 * r < ‖y‖ := by
      simpa only [Metric.mem_closedBall, dist_zero_right, not_le] using hy
    rw [comparisonIntegrand, stationaryKernelOperator_eq_zero hδ Γ μ hμ hr b hs hM hb y
      (stationaryCoefficient hδ Γ b hbc hcompact y).continuous.aestronglyMeasurable hyr]
    simp [stationaryEnvelope, hy]

/-- The manuscript's stationary comparison operator as an actual vector-valued integral. -/
def stationaryComparison (t : Euclidean d) : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ :=
  modulatedOperator (comparisonIntegrand hδ Γ μ hμ hr b hbc hcompact hs hM hb)
    (fun f => (continuous_comparisonIntegrand_apply hδ Γ μ hμ hr b hbc hcompact hs hM hb f).aestronglyMeasurable)
    (integrable_stationaryEnvelope d r M)
    (norm_comparisonIntegrand_le hδ Γ μ hμ hr b hbc hcompact hs hM hb) t

/-- Evaluation of the stationary comparison is exactly the modulated kernel integral. -/
theorem stationaryComparison_apply (t : Euclidean d) (f : Lp ℂ 2 μ) :
    stationaryComparison hδ Γ μ hμ hr b hbc hcompact hs hM hb t f =
      ∫ y, exponential t y • comparisonIntegrand hδ Γ μ hμ hr b hbc hcompact hs hM hb y f := rfl

/-- A finite explicit first moment controls the operator norm variation in the parameter. -/
theorem norm_stationaryComparison_sub_le (t s : Euclidean d) :
    ‖stationaryComparison hδ Γ μ hμ hr b hbc hcompact hs hM hb t -
      stationaryComparison hδ Γ μ hμ hr b hbc hcompact hs hM hb s‖ ≤
      (2 * Real.pi * ∫ y : Euclidean d, ‖y‖ * stationaryEnvelope r M y) * ‖t - s‖ :=
  norm_modulatedOperator_sub_le _ _ _ _ (integrable_stationaryEnvelope_moment d r M) t s
/-- The actual modulated stationary comparison is self-adjoint. -/
theorem stationaryComparison_isSelfAdjoint (t : Euclidean d) :
    IsSelfAdjoint (stationaryComparison hδ Γ μ hμ hr b hbc hcompact hs hM hb t) := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  intro f g
  let A := comparisonIntegrand hδ Γ μ hμ hr b hbc hcompact hs hM hb
  have hi (v : Lp ℂ 2 μ) : Integrable (fun y => exponential t y • A y v) :=
    integrable_modulatedOperator A
      (fun f => (continuous_comparisonIntegrand_apply hδ Γ μ hμ hr b hbc hcompact hs hM hb f).aestronglyMeasurable)
      (integrable_stationaryEnvelope d r M)
      (norm_comparisonIntegrand_le hδ Γ μ hμ hr b hbc hcompact hs hM hb) t v
  have ha (y : Euclidean d) : inner (𝕜 := ℂ) (A y f) g = inner (𝕜 := ℂ) f (A (-y) g) :=
    stationaryKernelOperator_inner hδ Γ μ hμ hr b hs hM hb y
      (stationaryCoefficient hδ Γ b hbc hcompact y).continuous.aestronglyMeasurable
      (stationaryCoefficient hδ Γ b hbc hcompact (-y)).continuous.aestronglyMeasurable f g
  have he (y : Euclidean d) : starRingEnd ℂ (exponential t y) = exponential t (-y) := by
    simp only [exponential, ← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I,
      inner_neg_right, Complex.ofReal_neg, map_ofNat]
    congr 1
    ring
  change inner (𝕜 := ℂ) (∫ y, exponential t y • A y f) g =
    inner (𝕜 := ℂ) f (∫ y, exponential t y • A y g)
  calc
    _ = ∫ y, inner (𝕜 := ℂ) (exponential t y • A y f) g := by
      rw [← inner_conj_symm, ← integral_inner (hi f), ← integral_conj]
      apply integral_congr_ae
      filter_upwards [] with y
      exact inner_conj_symm _ _
    _ = ∫ y, exponential t (-y) * inner (𝕜 := ℂ) f (A (-y) g) := by
      apply integral_congr_ae
      filter_upwards [] with y
      rw [inner_smul_left, he, ha]
    _ = ∫ y, exponential t y * inner (𝕜 := ℂ) f (A y g) := by
      exact integral_neg_eq_self (fun y => exponential t y * inner (𝕜 := ℂ) f (A y g)) volume
    _ = _ := by
      simp_rw [← inner_smul_right]
      exact integral_inner (hi g) f
end Comparison
end SeparatedConfiguration
end RieszEuclidean
