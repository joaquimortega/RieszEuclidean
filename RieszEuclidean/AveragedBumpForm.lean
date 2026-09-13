import RieszEuclidean.StationaryComparisonProjection
import RieszEuclidean.BoxOverlap
import RieszEuclidean.AveragedFourierForm
import RieszEuclidean.AveragedTests
import RieszEuclidean.BumpBoxKernel
noncomputable section
open MeasureTheory
namespace RieszEuclidean.SeparatedConfiguration
/-- Expanding the two normalized finite tests gives the paper's modulation and normalization. -/
theorem averagedTest_cross {d : ℕ} {X : Type*}
    (R : ℝ) (t : Euclidean d) (T : Euclidean d → X → X) (f g : X → ℂ)
    (Δ : X) {v w : Euclidean d} (hv : v ∈ euclideanBox d R) (hw : w ∈ euclideanBox d R) :
    averagedTest R t T f Δ w * star (averagedTest R t T g Δ v) =
      (volume.real (euclideanBox d R) : ℂ)⁻¹ * exponential t (v - w) *
        f (T w Δ) * star (g (T v Δ)) := by
  have he : exponential (-t) w * star (exponential (-t) v) = exponential t (v - w) := by
    change exponential (-t) w * starRingEnd ℂ (exponential (-t) v) = _
    simp only [exponential, ← Complex.exp_conj, map_mul, map_ofNat, Complex.conj_ofReal,
      Complex.conj_I, map_neg, inner_neg_left, inner_sub_right, Complex.ofReal_neg, Complex.ofReal_sub]
    rw [← Complex.exp_add]
    congr 1
    ring
  simp only [averagedTest, Set.indicator_of_mem hw, Set.indicator_of_mem hv,
    star_mul, starRingEnd_apply]
  have hn : ((((Real.sqrt (volume.real (euclideanBox d R)))⁻¹ : ℝ) : ℂ)) *
      star (((Real.sqrt (volume.real (euclideanBox d R)))⁻¹ : ℝ) : ℂ) =
      (volume.real (euclideanBox d R) : ℂ)⁻¹ := by
    change ((((Real.sqrt (volume.real (euclideanBox d R)))⁻¹ : ℝ) : ℂ) *
      starRingEnd ℂ ((((Real.sqrt (volume.real (euclideanBox d R)))⁻¹ : ℝ) : ℂ))) = _
    rw [Complex.conj_ofReal, ← Complex.ofReal_mul, ← Complex.ofReal_inv]
    congr 1
    rw [← mul_inv, ← pow_two, Real.sq_sqrt (show 0 ≤ volume.real (euclideanBox d R) from ENNReal.toReal_nonneg)]
  calc
    _ = ((((Real.sqrt (volume.real (euclideanBox d R)))⁻¹ : ℝ) : ℂ) *
        star (((Real.sqrt (volume.real (euclideanBox d R)))⁻¹ : ℝ) : ℂ)) *
      (exponential (-t) w * star (exponential (-t) v)) * f (T w Δ) * star (g (T v Δ)) := by ring
    _ = _ := by rw [hn, he]

/-- The actual bump projection pairing of finite tests expands to the compact double scalar integral. -/
theorem bump_projection_averagedTest_pairing {d : ℕ} {δ r : ℝ}
    {Λ : Set (Euclidean d)} (hΛ : Separated δ Λ) (hδ : 0 < δ) (hr : 2 * r < δ)
    (b : SchwartzMap (Euclidean d) ℂ) (hs : ∀ x, r ≤ ‖x‖ → b x = 0)
    (hn : ‖b.toLp 2 volume‖ = 1) {X : Type*} (T : Euclidean d → X → X)
    (f g : X → ℂ) (Δ : X) (R : ℝ) (t : Euclidean d)
    (hf : MemLp (averagedTest R t T f Δ) 2 volume)
    (hg : MemLp (averagedTest R t T g Δ) 2 volume) :
    inner (𝕜 := ℂ) (hg.toLp (averagedTest R t T g Δ))
      ((isometryRangeProjection (bumpSynthesis hΛ hr b hs hn)).op
        (hf.toLp (averagedTest R t T f Δ))) =
      (volume.real (euclideanBox d R) : ℂ)⁻¹ *
        ∫ v in euclideanBox d R, ∫ w in euclideanBox d R,
          exponential t (v - w) * bumpKernel Λ b v w * f (T w Δ) * star (g (T v Δ)) := by
  rw [bump_projection_memLp_pairing hΛ hδ hr b _ _ hs hn hg hf
    (hasCompactSupport_averagedTest R t T f Δ)]
  rw [← integral_const_mul]
  rw [← integral_indicator (measurableSet_euclideanBox d R)]
  apply integral_congr_ae
  filter_upwards [] with v
  by_cases hv : v ∈ euclideanBox d R
  · rw [Set.indicator_of_mem hv, ← integral_const_mul,
      ← integral_indicator (measurableSet_euclideanBox d R)]
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with w
    by_cases hw : w ∈ euclideanBox d R
    · rw [Set.indicator_of_mem hw]
      have he := averagedTest_cross R t T f g Δ hv hw
      calc
        _ = bumpKernel Λ b v w *
            (averagedTest R t T f Δ w * star (averagedTest R t T g Δ v)) := by ring
        _ = _ := by rw [he]; ring
    · simp [averagedTest, hw]
  · simp [averagedTest, hv]

/-- Absolute triple integration permits moving the hull average across the two spatial integrals. -/
theorem integral_triple_swap {X Y Z : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSpace Z] (μ : Measure X) (ν : Measure Y) (ρ : Measure Z)
    [SFinite μ] [SFinite ν] [SFinite ρ] {F : X × (Y × Z) → ℂ}
    (hF : Integrable F (μ.prod (ν.prod ρ))) :
    (∫ x, ∫ y, ∫ z, F (x, (y, z)) ∂ρ ∂ν ∂μ) =
      ∫ y, ∫ z, ∫ x, F (x, (y, z)) ∂μ ∂ρ ∂ν := by
  calc
    _ = ∫ x, ∫ p, F (x, p) ∂ν.prod ρ ∂μ := by
      apply integral_congr_ae
      filter_upwards [hF.prod_right_ae] with x hx
      exact (integral_prod _ hx).symm
    _ = ∫ p, ∫ x, F (x, p) ∂μ ∂ν.prod ρ := integral_integral_swap hF
    _ = _ := integral_prod _ hF.integral_prod_right

/-- Every hull translation is a measurable embedding, with inverse the opposite translation. -/
theorem measurableEmbedding_hullTranslate {d : ℕ} {δ : ℝ} (hδ : 0 < δ)
    (Γ : SeparatedConfiguration d δ) [MeasurableSpace (hull Γ)] [BorelSpace (hull Γ)]
    [CompactSpace (hull Γ)] (v : Euclidean d) :
    MeasurableEmbedding (hullTranslate hδ Γ v) := by
  apply Continuous.isClosedEmbedding _ _ |>.measurableEmbedding
  · exact (continuous_hullTranslate hδ Γ).comp (continuous_const.prodMk continuous_id)
  · intro Δ Θ he
    apply Subtype.ext
    have hh := congrArg (fun Ξ : hull Γ => translate (-v) Ξ.val) he
    change translate (-v) (translate v Δ.val) = translate (-v) (translate v Θ.val) at hh
    simpa using hh

/-- Stationarity and covariance identify the inner scalar integral of the averaged bump form. -/
theorem integral_covariant_bump_pairing {d : ℕ} {δ : ℝ} (hδ : 0 < δ)
    (Γ : SeparatedConfiguration d δ) [MeasurableSpace (hull Γ)] [BorelSpace (hull Γ)]
    [CompactSpace (hull Γ)] (μ : Measure (hull Γ))
    (hμ : ∀ z : Euclidean d, MeasurePreserving (hullTranslate hδ Γ z) μ μ)
    (b : Euclidean d → ℂ) (f g : hull Γ → ℂ) (v w : Euclidean d) :
    (∫ Δ, bumpKernel Δ.val.carrier b v w * f (hullTranslate hδ Γ w Δ) *
      star (g (hullTranslate hδ Γ v Δ)) ∂μ) =
    ∫ Δ, stationaryKernel b (v - w) Δ.val * f (hullTranslate hδ Γ (-(v - w)) Δ) *
      star (g Δ) ∂μ := by
  let F := fun Δ : hull Γ => stationaryKernel b (v - w) Δ.val *
    f (hullTranslate hδ Γ (-(v - w)) Δ) * star (g Δ)
  have he (Δ : hull Γ) : bumpKernel Δ.val.carrier b v w * f (hullTranslate hδ Γ w Δ) *
      star (g (hullTranslate hδ Γ v Δ)) = F (hullTranslate hδ Γ v Δ) := by
    have htrans : hullTranslate hδ Γ (-(v - w)) (hullTranslate hδ Γ v Δ) =
        hullTranslate hδ Γ w Δ := by
      apply Subtype.ext
      change translate (-(v - w)) (translate v Δ.val) = translate w Δ.val
      rw [translate_add]
      congr 1
      abel
    dsimp only [F]
    rw [htrans]
    change _ = bumpKernel (RieszEuclidean.translate v Δ.val.carrier) b 0 (-(v - w)) * _ * _
    rw [bumpKernel_translate]
    simp only [zero_add]
    congr 2
    congr 1
    abel
  simp_rw [he]
  exact (hμ v).integral_comp (measurableEmbedding_hullTranslate hδ Γ v) F
/-- The covariant scalar integral is exactly the L² pairing of the actual stationary integrand. -/
theorem integral_covariant_bump_pairing_Lp {d : ℕ} {δ r M : ℝ} (hδ : 0 < δ)
    (Γ : SeparatedConfiguration d δ) [MeasurableSpace (hull Γ)] [BorelSpace (hull Γ)]
    [CompactSpace (hull Γ)] (μ : Measure (hull Γ))
    (hμ : ∀ z : Euclidean d, MeasurePreserving (hullTranslate hδ Γ z) μ μ)
    (hr : 2 * r ≤ δ) (b : Euclidean d → ℂ)
    (hbc : Continuous b) (hcompact : HasCompactSupport b)
    (hs : ∀ x, r ≤ ‖x‖ → b x = 0) (hM : 0 ≤ M) (hb : ∀ x, ‖b x‖ ≤ M)
    (f g : Lp ℂ 2 μ) (v w : Euclidean d) :
    (∫ Δ, bumpKernel Δ.val.carrier b v w * f (hullTranslate hδ Γ w Δ) *
      star (g (hullTranslate hδ Γ v Δ)) ∂μ) =
    inner (𝕜 := ℂ) g (comparisonIntegrand hδ Γ μ hμ hr b hbc hcompact hs hM hb (v - w) f) := by
  rw [integral_covariant_bump_pairing hδ Γ μ hμ, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [stationaryKernelOperator_coe hδ Γ μ hμ hr b hs hM hb (v - w)
    (stationaryCoefficient hδ Γ b hbc hcompact (v - w)).continuous.aestronglyMeasurable f] with Δ hΔ
  change _ = inner (𝕜 := ℂ) (g Δ)
    (stationaryKernelOperator hδ Γ μ hμ hr b hs hM hb (v - w)
      (stationaryCoefficient hδ Γ b hbc hcompact (v - w)).continuous.aestronglyMeasurable f Δ)
  rw [hΔ]
  simp only [RCLike.inner_apply, starRingEnd_apply]

/-- A finite parameter family of stationary L² squares is jointly integrable. -/
theorem integrable_hull_square_parameters {d : ℕ} {δ : ℝ} (hδ : 0 < δ)
    (Γ : SeparatedConfiguration d δ) [MeasurableSpace (hull Γ)] [BorelSpace (hull Γ)]
    (μ : Measure (hull Γ)) [SFinite μ]
    (hμ : ∀ z : Euclidean d, MeasurePreserving (hullTranslate hδ Γ z) μ μ)
    {Y : Type*} [MeasurableSpace Y] (ν : Measure Y) [IsFiniteMeasure ν]
    (z : Y → Euclidean d) (hz : Measurable z) (f : Lp ℂ 2 μ) :
    Integrable (fun p : hull Γ × Y => ‖f (hullTranslate hδ Γ (z p.2) p.1)‖ ^ 2) (μ.prod ν) := by
  have hm : StronglyMeasurable (fun p : hull Γ × Y => ‖f (hullTranslate hδ Γ (z p.2) p.1)‖ ^ 2) :=
    ((Lp.stronglyMeasurable f).comp_measurable
      ((continuous_hullTranslate hδ Γ).measurable.comp
        ((hz.comp measurable_snd).prodMk measurable_fst))).norm.pow 2
  have hi : Integrable (fun Δ => ‖f Δ‖ ^ 2) μ :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable f)).mp (Lp.memLp f)
  apply (integrable_prod_iff' hm.aestronglyMeasurable).mpr
  constructor
  · exact Filter.Eventually.of_forall fun y => stationary_integrable_comp (hμ (z y))
      (Lp.stronglyMeasurable f |>.norm.pow 2) hi
  · have he : (fun y => ∫ Δ, ‖‖f (hullTranslate hδ Γ (z y) Δ)‖ ^ 2‖ ∂μ) =
        fun _ : Y => ∫ Δ, ‖f Δ‖ ^ 2 ∂μ := by
      funext y
      simp only [Real.norm_eq_abs, abs_pow, abs_norm]
      exact stationary_integral_comp (hμ (z y)) (Lp.stronglyMeasurable f |>.norm.pow 2)
    rw [he]
    exact integrable_const _

section Average
variable {d : ℕ} {δ r M : ℝ} (hδ : 0 < δ)
    (Γ : SeparatedConfiguration d δ) [MeasurableSpace (hull Γ)] [BorelSpace (hull Γ)]
    [CompactSpace (hull Γ)] (μ : Measure (hull Γ)) [IsProbabilityMeasure μ]
    (hμ : ∀ z : Euclidean d, MeasurePreserving (hullTranslate hδ Γ z) μ μ)
    (hr : 2 * r ≤ δ) (b : Euclidean d → ℂ)
    (hbc : Continuous b) (hcompact : HasCompactSupport b)
    (hs : ∀ x, r ≤ ‖x‖ → b x = 0) (hM : 0 ≤ M) (hb : ∀ x, ‖b x‖ ≤ M)

/-- The finite averaged comparison operator in the manuscript. -/
def stationaryComparisonAverage (t : Euclidean d) (R : ℝ) : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ :=
  fejerModulatedOperator (comparisonIntegrand hδ Γ μ hμ hr b hbc hcompact hs hM hb)
    (fun f => (continuous_comparisonIntegrand_apply hδ Γ μ hμ hr b hbc hcompact hs hM hb f).aestronglyMeasurable)
    (integrable_stationaryEnvelope d r M)
    (norm_comparisonIntegrand_le hδ Γ μ hμ hr b hbc hcompact hs hM hb) t R

/-- The finite averaged comparison has its concrete weighted vector integral. -/
theorem stationaryComparisonAverage_apply (t : Euclidean d) {R : ℝ} (hR : 0 < R)
    (f : Lp ℂ 2 μ) :
    stationaryComparisonAverage hδ Γ μ hμ hr b hbc hcompact hs hM hb t R f =
      ∫ y, ((fejerWeight R y : ℂ) * exponential t y) •
        comparisonIntegrand hδ Γ μ hμ hr b hbc hcompact hs hM hb y f :=
  fejerModulatedOperator_apply _ _ _ _ t hR f

/-- Pairing the finite comparison operator is the actual scalar weighted kernel integral. -/
theorem stationaryComparisonAverage_pairing (t : Euclidean d) {R : ℝ} (hR : 0 < R)
    (f g : Lp ℂ 2 μ) :
    inner (𝕜 := ℂ) g (stationaryComparisonAverage hδ Γ μ hμ hr b hbc hcompact hs hM hb t R f) =
      ∫ y, ((fejerWeight R y : ℂ) * exponential t y) *
        inner (𝕜 := ℂ) g (comparisonIntegrand hδ Γ μ hμ hr b hbc hcompact hs hM hb y f) := by
  let A := comparisonIntegrand hδ Γ μ hμ hr b hbc hcompact hs hM hb
  have hi : Integrable (fun y => exponential t y • A y f) :=
    integrable_modulatedOperator A
      (fun f => (continuous_comparisonIntegrand_apply hδ Γ μ hμ hr b hbc hcompact hs hM hb f).aestronglyMeasurable)
      (integrable_stationaryEnvelope d r M)
      (norm_comparisonIntegrand_le hδ Γ μ hμ hr b hbc hcompact hs hM hb) t f
  have hw := integrable_fejerWeight_smul hi hR
  rw [stationaryComparisonAverage_apply hδ Γ μ hμ hr b hbc hcompact hs hM hb t hR]
  simp_rw [← inner_smul_right]
  apply (integral_inner _ g).symm
  simpa only [RCLike.real_smul_eq_coe_smul (K := ℂ), smul_smul] using hw
/-- The actual finite comparison averages converge in operator norm uniformly in modulation. -/
theorem tendsto_stationaryComparisonAverage_error (t : ℝ → Euclidean d) :
    Filter.Tendsto (fun R : ℝ =>
      ‖stationaryComparisonAverage hδ Γ μ hμ hr b hbc hcompact hs hM hb (t R) R -
        stationaryComparison hδ Γ μ hμ hr b hbc hcompact hs hM hb (t R)‖)
      Filter.atTop (nhds 0) :=
  tendsto_fejerModulatedOperator_error _ _ _ _ t
include hr hbc hcompact hs hM hb in
/-- For continuous hull vectors the compact spatial expansion is absolutely integrable. -/
theorem integrable_covariant_bump_box_triple (t : Euclidean d) {R : ℝ} (hR : 0 < R)
    (f g : C(hull Γ, ℂ)) :
    Integrable (fun p : hull Γ × (Euclidean d × Euclidean d) =>
      exponential t (p.2.1 - p.2.2) * bumpKernel p.1.val.carrier b p.2.1 p.2.2 *
        f (hullTranslate hδ Γ p.2.2 p.1) * star (g (hullTranslate hδ Γ p.2.1 p.1)))
      (μ.prod ((volume.restrict (euclideanBox d R)).prod (volume.restrict (euclideanBox d R)))) := by
  letI : IsFiniteMeasure (volume.restrict (euclideanBox d R)) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using (volume_euclideanBox_pos_lt_top d hR).2⟩
  have hq : Continuous (fun p : hull Γ × (Euclidean d × Euclidean d) =>
      bumpKernel p.1.val.carrier b p.2.1 p.2.2) :=
    (continuous_configuration_bumpKernel_joint hδ b hbc hcompact).comp
      ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
  have hf : Continuous (fun p : hull Γ × (Euclidean d × Euclidean d) =>
      f (hullTranslate hδ Γ p.2.2 p.1)) :=
    f.continuous.comp ((continuous_hullTranslate hδ Γ).comp
      ((continuous_snd.comp continuous_snd).prodMk continuous_fst))
  have hg : Continuous (fun p : hull Γ × (Euclidean d × Euclidean d) =>
      star (g (hullTranslate hδ Γ p.2.1 p.1))) :=
    (g.continuous.comp ((continuous_hullTranslate hδ Γ).comp
      ((continuous_fst.comp continuous_snd).prodMk continuous_fst))).star
  have he : Continuous (fun p : hull Γ × (Euclidean d × Euclidean d) =>
      exponential t (p.2.1 - p.2.2)) := by
    unfold exponential
    fun_prop
  apply (integrable_const (M ^ 2 * ‖f‖ * ‖g‖)).mono' (((he.mul hq).mul hf).mul hg).aestronglyMeasurable
  filter_upwards [] with p
  rw [norm_mul, norm_mul, norm_mul, exponential_norm, one_mul, norm_star]
  exact mul_le_mul (mul_le_mul (norm_bumpKernel_le p.1.val.separated hr b hs hM hb _ _)
    (f.norm_coe_le_norm _) (norm_nonneg _) (sq_nonneg M))
    (g.norm_coe_le_norm _) (norm_nonneg _) (mul_nonneg (sq_nonneg M) (norm_nonneg f))

include hμ hr hbc hcompact hs hM hb in
/-- The compact triple expansion is absolutely integrable for all actual L² hull vectors. -/
theorem integrable_covariant_bump_box_triple_Lp (t : Euclidean d) {R : ℝ} (hR : 0 < R)
    (f g : Lp ℂ 2 μ) :
    Integrable (fun p : hull Γ × (Euclidean d × Euclidean d) =>
      exponential t (p.2.1 - p.2.2) * bumpKernel p.1.val.carrier b p.2.1 p.2.2 *
        f (hullTranslate hδ Γ p.2.2 p.1) * star (g (hullTranslate hδ Γ p.2.1 p.1)))
      (μ.prod ((volume.restrict (euclideanBox d R)).prod (volume.restrict (euclideanBox d R)))) := by
  let ν := (volume.restrict (euclideanBox d R)).prod (volume.restrict (euclideanBox d R))
  letI : IsFiniteMeasure (volume.restrict (euclideanBox d R)) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using (volume_euclideanBox_pos_lt_top d hR).2⟩
  have hf := integrable_hull_square_parameters hδ Γ μ hμ ν Prod.snd measurable_snd f
  have hg := integrable_hull_square_parameters hδ Γ μ hμ ν Prod.fst measurable_fst g
  have hq : Continuous (fun p : hull Γ × (Euclidean d × Euclidean d) =>
      bumpKernel p.1.val.carrier b p.2.1 p.2.2) :=
    (continuous_configuration_bumpKernel_joint hδ b hbc hcompact).comp
      ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
  have hfm : StronglyMeasurable (fun p : hull Γ × (Euclidean d × Euclidean d) =>
      f (hullTranslate hδ Γ p.2.2 p.1)) := (Lp.stronglyMeasurable f).comp_measurable
    ((continuous_hullTranslate hδ Γ).measurable.comp
      ((measurable_snd.comp measurable_snd).prodMk measurable_fst))
  have hgm : StronglyMeasurable (fun p : hull Γ × (Euclidean d × Euclidean d) =>
      star (g (hullTranslate hδ Γ p.2.1 p.1))) := continuous_star.comp_stronglyMeasurable ((Lp.stronglyMeasurable g).comp_measurable
    ((continuous_hullTranslate hδ Γ).measurable.comp
      ((measurable_fst.comp measurable_snd).prodMk measurable_fst)))
  have he : Continuous (fun p : hull Γ × (Euclidean d × Euclidean d) =>
      exponential t (p.2.1 - p.2.2)) := by unfold exponential; fun_prop
  apply ((hf.add hg).const_mul (M ^ 2 / 2)).mono'
    (((he.mul hq).stronglyMeasurable.mul hfm).mul hgm).aestronglyMeasurable
  filter_upwards [] with p
  simp only [Pi.mul_apply, Pi.add_apply]
  rw [norm_mul, norm_mul, norm_mul, exponential_norm, one_mul, norm_star]
  have hqbound := norm_bumpKernel_le p.1.val.separated hr b hs hM hb p.2.1 p.2.2
  have hle := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hqbound (norm_nonneg (f (hullTranslate hδ Γ p.2.2 p.1))))
    (norm_nonneg (g (hullTranslate hδ Γ p.2.1 p.1)))
  have hsq := sq_nonneg (‖f (hullTranslate hδ Γ p.2.2 p.1)‖ - ‖g (hullTranslate hδ Γ p.2.1 p.1)‖)
  have hprod := mul_nonneg (sq_nonneg M) hsq
  dsimp only [Prod.fst, Prod.snd] at *
  nlinarith

/-- The expanded scalar averaged bump form is the pairing of the actual finite comparison operator. -/
theorem normalized_averaged_bump_scalar_form (t : Euclidean d) {R : ℝ} (hR : 0 < R)
    (f g : Lp ℂ 2 μ) :
    (volume.real (euclideanBox d R) : ℂ)⁻¹ *
      (∫ v in euclideanBox d R, ∫ w in euclideanBox d R,
        exponential t (v - w) *
          ∫ Δ, bumpKernel Δ.val.carrier b v w * f (hullTranslate hδ Γ w Δ) *
            star (g (hullTranslate hδ Γ v Δ)) ∂μ) =
      inner (𝕜 := ℂ) g (stationaryComparisonAverage hδ Γ μ hμ hr b hbc hcompact hs hM hb t R f) := by
  simp_rw [integral_covariant_bump_pairing_Lp hδ Γ μ hμ hr b hbc hcompact hs hM hb f g]
  let H := fun y => exponential t y *
    inner (𝕜 := ℂ) g (comparisonIntegrand hδ Γ μ hμ hr b hbc hcompact hs hM hb y f)
  have hH : Continuous H :=
    (show Continuous (exponential t) by unfold exponential; fun_prop).mul
      (continuous_const.inner (continuous_comparisonIntegrand_apply hδ Γ μ hμ hr b hbc hcompact hs hM hb f))
  change (volume.real (euclideanBox d R) : ℂ)⁻¹ *
    (∫ v in euclideanBox d R, ∫ w in euclideanBox d R, H (v - w)) = _
  rw [normalized_integral_box_difference hR hH,
    stationaryComparisonAverage_pairing hδ Γ μ hμ hr b hbc hcompact hs hM hb t hR]
  apply integral_congr_ae
  filter_upwards [] with y
  exact (mul_assoc _ _ _).symm
/-- Continuous representatives may be used in the normalized scalar bump form. -/
theorem normalized_averaged_bump_scalar_form_continuous (t : Euclidean d) {R : ℝ} (hR : 0 < R)
    (f g : C(hull Γ, ℂ)) :
    (volume.real (euclideanBox d R) : ℂ)⁻¹ *
      (∫ v in euclideanBox d R, ∫ w in euclideanBox d R,
        exponential t (v - w) *
          ∫ Δ, bumpKernel Δ.val.carrier b v w * f (hullTranslate hδ Γ w Δ) *
            star (g (hullTranslate hδ Γ v Δ)) ∂μ) =
      inner (𝕜 := ℂ) (ContinuousMap.toLp 2 μ ℂ g)
        (stationaryComparisonAverage hδ Γ μ hμ hr b hbc hcompact hs hM hb t R
          (ContinuousMap.toLp 2 μ ℂ f)) := by
  rw [← normalized_averaged_bump_scalar_form hδ Γ μ hμ hr b hbc hcompact hs hM hb t hR]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with v
  apply integral_congr_ae
  filter_upwards [] with w
  congr 1
  apply integral_congr_ae
  filter_upwards [(hμ w).quasiMeasurePreserving.ae (ContinuousMap.coeFn_toLp (p := 2) μ (𝕜 := ℂ) f),
    (hμ v).quasiMeasurePreserving.ae (ContinuousMap.coeFn_toLp (p := 2) μ (𝕜 := ℂ) g)] with Δ hf hg
  rw [hf, hg]
end Average

/-- An arbitrary L² class representing a test has the concrete bump projection pairing. -/
theorem inner_bumpProjection_averagedTest {d : ℕ} {δ r : ℝ}
    {Λ : Set (Euclidean d)} (hΛ : Separated δ Λ) (hδ : 0 < δ) (hr : 2 * r < δ)
    (b : SchwartzMap (Euclidean d) ℂ) (hs : ∀ x, r ≤ ‖x‖ → b x = 0)
    (hn : ‖b.toLp 2 volume‖ = 1) {X : Type*} (T : Euclidean d → X → X)
    (f g : X → ℂ) (Δ : X) (R : ℝ) (t : Euclidean d) (jf jg : FullL2 d)
    (hjf : (jf : Euclidean d → ℂ) =ᵐ[volume] averagedTest R t T f Δ)
    (hjg : (jg : Euclidean d → ℂ) =ᵐ[volume] averagedTest R t T g Δ) :
    inner (𝕜 := ℂ) jg ((isometryRangeProjection (bumpSynthesis hΛ hr b hs hn)).op jf) =
      (volume.real (euclideanBox d R) : ℂ)⁻¹ *
        ∫ v in euclideanBox d R, ∫ w in euclideanBox d R,
          exponential t (v - w) * bumpKernel Λ b v w * f (T w Δ) * star (g (T v Δ)) := by
  have hf : MemLp (averagedTest R t T f Δ) 2 volume := (Lp.memLp jf).ae_eq hjf
  have hg : MemLp (averagedTest R t T g Δ) 2 volume := (Lp.memLp jg).ae_eq hjg
  have hef : jf = hf.toLp (averagedTest R t T f Δ) := Lp.ext (hjf.trans hf.coeFn_toLp.symm)
  have heg : jg = hg.toLp (averagedTest R t T g Δ) := Lp.ext (hjg.trans hg.coeFn_toLp.symm)
  rw [hef, heg]
  exact bump_projection_averagedTest_pairing hΛ hδ hr b hs hn T f g Δ R t hf hg

/-- The hull average of the actual bump projection is the finite comparison operator. -/
theorem integral_bumpProjection_averagedTest {d : ℕ} {δ r M : ℝ} (hδ : 0 < δ)
    (Γ : SeparatedConfiguration d δ) [MeasurableSpace (hull Γ)] [BorelSpace (hull Γ)]
    [CompactSpace (hull Γ)] (μ : Measure (hull Γ)) [IsProbabilityMeasure μ]
    (hμ : ∀ z : Euclidean d, MeasurePreserving (hullTranslate hδ Γ z) μ μ)
    (hr : 2 * r < δ) (b : SchwartzMap (Euclidean d) ℂ)
    (hcompact : HasCompactSupport b) (hs : ∀ x, r ≤ ‖x‖ → b x = 0)
    (hn : ‖b.toLp 2 volume‖ = 1) (hM : 0 ≤ M) (hb : ∀ x, ‖b x‖ ≤ M)
    (t : Euclidean d) {R : ℝ} (hR : 0 < R) (f g : C(hull Γ, ℂ))
    (jf jg : hull Γ → FullL2 d)
    (hjf : ∀ Δ, (jf Δ : Euclidean d → ℂ) =ᵐ[volume] averagedTest R t (hullTranslate hδ Γ) f Δ)
    (hjg : ∀ Δ, (jg Δ : Euclidean d → ℂ) =ᵐ[volume] averagedTest R t (hullTranslate hδ Γ) g Δ) :
    (∫ Δ, inner (𝕜 := ℂ) (jg Δ)
      ((isometryRangeProjection (bumpSynthesis Δ.val.separated hr b hs hn)).op (jf Δ)) ∂μ) =
      inner (𝕜 := ℂ) (ContinuousMap.toLp 2 μ ℂ g)
        (stationaryComparisonAverage hδ Γ μ hμ hr.le b b.continuous hcompact hs hM hb t R
          (ContinuousMap.toLp 2 μ ℂ f)) := by
  have hi := integrable_covariant_bump_box_triple hδ Γ μ hr.le b b.continuous hcompact hs hM hb t hR f g
  simp_rw [inner_bumpProjection_averagedTest _ hδ hr b hs hn (hullTranslate hδ Γ)
    f g _ R t _ _ (hjf _) (hjg _)]
  rw [integral_const_mul, integral_triple_swap μ (volume.restrict (euclideanBox d R))
    (volume.restrict (euclideanBox d R)) hi]
  rw [← normalized_averaged_bump_scalar_form_continuous hδ Γ μ hμ hr.le b b.continuous hcompact hs hM hb t hR]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with v
  apply integral_congr_ae
  filter_upwards [] with w
  simp only [mul_assoc, integral_const_mul]

/-- The actual averaged bump pairing is absolutely integrable on the hull. -/
theorem integrable_bumpProjection_averagedTest {d : ℕ} {δ r M : ℝ} (hδ : 0 < δ)
    (Γ : SeparatedConfiguration d δ) [MeasurableSpace (hull Γ)] [BorelSpace (hull Γ)]
    [CompactSpace (hull Γ)] (μ : Measure (hull Γ)) [IsProbabilityMeasure μ]
    (hr : 2 * r < δ) (b : SchwartzMap (Euclidean d) ℂ)
    (hcompact : HasCompactSupport b) (hs : ∀ x, r ≤ ‖x‖ → b x = 0)
    (hn : ‖b.toLp 2 volume‖ = 1) (hM : 0 ≤ M) (hb : ∀ x, ‖b x‖ ≤ M)
    (t : Euclidean d) {R : ℝ} (hR : 0 < R) (f g : C(hull Γ, ℂ))
    (jf jg : hull Γ → FullL2 d)
    (hjf : ∀ Δ, (jf Δ : Euclidean d → ℂ) =ᵐ[volume] averagedTest R t (hullTranslate hδ Γ) f Δ)
    (hjg : ∀ Δ, (jg Δ : Euclidean d → ℂ) =ᵐ[volume] averagedTest R t (hullTranslate hδ Γ) g Δ) :
    Integrable (fun Δ => inner (𝕜 := ℂ) (jg Δ)
      ((isometryRangeProjection (bumpSynthesis Δ.val.separated hr b hs hn)).op (jf Δ))) μ := by
  have hi := integrable_covariant_bump_box_triple hδ Γ μ hr.le b b.continuous hcompact hs hM hb t hR f g
  apply (hi.integral_prod_left.const_mul ((volume.real (euclideanBox d R) : ℂ)⁻¹)).congr
  filter_upwards [hi.prod_right_ae] with Δ hΔ
  rw [inner_bumpProjection_averagedTest _ hδ hr b hs hn (hullTranslate hδ Γ)
    f g Δ R t _ _ (hjf Δ) (hjg Δ)]
  rw [integral_prod _ hΔ]
/-- The hull average of the actual bump projection is the finite comparison operator. -/
theorem integral_bumpProjection_averagedTest_Lp {d : ℕ} {δ r M : ℝ} (hδ : 0 < δ)
    (Γ : SeparatedConfiguration d δ) [MeasurableSpace (hull Γ)] [BorelSpace (hull Γ)]
    [CompactSpace (hull Γ)] (μ : Measure (hull Γ)) [IsProbabilityMeasure μ]
    (hμ : ∀ z : Euclidean d, MeasurePreserving (hullTranslate hδ Γ z) μ μ)
    (hr : 2 * r < δ) (b : SchwartzMap (Euclidean d) ℂ)
    (hcompact : HasCompactSupport b) (hs : ∀ x, r ≤ ‖x‖ → b x = 0)
    (hn : ‖b.toLp 2 volume‖ = 1) (hM : 0 ≤ M) (hb : ∀ x, ‖b x‖ ≤ M)
    (t : Euclidean d) {R : ℝ} (hR : 0 < R) (f g : Lp ℂ 2 μ)
    (jf jg : hull Γ → FullL2 d)
    (hjf : ∀ᵐ Δ ∂μ, (jf Δ : Euclidean d → ℂ) =ᵐ[volume] averagedTest R t (hullTranslate hδ Γ) f Δ)
    (hjg : ∀ᵐ Δ ∂μ, (jg Δ : Euclidean d → ℂ) =ᵐ[volume] averagedTest R t (hullTranslate hδ Γ) g Δ) :
    (∫ Δ, inner (𝕜 := ℂ) (jg Δ)
      ((isometryRangeProjection (bumpSynthesis Δ.val.separated hr b hs hn)).op (jf Δ)) ∂μ) =
      inner (𝕜 := ℂ) g
        (stationaryComparisonAverage hδ Γ μ hμ hr.le b b.continuous hcompact hs hM hb t R
          f) := by
  have hi := integrable_covariant_bump_box_triple_Lp hδ Γ μ hμ hr.le b b.continuous hcompact hs hM hb t hR f g
  have he : (fun Δ => inner (𝕜 := ℂ) (jg Δ)
      ((isometryRangeProjection (bumpSynthesis Δ.val.separated hr b hs hn)).op (jf Δ))) =ᵐ[μ]
      (fun Δ => (volume.real (euclideanBox d R) : ℂ)⁻¹ *
        ∫ v in euclideanBox d R, ∫ w in euclideanBox d R,
          exponential t (v - w) * bumpKernel Δ.val.carrier b v w *
            f (hullTranslate hδ Γ w Δ) * star (g (hullTranslate hδ Γ v Δ))) := by
    filter_upwards [hjf, hjg] with Δ hf hg
    exact inner_bumpProjection_averagedTest _ hδ hr b hs hn (hullTranslate hδ Γ)
      f g Δ R t _ _ hf hg
  rw [integral_congr_ae he]
  rw [integral_const_mul, integral_triple_swap μ (volume.restrict (euclideanBox d R))
    (volume.restrict (euclideanBox d R)) hi]
  rw [← normalized_averaged_bump_scalar_form hδ Γ μ hμ hr.le b b.continuous hcompact hs hM hb t hR]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with v
  apply integral_congr_ae
  filter_upwards [] with w
  simp only [mul_assoc, integral_const_mul]

/-- The actual averaged bump pairing is absolutely integrable on the hull. -/
theorem integrable_bumpProjection_averagedTest_Lp {d : ℕ} {δ r M : ℝ} (hδ : 0 < δ)
    (Γ : SeparatedConfiguration d δ) [MeasurableSpace (hull Γ)] [BorelSpace (hull Γ)]
    [CompactSpace (hull Γ)] (μ : Measure (hull Γ)) [IsProbabilityMeasure μ]
    (hμ : ∀ z : Euclidean d, MeasurePreserving (hullTranslate hδ Γ z) μ μ)
    (hr : 2 * r < δ) (b : SchwartzMap (Euclidean d) ℂ)
    (hcompact : HasCompactSupport b) (hs : ∀ x, r ≤ ‖x‖ → b x = 0)
    (hn : ‖b.toLp 2 volume‖ = 1) (hM : 0 ≤ M) (hb : ∀ x, ‖b x‖ ≤ M)
    (t : Euclidean d) {R : ℝ} (hR : 0 < R) (f g : Lp ℂ 2 μ)
    (jf jg : hull Γ → FullL2 d)
    (hjf : ∀ᵐ Δ ∂μ, (jf Δ : Euclidean d → ℂ) =ᵐ[volume] averagedTest R t (hullTranslate hδ Γ) f Δ)
    (hjg : ∀ᵐ Δ ∂μ, (jg Δ : Euclidean d → ℂ) =ᵐ[volume] averagedTest R t (hullTranslate hδ Γ) g Δ) :
    Integrable (fun Δ => inner (𝕜 := ℂ) (jg Δ)
      ((isometryRangeProjection (bumpSynthesis Δ.val.separated hr b hs hn)).op (jf Δ))) μ := by
  have hi := integrable_covariant_bump_box_triple_Lp hδ Γ μ hμ hr.le b b.continuous hcompact hs hM hb t hR f g
  apply (hi.integral_prod_left.const_mul ((volume.real (euclideanBox d R) : ℂ)⁻¹)).congr
  filter_upwards [hi.prod_right_ae, hjf, hjg] with Δ hΔ hf hg
  rw [inner_bumpProjection_averagedTest _ hδ hr b hs hn (hullTranslate hδ Γ)
    f g Δ R t _ _ hf hg]
  rw [integral_prod _ hΔ]
end RieszEuclidean.SeparatedConfiguration
