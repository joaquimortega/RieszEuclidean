import RieszEuclidean.Koopman
import RieszEuclidean.FejerKernel
import RieszEuclidean.FejerWeights
import RieszEuclidean.Affine
import Mathlib.MeasureTheory.Integral.Prod
open MeasureTheory Set
namespace RieszEuclidean
variable {X : Type*} [MeasurableSpace X] {μ : Measure X}
/-- A measurable stationary action preserves integrals of actual measurable representatives. -/
theorem stationary_integral_comp {T : X → X} (hT : MeasurePreserving T μ μ)
    {g : X → ℝ} (hg : StronglyMeasurable g) :
    (∫ x, g (T x) ∂μ) = ∫ x, g x ∂μ := by
  have h := integral_map_of_stronglyMeasurable (μ := μ) hT.measurable hg
  rw [hT.map_eq] at h
  exact h.symm
/-- Stationary pullback preserves integrability of a measurable scalar representative. -/
theorem stationary_integrable_comp {T : X → X} (hT : MeasurePreserving T μ μ)
    {g : X → ℝ} (hgm : StronglyMeasurable g) (hg : Integrable g μ) :
    Integrable (fun x => g (T x)) μ := by
  apply (integrable_map_measure hgm.aestronglyMeasurable hT.measurable.aemeasurable).1
  rwa [hT.map_eq]
/-- An integrable weight times a stationary square has an integrable joint representative. -/
theorem integrable_weighted_stationary_square {d : ℕ} [SFinite μ]
    (T : Euclidean d → X → X) (hT : Measurable (fun p : X × Euclidean d => T p.2 p.1))
    (hμ : ∀ v, MeasurePreserving (T v) μ μ) (f : Lp ℂ 2 μ)
    {w : Euclidean d → ℝ} (hwm : StronglyMeasurable w) (hw : Integrable w)
    (hwpos : ∀ v, 0 ≤ w v) :
    Integrable (fun p : X × Euclidean d => w p.2 * ‖f (T p.2 p.1)‖ ^ 2) (μ.prod volume) := by
  have hfm : StronglyMeasurable (fun x => ‖f x‖ ^ 2) := (Lp.stronglyMeasurable f).norm.pow 2
  have hfi : Integrable (fun x => ‖f x‖ ^ 2) μ :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable f)).mp (Lp.memLp f)
  have hm : StronglyMeasurable (fun p : X × Euclidean d => w p.2 * ‖f (T p.2 p.1)‖ ^ 2) :=
    (hwm.comp_measurable measurable_snd).mul (hfm.comp_measurable hT)
  apply (integrable_prod_iff' hm.aestronglyMeasurable).mpr
  constructor
  · exact Filter.Eventually.of_forall fun v => (stationary_integrable_comp (hμ v) hfm hfi).const_mul (w v)
  · have he : (fun v => ∫ x, ‖w v * ‖f (T v x)‖ ^ 2‖ ∂μ) =
        fun v => w v * ∫ x, ‖f x‖ ^ 2 ∂μ := by
      funext v
      simp only [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hwpos v), abs_pow, abs_norm]
      rw [integral_const_mul, stationary_integral_comp (hμ v) hfm]
    rw [he]
    exact hw.mul_const _
/-- Averaging the weighted stationary square gives the product of the two energies. -/
theorem integral_weighted_stationary_square {d : ℕ} [SFinite μ]
    (T : Euclidean d → X → X) (hT : Measurable (fun p : X × Euclidean d => T p.2 p.1))
    (hμ : ∀ v, MeasurePreserving (T v) μ μ) (f : Lp ℂ 2 μ)
    {w : Euclidean d → ℝ} (hwm : StronglyMeasurable w) (hw : Integrable w)
    (hwpos : ∀ v, 0 ≤ w v) :
    (∫ x, (∫ v, w v * ‖f (T v x)‖ ^ 2) ∂μ) = (∫ v, w v) * ∫ x, ‖f x‖ ^ 2 ∂μ := by
  rw [integral_integral_swap (integrable_weighted_stationary_square T hT hμ f hwm hw hwpos)]
  calc
    _ = ∫ v, w v * ∫ x, ‖f x‖ ^ 2 ∂μ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun v => by
        change (∫ x, w v * ‖f (T v x)‖ ^ 2 ∂μ) = w v * ∫ x, ‖f x‖ ^ 2 ∂μ
        rw [integral_const_mul, stationary_integral_comp (hμ v) (g := fun x => ‖f x‖ ^ 2) ((Lp.stronglyMeasurable f).norm.pow 2)]
    _ = _ := integral_mul_const _ _
/-- The scalar box-supported test in the paper, using an actual representative. -/
noncomputable def averagedTest {d : ℕ} (R : ℝ) (t : Euclidean d)
    (T : Euclidean d → X → X) (f : X → ℂ) (x : X) (v : Euclidean d) : ℂ :=
  ((Real.sqrt (volume.real (euclideanBox d R)))⁻¹ : ℝ) *
    (euclideanBox d R).indicator (fun v => exponential (-t) v * f (T v x)) v
/-- The squared box normalization is the normalized indicator density. -/
noncomputable def averagedBoxWeight (d : ℕ) (R : ℝ) : Euclidean d → ℝ :=
  (euclideanBox d R).indicator (fun _ => (volume.real (euclideanBox d R))⁻¹)
omit [MeasurableSpace X] in
/-- Squaring the actual test gives the normalized weighted stationary energy. -/
theorem norm_averagedTest_sq {d : ℕ} (R : ℝ) (t : Euclidean d)
    (T : Euclidean d → X → X) (f : X → ℂ) (x : X) (v : Euclidean d) :
    ‖averagedTest R t T f x v‖ ^ 2 = averagedBoxWeight d R v * ‖f (T v x)‖ ^ 2 := by
  by_cases hv : v ∈ euclideanBox d R
  · simp only [averagedTest, averagedBoxWeight, Set.indicator_of_mem hv, norm_mul,
      Complex.norm_real, Real.norm_eq_abs, abs_inv, abs_of_nonneg (Real.sqrt_nonneg _),
      exponential_norm, one_mul, mul_pow, inv_pow]
    rw [Real.sq_sqrt (show 0 ≤ volume.real (euclideanBox d R) from ENNReal.toReal_nonneg)]
  · simp [averagedTest, averagedBoxWeight, hv]
/-- Joint measurability uses the chosen measurable representative and actual action. -/
theorem measurable_averagedTest {d : ℕ} (R : ℝ) (t : Euclidean d)
    (T : Euclidean d → X → X) (hT : Measurable (fun p : X × Euclidean d => T p.2 p.1))
    {f : X → ℂ} (hf : Measurable f) :
    Measurable (fun p : X × Euclidean d => averagedTest R t T f p.1 p.2) := by
  have he : Measurable (fun p : X × Euclidean d => exponential (-t) p.2 * f (T p.2 p.1)) :=
    ((show Continuous (exponential (-t)) by unfold exponential; fun_prop).measurable.comp measurable_snd).mul
      (hf.comp hT)
  have hi := he.indicator ((measurableSet_euclideanBox d R).preimage measurable_snd)
  convert measurable_const.mul hi using 1
/-- The normalized box weight is measurable. -/
theorem stronglyMeasurable_averagedBoxWeight (d : ℕ) (R : ℝ) :
    StronglyMeasurable (averagedBoxWeight d R) :=
  stronglyMeasurable_const.indicator (measurableSet_euclideanBox d R)
/-- Positive-radius box weights are integrable. -/
theorem integrable_averagedBoxWeight (d : ℕ) {R : ℝ} (hR : 0 < R) :
    Integrable (averagedBoxWeight d R) :=
  (integrable_indicator_iff (measurableSet_euclideanBox d R)).mpr
    (integrableOn_const.mpr (Or.inr (volume_euclideanBox_pos_lt_top d hR).2))
/-- The normalized box weight is nonnegative. -/
theorem averagedBoxWeight_nonneg (d : ℕ) (R : ℝ) (v : Euclidean d) :
    0 ≤ averagedBoxWeight d R v := by
  by_cases hv : v ∈ euclideanBox d R <;>
    simp [averagedBoxWeight, hv, inv_nonneg.mpr ENNReal.toReal_nonneg]
/-- The normalized box weight has unit integral. -/
theorem integral_averagedBoxWeight (d : ℕ) {R : ℝ} (hR : 0 < R) :
    (∫ v, averagedBoxWeight d R v) = 1 := by
  rw [averagedBoxWeight, integral_indicator_const _ (measurableSet_euclideanBox d R), smul_eq_mul]
  exact mul_inv_cancel₀ (ENNReal.toReal_pos (volume_euclideanBox_pos_lt_top d hR).1.ne'
    (volume_euclideanBox_pos_lt_top d hR).2.ne).ne'
/-- The actual scalar tests have integrable joint squared norm. -/
theorem integrable_averagedTest_sq {d : ℕ} [SFinite μ]
    (T : Euclidean d → X → X) (hT : Measurable (fun p : X × Euclidean d => T p.2 p.1))
    (hμ : ∀ v, MeasurePreserving (T v) μ μ) (f : Lp ℂ 2 μ) {R : ℝ} (hR : 0 < R)
    (t : Euclidean d) :
    Integrable (fun p : X × Euclidean d => ‖averagedTest R t T f p.1 p.2‖ ^ 2) (μ.prod volume) := by
  simpa only [norm_averagedTest_sq] using integrable_weighted_stationary_square T hT hμ f
    (stronglyMeasurable_averagedBoxWeight d R) (integrable_averagedBoxWeight d hR)
    (averagedBoxWeight_nonneg d R)
/-- Almost every scalar test is an actual L² function on Euclidean space. -/
theorem ae_memLp_averagedTest {d : ℕ} [SFinite μ]
    (T : Euclidean d → X → X) (hT : Measurable (fun p : X × Euclidean d => T p.2 p.1))
    (hμ : ∀ v, MeasurePreserving (T v) μ μ) (f : Lp ℂ 2 μ) {R : ℝ} (hR : 0 < R)
    (t : Euclidean d) : ∀ᵐ x ∂μ, MemLp (averagedTest R t T f x) 2 := by
  have hi := (integrable_averagedTest_sq T hT hμ f hR t).prod_right_ae
  filter_upwards [hi] with x hx
  have hm := (measurable_averagedTest R t T hT (Lp.stronglyMeasurable f).measurable).comp
    ((measurable_const (a := x)).prodMk measurable_id)
  exact (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mpr hx
/-- Squared L² norms of arbitrary measured-space vectors are their integrated squared norms. -/
theorem integral_sq_norm_lp (f : Lp ℂ 2 μ) : (∫ x, ‖f x‖ ^ 2 ∂μ) = ‖f‖ ^ 2 := by
  have h := congrArg Complex.re (L2.inner_def f f)
  change Complex.reCLM (inner (𝕜 := ℂ) f f) = Complex.reCLM (∫ x, inner (𝕜 := ℂ) (f x) (f x) ∂μ) at h
  rw [← Complex.reCLM.integral_comp_comm (L2.integrable_inner (𝕜 := ℂ) f f)] at h
  simp only [Complex.reCLM_apply, inner_self_eq_norm_sq_to_K] at h
  change ((‖f‖ : ℂ) ^ 2).re = ∫ x, ((‖f x‖ : ℂ) ^ 2).re ∂μ at h
  simpa only [← Complex.ofReal_pow, Complex.ofReal_re] using h.symm
/-- Tonelli and stationarity give exactly the paper's averaged energy identity. -/
theorem integral_averagedTest_energy {d : ℕ} [SFinite μ]
    (T : Euclidean d → X → X) (hT : Measurable (fun p : X × Euclidean d => T p.2 p.1))
    (hμ : ∀ v, MeasurePreserving (T v) μ μ) (f : Lp ℂ 2 μ) {R : ℝ} (hR : 0 < R)
    (t : Euclidean d) : (∫ x, (∫ v, ‖averagedTest R t T f x v‖ ^ 2) ∂μ) = ‖f‖ ^ 2 := by
  simp_rw [norm_averagedTest_sq]
  rw [integral_weighted_stationary_square T hT hμ f
    (stronglyMeasurable_averagedBoxWeight d R) (integrable_averagedBoxWeight d hR)
    (averagedBoxWeight_nonneg d R), integral_averagedBoxWeight d hR, one_mul, integral_sq_norm_lp]
omit [MeasurableSpace X] in
/-- Each scalar test is supported in its actual compact coordinate box. -/
theorem hasCompactSupport_averagedTest {d : ℕ} (R : ℝ) (t : Euclidean d)
    (T : Euclidean d → X → X) (f : X → ℂ) (x : X) :
    HasCompactSupport (averagedTest R t T f x) := by
  apply HasCompactSupport.intro (isCompact_euclideanBox d R)
  intro v hv
  simp [averagedTest, hv]
/-- Changing a Borel representative on a null set leaves almost every scalar test
unchanged almost everywhere in the Euclidean variable. -/
theorem averagedTest_congr_ae {d : ℕ} [SFinite μ]
    (T : Euclidean d → X → X) (hT : Measurable (fun p : X × Euclidean d => T p.2 p.1))
    (hμ : ∀ v, MeasurePreserving (T v) μ μ) {f g : X → ℂ}
    (hf : Measurable f) (hg : Measurable g) (hfg : f =ᵐ[μ] g)
    (R : ℝ) (t : Euclidean d) :
    ∀ᵐ x ∂μ, averagedTest R t T f x =ᵐ[volume] averagedTest R t T g x := by
  have hm : MeasurableSet {p : X × Euclidean d | f (T p.2 p.1) = g (T p.2 p.1)} :=
    measurableSet_eq_fun (hf.comp hT) (hg.comp hT)
  have he : ∀ᵐ x ∂μ, ∀ᵐ v ∂volume, f (T v x) = g (T v x) := by
    apply (Measure.ae_ae_comm hm).mpr
    exact Filter.Eventually.of_forall fun v => (hμ v).quasiMeasurePreserving.ae hfg
  filter_upwards [he] with x hx
  filter_upwards [hx] with v hv
  by_cases hbox : v ∈ euclideanBox d R <;> simp [averagedTest, hbox, hv]
namespace SeparatedConfiguration
/-- The paper's scalar tests on the actual compact hull satisfy joint measurability,
almost-everywhere L² membership, and the normalized averaged energy identity. -/
theorem hull_averagedTest_energy {d : ℕ} {δ : ℝ} (hδ : 0 < δ)
    (Γ : SeparatedConfiguration d δ)
    [MeasurableSpace (hull Γ)] [BorelSpace (hull Γ)]
    (μ : Measure (hull Γ)) [IsProbabilityMeasure μ]
    (hμ : ∀ v, MeasurePreserving (hullTranslate hδ Γ v) μ μ)
    (f : Lp ℂ 2 μ) {R : ℝ} (hR : 0 < R) (t : Euclidean d) :
    Measurable (fun p : hull Γ × Euclidean d =>
      averagedTest R t (hullTranslate hδ Γ) f p.1 p.2) ∧
    (∀ᵐ Δ ∂μ, MemLp (averagedTest R t (hullTranslate hδ Γ) f Δ) 2) ∧
    (∫ Δ, (∫ v, ‖averagedTest R t (hullTranslate hδ Γ) f Δ v‖ ^ 2) ∂μ) = ‖f‖ ^ 2 := by
  have hT : Measurable (fun p : hull Γ × Euclidean d => hullTranslate hδ Γ p.2 p.1) :=
    ((continuous_hullTranslate hδ Γ).comp (continuous_snd.prodMk continuous_fst)).measurable
  exact ⟨measurable_averagedTest R t _ hT (Lp.stronglyMeasurable f).measurable,
    ae_memLp_averagedTest _ hT hμ f hR t, integral_averagedTest_energy _ hT hμ f hR t⟩
end SeparatedConfiguration
end RieszEuclidean
