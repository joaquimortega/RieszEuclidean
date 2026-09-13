import RieszEuclidean.BumpKernelContinuity
import RieszEuclidean.VagueConvergence
import Mathlib.Topology.UniformSpace.HeineCantor
open MeasureTheory Filter Topology
open scoped CompactlySupported
namespace RieszEuclidean
/-- Counting integrals of compactly supported continuous complex tests are actual sums. -/
theorem configurationMeasure_integral_eq_tsum_complex {d : ℕ} {δ : ℝ}
    {Γ : Set (Euclidean d)} (hΓ : Separated δ Γ) (hδ : 0 < δ)
    (f : Euclidean d → ℂ) (hf : Continuous f) (hc : HasCompactSupport f) :
    (∫ x, f x ∂configurationMeasure Γ) = ∑' i : Γ, f i := by
  classical
  letI : Countable Γ := (hΓ.countable hδ).to_subtype
  letI := configurationMeasure_finiteOnCompacts hΓ hδ
  have hi := hf.integrable_of_hasCompactSupport hc (μ := configurationMeasure Γ)
  have him : Integrable (fun i : Γ => f i) Measure.count := by
    exact (integrable_map_measure hf.aestronglyMeasurable measurable_subtype_coe.aemeasurable).mp hi
  rw [configurationMeasure, integral_map measurable_subtype_coe.aemeasurable hf.aestronglyMeasurable,
    integral_countable' him]
  simp [measureReal_def]
/-- Complex compactly supported test integrals depend continuously on the configuration. -/
theorem continuous_configurationMeasure_integral_complex {d : ℕ} {δ : ℝ} (hδ : 0 < δ)
    (f : C_c(Euclidean d, ℂ)) :
    Continuous (fun Γ : SeparatedConfiguration d δ => ∫ x, f x ∂configurationMeasure Γ.carrier) := by
  let fr : C_c(Euclidean d, ℝ) :=
    ⟨⟨fun x => (f x).re, Complex.continuous_re.comp f.continuous⟩,
      f.hasCompactSupport.comp_left (g := Complex.re) rfl⟩
  let fi : C_c(Euclidean d, ℝ) :=
    ⟨⟨fun x => (f x).im, Complex.continuous_im.comp f.continuous⟩,
      f.hasCompactSupport.comp_left (g := Complex.im) rfl⟩
  have hr : Continuous (fun Γ : SeparatedConfiguration d δ =>
      ∫ x, (f x).re ∂configurationMeasure Γ.carrier) :=
    (continuous_apply fr).comp (SeparatedConfiguration.continuous_countingProfile hδ)
  have hi : Continuous (fun Γ : SeparatedConfiguration d δ =>
      ∫ x, (f x).im ∂configurationMeasure Γ.carrier) :=
    (continuous_apply fi).comp (SeparatedConfiguration.continuous_countingProfile hδ)
  have ht := (Complex.continuous_ofReal.comp hr).add
    ((Complex.continuous_ofReal.comp hi).mul (continuous_const (y := Complex.I)))
  convert ht using 1
  funext Γ
  letI := configurationMeasure_finiteOnCompacts Γ.separated hδ
  have hf := f.continuous.integrable_of_hasCompactSupport f.hasCompactSupport
    (μ := configurationMeasure Γ.carrier)
  change (∫ x, f x ∂configurationMeasure Γ.carrier) =
    (↑(∫ x, (f x).re ∂configurationMeasure Γ.carrier) : ℂ) +
      (↑(∫ x, (f x).im ∂configurationMeasure Γ.carrier) : ℂ) * Complex.I
  have hre : (∫ x, (f x).re ∂configurationMeasure Γ.carrier) =
      (∫ x, f x ∂configurationMeasure Γ.carrier).re := integral_re hf
  have him : (∫ x, (f x).im ∂configurationMeasure Γ.carrier) =
      (∫ x, f x ∂configurationMeasure Γ.carrier).im := integral_im hf
  rw [hre, him]
  exact (Complex.re_add_im _).symm
/-- The bump product is a genuine complex compactly supported continuous test. -/
noncomputable def bumpKernelTest {d : ℕ} (b : Euclidean d → ℂ) (hb : Continuous b)
    (hc : HasCompactSupport b) (v w : Euclidean d) : C_c(Euclidean d, ℂ) :=
  ⟨⟨fun x => b (v - x) * star (b (w - x)),
    (hb.comp (continuous_const.sub continuous_id)).mul
      (hb.comp (continuous_const.sub continuous_id)).star⟩,
    (hc.comp_homeomorph (Homeomorph.subLeft v)).mul_right⟩
/-- Counting the bump test is exactly the concrete series kernel. -/
theorem integral_bumpKernelTest {d : ℕ} {δ : ℝ} {Γ : Set (Euclidean d)}
    (hΓ : Separated δ Γ) (hδ : 0 < δ) (b : Euclidean d → ℂ)
    (hb : Continuous b) (hc : HasCompactSupport b) (v w : Euclidean d) :
    (∫ x, bumpKernelTest b hb hc v w x ∂configurationMeasure Γ) = bumpKernel Γ b v w :=
  configurationMeasure_integral_eq_tsum_complex hΓ hδ _
    (bumpKernelTest b hb hc v w).continuous (bumpKernelTest b hb hc v w).hasCompactSupport
/-- For fixed coordinates, the bump kernel varies continuously with the configuration. -/
theorem continuous_configuration_bumpKernel {d : ℕ} {δ : ℝ} (hδ : 0 < δ)
    (b : Euclidean d → ℂ) (hb : Continuous b) (hc : HasCompactSupport b)
    (v w : Euclidean d) :
    Continuous (fun Γ : SeparatedConfiguration d δ => bumpKernel Γ.carrier b v w) := by
  have ht := continuous_configurationMeasure_integral_complex hδ (bumpKernelTest b hb hc v w)
  convert ht using 1
  funext Γ
  exact (integral_bumpKernelTest Γ.separated hδ b hb hc v w).symm
/-- A compactly supported kernel test is jointly continuous in its two coordinates and centre. -/
theorem continuous_bumpKernelTest_family {d : ℕ} (b : Euclidean d → ℂ)
    (hb : Continuous b) :
    Continuous (fun p : (Euclidean d × Euclidean d) × Euclidean d =>
      b (p.1.1 - p.2) * star (b (p.1.2 - p.2))) :=
  (hb.comp (continuous_fst.fst.sub continuous_snd)).mul
    (hb.comp (continuous_fst.snd.sub continuous_snd)).star

/-- The concrete bump kernel is jointly continuous in configuration and both coordinates. -/
theorem continuous_configuration_bumpKernel_joint {d : ℕ} {δ : ℝ} (hδ : 0 < δ)
    (b : Euclidean d → ℂ) (hb : Continuous b) (hc : HasCompactSupport b) :
    Continuous (fun p : SeparatedConfiguration d δ × (Euclidean d × Euclidean d) =>
      bumpKernel p.1.carrier b p.2.1 p.2.2) := by
  apply SeqContinuous.continuous
  intro s p hsp
  let Γ := fun n => (s n).1
  let q := fun n => (s n).2
  let q₀ := p.2
  let F := fun q : Euclidean d × Euclidean d => bumpKernelTest b hb hc q.1 q.2
  obtain ⟨r, _, hr⟩ := hc.isBounded.subset_ball_lt 0 (0 : Euclidean d)
  have hbzero : ∀ x, r ≤ ‖x‖ → b x = 0 := by
    intro x hx
    by_contra hbx
    have hlt : ‖x‖ < r := by simpa using hr (subset_tsupport b hbx)
    exact (not_lt_of_ge hx) hlt
  let K := Metric.closedBall q₀.1 (r + 1)
  have hK : IsCompact K := isCompact_closedBall _ _
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  obtain ⟨N, hN⟩ := configurationMeasure_uniform_compact_bound hδ hK
  have hsup : ∀ q : Euclidean d × Euclidean d, dist q.1 q₀.1 < 1 →
      ∀ x, x ∉ K → F q x = 0 := by
    intro q hq x hx
    have hfar : r + 1 < dist x q₀.1 := lt_of_not_ge hx
    have hn : r ≤ ‖q.1 - x‖ := by
      have ht := dist_triangle x q.1 q₀.1
      rw [dist_comm x q.1, dist_eq_norm q.1 x] at ht
      linarith
    change b (q.1 - x) * star (b (q.2 - x)) = 0
    rw [hbzero _ hn, zero_mul]
  have hu : TendstoUniformly (fun q : Euclidean d × Euclidean d =>
      fun x : K => F q x) (fun x : K => F q₀ x) (𝓝 q₀) := by
    apply Continuous.tendstoUniformly
    exact (continuous_bumpKernelTest_family b hb).comp
      (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
  have hq : Tendsto q atTop (𝓝 q₀) := hsp.snd_nhds
  have hnhood : ∀ᶠ n in atTop, dist (q n).1 q₀.1 < 1 :=
    hq.fst_nhds (Metric.ball_mem_nhds q₀.1 zero_lt_one)
  have hz : Tendsto (fun n => (∫ x, F (q n) x ∂configurationMeasure (Γ n).carrier) -
      ∫ x, F q₀ x ∂configurationMeasure (Γ n).carrier) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply Metric.tendsto_atTop.mpr
    intro ε hε
    let η := ε / (N + 1 : ℝ)
    have hη : 0 < η := div_pos hε (by positivity)
    have he := hq (Metric.tendstoUniformly_iff.mp hu η hη)
    obtain ⟨n₀, hn₀⟩ := eventually_atTop.mp (hnhood.and he)
    refine ⟨n₀, fun n hn => ?_⟩
    let μ := configurationMeasure (Γ n).carrier
    letI := configurationMeasure_finiteOnCompacts (Γ n).separated hδ
    have hi₁ : Integrable (fun x => F (q n) x) μ :=
      (F (q n)).continuous.integrable_of_hasCompactSupport
      (F (q n)).hasCompactSupport (μ := μ)
    have hi₀ : Integrable (fun x => F q₀ x) μ :=
      (F q₀).continuous.integrable_of_hasCompactSupport
      (F q₀).hasCompactSupport (μ := μ)
    have hm : μ.real K ≤ N := by
      have hh := ENNReal.toReal_mono (by finiteness : (N : ENNReal) ≠ ⊤)
        (hN (Γ n).carrier (Γ n).separated)
      simpa only [measureReal_def, ENNReal.toReal_natCast] using hh
    have hbd : ‖(∫ x, F (q n) x ∂μ) - ∫ x, F q₀ x ∂μ‖ ≤ η * N := by
      rw [← integral_sub hi₁ hi₀,
        ← setIntegral_eq_integral_of_forall_compl_eq_zero (s := K) (by
          intro x hx
          rw [hsup (q n) (hn₀ n hn).1 x hx, hsup q₀ (by simp) x hx, _root_.sub_self])]
      apply (norm_setIntegral_le_of_norm_le_const hK.measure_lt_top ?_).trans
        (mul_le_mul_of_nonneg_left hm hη.le)
      intro x hx
      have hh := (hn₀ n hn).2 ⟨x, hx⟩
      simpa only [dist_eq_norm, norm_sub_rev] using hh.le
    have hsmall : η * N < ε := by
      dsimp [η]
      have hd : (N : ℝ) + 1 ≠ 0 := by positivity
      have hh := div_mul_cancel₀ ε hd
      nlinarith
    simpa only [dist_zero_right, norm_norm] using hbd.trans_lt hsmall
  have hfixed := (continuous_configurationMeasure_integral_complex hδ (F q₀)).tendsto p.1
  have htotal := hz.add (hfixed.comp hsp.fst_nhds)
  have ht : Tendsto (fun n => ∫ x, F (q n) x ∂configurationMeasure (Γ n).carrier)
      atTop (𝓝 (∫ x, F q₀ x ∂configurationMeasure p.1.carrier)) := by
    simpa only [Function.comp_def, Γ, sub_add_cancel, zero_add] using htotal
  convert ht using 1
  · funext n
    exact (integral_bumpKernelTest (Γ n).separated hδ b hb hc (q n).1 (q n).2).symm
  · congr 1
    exact (integral_bumpKernelTest p.1.separated hδ b hb hc q₀.1 q₀.2).symm
end RieszEuclidean
