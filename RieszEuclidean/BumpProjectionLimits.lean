import RieszEuclidean.ConfigurationKernel
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import RieszEuclidean.BumpSynthesis
import RieszEuclidean.BumpKernelProjection
import RieszEuclidean.SeparatedConfigurations
open MeasureTheory
namespace RieszEuclidean
/-- Synthesis analysis coefficients are the actual inner products with family vectors. -/
theorem orthonormalSynthesis_adjoint_apply {ι H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] {v : ι → H} (hv : Orthonormal ℂ v)
    (f : H) (i : ι) :
    (orthonormalSynthesis hv).toContinuousLinearMap.adjoint f i = inner (𝕜 := ℂ) (v i) f := by
  classical
  have hi := (orthonormalSynthesis hv).toContinuousLinearMap.adjoint_inner_right
    (lp.single 2 i 1) f
  change inner (𝕜 := ℂ) (lp.single 2 i 1)
    ((orthonormalSynthesis hv).toContinuousLinearMap.adjoint f) =
      inner (𝕜 := ℂ) (orthonormalSynthesis hv (lp.single 2 i 1)) f at hi
  rw [orthonormalSynthesis_single hv] at hi
  simpa only [lp.inner_single_left, RCLike.inner_apply, map_one, mul_one] using hi
/-- Finitely supported analysis coefficients give a finite expansion of the actual range projection. -/
theorem isometryRangeProjection_eq_sum_of_coefficients {ι H : Type}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {v : ι → H} (hv : Orthonormal ℂ v) (f : H) (s : Finset ι)
    (hs : ∀ i, i ∉ s → inner (𝕜 := ℂ) (v i) f = 0) :
    (isometryRangeProjection (orthonormalSynthesis hv)).op f =
      ∑ i ∈ s, inner (𝕜 := ℂ) (v i) f • v i := by
  classical
  have hc : (orthonormalSynthesis hv).toContinuousLinearMap.adjoint f =
      ∑ i ∈ s, inner (𝕜 := ℂ) (v i) f • lp.single 2 i 1 := by
    ext i
    rw [orthonormalSynthesis_adjoint_apply]
    simp only [lp.coeFn_sum, Finset.sum_apply, lp.coeFn_smul, Pi.smul_apply,
      lp.single_apply, smul_eq_mul, Pi.single_apply]
    by_cases hi : i ∈ s
    · simp [hi]
    · simp [hi, hs i hi]
  change orthonormalSynthesis hv ((orthonormalSynthesis hv).toContinuousLinearMap.adjoint f) = _
  rw [hc, _root_.map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_smul, orthonormalSynthesis_single]
/-- The translated bump coefficient is its actual scalar integral against a Schwartz input. -/
theorem translated_bump_inner_schwartz {d : ℕ} (b g : SchwartzMap (Euclidean d) ℂ)
    (i : Euclidean d) :
    inner (𝕜 := ℂ) (translationL2 (-i) (b.toLp 2 volume)) (g.toLp 2 volume) =
      ∫ x, star (b (x - i)) * g x := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [translated_bump_coe b i, g.coeFn_toLp 2 volume] with x hx hg
  rw [hx, hg]
  simp [RCLike.inner_apply, mul_comm]

/-- Compact support of the input forces only finitely many bump analysis coefficients to survive. -/
theorem finite_bump_coefficients_schwartz {d : ℕ} {δ r : ℝ} {Γ : Set (Euclidean d)}
    (hΓ : Separated δ Γ) (hδ : 0 < δ) (b g : SchwartzMap (Euclidean d) ℂ)
    (hs : ∀ x, r ≤ ‖x‖ → b x = 0) (hg : HasCompactSupport g) :
    ∃ s : Finset Γ, ∀ i : Γ, i ∉ s →
      inner (𝕜 := ℂ) (translationL2 (-(i : Euclidean d)) (b.toLp 2 volume))
        (g.toLp 2 volume) = 0 := by
  classical
  obtain ⟨R, _, hR⟩ := hg.isBounded.subset_ball_lt 0 (0 : Euclidean d)
  have hf := (hΓ.finite_inter_compact hδ (isCompact_closedBall (0 : Euclidean d)
    (R + r + 1))).preimage (f := fun i : Γ => (i : Euclidean d)) Subtype.val_injective.injOn
  refine ⟨hf.toFinset, ?_⟩
  intro i hi
  have hn : R + r + 1 < ‖(i : Euclidean d)‖ := by
    have hn' : ¬‖(i : Euclidean d)‖ ≤ R + r + 1 := by
      intro hn
      exact hi (hf.mem_toFinset.mpr ⟨i.property, by simpa using hn⟩)
    exact lt_of_not_ge hn'
  rw [translated_bump_inner_schwartz]
  apply integral_eq_zero_of_ae
  filter_upwards [] with x
  by_cases hx : g x = 0
  · simp [hx]
  · have hxR : ‖x‖ < R := by simpa using hR (subset_tsupport g hx)
    have hb : b (x - i) = 0 := by
      apply hs
      have ht := norm_sub_norm_le (i : Euclidean d) x
      rw [norm_sub_rev (i : Euclidean d) x] at ht
      linarith
    simp [hb]

/-- The actual synthesis projection of a compactly supported Schwartz function has a finite expansion. -/
theorem bump_projection_schwartz_finite_expansion {d : ℕ} {δ r : ℝ}
    {Γ : Set (Euclidean d)} (hΓ : Separated δ Γ) (hδ : 0 < δ) (hr : 2 * r < δ)
    (b g : SchwartzMap (Euclidean d) ℂ) (hs : ∀ x, r ≤ ‖x‖ → b x = 0)
    (hn : ‖b.toLp 2 volume‖ = 1) (hg : HasCompactSupport g) :
    ∃ s : Finset Γ,
      (isometryRangeProjection (bumpSynthesis hΓ hr b hs hn)).op (g.toLp 2 volume) =
        ∑ i ∈ s, (∫ x, star (b (x - i)) * g x) •
          translationL2 (-(i : Euclidean d)) (b.toLp 2 volume) := by
  obtain ⟨s, hcoeff⟩ := finite_bump_coefficients_schwartz hΓ hδ b g hs hg
  refine ⟨s, ?_⟩
  have he := isometryRangeProjection_eq_sum_of_coefficients
    (translated_bumps_orthonormal hΓ hr b hs hn) (g.toLp 2 volume) s hcoeff
  simpa only [bumpSynthesis, translated_bump_inner_schwartz] using he
/-- Finite sums of translated bump vectors have the expected pointwise representative. -/
theorem finite_bump_sum_coe {d : ℕ} {ι : Type} (s : Finset ι)
    (c : ι → ℂ) (p : ι → Euclidean d) (b : SchwartzMap (Euclidean d) ℂ) :
    ((∑ i ∈ s, c i • translationL2 (-(p i)) (b.toLp 2 volume) : FullL2 d) :
      Euclidean d → ℂ) =ᵐ[volume] fun x => ∑ i ∈ s, c i * b (x - p i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (Lp.coeFn_zero ℂ 2 volume)
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    filter_upwards [Lp.coeFn_add (c i • translationL2 (-(p i)) (b.toLp 2 volume))
      (∑ j ∈ s, c j • translationL2 (-(p j)) (b.toLp 2 volume)),
      Lp.coeFn_smul (c i) (translationL2 (-(p i)) (b.toLp 2 volume)),
      translated_bump_coe b (p i), ih] with x hx hc hb ihx
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hx hc
    rw [hx, hc, hb, ihx]

/-- A finite coefficient expansion agrees pointwise with the actual kernel integral. -/
theorem finite_bump_sum_eq_kernel_integral {d : ℕ} {δ r : ℝ} {Γ : Set (Euclidean d)}
    (hΓ : Separated δ Γ) (hr : 2 * r ≤ δ) (b : Euclidean d → ℂ)
    (hs : ∀ x, r ≤ ‖x‖ → b x = 0) (g : Euclidean d → ℂ) (s : Finset Γ)
    (hc : ∀ i : Γ, i ∉ s → (∫ x, star (b (x - i)) * g x) = 0) (v : Euclidean d) :
    (∑ i ∈ s, (∫ x, star (b (x - i)) * g x) * b (v - i)) =
      ∫ w, bumpKernel Γ b v w * g w := by
  classical
  rw [← tsum_eq_sum (s := s) (fun i hi => by rw [hc i hi, zero_mul])]
  by_cases he : ∃ i : Γ, b (v - i) ≠ 0
  · obtain ⟨i, hi⟩ := he
    rw [tsum_eq_single i (fun j hji => by
      have hj : b (v - j) = 0 := by
        by_contra hj
        exact hji (bump_active_unique hΓ hr b hs hj hi)
      rw [hj, mul_zero])]
    simp only [bumpKernel_eq_single hΓ hr b hs _ i hi, mul_assoc]
    rw [integral_const_mul, mul_comm]
  · have hz : ∀ i : Γ, b (v - i) = 0 := by simpa using he
    simp only [hz, mul_zero, tsum_zero, bumpKernel_eq_zero_of_no_active Γ b hz,
      zero_mul, integral_zero]

/-- On compactly supported Schwartz inputs, the actual synthesis projection has kernel qΓ. -/
theorem bump_projection_schwartz_kernel {d : ℕ} {δ r : ℝ}
    {Γ : Set (Euclidean d)} (hΓ : Separated δ Γ) (hδ : 0 < δ) (hr : 2 * r < δ)
    (b g : SchwartzMap (Euclidean d) ℂ) (hs : ∀ x, r ≤ ‖x‖ → b x = 0)
    (hn : ‖b.toLp 2 volume‖ = 1) (hg : HasCompactSupport g) :
    ((isometryRangeProjection (bumpSynthesis hΓ hr b hs hn)).op (g.toLp 2 volume) :
      Euclidean d → ℂ) =ᵐ[volume] fun v => ∫ w, bumpKernel Γ b v w * g w := by
  obtain ⟨s, hcoeff⟩ := finite_bump_coefficients_schwartz hΓ hδ b g hs hg
  have he := isometryRangeProjection_eq_sum_of_coefficients
    (translated_bumps_orthonormal hΓ hr b hs hn) (g.toLp 2 volume) s hcoeff
  change (isometryRangeProjection (bumpSynthesis hΓ hr b hs hn)).op (g.toLp 2 volume) = _ at he
  rw [he]
  have hae := finite_bump_sum_coe s
    (fun i : Γ => inner (𝕜 := ℂ) (translationL2 (-(i : Euclidean d)) (b.toLp 2 volume))
      (g.toLp 2 volume)) (fun i : Γ => (i : Euclidean d)) b
  filter_upwards [hae] with v hv
  rw [hv]
  simp only [translated_bump_inner_schwartz]
  exact finite_bump_sum_eq_kernel_integral hΓ hr.le b hs g s
    (fun i hi => by simpa only [translated_bump_inner_schwartz] using hcoeff i hi) v
/-- A support-radius bound supplies compact support for the actual bump. -/
theorem bump_hasCompactSupport_of_radius {d : ℕ} {r : ℝ} (b : Euclidean d → ℂ)
    (hs : ∀ x, r ≤ ‖x‖ → b x = 0) : HasCompactSupport b := by
  apply HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : Euclidean d) r)
  intro x hx
  have hn : ‖x‖ < r := lt_of_not_ge (fun hn => hx (hs x hn))
  simpa using hn.le

/-- Kernel integration against an integrable input is absolutely integrable at every output point. -/
theorem integrable_bumpKernel_apply {d : ℕ} {δ r M : ℝ} {Γ : Set (Euclidean d)}
    (hΓ : Separated δ Γ) (hδ : 0 < δ) (hr : 2 * r ≤ δ)
    (b : Euclidean d → ℂ) (hb : Continuous b)
    (hs : ∀ x, r ≤ ‖x‖ → b x = 0) (hM : 0 ≤ M) (hbound : ∀ x, ‖b x‖ ≤ M)
    {g : Euclidean d → ℂ} (hg : Integrable g) (v : Euclidean d) :
    Integrable (fun w => bumpKernel Γ b v w * g w) := by
  apply (hg.norm.const_mul (M ^ 2)).mono'
    (((continuous_bumpKernel hΓ hδ b hb hs).comp
      (continuous_const.prodMk continuous_id)).aestronglyMeasurable.mul hg.aestronglyMeasurable)
  filter_upwards [] with w
  change ‖bumpKernel Γ b v w * g w‖ ≤ M ^ 2 * ‖g w‖
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (norm_bumpKernel_le hΓ hr b hs hM hbound v w) (norm_nonneg _)

/-- Beurling configuration convergence gives pointwise convergence of actual kernel integrals. -/
theorem tendsto_bumpKernel_integral {d : ℕ} {δ r M : ℝ} {ι : Type*}
    {l : Filter ι} [l.IsCountablyGenerated]
    (hδ : 0 < δ) (hr : 2 * r ≤ δ) (b : Euclidean d → ℂ) (hb : Continuous b)
    (hs : ∀ x, r ≤ ‖x‖ → b x = 0) (hM : 0 ≤ M) (hbound : ∀ x, ‖b x‖ ≤ M)
    {Γ : ι → SeparatedConfiguration d δ} {Γ₀ : SeparatedConfiguration d δ}
    (hΓ : Filter.Tendsto Γ l (nhds Γ₀)) {g : Euclidean d → ℂ} (hg : Integrable g)
    (v : Euclidean d) :
    Filter.Tendsto (fun i => ∫ w, bumpKernel (Γ i).carrier b v w * g w) l
      (nhds (∫ w, bumpKernel Γ₀.carrier b v w * g w)) := by
  apply tendsto_integral_filter_of_dominated_convergence (fun w => M ^ 2 * ‖g w‖)
  · filter_upwards [] with i
    exact (integrable_bumpKernel_apply (Γ i).separated hδ hr b hb hs hM hbound hg v).aestronglyMeasurable
  · filter_upwards [] with i
    filter_upwards [] with w
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right
      (norm_bumpKernel_le (Γ i).separated hr b hs hM hbound v w) (norm_nonneg _)
  · exact hg.norm.const_mul (M ^ 2)
  · filter_upwards [] with w
    exact (((continuous_configuration_bumpKernel hδ b hb
      (bump_hasCompactSupport_of_radius b hs) v w).tendsto Γ₀).comp hΓ).mul_const (g w)
/-- The L² norm is the integral of the squared modulus of its representative. -/
theorem fullL2_norm_sq_integral {d : ℕ} (f : FullL2 d) :
    ‖f‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 := by
  rw [norm_sq_eq_re_inner (𝕜 := ℂ), L2.inner_def]
  have he := integral_re (L2.integrable_inner (𝕜 := ℂ) f f)
  rw [← he]
  apply integral_congr_ae
  filter_upwards [] with x
  exact (norm_sq_eq_re_inner (𝕜 := ℂ) (f x)).symm

/-- Kernel integration has a uniform pointwise bound in terms of the input L¹ norm. -/
theorem norm_bumpKernel_integral_le {d : ℕ} {δ r M : ℝ} {Γ : Set (Euclidean d)}
    (hΓ : Separated δ Γ) (hr : 2 * r ≤ δ) (b : Euclidean d → ℂ)
    (hs : ∀ x, r ≤ ‖x‖ → b x = 0) (hM : 0 ≤ M) (hbound : ∀ x, ‖b x‖ ≤ M)
    {g : Euclidean d → ℂ} (hg : Integrable g) (v : Euclidean d) :
    ‖∫ w, bumpKernel Γ b v w * g w‖ ≤ M ^ 2 * ∫ w, ‖g w‖ := by
  calc
    ‖∫ w, bumpKernel Γ b v w * g w‖ ≤ ∫ w, M ^ 2 * ‖g w‖ := by
      apply norm_integral_le_of_norm_le (hg.norm.const_mul (M ^ 2))
      filter_upwards [] with w
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (norm_bumpKernel_le hΓ hr b hs hM hbound v w)
        (norm_nonneg _)
    _ = M ^ 2 * ∫ w, ‖g w‖ := integral_const_mul _ _

/-- Compact input support and finite kernel propagation give a common compact output support. -/
theorem bumpKernel_integral_eq_zero_of_radius {d : ℕ} {r R : ℝ}
    (Γ : Set (Euclidean d)) (b g : Euclidean d → ℂ)
    (hs : ∀ x, r ≤ ‖x‖ → b x = 0) (hg : ∀ x, R ≤ ‖x‖ → g x = 0)
    {v : Euclidean d} (hv : R + 2 * r < ‖v‖) :
    (∫ w, bumpKernel Γ b v w * g w) = 0 := by
  apply integral_eq_zero_of_ae
  filter_upwards [] with w
  by_cases hw : g w = 0
  · simp [hw]
  · have hwR : ‖w‖ < R := lt_of_not_ge (fun hn => hw (hg _ hn))
    have hd : 2 * r < ‖v - w‖ := by
      have ht := norm_sub_norm_le v w
      linarith
    simp only [bumpKernel_eq_zero_of_two_mul_lt Γ b hs hd, zero_mul, Pi.zero_apply]
/-- The actual bump projections converge strongly on compactly supported Schwartz inputs. -/
theorem bump_projection_tendsto_compact_schwartz {d : ℕ} {δ r : ℝ}
    (hδ : 0 < δ) (hr : 2 * r < δ) (b g : SchwartzMap (Euclidean d) ℂ)
    (hs : ∀ x, r ≤ ‖x‖ → b x = 0) (hn : ‖b.toLp 2 volume‖ = 1)
    (hg : HasCompactSupport g) {Γ : ℕ → SeparatedConfiguration d δ}
    {Γ₀ : SeparatedConfiguration d δ} (hΓ : Filter.Tendsto Γ Filter.atTop (nhds Γ₀)) :
    Filter.Tendsto (fun n => (isometryRangeProjection
      (bumpSynthesis (Γ n).separated hr b hs hn)).op (g.toLp 2 volume)) Filter.atTop
      (nhds ((isometryRangeProjection (bumpSynthesis Γ₀.separated hr b hs hn)).op
        (g.toLp 2 volume))) := by
  classical
  let Q := fun Δ : SeparatedConfiguration d δ =>
    (isometryRangeProjection (bumpSynthesis Δ.separated hr b hs hn)).op (g.toLp 2 volume)
  let F := fun Δ : SeparatedConfiguration d δ => fun v => ∫ w, bumpKernel Δ.carrier b v w * g w
  have hrep : ∀ Δ, (Q Δ : Euclidean d → ℂ) =ᵐ[volume] F Δ :=
    fun Δ => bump_projection_schwartz_kernel Δ.separated hδ hr b g hs hn hg
  obtain ⟨M, hM⟩ := (bump_hasCompactSupport_of_radius b hs).exists_bound_of_continuous b.continuous
  have hM0 : 0 ≤ M := (norm_nonneg (b 0)).trans (hM 0)
  let C := M ^ 2 * ∫ w, ‖g w‖
  have hbound : ∀ Δ v, ‖F Δ v‖ ≤ C := fun Δ v =>
    norm_bumpKernel_integral_le Δ.separated hr.le b hs hM0 hM g.integrable v
  obtain ⟨R, _, hR⟩ := hg.isBounded.subset_ball_lt 0 (0 : Euclidean d)
  have hgzero : ∀ x, R ≤ ‖x‖ → g x = 0 := by
    intro x hx
    by_contra hxg
    have ht : ‖x‖ < R := by simpa using hR (subset_tsupport g hxg)
    exact (not_lt_of_ge hx) ht
  let K := Metric.closedBall (0 : Euclidean d) (R + 2 * r)
  have hzero : ∀ Δ v, v ∉ K → F Δ v = 0 := by
    intro Δ v hv
    apply bumpKernel_integral_eq_zero_of_radius Δ.carrier b g hs hgzero
    exact lt_of_not_ge (by simpa [K] using hv)
  have hmeas : ∀ Δ, StronglyMeasurable (F Δ) := by
    intro Δ
    apply StronglyMeasurable.integral_prod_right
    exact ((continuous_bumpKernel Δ.separated hδ b b.continuous hs).mul
      (g.continuous.comp continuous_snd)).stronglyMeasurable
  have hpoint : ∀ v, Filter.Tendsto (fun n => F (Γ n) v) Filter.atTop (nhds (F Γ₀ v)) :=
    tendsto_bumpKernel_integral hδ hr.le b b.continuous hs hM0 hM hΓ g.integrable
  have ht : Filter.Tendsto (fun n => ∫ v, ‖F (Γ n) v - F Γ₀ v‖ ^ 2) Filter.atTop (nhds 0) := by
    have hh := tendsto_integral_of_dominated_convergence
      (μ := volume) (F := fun n v => ‖F (Γ n) v - F Γ₀ v‖ ^ 2)
      (f := fun _ : Euclidean d => (0 : ℝ)) (K.indicator (fun _ => (2 * C) ^ 2))
    apply (by simpa only [integral_zero] using hh) <;> clear hh
    · intro n
      exact ((hmeas (Γ n)).sub (hmeas Γ₀)).norm.pow 2 |>.aestronglyMeasurable
    · apply (integrable_indicator_iff (Metric.isClosed_closedBall.measurableSet)).mpr
      exact integrableOn_const.mpr (Or.inr (isCompact_closedBall _ _).measure_lt_top)
    · intro n
      filter_upwards [] with v
      change ‖‖F (Γ n) v - F Γ₀ v‖ ^ 2‖ ≤ K.indicator (fun _ => (2 * C) ^ 2) v
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      by_cases hv : v ∈ K
      · rw [Set.indicator_of_mem hv]
        have hd := norm_sub_le (F (Γ n) v) (F Γ₀ v)
        have h1 := hbound (Γ n) v
        have h2 := hbound Γ₀ v
        nlinarith [norm_nonneg (F (Γ n) v - F Γ₀ v)]
      · simp only [Set.indicator_of_not_mem hv, hzero _ _ hv, _root_.sub_self, norm_zero,
          zero_pow (by decide : 2 ≠ 0), le_refl]
    · filter_upwards [] with v
      simpa using ((hpoint v).sub (tendsto_const_nhds (x := F Γ₀ v))).norm.pow 2
  have he : ∀ n, ‖Q (Γ n) - Q Γ₀‖ ^ 2 = ∫ v, ‖F (Γ n) v - F Γ₀ v‖ ^ 2 := by
    intro n
    rw [fullL2_norm_sq_integral]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub (Q (Γ n)) (Q Γ₀), hrep (Γ n), hrep Γ₀] with v hv h1 h2
    simp only [Pi.sub_apply] at hv
    rw [hv, h1, h2]
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hs' := ht.congr' (Filter.Eventually.of_forall fun n => (he n).symm)
  have hsqrt := Real.continuous_sqrt.continuousAt.tendsto.comp hs'
  simpa only [Function.comp_def, Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using hsqrt
open Metric Set Function
open scoped ENNReal
/-- Compactly supported Schwartz approximation retains the support property. -/
theorem compact_exists_compactSchwartz_eLpNorm_lt {d : ℕ} {f : Euclidean d → ℂ}
    (hf : Continuous f) (hs : HasCompactSupport f) {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ g : SchwartzMap (Euclidean d) ℂ, HasCompactSupport g ∧ eLpNorm (f - (g : Euclidean d → ℂ)) 2 volume < ε := by
  let K := Metric.cthickening 1 (tsupport f)
  have hK : IsCompact K := hs.cthickening
  have hfinite : volume K ^ (1 / (2 : ℝ)) ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg (by positivity) hK.measure_lt_top.ne
  obtain ⟨η, hη, hηε⟩ := ENNReal.exists_nnreal_pos_mul_lt hfinite hε
  obtain ⟨g, hg, hgs, hsupport, happrox⟩ :=
    smooth_compact_uniform_approx hf hs (show 0 < (η : ℝ) from hη)
  refine ⟨compactSchwartz g hg hgs, hgs, ?_⟩
  have hfs : support f ⊆ K :=
    (subset_tsupport f).trans (Metric.self_subset_cthickening (tsupport f))
  have hdiff : support (f - g) ⊆ K :=
    (support_sub f g).trans (union_subset hfs hsupport)
  have hb := eLpNorm_two_le_of_support hK.measurableSet hdiff
    (C := (η : ℝ)) (fun x => by
      simpa only [Pi.sub_apply, ← dist_eq_norm, dist_comm] using (happrox x).le)
  exact hb.trans_lt (by simpa only [ENNReal.ofReal_coe_nnreal, mul_comm] using hηε)

/-- Schwartz functions approximate every Euclidean L² function in the L² seminorm. -/
theorem memLp_exists_compactSchwartz_eLpNorm_lt {d : ℕ} {f : Euclidean d → ℂ}
    (hf : MemLp f 2 volume) {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ g : SchwartzMap (Euclidean d) ℂ, HasCompactSupport g ∧
      eLpNorm (f - (g : Euclidean d → ℂ)) 2 volume < ε := by
  obtain ⟨η, hη, hηε⟩ := ENNReal.exists_nnreal_pos_mul_lt (a := 2) (by norm_num) hε
  have hη0 : (η : ℝ≥0∞) ≠ 0 := by exact_mod_cast hη.ne'
  obtain ⟨c, hcs, hfc, hc, hcm⟩ :=
    hf.exists_hasCompactSupport_eLpNorm_sub_le (by norm_num) hη0
  obtain ⟨g, hgs, hcg⟩ := compact_exists_compactSchwartz_eLpNorm_lt hc hcs hη0
  refine ⟨g, hgs, ?_⟩
  have hsum := eLpNorm_add_le (hf.aestronglyMeasurable.sub hcm.aestronglyMeasurable)
    (hcm.aestronglyMeasurable.sub g.continuous.aestronglyMeasurable) (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have heq : (f - c) + (c - (g : Euclidean d → ℂ)) = f - (g : Euclidean d → ℂ) := by abel
  rw [heq] at hsum
  calc
    eLpNorm (f - (g : Euclidean d → ℂ)) 2 volume
        ≤ eLpNorm (f - c) 2 volume + eLpNorm (c - (g : Euclidean d → ℂ)) 2 volume := hsum
    _ ≤ (η : ℝ≥0∞) + η := add_le_add hfc hcg.le
    _ < ε := by simpa only [mul_two] using hηε

/-- Compactly supported Schwartz functions approximate every actual L² vector. -/
theorem exists_compactSchwartz_L2_dist_lt {d : ℕ} (f : FullL2 d) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : SchwartzMap (Euclidean d) ℂ, HasCompactSupport g ∧ dist f (g.toLp 2 volume) < ε := by
  obtain ⟨g, hgs, hg⟩ := memLp_exists_compactSchwartz_eLpNorm_lt (Lp.memLp f)
    (show ENNReal.ofReal ε ≠ 0 by positivity)
  refine ⟨g, hgs, ?_⟩
  rw [Lp.dist_def]
  have heq : eLpNorm ((f : Euclidean d → ℂ) - (g.toLp 2 volume : Euclidean d → ℂ)) 2 volume =
      eLpNorm ((f : Euclidean d → ℂ) - (g : Euclidean d → ℂ)) 2 volume := by
    apply eLpNorm_congr_ae
    filter_upwards [g.coeFn_toLp 2 volume] with x hx
    simp only [Pi.sub_apply, hx]
  rw [heq]
  exact ENNReal.toReal_lt_of_lt_ofReal hg

/-- Beurling configuration convergence gives strong convergence of the actual bump projections. -/
theorem bump_projection_stronglyConverges {d : ℕ} {δ r : ℝ}
    (hδ : 0 < δ) (hr : 2 * r < δ) (b : SchwartzMap (Euclidean d) ℂ)
    (hs : ∀ x, r ≤ ‖x‖ → b x = 0) (hn : ‖b.toLp 2 volume‖ = 1)
    {Γ : ℕ → SeparatedConfiguration d δ} {Γ₀ : SeparatedConfiguration d δ}
    (hΓ : Filter.Tendsto Γ Filter.atTop (nhds Γ₀)) :
    OrthProjection.StronglyConverges
      (fun n => (isometryRangeProjection (bumpSynthesis (Γ n).separated hr b hs hn)).op)
      (isometryRangeProjection (bumpSynthesis Γ₀.separated hr b hs hn)).op := by
  let P := fun Δ : SeparatedConfiguration d δ =>
    isometryRangeProjection (bumpSynthesis Δ.separated hr b hs hn)
  intro f
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨g, hgs, hfg⟩ := exists_compactSchwartz_L2_dist_lt f (by positivity : 0 < ε / 3)
  have ht := bump_projection_tendsto_compact_schwartz hδ hr b g hs hn hgs hΓ
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp ht (ε / 3) (by positivity)
  refine ⟨N, fun n hn' => ?_⟩
  have hleft : dist ((P (Γ n)).op f) ((P (Γ n)).op (g.toLp 2 volume)) ≤
      dist f (g.toLp 2 volume) := by
    rw [dist_eq_norm, ← map_sub, dist_eq_norm]
    exact (P (Γ n)).norm_op_apply_le _
  have hright : dist ((P Γ₀).op (g.toLp 2 volume)) ((P Γ₀).op f) ≤
      dist f (g.toLp 2 volume) := by
    rw [dist_eq_norm, ← map_sub, dist_eq_norm, norm_sub_rev f]
    exact (P Γ₀).norm_op_apply_le _
  have htri := dist_triangle ((P (Γ n)).op f) ((P (Γ n)).op (g.toLp 2 volume)) ((P Γ₀).op f)
  have htri' := dist_triangle ((P (Γ n)).op (g.toLp 2 volume))
    ((P Γ₀).op (g.toLp 2 volume)) ((P Γ₀).op f)
  have hmid := hN n hn'
  change dist ((P (Γ n)).op (g.toLp 2 volume)) ((P Γ₀).op (g.toLp 2 volume)) < ε / 3 at hmid
  change dist ((P (Γ n)).op f) ((P Γ₀).op f) < ε
  linarith

/-- The set-based Beurling hypothesis directly implies strong convergence of bump projections. -/
theorem bump_projection_stronglyConverges_of_weaklyConverges {d : ℕ} {δ r : ℝ}
    (hδ : 0 < δ) (hr : 2 * r < δ) (b : SchwartzMap (Euclidean d) ℂ)
    (hs : ∀ x, r ≤ ‖x‖ → b x = 0) (hn : ‖b.toLp 2 volume‖ = 1)
    {Γ : ℕ → SeparatedConfiguration d δ} {Γ₀ : SeparatedConfiguration d δ}
    (hΓ : WeaklyConverges (fun n => (Γ n).carrier) Γ₀.carrier) :
    OrthProjection.StronglyConverges
      (fun n => (isometryRangeProjection (bumpSynthesis (Γ n).separated hr b hs hn)).op)
      (isometryRangeProjection (bumpSynthesis Γ₀.separated hr b hs hn)).op :=
  bump_projection_stronglyConverges hδ hr b hs hn (SeparatedConfiguration.tendsto_of_weaklyConverges hΓ)
end RieszEuclidean
