import RieszEuclidean.AveragedFourierForm
import RieszEuclidean.AveragedTests
import RieszEuclidean.AveragedBumpForm
noncomputable section
open MeasureTheory Set
namespace RieszEuclidean
/-- The two negative test phases give the positive difference phase. -/
theorem averagedTest_phase_product {d : ℕ} (t v w : Euclidean d) :
    exponential (-t) w * star (exponential (-t) v) =
      (Real.fourierChar (inner (𝕜 := ℝ) t (v - w)) : ℂ) := by
  change exponential (-t) w * starRingEnd ℂ (exponential (-t) v) = _
  simp only [exponential, ← Complex.exp_conj, map_mul, Complex.conj_ofReal,
    Complex.conj_I, map_ofNat, inner_neg_left, inner_sub_right, Real.fourierChar_apply]
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring
/-- Expanding the two normalized test functions gives the finite box Fourier integrand. -/
theorem averagedTest_kernel_product {X : Type*} {d : ℕ} (R : ℝ) (t : Euclidean d)
    (T : Euclidean d → X → X) (f g : X → ℂ) (x : X)
    (k : Euclidean d → Euclidean d → ℂ) (v w : Euclidean d) :
    k v w * averagedTest R t T f x w * star (averagedTest R t T g x v) =
      (euclideanBox d R).indicator (fun v => (euclideanBox d R).indicator (fun w =>
        (volume.real (euclideanBox d R) : ℂ)⁻¹ *
          (k v w * (Real.fourierChar (inner (𝕜 := ℝ) t (v - w)) : ℂ) *
            f (T w x) * star (g (T v x)))) w) v := by
  by_cases hv : v ∈ euclideanBox d R <;> by_cases hw : w ∈ euclideanBox d R
  · simp only [averagedTest, indicator_of_mem hv, indicator_of_mem hw, star_mul,
      starRingEnd_apply]
    have hs (a : ℝ) : star (a : ℂ) = (a : ℂ) := Complex.conj_ofReal a
    rw [hs]
    have hn : (((Real.sqrt (volume.real (euclideanBox d R)))⁻¹ : ℝ) : ℂ) ^ 2 =
        (volume.real (euclideanBox d R) : ℂ)⁻¹ := by
      rw [← Complex.ofReal_pow, inv_pow, Real.sq_sqrt (show 0 ≤ volume.real (euclideanBox d R) from ENNReal.toReal_nonneg),
        Complex.ofReal_inv]
    rw [← averagedTest_phase_product]
    linear_combination k v w * exponential (-t) w * f (T w x) *
      star (exponential (-t) v) * star (g (T v x)) * hn
  all_goals simp [averagedTest, hv, hw]
/-- The actual L² test pairing expands into the compact double spatial integral. -/
theorem inner_fourierProjection_averagedTest {X : Type*} {d : ℕ}
    (Ω : Set (Euclidean d)) (hΩ : MeasurableSet Ω) (hfin : volume Ω ≠ ⊤)
    (R : ℝ) (t : Euclidean d) (T : Euclidean d → X → X) (f g : X → ℂ) (x : X)
    (jf jg : FullL2 d)
    (hjf : (jf : Euclidean d → ℂ) =ᵐ[volume] averagedTest R t T f x)
    (hjg : (jg : Euclidean d → ℂ) =ᵐ[volume] averagedTest R t T g x)
    (hfi : Integrable (averagedTest R t T f x)) :
    inner (𝕜 := ℂ) jg ((fourierProjection Ω hΩ).op jf) =
      (volume.real (euclideanBox d R) : ℂ)⁻¹ *
        (∫ v in euclideanBox d R, ∫ w in euclideanBox d R,
          domainKernel Ω (v - w) * (Real.fourierChar (inner (𝕜 := ℝ) t (v - w)) : ℂ) *
            f (T w x) * star (g (T v x))) := by
  rw [inner_fourierProjection_kernel Ω hΩ hfin jf jg (hfi.congr hjf.symm)]
  calc
    _ = ∫ v, ∫ w, domainKernel Ω (v - w) * averagedTest R t T f x w *
        star (averagedTest R t T g x v) := by
      apply integral_congr_ae
      filter_upwards [hjg] with v hv
      apply integral_congr_ae
      filter_upwards [hjf] with w hw
      rw [hv, hw]
    _ = _ := by
      simp_rw [averagedTest_kernel_product R t T f g x (fun v w => domainKernel Ω (v - w))]
      rw [← integral_indicator (measurableSet_euclideanBox d R)]
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with v
      by_cases hv : v ∈ euclideanBox d R
      · simp only [indicator_of_mem hv]
        rw [integral_indicator (measurableSet_euclideanBox d R), integral_const_mul]
      · simp only [indicator_of_not_mem hv, integral_zero, mul_zero]
/-- Absolute integration permits moving the stationary average through both spatial integrals. -/
theorem integral_triple_swap_first {X V W : Type*}
    [MeasurableSpace X] [MeasurableSpace V] [MeasurableSpace W]
    (μ : Measure X) (ν : Measure V) (κ : Measure W) [SFinite μ] [SFinite ν] [SFinite κ]
    (F : X → V → W → ℂ)
    (hF : Integrable (fun p : X × (V × W) => F p.1 p.2.1 p.2.2) (μ.prod (ν.prod κ))) :
    (∫ x, (∫ v, ∫ w, F x v w ∂κ ∂ν) ∂μ) =
      ∫ v, ∫ w, ∫ x, F x v w ∂μ ∂κ ∂ν := by
  calc
    _ = ∫ x, (∫ p : V × W, F x p.1 p.2 ∂ν.prod κ) ∂μ := by
      apply integral_congr_ae
      filter_upwards [hF.prod_right_ae] with x hx
      exact integral_integral hx
    _ = ∫ p : V × W, (∫ x, F x p.1 p.2 ∂μ) ∂ν.prod κ := integral_integral_swap hF
    _ = _ := integral_prod _ hF.integral_prod_right
namespace SeparatedConfiguration
/-- Continuous hull vectors give an absolutely integrable triple Fourier kernel. -/
theorem integrable_stationary_fourier_box_triple {d : ℕ} {δ : ℝ} (hδ : 0 < δ)
    (Γ : SeparatedConfiguration d δ) [MeasurableSpace (hull Γ)] [BorelSpace (hull Γ)]
    [CompactSpace (hull Γ)] (μ : Measure (hull Γ)) [IsProbabilityMeasure μ]
    (Ω : Set (Euclidean d)) (hΩ : MeasurableSet Ω) (hfin : volume Ω ≠ ⊤)
    (t : Euclidean d) {R : ℝ} (hR : 0 < R) (f g : C(hull Γ, ℂ)) :
    Integrable (fun p : hull Γ × (Euclidean d × Euclidean d) =>
      domainKernel Ω (p.2.1 - p.2.2) *
        (Real.fourierChar (inner (𝕜 := ℝ) t (p.2.1 - p.2.2)) : ℂ) *
          f (hullTranslate hδ Γ p.2.2 p.1) * star (g (hullTranslate hδ Γ p.2.1 p.1)))
      (μ.prod ((volume.restrict (euclideanBox d R)).prod (volume.restrict (euclideanBox d R)))) := by
  letI : IsFiniteMeasure (volume.restrict (euclideanBox d R)) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using (volume_euclideanBox_pos_lt_top d hR).2⟩
  have hk : Continuous (fun p : hull Γ × (Euclidean d × Euclidean d) =>
      domainKernel Ω (p.2.1 - p.2.2)) :=
    (continuous_domainKernel Ω hΩ hfin).comp
      ((continuous_fst.comp continuous_snd).sub (continuous_snd.comp continuous_snd))
  have hf : Continuous (fun p : hull Γ × (Euclidean d × Euclidean d) =>
      f (hullTranslate hδ Γ p.2.2 p.1)) :=
    f.continuous.comp ((continuous_hullTranslate hδ Γ).comp
      ((continuous_snd.comp continuous_snd).prodMk continuous_fst))
  have hg : Continuous (fun p : hull Γ × (Euclidean d × Euclidean d) =>
      star (g (hullTranslate hδ Γ p.2.1 p.1))) :=
    (g.continuous.comp ((continuous_hullTranslate hδ Γ).comp
      ((continuous_fst.comp continuous_snd).prodMk continuous_fst))).star
  have he : Continuous (fun p : hull Γ × (Euclidean d × Euclidean d) =>
      (Real.fourierChar (inner (𝕜 := ℝ) t (p.2.1 - p.2.2)) : ℂ)) :=
    (continuous_subtype_val.comp Real.continuous_fourierChar).comp
      (continuous_const.inner
        ((continuous_fst.comp continuous_snd).sub (continuous_snd.comp continuous_snd)))
  apply (integrable_const (volume.real Ω * ‖f‖ * ‖g‖)).mono'
    (((hk.mul he).mul hf).mul hg).aestronglyMeasurable
  filter_upwards [] with p
  rw [norm_mul, norm_mul, norm_mul, Circle.norm_coe, mul_one, norm_star]
  exact mul_le_mul (mul_le_mul (norm_domainKernel_le Ω _) (f.norm_coe_le_norm _)
    (norm_nonneg _) ENNReal.toReal_nonneg) (g.norm_coe_le_norm _) (norm_nonneg _)
    (mul_nonneg ENNReal.toReal_nonneg (norm_nonneg f))
/-- Stationary continuous representatives may replace their L² classes in the finite scalar form. -/
theorem normalized_stationary_fourier_form_continuous {d : ℕ} {δ : ℝ} (hδ : 0 < δ)
    (Γ : SeparatedConfiguration d δ) [MeasurableSpace (hull Γ)] [BorelSpace (hull Γ)]
    [CompactSpace (hull Γ)] (μ : Measure (hull Γ)) [IsProbabilityMeasure μ]
    (hμ : ∀ z : Euclidean d, MeasurePreserving (hullTranslate hδ Γ z) μ μ)
    (Ω : Set (Euclidean d)) (hΩ : MeasurableSet Ω) (hfin : volume Ω ≠ ⊤)
    (t : Euclidean d) {R : ℝ} (hR : 0 < R) (f g : C(hull Γ, ℂ)) :
    (volume.real (euclideanBox d R) : ℂ)⁻¹ *
      (∫ v in euclideanBox d R, ∫ w in euclideanBox d R,
        domainKernel Ω (v - w) * (Real.fourierChar (inner (𝕜 := ℝ) t (v - w)) : ℂ) *
          ∫ Δ, f (hullTranslate hδ Γ w Δ) * star (g (hullTranslate hδ Γ v Δ)) ∂μ) =
      inner (𝕜 := ℂ) (ContinuousMap.toLp 2 μ ℂ g)
        (finiteFilter (hullKoopmanUnitary hδ Γ μ hμ)
          (strongContinuous_hullKoopmanUnitary hδ Γ μ hμ) Ω hΩ hfin t hR
            (ContinuousMap.toLp 2 μ ℂ f)) := by
  rw [← normalized_stationary_fourier_form hδ Γ μ hμ Ω hΩ hfin t hR]
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
/-- The average of the actual Fourier projection on the normalized tests is the finite stationary filter. -/
theorem integral_fourierProjection_averagedTest {d : ℕ} {δ : ℝ} (hδ : 0 < δ)
    (Γ : SeparatedConfiguration d δ) [MeasurableSpace (hull Γ)] [BorelSpace (hull Γ)]
    [CompactSpace (hull Γ)] (μ : Measure (hull Γ)) [IsProbabilityMeasure μ]
    (hμ : ∀ z : Euclidean d, MeasurePreserving (hullTranslate hδ Γ z) μ μ)
    (Ω : Set (Euclidean d)) (hΩ : MeasurableSet Ω) (hfin : volume Ω ≠ ⊤)
    (t : Euclidean d) {R : ℝ} (hR : 0 < R) (f g : C(hull Γ, ℂ))
    (jf jg : hull Γ → FullL2 d)
    (hjf : ∀ Δ, (jf Δ : Euclidean d → ℂ) =ᵐ[volume] averagedTest R t (hullTranslate hδ Γ) f Δ)
    (hjg : ∀ Δ, (jg Δ : Euclidean d → ℂ) =ᵐ[volume] averagedTest R t (hullTranslate hδ Γ) g Δ)
    (hfi : ∀ Δ, Integrable (averagedTest R t (hullTranslate hδ Γ) f Δ)) :
    (∫ Δ, inner (𝕜 := ℂ) (jg Δ) ((fourierProjection Ω hΩ).op (jf Δ)) ∂μ) =
      inner (𝕜 := ℂ) (ContinuousMap.toLp 2 μ ℂ g)
        (finiteFilter (hullKoopmanUnitary hδ Γ μ hμ)
          (strongContinuous_hullKoopmanUnitary hδ Γ μ hμ) Ω hΩ hfin t hR
            (ContinuousMap.toLp 2 μ ℂ f)) := by
  have hi := integrable_stationary_fourier_box_triple hδ Γ μ Ω hΩ hfin t hR f g
  simp_rw [inner_fourierProjection_averagedTest Ω hΩ hfin R t (hullTranslate hδ Γ)
    f g _ _ _ (hjf _) (hjg _) (hfi _)]
  rw [integral_const_mul, integral_triple_swap_first μ (volume.restrict (euclideanBox d R)) (volume.restrict (euclideanBox d R)) _ hi]
  rw [← normalized_stationary_fourier_form_continuous hδ Γ μ hμ Ω hΩ hfin t hR]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with v
  apply integral_congr_ae
  filter_upwards [] with w
  simp only [mul_assoc, integral_const_mul]
/-- The averaged actual Fourier pairing is absolutely integrable on the stationary probability space. -/
theorem integrable_fourierProjection_averagedTest {d : ℕ} {δ : ℝ} (hδ : 0 < δ)
    (Γ : SeparatedConfiguration d δ) [MeasurableSpace (hull Γ)] [BorelSpace (hull Γ)]
    [CompactSpace (hull Γ)] (μ : Measure (hull Γ)) [IsProbabilityMeasure μ]
    (Ω : Set (Euclidean d)) (hΩ : MeasurableSet Ω) (hfin : volume Ω ≠ ⊤)
    (t : Euclidean d) {R : ℝ} (hR : 0 < R) (f g : C(hull Γ, ℂ))
    (jf jg : hull Γ → FullL2 d)
    (hjf : ∀ Δ, (jf Δ : Euclidean d → ℂ) =ᵐ[volume] averagedTest R t (hullTranslate hδ Γ) f Δ)
    (hjg : ∀ Δ, (jg Δ : Euclidean d → ℂ) =ᵐ[volume] averagedTest R t (hullTranslate hδ Γ) g Δ)
    (hfi : ∀ Δ, Integrable (averagedTest R t (hullTranslate hδ Γ) f Δ)) :
    Integrable (fun Δ => inner (𝕜 := ℂ) (jg Δ) ((fourierProjection Ω hΩ).op (jf Δ))) μ := by
  have hi := integrable_stationary_fourier_box_triple hδ Γ μ Ω hΩ hfin t hR f g
  apply (hi.integral_prod_left.const_mul ((volume.real (euclideanBox d R) : ℂ)⁻¹)).congr
  filter_upwards [hi.prod_right_ae] with Δ hΔ
  rw [inner_fourierProjection_averagedTest Ω hΩ hfin R t (hullTranslate hδ Γ)
    f g Δ _ _ (hjf Δ) (hjg Δ) (hfi Δ)]
  rw [integral_prod _ hΔ]
/-- Stationary L² squares dominate the absolute triple Fourier integrand. -/
theorem integrable_stationary_fourier_box_triple_Lp {d : ℕ} {δ : ℝ} (hδ : 0 < δ)
    (Γ : SeparatedConfiguration d δ) [MeasurableSpace (hull Γ)] [BorelSpace (hull Γ)]
    (μ : Measure (hull Γ)) [IsProbabilityMeasure μ]
    (hμ : ∀ z : Euclidean d, MeasurePreserving (hullTranslate hδ Γ z) μ μ)
    (Ω : Set (Euclidean d)) (hΩ : MeasurableSet Ω) (hfin : volume Ω ≠ ⊤)
    (t : Euclidean d) {R : ℝ} (hR : 0 < R) (f g : Lp ℂ 2 μ) :
    Integrable (fun p : hull Γ × (Euclidean d × Euclidean d) =>
      domainKernel Ω (p.2.1 - p.2.2) *
        (Real.fourierChar (inner (𝕜 := ℝ) t (p.2.1 - p.2.2)) : ℂ) *
          f (hullTranslate hδ Γ p.2.2 p.1) * star (g (hullTranslate hδ Γ p.2.1 p.1)))
      (μ.prod ((volume.restrict (euclideanBox d R)).prod (volume.restrict (euclideanBox d R)))) := by
  let ν := (volume.restrict (euclideanBox d R)).prod (volume.restrict (euclideanBox d R))
  letI : IsFiniteMeasure (volume.restrict (euclideanBox d R)) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using (volume_euclideanBox_pos_lt_top d hR).2⟩
  have hf := integrable_hull_square_parameters hδ Γ μ hμ ν Prod.snd measurable_snd f
  have hg := integrable_hull_square_parameters hδ Γ μ hμ ν Prod.fst measurable_fst g
  have hq : Continuous (fun p : hull Γ × (Euclidean d × Euclidean d) =>
      domainKernel Ω (p.2.1 - p.2.2)) :=
    (continuous_domainKernel Ω hΩ hfin).comp
      ((continuous_fst.comp continuous_snd).sub (continuous_snd.comp continuous_snd))
  have hfm : StronglyMeasurable (fun p : hull Γ × (Euclidean d × Euclidean d) =>
      f (hullTranslate hδ Γ p.2.2 p.1)) := (Lp.stronglyMeasurable f).comp_measurable
    ((continuous_hullTranslate hδ Γ).measurable.comp
      ((measurable_snd.comp measurable_snd).prodMk measurable_fst))
  have hgm : StronglyMeasurable (fun p : hull Γ × (Euclidean d × Euclidean d) =>
      star (g (hullTranslate hδ Γ p.2.1 p.1))) := continuous_star.comp_stronglyMeasurable ((Lp.stronglyMeasurable g).comp_measurable
    ((continuous_hullTranslate hδ Γ).measurable.comp
      ((measurable_fst.comp measurable_snd).prodMk measurable_fst)))
  have he : Continuous (fun p : hull Γ × (Euclidean d × Euclidean d) =>
      (Real.fourierChar (inner (𝕜 := ℝ) t (p.2.1 - p.2.2)) : ℂ))  := (continuous_subtype_val.comp Real.continuous_fourierChar).comp
    (continuous_const.inner ((continuous_fst.comp continuous_snd).sub (continuous_snd.comp continuous_snd)))
  apply ((hf.add hg).const_mul (volume.real Ω / 2)).mono'
    (((hq.mul he).stronglyMeasurable.mul hfm).mul hgm).aestronglyMeasurable
  filter_upwards [] with p
  simp only [Pi.mul_apply, Pi.add_apply]
  rw [norm_mul, norm_mul, norm_mul, Circle.norm_coe, mul_one, norm_star]
  have hqbound := norm_domainKernel_le Ω (p.2.1 - p.2.2)
  have hle := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hqbound (norm_nonneg (f (hullTranslate hδ Γ p.2.2 p.1))))
    (norm_nonneg (g (hullTranslate hδ Γ p.2.1 p.1)))
  have hsq := sq_nonneg (‖f (hullTranslate hδ Γ p.2.2 p.1)‖ - ‖g (hullTranslate hδ Γ p.2.1 p.1)‖)
  have hprod := mul_nonneg (show 0 ≤ volume.real Ω from ENNReal.toReal_nonneg) hsq
  dsimp only [Prod.fst, Prod.snd] at *
  nlinarith

/-- The average of the actual Fourier projection on the normalized tests is the finite stationary filter. -/
theorem integral_fourierProjection_averagedTest_Lp {d : ℕ} {δ : ℝ} (hδ : 0 < δ)
    (Γ : SeparatedConfiguration d δ) [MeasurableSpace (hull Γ)] [BorelSpace (hull Γ)]
    [CompactSpace (hull Γ)] (μ : Measure (hull Γ)) [IsProbabilityMeasure μ]
    (hμ : ∀ z : Euclidean d, MeasurePreserving (hullTranslate hδ Γ z) μ μ)
    (Ω : Set (Euclidean d)) (hΩ : MeasurableSet Ω) (hfin : volume Ω ≠ ⊤)
    (t : Euclidean d) {R : ℝ} (hR : 0 < R) (f g : Lp ℂ 2 μ)
    (jf jg : hull Γ → FullL2 d)
    (hjf : ∀ᵐ Δ ∂μ, (jf Δ : Euclidean d → ℂ) =ᵐ[volume] averagedTest R t (hullTranslate hδ Γ) f Δ)
    (hjg : ∀ᵐ Δ ∂μ, (jg Δ : Euclidean d → ℂ) =ᵐ[volume] averagedTest R t (hullTranslate hδ Γ) g Δ)
    (hfi : ∀ᵐ Δ ∂μ, Integrable (averagedTest R t (hullTranslate hδ Γ) f Δ)) :
    (∫ Δ, inner (𝕜 := ℂ) (jg Δ) ((fourierProjection Ω hΩ).op (jf Δ)) ∂μ) =
      inner (𝕜 := ℂ) g
        (finiteFilter (hullKoopmanUnitary hδ Γ μ hμ)
          (strongContinuous_hullKoopmanUnitary hδ Γ μ hμ) Ω hΩ hfin t hR
            f) := by
  have hi := integrable_stationary_fourier_box_triple_Lp hδ Γ μ hμ Ω hΩ hfin t hR f g
  have he : (fun Δ => inner (𝕜 := ℂ) (jg Δ) ((fourierProjection Ω hΩ).op (jf Δ))) =ᵐ[μ]
      (fun Δ => (volume.real (euclideanBox d R) : ℂ)⁻¹ *
        ∫ v in euclideanBox d R, ∫ w in euclideanBox d R,
          domainKernel Ω (v - w) * (Real.fourierChar (inner (𝕜 := ℝ) t (v - w)) : ℂ) *
            f (hullTranslate hδ Γ w Δ) * star (g (hullTranslate hδ Γ v Δ))) := by
    filter_upwards [hjf, hjg, hfi] with Δ hf hg hi
    exact inner_fourierProjection_averagedTest Ω hΩ hfin R t (hullTranslate hδ Γ)
      f g Δ _ _ hf hg hi
  rw [integral_congr_ae he]
  rw [integral_const_mul, integral_triple_swap_first μ (volume.restrict (euclideanBox d R)) (volume.restrict (euclideanBox d R)) _ hi]
  rw [← normalized_stationary_fourier_form hδ Γ μ hμ Ω hΩ hfin t hR]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with v
  apply integral_congr_ae
  filter_upwards [] with w
  simp only [mul_assoc, integral_const_mul]
/-- The averaged actual Fourier pairing is absolutely integrable on the stationary probability space. -/
theorem integrable_fourierProjection_averagedTest_Lp {d : ℕ} {δ : ℝ} (hδ : 0 < δ)
    (Γ : SeparatedConfiguration d δ) [MeasurableSpace (hull Γ)] [BorelSpace (hull Γ)]
    [CompactSpace (hull Γ)] (μ : Measure (hull Γ)) [IsProbabilityMeasure μ]
    (hμ : ∀ z : Euclidean d, MeasurePreserving (hullTranslate hδ Γ z) μ μ)
    (Ω : Set (Euclidean d)) (hΩ : MeasurableSet Ω) (hfin : volume Ω ≠ ⊤)
    (t : Euclidean d) {R : ℝ} (hR : 0 < R) (f g : Lp ℂ 2 μ)
    (jf jg : hull Γ → FullL2 d)
    (hjf : ∀ᵐ Δ ∂μ, (jf Δ : Euclidean d → ℂ) =ᵐ[volume] averagedTest R t (hullTranslate hδ Γ) f Δ)
    (hjg : ∀ᵐ Δ ∂μ, (jg Δ : Euclidean d → ℂ) =ᵐ[volume] averagedTest R t (hullTranslate hδ Γ) g Δ)
    (hfi : ∀ᵐ Δ ∂μ, Integrable (averagedTest R t (hullTranslate hδ Γ) f Δ)) :
    Integrable (fun Δ => inner (𝕜 := ℂ) (jg Δ) ((fourierProjection Ω hΩ).op (jf Δ))) μ := by
  have hi := integrable_stationary_fourier_box_triple_Lp hδ Γ μ hμ Ω hΩ hfin t hR f g
  apply (hi.integral_prod_left.const_mul ((volume.real (euclideanBox d R) : ℂ)⁻¹)).congr
  filter_upwards [hi.prod_right_ae, hjf, hjg, hfi] with Δ hΔ hf hg hi
  rw [inner_fourierProjection_averagedTest Ω hΩ hfin R t (hullTranslate hδ Γ)
    f g Δ _ _ hf hg hi]
  rw [integral_prod _ hΔ]
end SeparatedConfiguration
end RieszEuclidean
