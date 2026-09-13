import RieszEuclidean.FourierAgreement
import RieszEuclidean.SpectralMeasures

open MeasureTheory RealInnerProductSpace Filter
open scoped ZeroAtInfty Topology

namespace RieszEuclidean

/-- The positive Fourier character integral of a finite measure. -/
noncomputable def measureFourier {d : ℕ} (μ : Measure (Euclidean d)) (y : Euclidean d) : ℂ :=
  ∫ θ, (Real.fourierChar (inner (𝕜 := ℝ) y θ) : ℂ) ∂μ

private theorem measureFourier_eq_vector {d : ℕ} (μ : Measure (Euclidean d)) :
    measureFourier μ = VectorFourier.fourierIntegral Real.fourierChar μ
      (-innerₗ (Euclidean d)) (fun _ => (1 : ℂ)) := by
  ext y
  simp [measureFourier, VectorFourier.fourierIntegral, Circle.smul_def, mul_comm]

/-- Fourier character integrals of finite measures are continuous. -/
theorem continuous_measureFourier {d : ℕ} (μ : Measure (Euclidean d))
    [IsFiniteMeasure μ] : Continuous (measureFourier μ) := by
  rw [measureFourier_eq_vector]
  exact VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
    (continuous_fst.inner continuous_snd).neg (integrable_const _)

/-- A Fourier character integral is bounded by the total mass. -/
theorem norm_measureFourier_le_mass {d : ℕ} (μ : Measure (Euclidean d))
    (y : Euclidean d) : ‖measureFourier μ y‖ ≤ μ.real Set.univ := by
  calc
    _ ≤ ∫ θ, ‖(Real.fourierChar (inner (𝕜 := ℝ) y θ) : ℂ)‖ ∂μ :=
      norm_integral_le_integral_norm _
    _ = μ.real Set.univ := by simp

/-- Fubini transposes a positive Fourier character integral against an integrable test. -/
theorem integral_mul_measureFourier {d : ℕ} (μ : Measure (Euclidean d))
    [IsFiniteMeasure μ] {g : Euclidean d → ℂ} (hg : Integrable g) :
    (∫ y, g y * measureFourier μ y) = ∫ θ, Real.fourierIntegralInv g θ ∂μ := by
  have h := VectorFourier.integral_fourierIntegral_smul_eq_flip
    (L := -innerₗ (Euclidean d)) (μ := volume) (ν := μ)
    Real.continuous_fourierChar (continuous_fst.inner continuous_snd).neg hg
    (integrable_const (1 : ℂ))
  have hflip : (-innerₗ (Euclidean d)).flip = -innerₗ (Euclidean d) := by
    ext x y
    change -inner (𝕜 := ℝ) y x = -inner (𝕜 := ℝ) x y
    rw [real_inner_comm]
  simpa only [hflip, smul_eq_mul, mul_one, ← measureFourier_eq_vector,
    Real.fourierIntegralInv] using h.symm

/-- A uniform mass bound gives dominated convergence after an integrable Fourier test. -/
theorem tendsto_integral_mul_measureFourier {d : ℕ}
    (μ : ℕ → Measure (Euclidean d)) [∀ n, IsFiniteMeasure (μ n)]
    {M : ℝ} (hM : ∀ n, (μ n).real Set.univ ≤ M)
    {φ : Euclidean d → ℂ}
    (hφ : ∀ y, Tendsto (fun n => measureFourier (μ n) y) atTop (𝓝 (φ y)))
    {g : Euclidean d → ℂ} (hg : Integrable g) :
    Tendsto (fun n => ∫ y, g y * measureFourier (μ n) y) atTop
      (𝓝 (∫ y, g y * φ y)) := by
  apply tendsto_integral_of_dominated_convergence (fun y => ‖g y‖ * M)
  · intro n
    exact hg.aestronglyMeasurable.mul (continuous_measureFourier (μ n)).aestronglyMeasurable
  · exact hg.norm.mul_const M
  · intro n
    exact ae_of_all _ fun y => by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left ((norm_measureFourier_le_mass (μ n) y).trans (hM n))
        (norm_nonneg _)
  · exact ae_of_all _ fun y => tendsto_const_nhds.mul (hφ y)

/-- Convergence on real vanishing-at-infinity tests implies convergence on complex tests. -/
theorem tendsto_complex_zeroAtInfty_integrals_of_real {X : Type*}
    [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    (μn : ℕ → Measure X) [∀ n, IsFiniteMeasure (μn n)]
    (μ : Measure X) [IsFiniteMeasure μ] {l : Filter ℕ}
    (hreal : ∀ g : C₀(X, ℝ),
      Tendsto (fun n => ∫ x, g x ∂μn n) l (𝓝 (∫ x, g x ∂μ)))
    (g : C₀(X, ℂ)) :
    Tendsto (fun n => ∫ x, g x ∂μn n) l (𝓝 (∫ x, g x ∂μ)) := by
  let gr : C₀(X, ℝ) :=
    ⟨⟨fun x => (g x).re, Complex.continuous_re.comp g.continuous⟩,
      Complex.continuous_re.continuousAt.tendsto.comp g.zero_at_infty'⟩
  let gi : C₀(X, ℝ) :=
    ⟨⟨fun x => (g x).im, Complex.continuous_im.comp g.continuous⟩,
      Complex.continuous_im.continuousAt.tendsto.comp g.zero_at_infty'⟩
  have hr := Complex.continuous_ofReal.continuousAt.tendsto.comp (hreal gr)
  have hi := Complex.continuous_ofReal.continuousAt.tendsto.comp (hreal gi)
  have h := hr.add (hi.mul_const Complex.I)
  change Tendsto
    (fun n => (↑(∫ x, (g x).re ∂μn n) : ℂ) + ↑(∫ x, (g x).im ∂μn n) * Complex.I) l
    (𝓝 ((↑(∫ x, (g x).re ∂μ) : ℂ) + ↑(∫ x, (g x).im ∂μ) * Complex.I)) at h
  have hsplit (ν : Measure X) [IsFiniteMeasure ν] :
      (↑(∫ x, (g x).re ∂ν) : ℂ) + ↑(∫ x, (g x).im ∂ν) * Complex.I = ∫ x, g x ∂ν :=
    integral_re_add_im (show Integrable (fun x => g x) ν from g.toBCF.integrable ν)
  simpa only [hsplit] using h

/-- Bounded mass and convergence on vanishing-at-infinity tests identify the Fourier limit.
The measure convergence can occur along an arbitrary nontrivial refining filter. -/
theorem representsCorrelation_of_bounded_vague_limit {d : ℕ}
    (μn : ℕ → Measure (Euclidean d)) [∀ n, IsFiniteMeasure (μn n)]
    (μ : Measure (Euclidean d)) [IsFiniteMeasure μ]
    {M : ℝ} (hM : ∀ n, (μn n).real Set.univ ≤ M)
    {l : Filter ℕ} [l.NeBot] (hl : l ≤ atTop)
    (hvague : ∀ g : C₀(Euclidean d, ℂ),
      Tendsto (fun n => ∫ θ, g θ ∂μn n) l (𝓝 (∫ θ, g θ ∂μ)))
    {φ : Euclidean d → ℂ} (hcφ : Continuous φ)
    (hφ : ∀ y, Tendsto (fun n => measureFourier (μn n) y) atTop (𝓝 (φ y))) :
    RepresentsCorrelation φ μ := by
  have htest (g : SchwartzMap (Euclidean d) ℂ) :
      (∫ y, g y * φ y) = ∫ y, g y * measureFourier μ y := by
    have hleft := (tendsto_integral_mul_measureFourier μn hM hφ g.integrable).mono_left hl
    have hright := hvague (((SchwartzMap.fourierTransformCLE ℂ).symm g).toZeroAtInfty)
    simp only [SchwartzMap.toZeroAtInfty_apply, SchwartzMap.fourierTransformCLE_symm_apply] at hright
    simp_rw [← integral_mul_measureFourier _ g.integrable] at hright
    exact tendsto_nhds_unique hleft hright
  have hae : φ =ᵐ[volume] measureFourier μ := by
    apply ae_eq_of_integral_contDiff_smul_eq hcφ.locallyIntegrable
      (continuous_measureFourier μ).locallyIntegrable
    intro g hg hgs
    let gC : SchwartzMap (Euclidean d) ℂ := compactSchwartz (fun x => (g x : ℂ))
      (Complex.ofRealCLM.contDiff.comp hg) (hgs.comp_left Complex.ofReal_zero)
    simpa only [Complex.real_smul] using htest gC
  exact ⟨inferInstance, congrFun (Measure.eq_of_ae_eq hae hcφ (continuous_measureFourier μ))⟩

end RieszEuclidean
