import RieszEuclidean.HullGap
import RieszEuclidean.L2Multiplier
import RieszEuclidean.SpectralMeasures
import RieszEuclidean.FejerKernel
import RieszEuclidean.BoundarySymbols
noncomputable section
open MeasureTheory
open scoped NNReal ENNReal
namespace RieszEuclidean
/-- Ordinary translation with the sign matching the paper's positive Fourier transform. -/
def physicalTranslationUnitary {d : ℕ} (y : Euclidean d) : FullL2 d ≃ₗᵢ[ℂ] FullL2 d :=
  LinearIsometryEquiv.ofSurjective (translationL2 (-y)) (translationL2_surjective (-y))
/-- Ordinary translation is the actual map a(x) ↦ a(x-y). -/
theorem physicalTranslationUnitary_coe {d : ℕ} (y : Euclidean d) (f : FullL2 d) :
    (physicalTranslationUnitary y f : Euclidean d → ℂ) =ᵐ[volume] fun x => f (x - y) := by
  simpa only [sub_eq_add_neg] using translationL2_coe (-y) f
/-- Fourier modulation as an actual bounded multiplier. -/
def physicalModulation {d : ℕ} (y : Euclidean d) : FullL2 d →L[ℂ] FullL2 d :=
  l2MultiplierCLM (fun θ => (Real.fourierChar (inner (𝕜 := ℝ) y θ) : ℂ))
    (((continuous_subtype_val.comp Real.continuous_fourierChar).comp
      (continuous_const.inner continuous_id)).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun _ => le_of_eq (Circle.norm_coe _))
/-- Fourier modulation has the pointwise character representative. -/
theorem physicalModulation_coe {d : ℕ} (y : Euclidean d) (f : FullL2 d) :
    (physicalModulation y f : Euclidean d → ℂ) =ᵐ[volume]
      fun θ => (Real.fourierChar (inner (𝕜 := ℝ) y θ) : ℂ) * f θ :=
  l2Multiplier_coe _
    (((continuous_subtype_val.comp Real.continuous_fourierChar).comp
      (continuous_const.inner continuous_id)).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun _ => le_of_eq (Circle.norm_coe _)) f
/-- Positive-sign Fourier transformation turns a negative spatial shift into a positive character. -/
theorem inverseFourier_translate_character {d : ℕ} (y : Euclidean d) (f : Euclidean d → ℂ) :
    Real.fourierIntegralInv (fun x => f (x - y)) =
      fun θ => (Real.fourierChar (inner (𝕜 := ℝ) y θ) : ℂ) * Real.fourierIntegralInv f θ := by
  have h := VectorFourier.fourierIntegral_comp_add_right Real.fourierChar volume
    (-innerₗ (Euclidean d)) f (-y)
  simpa only [Real.fourierIntegralInv, Function.comp_def, sub_eq_add_neg,
    LinearMap.neg_apply, innerₗ_apply, inner_neg_left, neg_neg, Circle.smul_def, smul_eq_mul] using h
/-- The Fourier translation formula holds for actual L¹∩L² classes. -/
theorem paperFourierL2_physicalTranslation_integrable {d : ℕ} (y : Euclidean d)
    (f : FullL2 d) (hf : Integrable (f : Euclidean d → ℂ)) :
    paperFourierL2 d (physicalTranslationUnitary y f) =
      physicalModulation y (paperFourierL2 d f) := by
  apply Lp.ext
  filter_upwards [paperFourierL2_eq_integral (physicalTranslationUnitary y f)
      (translationL2_integrable (-y) f hf),
    physicalModulation_coe y (paperFourierL2 d f), paperFourierL2_eq_integral f hf]
      with θ hleft hright hfθ
  rw [hleft, hright, hfθ]
  have he : Real.fourierIntegralInv (physicalTranslationUnitary y f : Euclidean d → ℂ) =
      Real.fourierIntegralInv (fun x => f (x - y)) := by
    funext ξ
    apply integral_congr_ae
    filter_upwards [physicalTranslationUnitary_coe y f] with x hx
    simp only [hx]
  rw [he, inverseFourier_translate_character]
/-- Parseval's actual Fourier unitary diagonalizes ordinary translation on all L² vectors. -/
theorem paperFourierL2_physicalTranslation {d : ℕ} (y : Euclidean d) (f : FullL2 d) :
    paperFourierL2 d (physicalTranslationUnitary y f) =
      physicalModulation y (paperFourierL2 d f) := by
  refine (schwartz_toL2_denseRange d).induction_on f ?_ ?_
  · exact isClosed_eq
      ((paperFourierL2 d).continuous.comp (physicalTranslationUnitary y).continuous)
      ((physicalModulation y).continuous.comp (paperFourierL2 d).continuous)
  · intro g
    exact paperFourierL2_physicalTranslation_integrable y _
      (g.integrable.congr (g.coeFn_toLp 2 volume).symm)
/-- Ordinary translation has the paper's scalar Fourier-density pairing. -/
theorem physicalTranslation_correlation_integral {d : ℕ} (f : FullL2 d) (y : Euclidean d) :
    unitaryCorrelation physicalTranslationUnitary f y =
      ∫ θ, (Real.fourierChar (inner (𝕜 := ℝ) y θ) : ℂ) *
        (‖paperFourierL2 d f θ‖ ^ 2 : ℝ) := by
  unfold unitaryCorrelation
  rw [← (paperFourierL2 d).inner_map_map f (physicalTranslationUnitary y f),
    paperFourierL2_physicalTranslation, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [physicalModulation_coe y (paperFourierL2 d f)] with θ hθ
  rw [hθ]
  simp [RCLike.inner_apply, mul_assoc, RCLike.mul_conj]
/-- The actual scalar spectral measure of a physical-space vector is its Fourier squared density. -/
def physicalSpectralMeasure {d : ℕ} (f : FullL2 d) : Measure (Euclidean d) :=
  volume.withDensity (fun θ => ENNReal.ofReal (‖paperFourierL2 d f θ‖ ^ 2))
/-- Parseval gives integrability of the squared Fourier density. -/
theorem integrable_physicalSpectralDensity {d : ℕ} (f : FullL2 d) :
    Integrable (fun θ => ‖paperFourierL2 d f θ‖ ^ 2) :=
  (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable (paperFourierL2 d f))).mp
    (Lp.memLp (paperFourierL2 d f))
/-- The explicit physical spectral measure is finite. -/
theorem physicalSpectralMeasure_finite {d : ℕ} (f : FullL2 d) :
    IsFiniteMeasure (physicalSpectralMeasure f) :=
  isFiniteMeasure_withDensity_ofReal (integrable_physicalSpectralDensity f).2
/-- The physical spectral measure is absolutely continuous with respect to Euclidean volume. -/
theorem physicalSpectralMeasure_absolutelyContinuous {d : ℕ} (f : FullL2 d) :
    physicalSpectralMeasure f ≪ volume := withDensity_absolutelyContinuous _ _
/-- The Fourier squared density represents the actual translation correlation; no existence theorem is used. -/
theorem represents_physicalTranslationCorrelation {d : ℕ} (f : FullL2 d) :
    RepresentsCorrelation (unitaryCorrelation physicalTranslationUnitary f) (physicalSpectralMeasure f) := by
  refine ⟨physicalSpectralMeasure_finite f, ?_⟩
  intro y
  have hm : Measurable (fun θ => ENNReal.ofReal (‖paperFourierL2 d f θ‖ ^ 2)) :=
    (show Measurable (fun θ => ‖paperFourierL2 d f θ‖ ^ 2) from
      ((Lp.stronglyMeasurable (paperFourierL2 d f)).norm.pow 2).measurable).ennreal_ofReal
  rw [physicalSpectralMeasure, integral_withDensity_eq_integral_toReal_smul hm
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  rw [physicalTranslation_correlation_integral]
  apply integral_congr_ae
  filter_upwards [] with θ
  rw [ENNReal.toReal_ofReal (sq_nonneg _), Complex.real_smul]
  exact mul_comm _ _
/-- The explicit spectral density has total mass equal to the original L² energy. -/
theorem physicalSpectralMeasure_mass {d : ℕ} (f : FullL2 d) :
    (physicalSpectralMeasure f).real Set.univ = ‖f‖ ^ 2 := by
  apply (represents_physicalTranslationCorrelation f).unitary_mass physicalTranslationUnitary
  intro g
  change translationL2 (-0) g = g
  simpa only [neg_zero] using translationL2_zero g
/-- In positive dimension the physical spectral measure has no atom at zero. -/
theorem physicalSpectralMeasure_singleton_zero {d : ℕ} (hd : 0 < d) (f : FullL2 d) :
    physicalSpectralMeasure f {0} = 0 := by
  letI : NeZero d := ⟨hd.ne'⟩
  exact physicalSpectralMeasure_absolutelyContinuous f (measure_singleton 0)
/-- Ordinary translations have no nonzero invariant L² vector in positive dimension. -/
theorem eq_zero_of_physicalTranslation_invariant {d : ℕ} (hd : 0 < d) (f : FullL2 d)
    (hf : ∀ y : Euclidean d, physicalTranslationUnitary y f = f) : f = 0 := by
  have hdens : RepresentsCorrelation (unitaryCorrelation physicalTranslationUnitary f)
      (((‖f‖₊ ^ 2 : ℝ≥0) : ℝ≥0∞) • Measure.dirac (0 : Euclidean d)) := by
    convert (representsCorrelation_one (d := d)).smul (‖f‖₊ ^ 2) using 1
    funext y
    simp [unitaryCorrelation, hf y, inner_self_eq_norm_sq_to_K]
  have he := (represents_physicalTranslationCorrelation f).unique hdens
  have hzero := physicalSpectralMeasure_singleton_zero hd f
  rw [he] at hzero
  have hn : (‖f‖₊ ^ 2 : ℝ≥0∞) = 0 := by simpa using hzero
  have hn0 : ‖f‖₊ ^ 2 = 0 := by exact_mod_cast hn
  have hn' : ‖f‖ ^ 2 = 0 := by
    have hh := congrArg (fun x : ℝ≥0 => (x : ℝ)) hn0
    simpa only [NNReal.coe_pow, coe_nnnorm, NNReal.coe_zero] using hh
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp hn')
/-- The original translationL2 family likewise has no nonzero invariant vector. -/
theorem eq_zero_of_translationL2_invariant {d : ℕ} (hd : 0 < d) (f : FullL2 d)
    (hf : ∀ y : Euclidean d, translationL2 y f = f) : f = 0 :=
  eq_zero_of_physicalTranslation_invariant hd f (fun y => hf (-y))
/-- Uniqueness identifies every representing measure with the actual Fourier density. -/
theorem physicalSpectralMeasure_unique {d : ℕ} (f : FullL2 d)
    {σ : Measure (Euclidean d)}
    (hσ : RepresentsCorrelation (unitaryCorrelation physicalTranslationUnitary f) σ) :
    σ = volume.withDensity (fun θ => ENNReal.ofReal (‖paperFourierL2 d f θ‖ ^ 2)) :=
  hσ.unique (represents_physicalTranslationCorrelation f)
/-- Changing the boundary cutoff at zero does not change its physical spectral representative. -/
theorem physical_boundarySymbols_ae_eq {d : ℕ} (hd : 0 < d) (f : FullL2 d)
    (Ω : Set (Euclidean d)) (t : Euclidean d) :
    interiorBoundarySymbol Ω t =ᵐ[physicalSpectralMeasure f] cutoffSymbol Ω t := by
  have hz : ∀ᵐ θ ∂physicalSpectralMeasure f, θ ≠ 0 := by
    simpa only [ae_iff, not_not, Set.setOf_eq_eq_singleton] using physicalSpectralMeasure_singleton_zero hd f
  filter_upwards [hz] with θ hθ
  simp [interiorBoundarySymbol, hθ]
/-- The two boundary cutoff norms coincide on ordinary physical L² space. -/
theorem physical_boundarySymbol_norms_equal {d : ℕ} (hd : 0 < d) (f : FullL2 d)
    (Ω : Set (Euclidean d)) (t : Euclidean d) :
    (∫ θ, ‖interiorBoundarySymbol Ω t θ‖ ^ 2 ∂physicalSpectralMeasure f) =
      ∫ θ, ‖cutoffSymbol Ω t θ‖ ^ 2 ∂physicalSpectralMeasure f :=
  integral_congr_ae ((physical_boundarySymbols_ae_eq hd f Ω t).fun_comp fun z => ‖z‖ ^ 2)
/-- Inserting the zero frequency leaves the actual physical Fourier projection unchanged. -/
theorem fourierProjection_insert_zero_eq {d : ℕ} (hd : 0 < d)
    (Ω : Set (Euclidean d)) (hΩ : MeasurableSet Ω) :
    (fourierProjection (insert 0 Ω) (hΩ.insert 0)).op = (fourierProjection Ω hΩ).op := by
  letI : NeZero d := ⟨hd.ne'⟩
  apply ContinuousLinearMap.ext
  intro f
  apply (paperFourierL2 d).injective
  rw [fourierProjection_transform, fourierProjection_transform]
  apply Lp.ext
  have hz : ∀ᵐ θ : Euclidean d, θ ≠ 0 := by
    simpa only [ae_iff, not_not, Set.setOf_eq_eq_singleton] using (measure_singleton (μ := volume) (0 : Euclidean d))
  filter_upwards [domainCutoff_coe (insert 0 Ω) (hΩ.insert 0) (paperFourierL2 d f),
    domainCutoff_coe Ω hΩ (paperFourierL2 d f), hz] with θ hleft hright hθ
  rw [hleft, hright]
  by_cases hmem : θ ∈ Ω <;> simp [hmem, hθ]
end RieszEuclidean
