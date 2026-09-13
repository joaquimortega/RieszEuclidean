import RieszEuclidean.AveragedFourierExpansion
import RieszEuclidean.AveragedTestNorms
noncomputable section
open MeasureTheory
namespace RieszEuclidean.SeparatedConfiguration
/-- Canonical normalized tests give the actual averaged bump pairing and its integrability. -/
theorem canonical_averaged_bump_pairing {d : ℕ} {δ r M : ℝ} (hδ : 0 < δ)
    (Γ : SeparatedConfiguration d δ) [MeasurableSpace (hull Γ)] [BorelSpace (hull Γ)]
    [CompactSpace (hull Γ)] (μ : Measure (hull Γ)) [IsProbabilityMeasure μ]
    (hμ : ∀ z : Euclidean d, MeasurePreserving (hullTranslate hδ Γ z) μ μ)
    (hr : 2 * r < δ) (b : SchwartzMap (Euclidean d) ℂ)
    (hcompact : HasCompactSupport b) (hs : ∀ x, r ≤ ‖x‖ → b x = 0)
    (hn : ‖b.toLp 2 volume‖ = 1) (hM : 0 ≤ M) (hb : ∀ x, ‖b x‖ ≤ M)
    (t : Euclidean d) {R : ℝ} (hR : 0 < R) (f g : Lp ℂ 2 μ) :
    Integrable (fun Δ => inner (𝕜 := ℂ) (averagedTestL2 R t (hullTranslate hδ Γ) g Δ)
      ((isometryRangeProjection (bumpSynthesis Δ.val.separated hr b hs hn)).op
        (averagedTestL2 R t (hullTranslate hδ Γ) f Δ))) μ ∧
    (∫ Δ, inner (𝕜 := ℂ) (averagedTestL2 R t (hullTranslate hδ Γ) g Δ)
      ((isometryRangeProjection (bumpSynthesis Δ.val.separated hr b hs hn)).op
        (averagedTestL2 R t (hullTranslate hδ Γ) f Δ)) ∂μ) =
      inner (𝕜 := ℂ) g
        (stationaryComparisonAverage hδ Γ μ hμ hr.le b b.continuous hcompact hs hM hb t R f) := by
  have hf := (hull_averagedTestL2_norm_energy hδ Γ μ hμ f hR t).1
  have hg := (hull_averagedTestL2_norm_energy hδ Γ μ hμ g hR t).1
  exact ⟨integrable_bumpProjection_averagedTest_Lp hδ Γ μ hμ hr b hcompact hs hn hM hb t hR f g _ _ hf hg,
    integral_bumpProjection_averagedTest_Lp hδ Γ μ hμ hr b hcompact hs hn hM hb t hR f g _ _ hf hg⟩
/-- Canonical normalized tests give the actual averaged Fourier pairing and its integrability. -/
theorem canonical_averaged_fourier_pairing {d : ℕ} {δ : ℝ} (hδ : 0 < δ)
    (Γ : SeparatedConfiguration d δ) [MeasurableSpace (hull Γ)] [BorelSpace (hull Γ)]
    [CompactSpace (hull Γ)] (μ : Measure (hull Γ)) [IsProbabilityMeasure μ]
    (hμ : ∀ z : Euclidean d, MeasurePreserving (hullTranslate hδ Γ z) μ μ)
    (Ω : Set (Euclidean d)) (hΩ : MeasurableSet Ω) (hfin : volume Ω ≠ ⊤)
    (t : Euclidean d) {R : ℝ} (hR : 0 < R) (f g : Lp ℂ 2 μ) :
    Integrable (fun Δ => inner (𝕜 := ℂ) (averagedTestL2 R t (hullTranslate hδ Γ) g Δ)
      ((fourierProjection Ω hΩ).op (averagedTestL2 R t (hullTranslate hδ Γ) f Δ))) μ ∧
    (∫ Δ, inner (𝕜 := ℂ) (averagedTestL2 R t (hullTranslate hδ Γ) g Δ)
      ((fourierProjection Ω hΩ).op (averagedTestL2 R t (hullTranslate hδ Γ) f Δ)) ∂μ) =
      inner (𝕜 := ℂ) g
        (finiteFilter (hullKoopmanUnitary hδ Γ μ hμ)
          (strongContinuous_hullKoopmanUnitary hδ Γ μ hμ) Ω hΩ hfin t hR f) := by
  have hf := (hull_averagedTestL2_norm_energy hδ Γ μ hμ f hR t).1
  have hg := (hull_averagedTestL2_norm_energy hδ Γ μ hμ g hR t).1
  have hT : Measurable (fun p : hull Γ × Euclidean d => hullTranslate hδ Γ p.2 p.1) :=
    ((continuous_hullTranslate hδ Γ).comp (continuous_snd.prodMk continuous_fst)).measurable
  have hfi := ae_integrable_averagedTest (hullTranslate hδ Γ) hT hμ f hR t
  exact ⟨integrable_fourierProjection_averagedTest_Lp hδ Γ μ hμ Ω hΩ hfin t hR f g _ _ hf hg hfi,
    integral_fourierProjection_averagedTest_Lp hδ Γ μ hμ Ω hΩ hfin t hR f g _ _ hf hg hfi⟩
end RieszEuclidean.SeparatedConfiguration
