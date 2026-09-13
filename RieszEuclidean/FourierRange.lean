import RieszEuclidean.DomainExtension
noncomputable section
open MeasureTheory
namespace RieszEuclidean
/-- Embed domain L² isometrically into the Fourier projection range. -/
def fourierDomainEmbedding {d : ℕ} (Ω : Set (Euclidean d)) (hΩ : MeasurableSet Ω) :
    DomainL2 Ω →ₗᵢ[ℂ] FullL2 d :=
  (paperFourierL2 d).symm.toLinearIsometry.comp (domainExtensionLI Ω hΩ)
/-- The embedding has exactly the range of the Fourier projection. -/
theorem fourierDomainEmbedding_range {d : ℕ} (Ω : Set (Euclidean d)) (hΩ : MeasurableSet Ω) :
    LinearMap.range (fourierDomainEmbedding Ω hΩ).toLinearMap = (fourierProjection Ω hΩ).range := by
  ext f
  constructor
  · rintro ⟨g, rfl⟩
    apply ((fourierProjection Ω hΩ).mem_range_iff _).mpr
    apply (paperFourierL2 d).injective
    rw [fourierProjection_transform]
    change domainCutoff Ω hΩ ((paperFourierL2 d) ((paperFourierL2 d).symm
      (domainExtension Ω hΩ g))) = (paperFourierL2 d) ((paperFourierL2 d).symm (domainExtension Ω hΩ g))
    rw [LinearIsometryEquiv.apply_symm_apply, ← domainExtension_restriction, domainRestriction_extension]
  · intro hf
    refine ⟨domainRestriction Ω (paperFourierL2 d f), ?_⟩
    apply (paperFourierL2 d).injective
    change (paperFourierL2 d) ((paperFourierL2 d).symm
      (domainExtension Ω hΩ (domainRestriction Ω (paperFourierL2 d f)))) = paperFourierL2 d f
    rw [LinearIsometryEquiv.apply_symm_apply, domainExtension_restriction, ← fourierProjection_transform]
    rw [((fourierProjection Ω hΩ).mem_range_iff f).mp hf]
/-- Embedding the restricted Fourier transform is the Fourier projection itself. -/
theorem fourierDomainEmbedding_restriction {d : ℕ} (Ω : Set (Euclidean d)) (hΩ : MeasurableSet Ω)
    (f : FullL2 d) :
    fourierDomainEmbedding Ω hΩ (domainRestriction Ω (paperFourierL2 d f)) =
      (fourierProjection Ω hΩ).op f := by
  apply (paperFourierL2 d).injective
  change (paperFourierL2 d) ((paperFourierL2 d).symm
    (domainExtension Ω hΩ (domainRestriction Ω (paperFourierL2 d f)))) = _
  rw [LinearIsometryEquiv.apply_symm_apply, domainExtension_restriction, fourierProjection_transform]
end RieszEuclidean
