import RieszEuclidean.BumpIdentity
import RieszEuclidean.FourierRange
import RieszEuclidean.RangeIso
open MeasureTheory
namespace RieszEuclidean
/-- The concrete bump projection has distance less than one from the Fourier projection. -/
theorem initial_bump_gap {d : ℕ} {Ω Λ : Set (Euclidean d)}
    (hΩ : MeasurableSet Ω) (b : SchwartzMap (Euclidean d) ℂ)
    (V : SeqL2 Λ →ₗᵢ[ℂ] FullL2 d)
    (hV : ∀ i : Λ, V (lp.single 2 i 1) = translationL2 (-(i : Euclidean d)) (b.toLp 2 volume))
    (S : SeqL2 Λ ≃L[ℂ] DomainL2 Ω)
    (hS : ∀ i : Λ, (S (lp.single 2 i 1) : Euclidean d → ℂ) =ᵐ[volume.restrict Ω]
      exponential (i : Euclidean d))
    {c : ℝ} (hc : 0 < c) (hl : ∀ x ∈ Ω, c ≤ ‖Real.fourierIntegralInv b x‖) :
    ‖(fourierProjection Ω hΩ).op - (isometryRangeProjection V).op‖ < 1 := by
  apply ((fourierProjection Ω hΩ).gap_iff_rangeIso (isometryRangeProjection V)).mpr
  apply rangeIso_of_synthesis (fourierProjection Ω hΩ) (isometryRangeProjection V)
    V (fourierDomainEmbedding Ω hΩ) (isometryRangeProjection_range V).symm
    (fourierDomainEmbedding_range Ω hΩ) (S.trans (bumpFourierMultiplier Ω hΩ b hc hl))
  intro a
  have he := DFunLike.congr_fun (bump_synthesis_identity hΩ b V hV S hS hc hl) a
  rw [← fourierDomainEmbedding_restriction Ω hΩ (V a)]
  exact congrArg (fourierDomainEmbedding Ω hΩ) he
/-- Every exponential Riesz basis on a bounded domain supplies the paper's small bump and initial gap. -/
theorem exists_initial_bump_gap {d : ℕ} {Ω Λ : Set (Euclidean d)}
    (hΩ : MeasurableSet Ω) (hb : Bornology.IsBounded Ω)
    (hB : HasExponentialRieszBasis Ω Λ) :
    ∃ δ r : ℝ, 0 < δ ∧ Separated δ Λ ∧ 0 < r ∧ 2 * r < δ ∧
      ∃ b : SchwartzMap (Euclidean d) ℂ,
        HasCompactSupport b ∧ ‖b.toLp 2 volume‖ = 1 ∧
        (∀ ξ, (b ξ).im = 0 ∧ 0 ≤ (b ξ).re) ∧
        (∀ ξ, r ≤ ‖ξ‖ → b ξ = 0) ∧
        (∃ c : ℝ, 0 < c ∧ ∀ x ∈ Ω, c ≤ ‖Real.fourierIntegralInv b x‖) ∧
        ∃ V : SeqL2 Λ →ₗᵢ[ℂ] FullL2 d,
          (∀ i : Λ, V (lp.single 2 i 1) = translationL2 (-(i : Euclidean d)) (b.toLp 2 volume)) ∧
          ‖(fourierProjection Ω hΩ).op - (isometryRangeProjection V).op‖ < 1 := by
  classical
  obtain ⟨δ, hδ, hΛ⟩ := riesz_frequencies_separated hΩ hb hB
  obtain ⟨r, hr, hrδ, b, hs, hn, hp, hz, c, hc, hl⟩ := exists_bump_fourier_lower hb hδ
  let V := bumpSynthesis hΛ hrδ b hz hn
  have hV : ∀ i : Λ, V (lp.single 2 i 1) =
      translationL2 (-(i : Euclidean d)) (b.toLp 2 volume) := by
    intro i
    exact orthonormalSynthesis_single (translated_bumps_orthonormal hΛ hrδ b hz hn) i
  obtain ⟨S, hS⟩ := hB
  exact ⟨δ, r, hδ, hΛ, hr, hrδ, b, hs, hn, hp, hz, ⟨c, hc, hl⟩,
    V, hV, initial_bump_gap hΩ b V hV S hS hc hl⟩
end RieszEuclidean
