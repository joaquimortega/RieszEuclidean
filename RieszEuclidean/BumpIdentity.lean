import RieszEuclidean.BumpMultiplier
import RieszEuclidean.DomainRestriction
open MeasureTheory
namespace RieszEuclidean
/-- The domain multiplier has its exact Fourier representative. -/
theorem bumpFourierMultiplier_coe {d : ℕ} (Ω : Set (Euclidean d)) (hΩ : MeasurableSet Ω)
    (b : SchwartzMap (Euclidean d) ℂ) {c : ℝ} (hc : 0 < c)
    (hl : ∀ x ∈ Ω, c ≤ ‖Real.fourierIntegralInv b x‖) (f : DomainL2 Ω) :
    (bumpFourierMultiplier Ω hΩ b hc hl f : Euclidean d → ℂ) =ᵐ[volume.restrict Ω]
      fun x => Real.fourierIntegralInv b x * f x := by
  unfold bumpFourierMultiplier
  exact l2MultiplierEquiv_coe _ _ _ _ _ f
/-- On coordinate vectors the Fourier restriction of bump synthesis is multiplier times Riesz synthesis. -/
theorem bump_synthesis_coordinate {d : ℕ} {Ω Λ : Set (Euclidean d)}
    (hΩ : MeasurableSet Ω) (b : SchwartzMap (Euclidean d) ℂ)
    (V : SeqL2 Λ →ₗᵢ[ℂ] FullL2 d)
    (hV : ∀ i : Λ, V (lp.single 2 i 1) = translationL2 (-(i : Euclidean d)) (b.toLp 2 volume))
    (S : SeqL2 Λ ≃L[ℂ] DomainL2 Ω)
    (hS : ∀ i : Λ, (S (lp.single 2 i 1) : Euclidean d → ℂ) =ᵐ[volume.restrict Ω]
      exponential (i : Euclidean d))
    {c : ℝ} (hc : 0 < c) (hl : ∀ x ∈ Ω, c ≤ ‖Real.fourierIntegralInv b x‖) (i : Λ) :
    domainRestriction Ω (paperFourierL2 d (V (lp.single 2 i 1))) =
      bumpFourierMultiplier Ω hΩ b hc hl (S (lp.single 2 i 1)) := by
  rw [hV]
  apply Lp.ext
  have ht := (paperFourierL2_translated_bump b (i : Euclidean d)).filter_mono
    (ae_mono (Measure.restrict_le_self (s := Ω)))
  filter_upwards [domainRestriction_coe Ω
      (paperFourierL2 d (translationL2 (-(i : Euclidean d)) (b.toLp 2 volume))),
    ht, bumpFourierMultiplier_coe Ω hΩ b hc hl (S (lp.single 2 i 1)), hS i]
    with x h1 h2 h3 h4
  rw [h1, h2, h3, h4, mul_comm]
/-- Continuous linear maps on complex ℓ² are determined by unit coordinate vectors. -/
theorem seqL2_ext_on_single {ι H : Type} [DecidableEq ι] [NormedAddCommGroup H]
    [NormedSpace ℂ H] (A B : SeqL2 ι →L[ℂ] H)
    (h : ∀ i, A (lp.single 2 i 1) = B (lp.single 2 i 1)) : A = B := by
  apply lp.ext_continuousLinearMap (by norm_num : (2 : ENNReal) ≠ ⊤)
  intro i
  apply ContinuousLinearMap.ext
  intro z
  change A (lp.single 2 i z) = B (lp.single 2 i z)
  have hz : lp.single (E := fun _ : ι => ℂ) 2 i z = z • lp.single 2 i 1 := by
    rw [← lp.single_smul]
    simp
  rw [hz, map_smul, map_smul, h]
/-- The exact synthesis identity holds on all square-summable coefficient sequences. -/
theorem bump_synthesis_identity {d : ℕ} {Ω Λ : Set (Euclidean d)}
    (hΩ : MeasurableSet Ω) (b : SchwartzMap (Euclidean d) ℂ)
    (V : SeqL2 Λ →ₗᵢ[ℂ] FullL2 d)
    (hV : ∀ i : Λ, V (lp.single 2 i 1) = translationL2 (-(i : Euclidean d)) (b.toLp 2 volume))
    (S : SeqL2 Λ ≃L[ℂ] DomainL2 Ω)
    (hS : ∀ i : Λ, (S (lp.single 2 i 1) : Euclidean d → ℂ) =ᵐ[volume.restrict Ω]
      exponential (i : Euclidean d))
    {c : ℝ} (hc : 0 < c) (hl : ∀ x ∈ Ω, c ≤ ‖Real.fourierIntegralInv b x‖) :
    (domainRestrictionCLM Ω).comp
      ((paperFourierL2 d).toContinuousLinearEquiv.toContinuousLinearMap.comp V.toContinuousLinearMap) =
      (bumpFourierMultiplier Ω hΩ b hc hl).toContinuousLinearMap.comp S.toContinuousLinearMap := by
  apply seqL2_ext_on_single
  intro i
  exact bump_synthesis_coordinate hΩ b V hV S hS hc hl i
end RieszEuclidean
