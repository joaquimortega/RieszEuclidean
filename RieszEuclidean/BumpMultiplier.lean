import RieszEuclidean.L2Multiplier
import RieszEuclidean.BumpTransform
open MeasureTheory
noncomputable section
namespace RieszEuclidean
/-- A bump with a positive Fourier lower bound gives an invertible multiplier on the domain. -/
def bumpFourierMultiplier {d : ℕ} (Ω : Set (Euclidean d)) (hΩ : MeasurableSet Ω)
    (b : SchwartzMap (Euclidean d) ℂ) {c : ℝ} (hc : 0 < c)
    (hl : ∀ x ∈ Ω, c ≤ ‖Real.fourierIntegralInv b x‖) : DomainL2 Ω ≃L[ℂ] DomainL2 Ω := by
  have hm : AEStronglyMeasurable (Real.fourierIntegralInv b) (volume.restrict Ω) :=
    (VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (continuous_fst.inner continuous_snd).neg b.integrable).aestronglyMeasurable
  have hu : ∀ᵐ x ∂volume.restrict Ω, ‖Real.fourierIntegralInv b x‖ ≤ ∫ ξ, ‖b ξ‖ :=
    Filter.Eventually.of_forall (fun x => VectorFourier.norm_fourierIntegral_le_integral_norm _ _ _ _ _)
  have hl' : ∀ᵐ x ∂volume.restrict Ω, c ≤ ‖Real.fourierIntegralInv b x‖ := by
    filter_upwards [ae_restrict_mem hΩ] with x hx
    exact hl x hx
  exact l2MultiplierEquiv (Real.fourierIntegralInv b) hm hu hc hl'
end RieszEuclidean
