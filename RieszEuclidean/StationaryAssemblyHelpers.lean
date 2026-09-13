import RieszEuclidean.AveragedLimitGap
import RieszEuclidean.ControlMeasure
noncomputable section
open MeasureTheory
namespace RieszEuclidean
/-- The scalar squared integral of a normalized Schwartz bump is one. -/
theorem integral_sq_norm_schwartz_of_toLp_norm_one {d : ℕ}
    (b : SchwartzMap (Euclidean d) ℂ) (hn : ‖b.toLp 2 volume‖ = 1) :
    (∫ x, ‖b x‖ ^ 2) = 1 := by
  have he : (∫ x, ‖b x‖ ^ 2) = ∫ x, ‖(b.toLp 2 volume : FullL2 d) x‖ ^ 2 := by
    apply integral_congr_ae
    filter_upwards [b.coeFn_toLp 2 volume] with x hx
    rw [hx]
  rw [he, integral_sq_norm_fullL2, hn, one_pow]
namespace SeparatedConfiguration
/-- The actual comparison projections vary continuously in operator norm. -/
theorem continuous_stationaryComparison {d : ℕ} {δ r M : ℝ} (hδ : 0 < δ)
    (Γ : SeparatedConfiguration d δ) [MeasurableSpace (hull Γ)] [BorelSpace (hull Γ)]
    [CompactSpace (hull Γ)] (μ : Measure (hull Γ)) [IsProbabilityMeasure μ]
    (hμ : ∀ z : Euclidean d, MeasurePreserving (hullTranslate hδ Γ z) μ μ)
    (hr : 2 * r ≤ δ) (b : Euclidean d → ℂ)
    (hbc : Continuous b) (hcompact : HasCompactSupport b)
    (hs : ∀ x, r ≤ ‖x‖ → b x = 0) (hM : 0 ≤ M) (hb : ∀ x, ‖b x‖ ≤ M) :
    Continuous (stationaryComparison hδ Γ μ hμ hr b hbc hcompact hs hM hb) := by
  refine LipschitzWith.continuous (LipschitzWith.of_dist_le' (K := 2 * Real.pi * ∫ y : Euclidean d, ‖y‖ * stationaryEnvelope r M y) ?_)
  intro t s
  simpa only [dist_eq_norm] using norm_stationaryComparison_sub_le hδ Γ μ hμ hr b hbc hcompact hs hM hb t s
end SeparatedConfiguration
end RieszEuclidean
