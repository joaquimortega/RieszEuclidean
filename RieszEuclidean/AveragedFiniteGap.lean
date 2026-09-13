import RieszEuclidean.AveragedCanonicalForms
import RieszEuclidean.AveragedGap
import RieszEuclidean.HullGap
noncomputable section
open MeasureTheory
namespace RieszEuclidean.SeparatedConfiguration
/-- The actual finite Fourier filter and comparison average inherit the uniform hull gap. -/
theorem norm_finiteFilter_sub_stationaryComparisonAverage_le {d : ℕ} {δ r M γ : ℝ}
    (hδ : 0 < δ) (Γ : SeparatedConfiguration d δ)
    [MeasurableSpace (hull Γ)] [BorelSpace (hull Γ)] [CompactSpace (hull Γ)]
    (μ : Measure (hull Γ)) [IsProbabilityMeasure μ]
    (hμ : ∀ z : Euclidean d, MeasurePreserving (hullTranslate hδ Γ z) μ μ)
    (Ω : Set (Euclidean d)) (hΩ : MeasurableSet Ω) (hfin : volume Ω ≠ ⊤)
    (hr : 2 * r < δ) (b : SchwartzMap (Euclidean d) ℂ)
    (hcompact : HasCompactSupport b) (hs : ∀ x, r ≤ ‖x‖ → b x = 0)
    (hn : ‖b.toLp 2 volume‖ = 1) (hM : 0 ≤ M) (hb : ∀ x, ‖b x‖ ≤ M)
    (hγ : 0 ≤ γ)
    (hgap : ∀ Δ : hull Γ, ‖(fourierProjection Ω hΩ).op -
      (isometryRangeProjection (bumpSynthesis Δ.val.separated hr b hs hn)).op‖ ≤ γ)
    (t : Euclidean d) {R : ℝ} (hR : 0 < R) :
    ‖finiteFilter (hullKoopmanUnitary hδ Γ μ hμ)
        (strongContinuous_hullKoopmanUnitary hδ Γ μ hμ) Ω hΩ hfin t hR -
      stationaryComparisonAverage hδ Γ μ hμ hr.le b b.continuous hcompact hs hM hb t R‖ ≤ γ := by
  let J := fun f : Lp ℂ 2 μ => averagedTestL2 R t (hullTranslate hδ Γ) f
  let P := (fourierProjection Ω hΩ).op
  let Q := fun Δ : hull Γ => (isometryRangeProjection (bumpSynthesis Δ.val.separated hr b hs hn)).op
  let F := fun (f g : Lp ℂ 2 μ) (Δ : hull Γ) =>
    inner (𝕜 := ℂ) (J g Δ) (P (J f Δ)) - inner (𝕜 := ℂ) (J g Δ) (Q Δ (J f Δ))
  have hP (f g : Lp ℂ 2 μ) := canonical_averaged_fourier_pairing hδ Γ μ hμ Ω hΩ hfin t hR f g
  have hQ (f g : Lp ℂ 2 μ) := canonical_averaged_bump_pairing hδ Γ μ hμ hr b hcompact hs hn hM hb t hR f g
  refine norm_operator_le_of_averaged_scalar_pairings μ _ (fun f Δ => ‖J f Δ‖)
    (fun f => (hull_averagedTestL2_norm_energy hδ Γ μ hμ f hR t).2.1)
    (fun _ => Filter.Eventually.of_forall fun _ => norm_nonneg _)
    (fun f => (hull_averagedTestL2_norm_energy hδ Γ μ hμ f hR t).2.2) F
    (fun f g => ((hP f g).1.sub (hQ f g).1).aestronglyMeasurable) ?_ hγ ?_
  · intro f g
    change inner (𝕜 := ℂ) g (_ - _) = _
    rw [inner_sub_right]
    exact ((integral_sub (hP f g).1 (hQ f g).1).trans
      (congrArg₂ (fun x y : ℂ => x - y) (hP f g).2 (hQ f g).2)).symm
  · intro f g
    filter_upwards [] with Δ
    change ‖inner (𝕜 := ℂ) (J g Δ) (P (J f Δ)) -
      inner (𝕜 := ℂ) (J g Δ) (Q Δ (J f Δ))‖ ≤ _
    rw [← inner_sub_right]
    change ‖inner (𝕜 := ℂ) (J g Δ) ((P - Q Δ) (J f Δ))‖ ≤ _
    calc
      _ ≤ ‖J g Δ‖ * ‖(P - Q Δ) (J f Δ)‖ := norm_inner_le_norm _ _
      _ ≤ ‖J g Δ‖ * (γ * ‖J f Δ‖) := mul_le_mul_of_nonneg_left
        (((P - Q Δ).le_opNorm (J f Δ)).trans
          (mul_le_mul_of_nonneg_right (hgap Δ) (norm_nonneg _))) (norm_nonneg _)
      _ = _ := by ring
end RieszEuclidean.SeparatedConfiguration
