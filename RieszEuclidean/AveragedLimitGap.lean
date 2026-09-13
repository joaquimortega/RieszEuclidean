import RieszEuclidean.AveragedFiniteGap
import RieszEuclidean.StationaryCutoffs
noncomputable section
open MeasureTheory Filter Topology
namespace RieszEuclidean.SeparatedConfiguration
/-- The actual stationary cutoff inherits the hull gap from its finite filters. -/
theorem norm_stationaryCutoff_sub_comparison_le {d : ℕ} {δ r M γ : ℝ}
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
    (t : Euclidean d) (P : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ)
    (hlim : ∀ f, Tendsto (fun R : ℝ => integratedUnitary (hullKoopmanUnitary hδ Γ μ hμ)
      (finiteFilterKernel Ω t R) f) atTop (𝓝 (P f))) :
    ‖P - stationaryComparison hδ Γ μ hμ hr.le b b.continuous hcompact hs hM hb t‖ ≤ γ := by
  have hpos (R : ℝ) : 0 < max 1 R := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  let A := fun R : ℝ => finiteFilter (hullKoopmanUnitary hδ Γ μ hμ)
    (strongContinuous_hullKoopmanUnitary hδ Γ μ hμ) Ω hΩ hfin t (hpos R)
  let B := fun R : ℝ => stationaryComparisonAverage hδ Γ μ hμ hr.le b b.continuous hcompact hs hM hb t (max 1 R)
  let C := stationaryComparison hδ Γ μ hμ hr.le b b.continuous hcompact hs hM hb t
  have hA (f : Lp ℂ 2 μ) : Tendsto (fun R => A R f) atTop (𝓝 (P f)) := by
    apply (hlim f).congr'
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with R hR
    change integratedUnitary _ (finiteFilterKernel Ω t R) f =
      integratedUnitary _ (finiteFilterKernel Ω t (max 1 R)) f
    rw [max_eq_right hR]
  have hE : Tendsto (fun R => ‖B R - C‖) atTop (𝓝 0) := by
    apply (tendsto_stationaryComparisonAverage_error hδ Γ μ hμ hr.le b b.continuous hcompact hs hM hb
      (fun _ => t)).congr'
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with R hR
    dsimp only [B, C]
    rw [max_eq_right hR]
  have hB (f : Lp ℂ 2 μ) : Tendsto (fun R => B R f) atTop (𝓝 (C f)) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    have he : Tendsto (fun R => ‖B R - C‖ * ‖f‖) atTop (𝓝 0) := by
      simpa using hE.mul_const ‖f‖
    exact squeeze_zero (fun _ => norm_nonneg _) (fun R => (B R - C).le_opNorm f) he
  exact norm_sub_le_of_strong_filter_limits A B P C hγ hA hB
    (Eventually.of_forall fun R => norm_finiteFilter_sub_stationaryComparisonAverage_le
      hδ Γ μ hμ Ω hΩ hfin hr b hcompact hs hn hM hb hγ hgap t (hpos R))
/-- The actual stationary cutoff family has the same uniform comparison gap on every good parameter. -/
theorem exists_stationary_cutoff_family_with_comparison_gap {d : ℕ} {δ r M γ : ℝ}
    (hδ : 0 < δ) (Γ : SeparatedConfiguration d δ)
    [MeasurableSpace (hull Γ)] [BorelSpace (hull Γ)] [CompactSpace (hull Γ)]
    (μ : Measure (hull Γ)) [IsProbabilityMeasure μ]
    (hμ : ∀ z : Euclidean d, MeasurePreserving (hullTranslate hδ Γ z) μ μ)
    (σ : Lp ℂ 2 μ → Measure (Euclidean d))
    (hσ : ∀ f, RepresentsCorrelation (unitaryCorrelation (hullKoopmanUnitary hδ Γ μ hμ) f) (σ f))
    (ν : Measure (Euclidean d)) [SFinite ν] (hdom : ∀ f, σ f ≪ ν)
    (Ω : Set (Euclidean d)) (hΩ : MeasurableSet Ω) (hfin : volume Ω ≠ ⊤)
    (hboundary : volume (frontier Ω) = 0)
    (hr : 2 * r < δ) (b : SchwartzMap (Euclidean d) ℂ)
    (hcompact : HasCompactSupport b) (hs : ∀ x, r ≤ ‖x‖ → b x = 0)
    (hn : ‖b.toLp 2 volume‖ = 1) (hM : 0 ≤ M) (hb : ∀ x, ‖b x‖ ≤ M)
    (hγ : 0 ≤ γ)
    (hgap : ∀ Δ : hull Γ, ‖(fourierProjection Ω hΩ).op -
      (isometryRangeProjection (bumpSynthesis Δ.val.separated hr b hs hn)).op‖ ≤ γ) :
    MeasurableSet (goodParameters ν (frontier Ω)) ∧
      volume (goodParameters ν (frontier Ω))ᶜ = 0 ∧
      ∃ P : goodParameters ν (frontier Ω) → Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ,
        (∀ t, ‖P t‖ ≤ 1 ∧ IsSelfAdjoint (P t) ∧ (P t).comp (P t) = P t) ∧
        (∀ (t : goodParameters ν (frontier Ω)) f, Tendsto (fun R : ℝ =>
          integratedUnitary (hullKoopmanUnitary hδ Γ μ hμ) (finiteFilterKernel Ω t R) f)
          atTop (𝓝 (P t f))) ∧
        (∀ t f, ‖P t f‖ ^ 2 = (σ f).real {θ | (t : Euclidean d) + θ ∈ Ω}) ∧
        (∀ s t f, ‖P s f - P t f‖ ^ 2 =
          ∫ θ, ‖cutoffSymbol Ω s θ - cutoffSymbol Ω t θ‖ ^ 2 ∂σ f) ∧
        (∀ t, ‖P t - stationaryComparison hδ Γ μ hμ hr.le b b.continuous hcompact hs hM hb t‖ ≤ γ) := by
  obtain ⟨hmeas, hnull, P, hP, hlim, hnorm, hdiff⟩ := exists_stationary_cutoff_family
    (hullKoopmanUnitary hδ Γ μ hμ) (strongContinuous_hullKoopmanUnitary hδ Γ μ hμ)
    (hullKoopmanUnitary_add hδ Γ μ hμ) (hullKoopmanUnitary_zero hδ Γ μ hμ)
    σ hσ ν hdom Ω hΩ hfin hboundary
  refine ⟨hmeas, hnull, P, hP, hlim, hnorm, hdiff, ?_⟩
  intro t
  exact norm_stationaryCutoff_sub_comparison_le hδ Γ μ hμ Ω hΩ hfin hr b hcompact hs hn hM hb hγ hgap t (P t) (hlim t)
end RieszEuclidean.SeparatedConfiguration
