import RieszEuclidean.StationaryAssemblyHelpers
import RieszEuclidean.SphereCutoffObstruction
import RieszEuclidean.HullInvariantMeasure
noncomputable section
open MeasureTheory Metric
namespace RieszEuclidean.SeparatedConfiguration
/-- The actual stationary hull data and representing measures contradict a strict bump gap for a ball. -/
theorem sphere_stationary_hull_gap_obstruction {d : ℕ} {δ r ρ γ : ℝ}
    (hd : 2 ≤ d) (a : Euclidean d) (hρ : 0 < ρ)
    (hδ : 0 < δ) (Γ : SeparatedConfiguration d δ)
    [MeasurableSpace (hull Γ)] [BorelSpace (hull Γ)]
    (μ : Measure (hull Γ)) [IsProbabilityMeasure μ]
    (hμ : ∀ z : Euclidean d, MeasurePreserving (hullTranslate hδ Γ z) μ μ)
    (σ : Lp ℂ 2 μ → Measure (Euclidean d))
    (hσ : ∀ f, RepresentsCorrelation (unitaryCorrelation (hullKoopmanUnitary hδ Γ μ hμ) f) (σ f))
    (hr : 2 * r < δ) (b : SchwartzMap (Euclidean d) ℂ)
    (hcompact : HasCompactSupport b) (hs : ∀ x, r ≤ ‖x‖ → b x = 0)
    (hn : ‖b.toLp 2 volume‖ = 1) (hγ0 : 0 ≤ γ) (hγ : γ < 1)
    (hgap : ∀ Δ : hull Γ, ‖(fourierProjection (ball a ρ) measurableSet_ball).op -
      (isometryRangeProjection (bumpSynthesis Δ.val.separated hr b hs hn)).op‖ ≤ γ) : False := by
  letI : CompactSpace (hull Γ) := isCompact_iff_compactSpace.mp (isCompact_hull hδ Γ)
  letI := separableSpace_hullLp hδ Γ μ
  let u : Lp ℂ 2 μ := Lp.const 2 μ (1 : ℂ)
  have hu : ‖u‖ = 1 := norm_stationary_one
  obtain ⟨h, _, hν, hdom⟩ := exists_spectralControlMeasure (hullKoopmanUnitary hδ Γ μ hμ)
    (hullKoopmanUnitary_zero hδ Γ μ hμ) σ hσ u hu
  let ν := spectralControlMeasure σ h
  letI : IsProbabilityMeasure ν := hν
  let C : ℝ := max 0 (SchwartzMap.seminorm ℝ 0 0 b)
  have hC : 0 ≤ C := le_max_left _ _
  have hb : ∀ x, ‖b x‖ ≤ C := fun x => (b.norm_le_seminorm ℝ x).trans (le_max_right _ _)
  have hfin : volume (ball a ρ) ≠ ⊤ := isBounded_ball.measure_lt_top.ne
  have hboundary : volume (frontier (ball a ρ)) = 0 := by
    rw [frontier_ball a hρ.ne']
    exact volume_sphere_eq_zero a hρ.ne'
  obtain ⟨_, hG, P, hP, _, hnorm, hdiff, hPg⟩ :=
    exists_stationary_cutoff_family_with_comparison_gap hδ Γ μ hμ σ hσ ν hdom
      (ball a ρ) measurableSet_ball hfin hboundary hr b hcompact hs hn hC hb hγ0 hgap
  have hnorm' (t : goodParameters ν (frontier (ball a ρ))) (f : Lp ℂ 2 μ) :
      ‖P t f‖ ^ 2 = ∫ θ, ‖cutoffSymbol (ball a ρ) t θ‖ ^ 2 ∂σ f := by
    letI := (hσ f).1
    rw [hnorm, integral_cutoffSymbol_sq (σ f) (ball a ρ) measurableSet_ball t]
  have hσu : σ u = Measure.dirac 0 := (hσ u).unique (represents_hullCorrelation_one hδ Γ μ hμ)
  exact sphere_cutoffs_continuous_comparison_obstruction hd a hρ hG σ
    (fun f => (hσ f).1) ν hdom P hP hnorm' hdiff u hu hσu
    (stationaryComparison hδ Γ μ hμ hr.le b b.continuous hcompact hs hC hb)
    (continuous_stationaryComparison hδ Γ μ hμ hr.le b b.continuous hcompact hs hC hb)
    (stationaryComparison_isSelfAdjoint hδ Γ μ hμ hr.le b b.continuous hcompact hs hC hb)
    (stationaryComparison_idempotent hδ Γ μ hμ hr.le b b.continuous hcompact hs hC hb
      (integral_sq_norm_schwartz_of_toLp_norm_one b hn)) hγ hPg
/-- Conditional only on representing measures for actual stationary correlations, balls have no exponential Riesz basis. -/
theorem not_hasExponentialRieszBasis_ball_of_hull_representations {d : ℕ}
    (hd : 2 ≤ d) (a : Euclidean d) {ρ : ℝ} (hρ : 0 < ρ)
    (hrep : ∀ {δ : ℝ} (hδ : 0 < δ) (Γ : SeparatedConfiguration d δ)
      [MeasurableSpace (hull Γ)] [BorelSpace (hull Γ)]
      (μ : Measure (hull Γ)) [IsProbabilityMeasure μ]
      (hμ : ∀ z : Euclidean d, MeasurePreserving (hullTranslate hδ Γ z) μ μ),
      ∃ σ : Lp ℂ 2 μ → Measure (Euclidean d), ∀ f,
        RepresentsCorrelation (unitaryCorrelation (hullKoopmanUnitary hδ Γ μ hμ) f) (σ f))
    (Λ : Set (Euclidean d)) : ¬HasExponentialRieszBasis (ball a ρ) Λ := by
  intro hB
  obtain ⟨δ, r, hδ, _, hr, Γ, b, hs, hn, _, hcompact, _, γ, hγ0, hγ, hgap⟩ :=
    exists_riesz_basis_uniform_hull_gap measurableSet_ball isBounded_ball hB
  letI : MeasurableSpace (hull Γ) := borel (hull Γ)
  letI : BorelSpace (hull Γ) := ⟨rfl⟩
  obtain ⟨μ, hprob, hμ⟩ := exists_hull_invariant_probability hδ Γ
  letI : IsProbabilityMeasure μ := hprob
  obtain ⟨σ, hσ⟩ := hrep hδ Γ μ hμ
  exact sphere_stationary_hull_gap_obstruction hd a hρ hδ Γ μ hμ σ hσ hr b hcompact hs hn hγ0 hγ
    (fun Δ => hgap Δ.val Δ.property)
end RieszEuclidean.SeparatedConfiguration
