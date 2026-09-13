import RieszEuclidean.TriangleCutoffObstruction
import RieszEuclidean.AveragedLimitGap
import RieszEuclidean.StationaryAssemblyHelpers
import RieszEuclidean.StationaryComparisonProjection
import RieszEuclidean.HullGap
import RieszEuclidean.HullInvariantMeasure

noncomputable section
open MeasureTheory Filter Topology
namespace RieszEuclidean.SeparatedConfiguration

/-- The actual triangle Fourier-to-bump hull gap contradicts the stationary boundary
jump, assuming only existence of representing measures for the hull correlations. -/
theorem standardTriangle_hull_gap_obstruction {δ r M γ : ℝ}
    (s : ℝ) (hspos : 0 < s) (hδ : 0 < δ) (Γ : SeparatedConfiguration 2 δ)
    [MeasurableSpace (hull Γ)] [BorelSpace (hull Γ)] [CompactSpace (hull Γ)]
    (μ : Measure (hull Γ)) [IsProbabilityMeasure μ]
    (hμ : ∀ z : Euclidean 2, MeasurePreserving (hullTranslate hδ Γ z) μ μ)
    (σ : Lp ℂ 2 μ → Measure (Euclidean 2))
    (hσ : ∀ f, RepresentsCorrelation (unitaryCorrelation (hullKoopmanUnitary hδ Γ μ hμ) f) (σ f))
    (hr : 2 * r < δ) (b : SchwartzMap (Euclidean 2) ℂ)
    (hcompact : HasCompactSupport b) (hs : ∀ x, r ≤ ‖x‖ → b x = 0)
    (hn : ‖b.toLp 2 volume‖ = 1) (hM : 0 ≤ M) (hb : ∀ x, ‖b x‖ ≤ M)
    (hγ : 0 ≤ γ) (hγlt : γ < 1)
    (hgap : ∀ Δ : hull Γ,
      ‖(fourierProjection (standardTriangle s) (standardTriangle_isOpen s).measurableSet).op -
        (isometryRangeProjection (bumpSynthesis Δ.val.separated hr b hs hn)).op‖ ≤ γ) : False := by
  letI := separableSpace_hullLp hδ Γ μ
  obtain ⟨v, _, hν, hdom⟩ := exists_spectralControlMeasure
    (hullKoopmanUnitary hδ Γ μ hμ) (hullKoopmanUnitary_zero hδ Γ μ hμ)
    σ hσ (Lp.const 2 μ (1 : ℂ)) norm_stationary_one
  letI := hν
  have hfin : volume (standardTriangle s) ≠ ⊤ :=
    (standardTriangle_isBounded s hspos.le).measure_lt_top.ne
  obtain ⟨_, hG, P, hP, _, hnorm, hdiff, hPg⟩ :=
    exists_stationary_cutoff_family_with_comparison_gap hδ Γ μ hμ σ hσ
      (spectralControlMeasure σ v) hdom (standardTriangle s)
      (standardTriangle_isOpen s).measurableSet hfin (standardTriangle_volume_frontier s)
      hr b hcompact hs hn hM hb hγ hgap
  have hnorm' : ∀ t f, ‖P t f‖ ^ 2 =
      ∫ θ, ‖cutoffSymbol (standardTriangle s) t θ‖ ^ 2 ∂σ f := by
    intro t f
    letI := (hσ f).1
    rw [integral_cutoffSymbol_sq (σ f) (standardTriangle s)
      (standardTriangle_isOpen s).measurableSet]
    exact hnorm t f
  have hσone : σ (Lp.const 2 μ (1 : ℂ)) = Measure.dirac 0 :=
    (hσ _).unique (represents_hullCorrelation_one hδ Γ μ hμ)
  exact standardTriangle_cutoffs_continuous_comparison_obstruction s hspos hG
    σ (fun f => (hσ f).1) (spectralControlMeasure σ v) hdom P hP hnorm' hdiff
    (Lp.const 2 μ (1 : ℂ)) norm_stationary_one hσone
    (stationaryComparison hδ Γ μ hμ hr.le b b.continuous hcompact hs hM hb)
    (continuous_stationaryComparison hδ Γ μ hμ hr.le b b.continuous hcompact hs hM hb)
    (stationaryComparison_isSelfAdjoint hδ Γ μ hμ hr.le b b.continuous hcompact hs hM hb)
    (stationaryComparison_idempotent hδ Γ μ hμ hr.le b b.continuous hcompact hs hM hb
      (integral_sq_norm_schwartz_of_toLp_norm_one b hn)) hγlt hPg

/-- For the literal standard triangle, the exponential Riesz basis assumption reduces
given representing measures on stationary hulls. -/
theorem standardTriangle_no_exponentialRieszBasis_of_hull_representations
    (s : ℝ) (hspos : 0 < s)
    (hrep : ∀ {δ : ℝ} (hδ : 0 < δ) (Γ : SeparatedConfiguration 2 δ)
      [MeasurableSpace (hull Γ)] [BorelSpace (hull Γ)]
      (μ : Measure (hull Γ)) [IsProbabilityMeasure μ]
      (hμ : ∀ z : Euclidean 2, MeasurePreserving (hullTranslate hδ Γ z) μ μ),
      ∃ σ : Lp ℂ 2 μ → Measure (Euclidean 2),
        ∀ f, RepresentsCorrelation
          (unitaryCorrelation (hullKoopmanUnitary hδ Γ μ hμ) f) (σ f))
    (Λ : Set (Euclidean 2)) : ¬ HasExponentialRieszBasis (standardTriangle s) Λ := by
  intro hB
  obtain ⟨δ, r, hδ, _, hr, Γ, b, hs, hn, _, hcompact, _, γ, hγ, hγlt, hgap⟩ :=
    exists_riesz_basis_uniform_hull_gap (standardTriangle_isOpen s).measurableSet
      (standardTriangle_isBounded s hspos.le) hB
  letI : MeasurableSpace (hull Γ) := borel (hull Γ)
  letI : BorelSpace (hull Γ) := ⟨rfl⟩
  letI : CompactSpace (hull Γ) := isCompact_iff_compactSpace.mp (isCompact_hull hδ Γ)
  obtain ⟨μ, hμprob, hμ⟩ := exists_hull_invariant_probability hδ Γ
  letI := hμprob
  obtain ⟨σ, hσ⟩ := hrep hδ Γ μ hμ
  exact standardTriangle_hull_gap_obstruction s hspos hδ Γ μ hμ σ hσ hr b hcompact hs hn
    (show 0 ≤ SchwartzMap.seminorm ℝ 0 0 b from apply_nonneg _ _)
    (SchwartzMap.norm_le_seminorm ℝ b) hγ hγlt (fun Δ => hgap Δ.val Δ.property)

end RieszEuclidean.SeparatedConfiguration
