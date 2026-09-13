import RieszEuclidean.PolygonCutoffObstruction
import RieszEuclidean.AveragedLimitGap
import RieszEuclidean.StationaryAssemblyHelpers
import RieszEuclidean.StationaryComparisonProjection
import RieszEuclidean.HullGap
import RieszEuclidean.HullInvariantMeasure

noncomputable section
open MeasureTheory Filter Topology
namespace RieszEuclidean.SeparatedConfiguration

variable {ι : Type*} [Fintype ι]

/-- The actual unpaired polygon-face Fourier-to-bump hull gap contradicts the stationary boundary
jump, assuming only existence of representing measures for the hull correlations. -/
theorem unpairedSupportingFace_hull_gap_obstruction {δ r M γ : ℝ}
    (normal : ι → Euclidean 2) (offset : ι → ℝ) (j : ι)
    (hnormal : normal j ≠ 0) (hface : (strictSupportingFace normal offset j).Nonempty)
    (hparallel : ∀ i, i ≠ j → ∀ r : ℝ, normal i ≠ r • normal j)
    (hbounded : Bornology.IsBounded (strictHalfspaceIntersection normal offset)) (hδ : 0 < δ) (Γ : SeparatedConfiguration 2 δ)
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
      ‖(fourierProjection (strictHalfspaceIntersection normal offset) (strictHalfspaceIntersection_isOpen normal offset).measurableSet).op -
        (isometryRangeProjection (bumpSynthesis Δ.val.separated hr b hs hn)).op‖ ≤ γ) : False := by
  letI := separableSpace_hullLp hδ Γ μ
  obtain ⟨v, _, hν, hdom⟩ := exists_spectralControlMeasure
    (hullKoopmanUnitary hδ Γ μ hμ) (hullKoopmanUnitary_zero hδ Γ μ hμ)
    σ hσ (Lp.const 2 μ (1 : ℂ)) norm_stationary_one
  letI := hν
  have hfin : volume (strictHalfspaceIntersection normal offset) ≠ ⊤ :=
    (hbounded).measure_lt_top.ne
  obtain ⟨_, hG, P, hP, _, hnorm, hdiff, hPg⟩ :=
    exists_stationary_cutoff_family_with_comparison_gap hδ Γ μ hμ σ hσ
      (spectralControlMeasure σ v) hdom (strictHalfspaceIntersection normal offset)
      (strictHalfspaceIntersection_isOpen normal offset).measurableSet hfin (strictHalfspaceIntersection_volume_frontier normal offset)
      hr b hcompact hs hn hM hb hγ hgap
  have hnorm' : ∀ t f, ‖P t f‖ ^ 2 =
      ∫ θ, ‖cutoffSymbol (strictHalfspaceIntersection normal offset) t θ‖ ^ 2 ∂σ f := by
    intro t f
    letI := (hσ f).1
    rw [integral_cutoffSymbol_sq (σ f) (strictHalfspaceIntersection normal offset)
      (strictHalfspaceIntersection_isOpen normal offset).measurableSet]
    exact hnorm t f
  have hσone : σ (Lp.const 2 μ (1 : ℂ)) = Measure.dirac 0 :=
    (hσ _).unique (represents_hullCorrelation_one hδ Γ μ hμ)
  exact unpairedSupportingFace_cutoffs_continuous_comparison_obstruction normal offset j hnormal hface hparallel hG
    σ (fun f => (hσ f).1) (spectralControlMeasure σ v) hdom P hP hnorm' hdiff
    (Lp.const 2 μ (1 : ℂ)) norm_stationary_one hσone
    (stationaryComparison hδ Γ μ hμ hr.le b b.continuous hcompact hs hM hb)
    (continuous_stationaryComparison hδ Γ μ hμ hr.le b b.continuous hcompact hs hM hb)
    (stationaryComparison_isSelfAdjoint hδ Γ μ hμ hr.le b b.continuous hcompact hs hM hb)
    (stationaryComparison_idempotent hδ Γ μ hμ hr.le b b.continuous hcompact hs hM hb
      (integral_sq_norm_schwartz_of_toLp_norm_one b hn)) hγlt hPg

/-- For a bounded finite halfspace domain with a genuine unpaired face, the Riesz basis assumption reduces
given representing measures on stationary hulls. -/
theorem unpairedSupportingFace_no_exponentialRieszBasis_of_hull_representations
    (normal : ι → Euclidean 2) (offset : ι → ℝ) (j : ι)
    (hnormal : normal j ≠ 0) (hface : (strictSupportingFace normal offset j).Nonempty)
    (hparallel : ∀ i, i ≠ j → ∀ r : ℝ, normal i ≠ r • normal j)
    (hbounded : Bornology.IsBounded (strictHalfspaceIntersection normal offset))
    (hrep : ∀ {δ : ℝ} (hδ : 0 < δ) (Γ : SeparatedConfiguration 2 δ)
      [MeasurableSpace (hull Γ)] [BorelSpace (hull Γ)]
      (μ : Measure (hull Γ)) [IsProbabilityMeasure μ]
      (hμ : ∀ z : Euclidean 2, MeasurePreserving (hullTranslate hδ Γ z) μ μ),
      ∃ σ : Lp ℂ 2 μ → Measure (Euclidean 2),
        ∀ f, RepresentsCorrelation
          (unitaryCorrelation (hullKoopmanUnitary hδ Γ μ hμ) f) (σ f))
    (Λ : Set (Euclidean 2)) : ¬ HasExponentialRieszBasis (strictHalfspaceIntersection normal offset) Λ := by
  intro hB
  obtain ⟨δ, r, hδ, _, hr, Γ, b, hs, hn, _, hcompact, _, γ, hγ, hγlt, hgap⟩ :=
    exists_riesz_basis_uniform_hull_gap (strictHalfspaceIntersection_isOpen normal offset).measurableSet
      (hbounded) hB
  letI : MeasurableSpace (hull Γ) := borel (hull Γ)
  letI : BorelSpace (hull Γ) := ⟨rfl⟩
  letI : CompactSpace (hull Γ) := isCompact_iff_compactSpace.mp (isCompact_hull hδ Γ)
  obtain ⟨μ, hμprob, hμ⟩ := exists_hull_invariant_probability hδ Γ
  letI := hμprob
  obtain ⟨σ, hσ⟩ := hrep hδ Γ μ hμ
  exact unpairedSupportingFace_hull_gap_obstruction normal offset j hnormal hface hparallel hbounded hδ Γ μ hμ σ hσ hr b hcompact hs hn
    (show 0 ≤ SchwartzMap.seminorm ℝ 0 0 b from apply_nonneg _ _)
    (SchwartzMap.norm_le_seminorm ℝ b) hγ hγlt (fun Δ => hgap Δ.val Δ.property)

/-- Every bounded normalized irredundant odd-sided planar halfspace polygon has no
exponential Riesz basis, given the stationary hull correlation representations.
The unpaired face and all boundary jump data are derived from the odd-side geometry. -/
theorem oddSupportingPolygon_no_exponentialRieszBasis_of_hull_representations
    (normal : ι → Euclidean 2) (offset : ι → ℝ)
    (hunit : ∀ i, ‖normal i‖ = 1)
    (hface : ∀ i, (strictSupportingFace normal offset i).Nonempty)
    (hodd : Odd (Fintype.card ι))
    (hbounded : Bornology.IsBounded (strictHalfspaceIntersection normal offset))
    (hrep : ∀ {δ : ℝ} (hδ : 0 < δ) (Γ : SeparatedConfiguration 2 δ)
      [MeasurableSpace (hull Γ)] [BorelSpace (hull Γ)]
      (μ : Measure (hull Γ)) [IsProbabilityMeasure μ]
      (hμ : ∀ z : Euclidean 2, MeasurePreserving (hullTranslate hδ Γ z) μ μ),
      ∃ σ : Lp ℂ 2 μ → Measure (Euclidean 2),
        ∀ f, RepresentsCorrelation
          (unitaryCorrelation (hullKoopmanUnitary hδ Γ μ hμ) f) (σ f))
    (Λ : Set (Euclidean 2)) :
    ¬ HasExponentialRieszBasis (strictHalfspaceIntersection normal offset) Λ := by
  obtain ⟨j, hj⟩ := odd_strictSupportingFaces_exists_unpaired normal offset hunit hface hodd
  exact unpairedSupportingFace_no_exponentialRieszBasis_of_hull_representations
    normal offset j (fun h => by simpa only [h, norm_zero, zero_ne_one] using hunit j)
    (hface j) hj hbounded hrep Λ

end RieszEuclidean.SeparatedConfiguration
