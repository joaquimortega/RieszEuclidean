import RieszEuclidean.StationaryAssemblyHelpers
import RieszEuclidean.BoundaryCutoffLimits
import RieszEuclidean.HullGap
import RieszEuclidean.HullInvariantMeasure
import RieszEuclidean.StationaryComparisonProjection

noncomputable section
open MeasureTheory Filter Topology
namespace RieszEuclidean

/-- Positive measure in every neighborhood puts the point in the ordinary closure. -/
theorem mem_closure_of_positive_neighborhood_measure {d : ℕ} {Ω : Set (Euclidean d)}
    {t : Euclidean d} (h : ∀ V ∈ nhds t, 0 < volume (V ∩ Ω)) : t ∈ closure Ω := by
  apply _root_.mem_closure_iff.mpr
  intro V hV htV
  exact nonempty_of_measure_ne_zero (h V (hV.mem_nhds htV)).ne'

/-- The manuscript's boundary overlap and local separation conditions select one
point that is simultaneously clean for the entire control measure and approachable
from both ambient open sides. -/
theorem exists_clean_two_sided_boundary_point {d : ℕ} {Ω : Set (Euclidean d)}
    (ν : Measure (Euclidean d)) [IsFiniteMeasure ν] (hν : ν ≠ 0)
    (hsupport : ν (frontier Ω)ᶜ = 0)
    (hoverlap : ∀ θ : Euclidean d, θ ≠ 0 →
      ν (frontier Ω ∩ RieszEuclidean.translate θ (frontier Ω)) = 0)
    (hsep : ∀ᵐ t ∂ν, ∀ V ∈ nhds t,
      0 < volume (V ∩ Ω) ∧ 0 < volume (V ∩ (closure Ω)ᶜ))
    (σ : Measure (Euclidean d)) [SFinite σ] :
    ∃ t ∈ frontier Ω,
      σ {θ | θ ≠ 0 ∧ t + θ ∈ frontier Ω} = 0 ∧
      t ∈ closure Ω ∧ t ∈ closure (closure Ω)ᶜ := by
  haveI : NeZero ν := ⟨hν⟩
  have htranslate (θ : Euclidean d) (hθ : θ ≠ 0) : ν {t | t + θ ∈ frontier Ω} = 0 := by
    rw [← measure_inter_conull hsupport, Set.inter_comm]
    exact hoverlap θ hθ
  have hclean := boundary_exceptional_mass_ae_zero σ ν isClosed_frontier.measurableSet htranslate
  have hboundary : ∀ᵐ t ∂ν, t ∈ frontier Ω := by
    simpa only [compl_compl] using compl_mem_ae_iff.mpr hsupport
  have hall : ∀ᵐ t ∂ν, t ∈ frontier Ω ∧
      σ {θ | θ ≠ 0 ∧ t + θ ∈ frontier Ω} = 0 ∧
      t ∈ closure Ω ∧ t ∈ closure (closure Ω)ᶜ := by
    filter_upwards [hclean, hboundary, hsep] with t ht hb hs
    exact ⟨hb, ht,
      mem_closure_of_positive_neighborhood_measure (fun V hV => (hs V hV).1),
      mem_closure_of_positive_neighborhood_measure (fun V hV => (hs V hV).2)⟩
  exact hall.exists

namespace SeparatedConfiguration

/-- For the exact general boundary-measure criterion, actual stationary hull data
and representing correlations contradict any strict uniform Fourier-to-bump gap. -/
theorem general_boundary_hull_gap_obstruction {d : ℕ} {δ r M γ : ℝ}
    (Ω : Set (Euclidean d)) (hΩ : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
    (hboundary : volume (frontier Ω) = 0)
    (ν : Measure (Euclidean d)) [IsFiniteMeasure ν] (hν : ν ≠ 0)
    (hsupport : ν (frontier Ω)ᶜ = 0)
    (hoverlap : ∀ θ : Euclidean d, θ ≠ 0 →
      ν (frontier Ω ∩ RieszEuclidean.translate θ (frontier Ω)) = 0)
    (hsep : ∀ᵐ t ∂ν, ∀ V ∈ nhds t,
      0 < volume (V ∩ Ω) ∧ 0 < volume (V ∩ (closure Ω)ᶜ))
    (hδ : 0 < δ) (Γ : SeparatedConfiguration d δ)
    [MeasurableSpace (hull Γ)] [BorelSpace (hull Γ)]
    (μ : Measure (hull Γ)) [IsProbabilityMeasure μ]
    (hμ : ∀ z : Euclidean d, MeasurePreserving (hullTranslate hδ Γ z) μ μ)
    (σ : Lp ℂ 2 μ → Measure (Euclidean d))
    (hσ : ∀ f, RepresentsCorrelation (unitaryCorrelation (hullKoopmanUnitary hδ Γ μ hμ) f) (σ f))
    (hr : 2 * r < δ) (b : SchwartzMap (Euclidean d) ℂ)
    (hcompact : HasCompactSupport b) (hs : ∀ x, r ≤ ‖x‖ → b x = 0)
    (hn : ‖b.toLp 2 volume‖ = 1) (hM : 0 ≤ M) (hb : ∀ x, ‖b x‖ ≤ M)
    (hγ : 0 ≤ γ) (hγlt : γ < 1)
    (hgap : ∀ Δ : hull Γ, ‖(fourierProjection Ω hΩ.measurableSet).op -
      (isometryRangeProjection (bumpSynthesis Δ.val.separated hr b hs hn)).op‖ ≤ γ) : False := by
  letI : CompactSpace (hull Γ) := isCompact_iff_compactSpace.mp (isCompact_hull hδ Γ)
  letI := separableSpace_hullLp hδ Γ μ
  obtain ⟨v, _, hτ, hdom⟩ := exists_spectralControlMeasure
    (hullKoopmanUnitary hδ Γ μ hμ) (hullKoopmanUnitary_zero hδ Γ μ hμ)
    σ hσ (Lp.const 2 μ (1 : ℂ)) norm_stationary_one
  letI := hτ
  obtain ⟨t₀, ht₀, hclean, _, houtside⟩ := exists_clean_two_sided_boundary_point
    ν hν hsupport hoverlap hsep (spectralControlMeasure σ v)
  obtain ⟨_, hG, P, hP, _, hnorm, hdiff, hPg⟩ :=
    exists_stationary_cutoff_family_with_comparison_gap hδ Γ μ hμ σ hσ
      (spectralControlMeasure σ v) hdom Ω hΩ.measurableSet hbounded.measure_lt_top.ne
      hboundary hr b hcompact hs hn hM hb hγ hgap
  have hnorm' : ∀ t f, ‖P t f‖ ^ 2 = ∫ θ, ‖cutoffSymbol Ω t θ‖ ^ 2 ∂σ f := by
    intro t f
    letI := (hσ f).1
    rw [integral_cutoffSymbol_sq (σ f) Ω hΩ.measurableSet]
    exact hnorm t f
  have hσone : σ (Lp.const 2 μ (1 : ℂ)) = Measure.dirac 0 :=
    (hσ _).unique (represents_hullCorrelation_one hδ Γ μ hμ)
  exact boundary_cutoffs_continuous_comparison_obstruction hΩ hG ht₀ houtside
    σ (fun f => (hσ f).1) (fun f => hdom f hclean) P hP hnorm' hdiff
    (Lp.const 2 μ (1 : ℂ)) norm_stationary_one hσone
    (stationaryComparison hδ Γ μ hμ hr.le b b.continuous hcompact hs hM hb)
    (continuous_stationaryComparison hδ Γ μ hμ hr.le b b.continuous hcompact hs hM hb).continuousAt
    (stationaryComparison_isSelfAdjoint hδ Γ μ hμ hr.le b b.continuous hcompact hs hM hb t₀)
    (stationaryComparison_idempotent hδ Γ μ hμ hr.le b b.continuous hcompact hs hM hb
      (integral_sq_norm_schwartz_of_toLp_norm_one b hn) t₀) hγlt hPg

/-- The manuscript's general boundary condition excludes exponential Riesz bases,
conditional only on representing measures for actual stationary hull correlations.
No smoothness, convexity, or local halfspace description of the boundary is required. -/
theorem no_exponentialRieszBasis_of_general_boundary_and_hull_representations {d : ℕ}
    (Ω : Set (Euclidean d)) (hΩ : IsOpen Ω ∧ Ω.Nonempty) (hbounded : Bornology.IsBounded Ω)
    (hboundary : volume (frontier Ω) = 0)
    (ν : Measure (Euclidean d)) [IsFiniteMeasure ν] (hν : ν ≠ 0)
    (hsupport : ν (frontier Ω)ᶜ = 0)
    (hoverlap : ∀ θ : Euclidean d, θ ≠ 0 →
      ν (frontier Ω ∩ RieszEuclidean.translate θ (frontier Ω)) = 0)
    (hsep : ∀ᵐ t ∂ν, ∀ V ∈ nhds t,
      0 < volume (V ∩ Ω) ∧ 0 < volume (V ∩ (closure Ω)ᶜ))
    (hrep : ∀ {δ : ℝ} (hδ : 0 < δ) (Γ : SeparatedConfiguration d δ)
      [MeasurableSpace (hull Γ)] [BorelSpace (hull Γ)]
      (μ : Measure (hull Γ)) [IsProbabilityMeasure μ]
      (hμ : ∀ z : Euclidean d, MeasurePreserving (hullTranslate hδ Γ z) μ μ),
      ∃ σ : Lp ℂ 2 μ → Measure (Euclidean d),
        ∀ f, RepresentsCorrelation
          (unitaryCorrelation (hullKoopmanUnitary hδ Γ μ hμ) f) (σ f))
    (Λ : Set (Euclidean d)) : ¬ HasExponentialRieszBasis Ω Λ := by
  intro hB
  obtain ⟨δ, r, hδ, _, hr, Γ, b, hs, hn, _, hcompact, _, γ, hγ, hγlt, hgap⟩ :=
    exists_riesz_basis_uniform_hull_gap hΩ.1.measurableSet hbounded hB
  letI : MeasurableSpace (hull Γ) := borel (hull Γ)
  letI : BorelSpace (hull Γ) := ⟨rfl⟩
  obtain ⟨μ, hμprob, hμ⟩ := exists_hull_invariant_probability hδ Γ
  letI := hμprob
  obtain ⟨σ, hσ⟩ := hrep hδ Γ μ hμ
  exact general_boundary_hull_gap_obstruction Ω hΩ.1 hbounded hboundary ν hν hsupport hoverlap hsep
    hδ Γ μ hμ σ hσ hr b hcompact hs hn
    (show 0 ≤ SchwartzMap.seminorm ℝ 0 0 b from apply_nonneg _ _)
    (SchwartzMap.norm_le_seminorm ℝ b) hγ hγlt (fun Δ => hgap Δ.val Δ.property)

end SeparatedConfiguration
end RieszEuclidean
