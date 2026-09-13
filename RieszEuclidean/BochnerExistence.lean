import RieszEuclidean.BochnerApproximateMeasures
import RieszEuclidean.BochnerMeasureLimit
import RieszEuclidean.BochnerFourierLimit
noncomputable section
open MeasureTheory Filter Topology
namespace RieszEuclidean
/-- Bochner existence for actual strongly continuous unitary correlations on a separable Hilbert space. -/
theorem exists_representsCorrelation_unitary {d : ℕ} {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H]
    (U : Euclidean d → H ≃ₗᵢ[ℂ] H) (hU : ∀ f, Continuous (fun x => U x f))
    (hadd : ∀ z y f, U z (U y f) = U (z + y) f) (f : H) :
    ∃ σ : Measure (Euclidean d), RepresentsCorrelation (unitaryCorrelation U f) σ := by
  obtain ⟨s, hs, ⟨e⟩⟩ := exists_countable_hilbertBasis (H := H)
  letI : Countable s := hs
  have hpos (n : ℕ) : 0 < (n : ℝ) + 1 := by positivity
  let μn : ℕ → Measure (Euclidean d) := fun n => bochnerApproxMeasure (hpos n) U hU f e
  letI (n : ℕ) : IsFiniteMeasure (μn n) := bochnerApproxMeasure_finite (hpos n) U hU f e
  have hmass (n : ℕ) : (μn n).real Set.univ ≤ ‖f‖ ^ 2 :=
    le_of_eq (bochnerApproxMeasure_mass (hpos n) U hU f e)
  obtain ⟨σ, hσfin, _, l, hl, hlsub, hvague⟩ :=
    exists_finiteMeasure_vague_limit μn (sq_nonneg ‖f‖) hmass
  letI : IsFiniteMeasure σ := hσfin
  letI : l.NeBot := hl
  refine ⟨σ, representsCorrelation_of_bounded_vague_limit μn σ hmass hlsub
    (tendsto_complex_zeroAtInfty_integrals_of_real μn σ hvague)
    (continuous_unitaryCorrelation U hU f) ?_⟩
  intro y
  have hradius : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
  have hw := (tendsto_fejerWeight y).comp hradius
  have hc := Complex.continuous_ofReal.continuousAt.tendsto.comp hw
  have ht := hc.mul_const (unitaryCorrelation U f y)
  simpa only [measureFourier, μn, bochnerApproxMeasure_fourier _ U hU hadd f e,
    Complex.ofReal_one, one_mul] using ht
/-- Choosing the constructed measures gives a spectral family for every original Hilbert-space vector. -/
theorem exists_unitary_spectralMeasures {d : ℕ} {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H]
    (U : Euclidean d → H ≃ₗᵢ[ℂ] H) (hU : ∀ f, Continuous (fun x => U x f))
    (hadd : ∀ z y f, U z (U y f) = U (z + y) f) :
    ∃ σ : H → Measure (Euclidean d), ∀ f, RepresentsCorrelation (unitaryCorrelation U f) (σ f) := by
  choose σ hσ using exists_representsCorrelation_unitary U hU hadd
  exact ⟨σ, hσ⟩
namespace SeparatedConfiguration
/-- Actual stationary hulls have representing spectral measures, with all existence hypotheses discharged. -/
theorem exists_hull_spectralMeasures {d : ℕ} {δ : ℝ} (hδ : 0 < δ)
    (Γ : SeparatedConfiguration d δ) [MeasurableSpace (hull Γ)] [BorelSpace (hull Γ)]
    (μ : Measure (hull Γ)) [IsProbabilityMeasure μ]
    (hμ : ∀ z : Euclidean d, MeasurePreserving (hullTranslate hδ Γ z) μ μ) :
    ∃ σ : Lp ℂ 2 μ → Measure (Euclidean d), ∀ f,
      RepresentsCorrelation (unitaryCorrelation (hullKoopmanUnitary hδ Γ μ hμ) f) (σ f) := by
  letI := separableSpace_hullLp hδ Γ μ
  exact exists_unitary_spectralMeasures (hullKoopmanUnitary hδ Γ μ hμ)
    (strongContinuous_hullKoopmanUnitary hδ Γ μ hμ) (hullKoopmanUnitary_add hδ Γ μ hμ)
end SeparatedConfiguration
end RieszEuclidean
