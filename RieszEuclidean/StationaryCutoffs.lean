import RieszEuclidean.FiniteFilters
import RieszEuclidean.SmoothedFejer
import RieszEuclidean.GoodParameters
import RieszEuclidean.SpectralCutoffDifference
/-!
# Stationary spectral cutoffs from the actual finite filters

Given representing spectral measures and a common control measure, the concrete
finite box filters converge strongly to orthogonal contractions simultaneously
on the measurable conull set of good parameters. The spectral mass and difference
identities hold for these same limits. Bochner existence is an explicit dependency.
-/

noncomputable section
open MeasureTheory Set Filter Topology
namespace RieszEuclidean
/-- The spectral indicator of the translated domain. -/
def cutoffSymbol {d : ℕ} (Ω : Set (Euclidean d)) (t θ : Euclidean d) : ℂ :=
  Ω.indicator (fun _ => (1 : ℂ)) (t + θ)

/-- The limiting domain symbol is idempotent. -/
theorem cutoffSymbol_idempotent {d : ℕ} (Ω : Set (Euclidean d)) (t θ : Euclidean d) :
    cutoffSymbol Ω t θ * cutoffSymbol Ω t θ = cutoffSymbol Ω t θ := by
  by_cases h : t + θ ∈ Ω <;> simp [cutoffSymbol, h]

/-- The concrete smoothed symbols converge almost everywhere for any dominated measure. -/
theorem fejerCutoff_ae_tendsto_of_goodParameter {d : ℕ}
    {μ ν : Measure (Euclidean d)} (hdom : ν ≪ μ)
    {Ω : Set (Euclidean d)} (hΩ : MeasurableSet Ω)
    {t : Euclidean d} (ht : t ∈ goodParameters μ (frontier Ω)) :
    ∀ᵐ θ ∂ν, Tendsto (fun R : ℝ => (fejerCutoff Ω R (t + θ) : ℂ)) atTop
      (𝓝 (cutoffSymbol Ω t θ)) := by
  have hn : ν {θ | t + θ ∈ frontier Ω} = 0 := hdom ht
  have ha : ∀ᵐ θ ∂ν, t + θ ∉ frontier Ω := by
    simpa only [ae_iff, not_not] using hn
  filter_upwards [ha] with θ hθ
  have h := Complex.continuous_ofReal.continuousAt.tendsto.comp (tendsto_fejerCutoff hΩ hθ)
  convert h using 1
  by_cases hm : t + θ ∈ Ω <;> simp [cutoffSymbol, hm]
/-- Positive regularization of the radius does not affect the limiting symbols. -/
theorem finiteFilterKernel_ae_symbol_tendsto {d : ℕ}
    (Ω : Set (Euclidean d)) (hΩ : MeasurableSet Ω) (hfin : volume Ω ≠ ⊤)
    {μ ν : Measure (Euclidean d)} (hdom : ν ≪ μ)
    {t : Euclidean d} (ht : t ∈ goodParameters μ (frontier Ω)) :
    ∀ᵐ θ ∂ν, Tendsto (fun R : ℝ =>
      integratedKernelSymbol (finiteFilterKernel Ω t (max 1 R)) θ) atTop
      (𝓝 (cutoffSymbol Ω t θ)) := by
  filter_upwards [fejerCutoff_ae_tendsto_of_goodParameter hdom hΩ ht] with θ hθ
  apply hθ.congr'
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with R hR
  rw [max_eq_right hR, integratedKernelSymbol_finiteFilterKernel_eq_fejerCutoff Ω hΩ hfin t
    (zero_lt_one.trans_le hR)]

/-- The actual finite filters converge to an orthogonal contraction at each good parameter.
The representing measures are supplied explicitly, leaving Bochner existence as a separate dependency. -/
theorem exists_stationary_cutoff {d : ℕ} {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (U : Euclidean d → H ≃ₗᵢ[ℂ] H)
    (hU : ∀ f, Continuous (fun y => U y f))
    (hadd : ∀ z y f, U z (U y f) = U (z + y) f) (h0 : ∀ f, U 0 f = f)
    (σ : H → Measure (Euclidean d))
    (hσ : ∀ f, RepresentsCorrelation (unitaryCorrelation U f) (σ f))
    (μ : Measure (Euclidean d)) (hdom : ∀ f, σ f ≪ μ)
    (Ω : Set (Euclidean d)) (hΩ : MeasurableSet Ω) (hfin : volume Ω ≠ ⊤)
    {t : Euclidean d} (ht : t ∈ goodParameters μ (frontier Ω)) :
    ∃ P : H →L[ℂ] H, ‖P‖ ≤ 1 ∧ IsSelfAdjoint P ∧ P.comp P = P ∧
      (∀ f, Tendsto (fun R : ℝ => integratedUnitary U (finiteFilterKernel Ω t R) f)
        atTop (𝓝 (P f))) ∧
      ∀ f, ‖P f‖ ^ 2 = ∫ θ, ‖cutoffSymbol Ω t θ‖ ^ 2 ∂σ f := by
  have hpos (R : ℝ) : 0 < max 1 R := zero_lt_one.trans_le (le_max_left _ _)
  have hb (R : ℝ) (θ : Euclidean d) :
      ‖integratedKernelSymbol (finiteFilterKernel Ω t (max 1 R)) θ‖ ≤ 1 := by
    rw [integratedKernelSymbol_finiteFilterKernel_eq_fejerCutoff Ω hΩ hfin t (hpos R)]
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (fejerCutoff_mem_Icc hΩ (hpos R) (t + θ)).1]
    exact (fejerCutoff_mem_Icc hΩ (hpos R) (t + θ)).2
  obtain ⟨P, hn, hs, hi, hlim, hnorm⟩ := exists_spectral_cutoff_of_symbol_tendsto
    (l := atTop) U hU hadd h0 σ hσ
    (fun R => integrable_finiteFilterKernel Ω hΩ hfin t (hpos R)) hb
    (fun R => finiteFilter_isSelfAdjoint U hU hadd h0 Ω hΩ hfin t (hpos R))
    (fun f => finiteFilterKernel_ae_symbol_tendsto Ω hΩ hfin (hdom f) ht)
    (fun _ => Filter.Eventually.of_forall (cutoffSymbol_idempotent Ω t))
  refine ⟨P, hn, hs, hi, ?_, hnorm⟩
  intro f
  apply (hlim f).congr'
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with R hR
  rw [max_eq_right hR]

/-- The cutoff norm integral is the spectral mass of the translated domain. -/
theorem integral_cutoffSymbol_sq {d : ℕ} (ν : Measure (Euclidean d))
    (Ω : Set (Euclidean d)) (hΩ : MeasurableSet Ω) (t : Euclidean d) :
    (∫ θ, ‖cutoffSymbol Ω t θ‖ ^ 2 ∂ν) = ν.real {θ | t + θ ∈ Ω} := by
  have he : (fun θ => ‖cutoffSymbol Ω t θ‖ ^ 2) =
      {θ | t + θ ∈ Ω}.indicator (fun _ => (1 : ℝ)) := by
    funext θ
    by_cases h : t + θ ∈ Ω <;> simp [cutoffSymbol, h]
  rw [he]
  exact integral_indicator_one (μ := ν) (hΩ.preimage ((measurable_const (a := t)).add measurable_id))

/-- Two actual stationary cutoff limits satisfy the spectral difference identity. -/
theorem stationary_cutoff_difference_sq {d : ℕ} {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (U : Euclidean d → H ≃ₗᵢ[ℂ] H)
    (hU : ∀ f, Continuous (fun y => U y f))
    (hadd : ∀ z y f, U z (U y f) = U (z + y) f)
    (f : H) (ν : Measure (Euclidean d))
    (hν : RepresentsCorrelation (unitaryCorrelation U f) ν)
    (μ : Measure (Euclidean d)) (hdom : ν ≪ μ)
    (Ω : Set (Euclidean d)) (hΩ : MeasurableSet Ω) (hfin : volume Ω ≠ ⊤)
    {s t : Euclidean d} (hs : s ∈ goodParameters μ (frontier Ω))
    (ht : t ∈ goodParameters μ (frontier Ω)) {u v : H}
    (hu : Tendsto (fun R : ℝ => integratedUnitary U (finiteFilterKernel Ω s R) f)
      atTop (𝓝 u))
    (hv : Tendsto (fun R : ℝ => integratedUnitary U (finiteFilterKernel Ω t R) f)
      atTop (𝓝 v)) :
    ‖u - v‖ ^ 2 = ∫ θ, ‖cutoffSymbol Ω s θ - cutoffSymbol Ω t θ‖ ^ 2 ∂ν := by
  have hpos (R : ℝ) : 0 < max 1 R := zero_lt_one.trans_le (le_max_left _ _)
  have hb (z : Euclidean d) (R : ℝ) (θ : Euclidean d) :
      ‖integratedKernelSymbol (finiteFilterKernel Ω z (max 1 R)) θ‖ ≤ 1 := by
    rw [integratedKernelSymbol_finiteFilterKernel_eq_fejerCutoff Ω hΩ hfin z (hpos R)]
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (fejerCutoff_mem_Icc hΩ (hpos R) (z + θ)).1]
    exact (fejerCutoff_mem_Icc hΩ (hpos R) (z + θ)).2
  apply strong_limit_spectral_difference_sq U hU hadd
    (fun R => integrable_finiteFilterKernel Ω hΩ hfin s (hpos R))
    (fun R => integrable_finiteFilterKernel Ω hΩ hfin t (hpos R)) f hν
    (hb s) (hb t)
    (finiteFilterKernel_ae_symbol_tendsto Ω hΩ hfin hdom hs)
    (finiteFilterKernel_ae_symbol_tendsto Ω hΩ hfin hdom ht)
  · apply hu.congr'
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with R hR
    rw [max_eq_right hR]
  · apply hv.congr'
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with R hR
    rw [max_eq_right hR]

/-- Simultaneous stationary projections on the measurable conull good-parameter set.
All claims are conditional only on the explicitly supplied spectral measures and control measure. -/
theorem exists_stationary_cutoff_family {d : ℕ} {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (U : Euclidean d → H ≃ₗᵢ[ℂ] H)
    (hU : ∀ f, Continuous (fun y => U y f))
    (hadd : ∀ z y f, U z (U y f) = U (z + y) f) (h0 : ∀ f, U 0 f = f)
    (σ : H → Measure (Euclidean d))
    (hσ : ∀ f, RepresentsCorrelation (unitaryCorrelation U f) (σ f))
    (μ : Measure (Euclidean d)) [SFinite μ] (hdom : ∀ f, σ f ≪ μ)
    (Ω : Set (Euclidean d)) (hΩ : MeasurableSet Ω) (hfin : volume Ω ≠ ⊤)
    (hboundary : volume (frontier Ω) = 0) :
    MeasurableSet (goodParameters μ (frontier Ω)) ∧
      volume (goodParameters μ (frontier Ω))ᶜ = 0 ∧
      ∃ P : goodParameters μ (frontier Ω) → H →L[ℂ] H,
        (∀ t, ‖P t‖ ≤ 1 ∧ IsSelfAdjoint (P t) ∧ (P t).comp (P t) = P t) ∧
        (∀ (t : goodParameters μ (frontier Ω)) f, Tendsto (fun R : ℝ => integratedUnitary U (finiteFilterKernel Ω t R) f)
          atTop (𝓝 (P t f))) ∧
        (∀ t f, ‖P t f‖ ^ 2 = (σ f).real {θ | (t : Euclidean d) + θ ∈ Ω}) ∧
        (∀ s t f, ‖P s f - P t f‖ ^ 2 =
          ∫ θ, ‖cutoffSymbol Ω s θ - cutoffSymbol Ω t θ‖ ^ 2 ∂σ f) := by
  classical
  have hex (t : goodParameters μ (frontier Ω)) :=
    exists_stationary_cutoff U hU hadd h0 σ hσ μ hdom Ω hΩ hfin t.property
  choose P hPn hPs hPi hPt hPm using hex
  obtain ⟨hmeas, hnull⟩ := frontier_goodParameters μ hboundary
  refine ⟨hmeas, hnull, P, fun t => ⟨hPn t, hPs t, hPi t⟩, hPt, ?_, ?_⟩
  · intro t f
    rw [hPm t f, integral_cutoffSymbol_sq (σ f) Ω hΩ t]
  · intro s t f
    exact stationary_cutoff_difference_sq U hU hadd f (σ f) (hσ f) μ (hdom f)
      Ω hΩ hfin s.property t.property (hPt s f) (hPt t f)

end RieszEuclidean
