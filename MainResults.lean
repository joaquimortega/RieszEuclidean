import RieszEuclidean

/-!
# Implemented result statements and concrete definitions

This compact Comparator reference covers proved foundational, Fourier, affine
configuration-space results and invariant probability measures. It does not contain or certify the unfinished geometric main
theorems. Its wrapper proofs use the checked modular library, so the reference
needs neither theorem placeholders nor warning suppressions.
-/
noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal
namespace RieszEuclidean.Results

/-- Euclidean space in the dimension appearing in the manuscript. -/
abbrev Space (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- The paper's concrete exponential Riesz basis predicate, written out for review. -/
def HasBasis {d : ℕ} (Ω Λ : Set (Space d)) : Prop := by
  classical
  exact ∃ S : lp (fun _ : Λ => ℂ) 2 ≃L[ℂ] Lp ℂ 2 (volume.restrict Ω),
    ∀ ξ : Λ, (S (lp.single 2 ξ 1) : Space d → ℂ) =ᵐ[volume.restrict Ω]
      fun x => Complex.exp
        (2 * (Real.pi : ℂ) * Complex.I * (inner (𝕜 := ℝ) ξ.val x : ℂ))

/-- An arbitrary invertible affine image of the domain. -/
def affineImage {d : ℕ} (a : Space d) (A : Space d ≃L[ℝ] Space d)
    (Ω : Set (Space d)) : Set (Space d) := (fun x => a + A x) '' Ω

/-- Lemma 2.1 with its actual restriction-to-range definition. -/
theorem projection_gap {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (P Q : OrthProjection H) :
    ‖P.op - Q.op‖ < 1 ↔
      ∃ e : Q.range ≃L[ℂ] P.range, ∀ x : Q.range, (e x : H) = P.op x :=
  OrthProjection.gap_iff_rangeIso P Q

/-- Lemma 2.2: strict inclusion of ranges is incompatible with two gaps below one. -/
theorem strict_inclusion_obstruction {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (P Q M : OrthProjection H)
    (h : P.range < Q.range) : ¬ (‖P.op - M.op‖ < 1 ∧ ‖Q.op - M.op‖ < 1) :=
  OrthProjection.nested_not_both_gap P Q M h

/-- Beurling weak limits retain a uniform separation constant. -/
theorem weak_limit_separation {d : ℕ} {δ : ℝ}
    {Γ : ℕ → Set (Space d)} {Γ₀ : Set (Space d)}
    (h : WeaklyConverges Γ Γ₀) (hsep : ∀ j, Separated δ (Γ j)) :
    Separated δ Γ₀ := h.separated hsep

/-- Arbitrary affine transport of the concrete synthesis predicate. -/
theorem affine_invariance {d : ℕ} (a : Space d) (A : Space d ≃L[ℝ] Space d)
    (Ω : Set (Space d)) :
    (∃ Λ, HasBasis (affineImage a A Ω) Λ) ↔ ∃ Λ, HasBasis Ω Λ :=
  exists_exponentialRieszBasis_affine_iff a A Ω

/-- The concrete Euclidean Schwartz Parseval pairing underlying the L² extension. -/
theorem fourier_parseval {d : ℕ} (f g : SchwartzMap (Space d) ℂ) :
    (∫ x, Real.fourierIntegral f x * starRingEnd ℂ (Real.fourierIntegral g x)) =
      ∫ x, f x * starRingEnd ℂ (g x) := schwartz_parseval f g

/-- Existence of the actual Euclidean unitary Fourier map and its measurable-domain cutoffs. -/
theorem euclidean_fourier_cutoff (d : ℕ) :
    ∃ U : Lp ℂ 2 (volume : Measure (Euclidean d)) ≃ₗᵢ[ℂ]
        Lp ℂ 2 (volume : Measure (Euclidean d)),
      (∀ f : SchwartzMap (Euclidean d) ℂ,
        (U (f.toLp 2 volume) : Euclidean d → ℂ) =ᵐ[volume] Real.fourierIntegralInv f) ∧
      ∀ Ω : Set (Euclidean d), MeasurableSet Ω →
        ∃ P : OrthProjection (Lp ℂ 2 (volume : Measure (Euclidean d))),
          ∀ f, (U (P.op f) : Euclidean d → ℂ) =ᵐ[volume]
            Ω.indicator (U f : Euclidean d → ℂ) := by
  refine ⟨paperFourierL2 d, paperFourierL2_schwartz d, ?_⟩
  intro Ω hΩ
  refine ⟨fourierProjection Ω hΩ, ?_⟩
  intro f
  rw [fourierProjection_transform]
  exact domainCutoff_coe Ω hΩ _
/-- Schwartz functions are dense in Euclidean L². -/
theorem schwartz_density (d : ℕ) :
    DenseRange (fun f : SchwartzMap (Euclidean d) ℂ => f.toLp 2 volume) :=
  schwartz_toL2_denseRange d
/-- The complete initial Fourier construction, with integral, kernel and translation semantics. -/
theorem euclidean_fourier_analysis (d : ℕ) :
    ∃ U : Lp ℂ 2 (volume : Measure (Euclidean d)) ≃ₗᵢ[ℂ]
        Lp ℂ 2 (volume : Measure (Euclidean d)),
      (∀ f : Lp ℂ 2 (volume : Measure (Euclidean d)), Integrable (f : Euclidean d → ℂ) →
        (U f : Euclidean d → ℂ) =ᵐ[volume] Real.fourierIntegralInv f) ∧
      ∀ Ω : Set (Euclidean d), MeasurableSet Ω → volume Ω ≠ ⊤ →
        ∃ P : OrthProjection (Lp ℂ 2 (volume : Measure (Euclidean d))),
          (∀ f, (U (P.op f) : Euclidean d → ℂ) =ᵐ[volume]
            Ω.indicator (U f : Euclidean d → ℂ)) ∧
          (∀ f : Lp ℂ 2 (volume : Measure (Euclidean d)), Integrable (f : Euclidean d → ℂ) →
            (P.op f : Euclidean d → ℂ) =ᵐ[volume] fun v =>
              ∫ w, (∫ x in Ω, (Real.fourierChar (-inner (𝕜 := ℝ) x (v - w)) : ℂ)) * f w) ∧
          ∀ (t : Euclidean d) (f g : Lp ℂ 2 (volume : Measure (Euclidean d))),
            (g : Euclidean d → ℂ) =ᵐ[volume] (fun x => f (x + t)) →
            (P.op g : Euclidean d → ℂ) =ᵐ[volume] fun x => P.op f (x + t) := by
  refine ⟨paperFourierL2 d, fun f hf => paperFourierL2_eq_integral f hf, ?_⟩
  intro Ω hΩ hfin
  refine ⟨fourierProjection Ω hΩ, ?_, ?_, ?_⟩
  · intro f
    rw [fourierProjection_transform]
    exact domainCutoff_coe Ω hΩ _
  · intro f hf
    exact fourierProjection_kernel Ω hΩ hfin f hf
  · intro t f g hg
    have heq : g = translationL2 t f := Lp.ext (hg.trans (translationL2_coe t f).symm)
    rw [heq, fourierProjection_translation Ω hΩ hfin]
    exact translationL2_coe t _
/-- Every exponential Riesz basis on a bounded domain supplies the paper's small bump and initial gap. -/
theorem initial_bumps {d : ℕ} {Ω Λ : Set (Euclidean d)}
    (hΩ : MeasurableSet Ω) (hb : Bornology.IsBounded Ω)
    (hB : HasExponentialRieszBasis Ω Λ) :
    ∃ δ r : ℝ, 0 < δ ∧ Separated δ Λ ∧ 0 < r ∧ 2 * r < δ ∧
      ∃ b : SchwartzMap (Euclidean d) ℂ,
        HasCompactSupport b ∧ ‖b.toLp 2 volume‖ = 1 ∧
        (∀ ξ, (b ξ).im = 0 ∧ 0 ≤ (b ξ).re) ∧
        (∀ ξ, r ≤ ‖ξ‖ → b ξ = 0) ∧
        (∃ c : ℝ, 0 < c ∧ ∀ x ∈ Ω, c ≤ ‖Real.fourierIntegralInv b x‖) ∧
        ∃ V : SeqL2 Λ →ₗᵢ[ℂ] FullL2 d,
          (∀ i : Λ, V (lp.single 2 i 1) = translationL2 (-(i : Euclidean d)) (b.toLp 2 volume)) ∧
          ‖(fourierProjection Ω hΩ).op - (isometryRangeProjection V).op‖ < 1 :=
  exists_initial_bump_gap hΩ hb hB
/-- The separated configuration space is compact metrizable, realizes Beurling weak
convergence, and carries a jointly continuous real translation action. -/
theorem compact_configuration_space (d : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    CompactSpace (SeparatedConfiguration d δ) ∧
    TopologicalSpace.MetrizableSpace (SeparatedConfiguration d δ) ∧
    (∀ (Γ : ℕ → SeparatedConfiguration d δ) (Γ₀ : SeparatedConfiguration d δ),
      Filter.Tendsto Γ Filter.atTop (nhds Γ₀) ↔
        WeaklyConverges (fun n => (Γ n).carrier) Γ₀.carrier) ∧
    Continuous (fun p : Euclidean d × SeparatedConfiguration d δ =>
      SeparatedConfiguration.translate p.1 p.2) :=
  ⟨SeparatedConfiguration.compactSpace hδ, inferInstance,
    fun _ _ => SeparatedConfiguration.tendsto_iff_weaklyConverges hδ,
    SeparatedConfiguration.continuous_translate hδ⟩
/-- The actual translation hull has an invariant Borel probability measure,
constructed by continuous Euclidean box averaging. -/
theorem hull_invariant_probability {d : ℕ} {δ : ℝ} (hδ : 0 < δ)
    (Γ : SeparatedConfiguration d δ)
    [MeasurableSpace (SeparatedConfiguration.hull Γ)] [BorelSpace (SeparatedConfiguration.hull Γ)] :
    ∃ μ : Measure (SeparatedConfiguration.hull Γ), IsProbabilityMeasure μ ∧
      ∀ z : Euclidean d, MeasurePreserving (SeparatedConfiguration.hullTranslate hδ Γ z) μ μ :=
  SeparatedConfiguration.exists_hull_invariant_probability hδ Γ
/-- The invariant hull measure gives the paper's strongly continuous unitary
representation, on a separable Hilbert space with an invariant unit constant. -/
theorem stationary_koopman {d : ℕ} {δ : ℝ} (hδ : 0 < δ)
    (Γ : SeparatedConfiguration d δ)
    [MeasurableSpace (SeparatedConfiguration.hull Γ)] [BorelSpace (SeparatedConfiguration.hull Γ)]
    (μ : Measure (SeparatedConfiguration.hull Γ)) [IsProbabilityMeasure μ]
    (hμ : ∀ z : Euclidean d, MeasurePreserving (SeparatedConfiguration.hullTranslate hδ Γ z) μ μ) :
    ∃ U : Euclidean d → (Lp ℂ 2 μ ≃ₗᵢ[ℂ] Lp ℂ 2 μ),
      (∀ z f, (U z f : SeparatedConfiguration.hull Γ → ℂ) =ᵐ[μ]
        fun x => f (SeparatedConfiguration.hullTranslate hδ Γ (-z) x)) ∧
      (∀ z y f, U z (U y f) = U (z + y) f) ∧
      (∀ f, U 0 f = f) ∧
      (∀ f, Continuous (fun z => U z f)) ∧
      TopologicalSpace.SeparableSpace (Lp ℂ 2 μ) ∧
      ‖Lp.const 2 μ (1 : ℂ)‖ = 1 ∧
      ∀ z, U z (Lp.const 2 μ (1 : ℂ)) = Lp.const 2 μ (1 : ℂ) := by
  refine ⟨SeparatedConfiguration.hullKoopmanUnitary hδ Γ μ hμ, ?_,
    SeparatedConfiguration.hullKoopmanUnitary_add hδ Γ μ hμ,
    SeparatedConfiguration.hullKoopmanUnitary_zero hδ Γ μ hμ,
    SeparatedConfiguration.strongContinuous_hullKoopmanUnitary hδ Γ μ hμ,
    SeparatedConfiguration.separableSpace_hullLp hδ Γ μ, norm_stationary_one,
    fun z => SeparatedConfiguration.hullKoopmanUnitary_const hδ Γ μ hμ z 1⟩
  intro z f
  rw [SeparatedConfiguration.hullKoopmanUnitary_apply]
  exact Lp.coeFn_compMeasurePreserving f (hμ (-z))
/-- Beurling weak convergence is precisely vague counting-measure convergence
for configurations sharing a positive separation bound. -/
theorem beurling_iff_vague {d : ℕ} {δ : ℝ} (hδ : 0 < δ)
    {Γ : ℕ → Set (Euclidean d)} {Δ : Set (Euclidean d)}
    (hΓ : ∀ n, Separated δ (Γ n)) (hΔ : Separated δ Δ) :
    WeaklyConverges Γ Δ ↔ ∀ f : CompactlySupportedContinuousMap (Euclidean d) ℝ,
      Filter.Tendsto (fun n => ∫ x, f x ∂configurationMeasure (Γ n)) Filter.atTop
        (nhds (∫ x, f x ∂configurationMeasure Δ)) :=
  weaklyConverges_iff_vague hδ hΓ hΔ
/-- The L¹ integrated unitary operator has the manuscript's spectral norm,
provided the vector correlation is represented by the supplied finite measure. -/
theorem integrated_spectral_norm {d : ℕ} {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (U : Euclidean d → H ≃ₗᵢ[ℂ] H)
    (hU : ∀ f, Continuous (fun y => U y f))
    (hadd : ∀ z y f, U z (U y f) = U (z + y) f)
    {a : Euclidean d → ℂ} (ha : Integrable a) (f : H)
    {σ : Measure (Euclidean d)} (hσ : RepresentsCorrelation (unitaryCorrelation U f) σ) :
    ‖∫ y, a y • U y f‖ ^ 2 = ∫ θ, ‖Real.fourierIntegralInv a θ‖ ^ 2 ∂σ := by
  simpa only [integratedUnitary, integratedKernelSymbol_eq_fourierInv] using
    integratedUnitary_spectral_norm_sq U hU hadd ha f hσ
/-- The continuous box Fejér kernels have unit mass and concentrate at zero;
their actual domain cutoffs converge off the frontier. -/
theorem continuous_fejer {d : ℕ} (Ω : Set (Euclidean d)) (hΩ : MeasurableSet Ω) :
    (∀ R > 0, Integrable (fejerKernel d R) ∧ (∫ x, fejerKernel d R x) = 1 ∧
      ∀ x, 0 ≤ fejerKernel d R x) ∧
    (∀ ε > 0, Filter.Tendsto
      (fun R : ℝ => ∫ x in (Metric.closedBall 0 ε)ᶜ, fejerKernel d R x)
      Filter.atTop (nhds 0)) ∧
    (∀ R > 0, ∀ x, fejerCutoff Ω R x ∈ Set.Icc (0 : ℝ) 1) ∧
    ∀ x ∉ frontier Ω, Filter.Tendsto (fun R : ℝ => fejerCutoff Ω R x)
      Filter.atTop (nhds (Ω.indicator (fun _ => (1 : ℝ)) x)) := by
  refine ⟨?_, fun _ hε => tendsto_fejerKernel_tail d hε,
    fun _ hR x => fejerCutoff_mem_Icc hΩ hR x, fun _ hx => tendsto_fejerCutoff hΩ hx⟩
  intro R hR
  exact ⟨(fejerKernel_integrable_integral d hR).1,
    (fejerKernel_integrable_integral d hR).2, fejerKernel_nonneg d R⟩
/-- The finite filter uses the Fourier transform of the actual domain kernel. -/
theorem finite_filter_symbol {d : ℕ} (Ω : Set (Euclidean d))
    (hΩ : MeasurableSet Ω) (hfin : volume Ω ≠ ⊤) (t : Euclidean d)
    {R : ℝ} (hR : 0 < R) :
    Integrable (finiteFilterKernel Ω t R) ∧ ∀ θ,
      Real.fourierIntegralInv (finiteFilterKernel Ω t R) θ =
        (fejerCutoff Ω R (t + θ) : ℂ) := by
  refine ⟨integrable_finiteFilterKernel Ω hΩ hfin t hR, fun θ => ?_⟩
  rw [← integratedKernelSymbol_eq_fourierInv]
  exact integratedKernelSymbol_finiteFilterKernel_eq_fejerCutoff Ω hΩ hfin t hR θ
/-- Separability produces a probability control measure from the supplied spectral measures. -/
theorem spectral_control_measure {d : ℕ} {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [TopologicalSpace.SeparableSpace H]
    (U : Euclidean d → H ≃ₗᵢ[ℂ] H) (h0 : ∀ f, U 0 f = f)
    (σ : H → Measure (Euclidean d))
    (hσ : ∀ f, RepresentsCorrelation (unitaryCorrelation U f) (σ f))
    (u : H) (hu : ‖u‖ = 1) :
    ∃ h : ℕ → H, (∀ n, ‖h n‖ = 1) ∧
      IsProbabilityMeasure (spectralControlMeasure σ h) ∧
      ∀ f, σ f ≪ spectralControlMeasure σ h :=
  exists_spectralControlMeasure U h0 σ hσ u hu
/-- The actual finite filters give simultaneous orthogonal cutoffs, conditional on
the explicitly supplied representing measures and their common domination. -/
theorem stationary_cutoffs {d : ℕ} {H : Type*}
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
          ∫ θ, ‖cutoffSymbol Ω s θ - cutoffSymbol Ω t θ‖ ^ 2 ∂σ f) :=
  exists_stationary_cutoff_family U hU hadd h0 σ hσ μ hdom Ω hΩ hfin hboundary
/-- The concrete bump kernel is continuous in its spatial variables and satisfies
the integrable projection identity. -/
theorem bump_kernel_projection {d : ℕ} {δ r : ℝ} {Γ : Set (Euclidean d)}
    (hΓ : Separated δ Γ) (hδ : 0 < δ) (hr : 2 * r ≤ δ) (b : Euclidean d → ℂ)
    (hb : Continuous b) (hs : ∀ x, r ≤ ‖x‖ → b x = 0)
    (hi : Integrable (fun x => ‖b x‖ ^ 2)) (hn : (∫ x, ‖b x‖ ^ 2) = 1) :
    Continuous (fun p : Euclidean d × Euclidean d => bumpKernel Γ b p.1 p.2) ∧
    ∀ v w, Integrable (fun u => bumpKernel Γ b v u * bumpKernel Γ b u w) ∧
      (∫ u, bumpKernel Γ b v u * bumpKernel Γ b u w) = bumpKernel Γ b v w :=
  ⟨continuous_bumpKernel hΓ hδ b hb hs, fun v w =>
    ⟨integrable_bumpKernel_product hΓ hr b hs hi v w,
      integral_bumpKernel_product hΓ hr b hs hn v w⟩⟩
end RieszEuclidean.Results
