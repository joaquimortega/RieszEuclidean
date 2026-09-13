import RieszEuclidean.SymbolBound
import RieszEuclidean.IntegratedAlgebra
import RieszEuclidean.StrongOperatorLimits
import Mathlib.MeasureTheory.Integral.DominatedConvergence

open MeasureTheory Filter Topology

namespace RieszEuclidean

variable {d : ℕ} {ι H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The squared difference of integrated actions is the spectral squared symbol difference. -/
theorem integratedUnitary_spectral_difference_sq [CompleteSpace H]
    (U : Euclidean d → H ≃ₗᵢ[ℂ] H)
    (hU : ∀ f, Continuous (fun y => U y f))
    (hadd : ∀ z y f, U z (U y f) = U (z + y) f)
    {a b : Euclidean d → ℂ} (ha : Integrable a) (hb : Integrable b) (f : H)
    {σ : Measure (Euclidean d)} (hσ : RepresentsCorrelation (unitaryCorrelation U f) σ) :
    ‖integratedUnitary U a f - integratedUnitary U b f‖ ^ 2 =
      ∫ θ, ‖integratedKernelSymbol a θ - integratedKernelSymbol b θ‖ ^ 2 ∂σ := by
  have ht := integratedUnitary_spectral_norm_sq U hU hadd (ha.sub hb) f hσ
  have he : integratedUnitary U (a - b) f =
      integratedUnitary U a f - integratedUnitary U b f := by
    simp only [integratedUnitary, Pi.sub_apply, sub_smul]
    exact integral_sub (integrable_unitary_smul U hU ha f)
      (integrable_unitary_smul U hU hb f)
  rw [he] at ht
  simpa only [show a - b = (fun y => a y - b y) from rfl,
    integratedKernelSymbol_sub ha hb] using ht

/-- Bounded almost-everywhere convergent symbols give a pointwise Cauchy integrated action. -/
theorem integratedUnitary_cauchy_of_symbol_tendsto [CompleteSpace H]
    {l : Filter ι} [NeBot l] [l.IsCountablyGenerated]
    (U : Euclidean d → H ≃ₗᵢ[ℂ] H)
    (hU : ∀ f, Continuous (fun y => U y f))
    (hadd : ∀ z y f, U z (U y f) = U (z + y) f)
    {a : ι → Euclidean d → ℂ} (ha : ∀ i, Integrable (a i)) (f : H)
    {σ : Measure (Euclidean d)} (hσ : RepresentsCorrelation (unitaryCorrelation U f) σ)
    (hb : ∀ i θ, ‖integratedKernelSymbol (a i) θ‖ ≤ 1)
    {b : Euclidean d → ℂ}
    (ht : ∀ᵐ θ ∂σ, Tendsto (fun i => integratedKernelSymbol (a i) θ) l (𝓝 (b θ))) :
    Cauchy (l.map (fun i => integratedUnitary U (a i) f)) := by
  letI := hσ.1
  have hlim : Tendsto (fun p : ι × ι => ∫ θ,
      ‖integratedKernelSymbol (a p.1) θ - integratedKernelSymbol (a p.2) θ‖ ^ 2 ∂σ)
      (l ×ˢ l) (𝓝 0) := by
    have hh := tendsto_integral_filter_of_dominated_convergence
      (μ := σ) (l := l ×ˢ l)
      (F := fun p θ => ‖integratedKernelSymbol (a p.1) θ -
        integratedKernelSymbol (a p.2) θ‖ ^ 2)
      (f := fun _ : Euclidean d => (0 : ℝ))
      (fun _ => (4 : ℝ))
    apply (by simpa only [integral_zero] using hh) <;> clear hh
    · filter_upwards [] with p
      have hi := (integrable_integratedKernelSymbol_sq ((ha p.1).sub (ha p.2)) σ)
      simpa only [show a p.1 - a p.2 = (fun y => a p.1 y - a p.2 y) from rfl,
        integratedKernelSymbol_sub (ha p.1) (ha p.2)] using hi.aestronglyMeasurable
    · filter_upwards [] with p
      filter_upwards [] with θ
      have hn := norm_sub_le (integratedKernelSymbol (a p.1) θ)
        (integratedKernelSymbol (a p.2) θ)
      have h1 := hb p.1 θ
      have h2 := hb p.2 θ
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      nlinarith [norm_nonneg (integratedKernelSymbol (a p.1) θ -
        integratedKernelSymbol (a p.2) θ)]
    · exact integrable_const _
    · filter_upwards [ht] with θ hθ
      simpa using ((hθ.comp tendsto_fst).sub (hθ.comp tendsto_snd)).norm.pow 2
  rw [cauchy_map_iff']
  apply Metric.uniformity_basis_dist.tendsto_right_iff.mpr
  intro ε hε
  have he := hlim.eventually (gt_mem_nhds (sq_pos_of_pos hε))
  filter_upwards [he] with p hp
  rw [dist_eq_norm]
  rw [← integratedUnitary_spectral_difference_sq U hU hadd (ha p.1) (ha p.2) f hσ] at hp
  nlinarith [norm_nonneg (integratedUnitary U (a p.1) f - integratedUnitary U (a p.2) f)]

/-- The spectral norm identity passes to a strong limit of bounded convergent symbols. -/
theorem strong_limit_spectral_norm_sq [CompleteSpace H]
    {l : Filter ι} [NeBot l] [l.IsCountablyGenerated]
    (U : Euclidean d → H ≃ₗᵢ[ℂ] H)
    (hU : ∀ f, Continuous (fun y => U y f))
    (hadd : ∀ z y f, U z (U y f) = U (z + y) f)
    {a : ι → Euclidean d → ℂ} (ha : ∀ i, Integrable (a i)) (f : H)
    {σ : Measure (Euclidean d)} (hσ : RepresentsCorrelation (unitaryCorrelation U f) σ)
    (hb : ∀ i θ, ‖integratedKernelSymbol (a i) θ‖ ≤ 1)
    {b : Euclidean d → ℂ}
    (ht : ∀ᵐ θ ∂σ, Tendsto (fun i => integratedKernelSymbol (a i) θ) l (𝓝 (b θ)))
    {g : H} (hg : Tendsto (fun i => integratedUnitary U (a i) f) l (𝓝 g)) :
    ‖g‖ ^ 2 = ∫ θ, ‖b θ‖ ^ 2 ∂σ := by
  letI := hσ.1
  have hi := tendsto_integral_filter_of_dominated_convergence
    (μ := σ) (l := l) (F := fun i θ => ‖integratedKernelSymbol (a i) θ‖ ^ 2)
    (f := fun θ => ‖b θ‖ ^ 2) (fun _ => (1 : ℝ))
    (Filter.Eventually.of_forall fun i =>
      (integrable_integratedKernelSymbol_sq (ha i) σ).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun i => Filter.Eventually.of_forall fun θ => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      change ‖integratedKernelSymbol (a i) θ‖ ^ 2 ≤ 1
      nlinarith [hb i θ, norm_nonneg (integratedKernelSymbol (a i) θ)])
    (integrable_const _)
    (ht.mono fun θ hθ => hθ.norm.pow 2)
  apply tendsto_nhds_unique (hg.norm.pow 2)
  exact hi.congr' (Filter.Eventually.of_forall fun i =>
    (integratedUnitary_spectral_norm_sq U hU hadd (ha i) f hσ).symm)

/-- A bounded almost-everywhere symbol limit determines the norm of an actual vector limit. -/
theorem exists_integratedUnitary_limit_spectral_norm [CompleteSpace H]
    {l : Filter ι} [NeBot l] [l.IsCountablyGenerated]
    (U : Euclidean d → H ≃ₗᵢ[ℂ] H)
    (hU : ∀ f, Continuous (fun y => U y f))
    (hadd : ∀ z y f, U z (U y f) = U (z + y) f)
    {a : ι → Euclidean d → ℂ} (ha : ∀ i, Integrable (a i)) (f : H)
    {σ : Measure (Euclidean d)} (hσ : RepresentsCorrelation (unitaryCorrelation U f) σ)
    (hb : ∀ i θ, ‖integratedKernelSymbol (a i) θ‖ ≤ 1)
    {b : Euclidean d → ℂ}
    (ht : ∀ᵐ θ ∂σ, Tendsto (fun i => integratedKernelSymbol (a i) θ) l (𝓝 (b θ))) :
    ∃ g : H, Tendsto (fun i => integratedUnitary U (a i) f) l (𝓝 g) ∧
      ‖g‖ ^ 2 = ∫ θ, ‖b θ‖ ^ 2 ∂σ := by
  obtain ⟨g, hg⟩ := cauchy_map_iff_exists_tendsto.mp
    (integratedUnitary_cauchy_of_symbol_tendsto U hU hadd ha f hσ hb ht)
  exact ⟨g, hg, strong_limit_spectral_norm_sq U hU hadd ha f hσ hb ht hg⟩

/-- Idempotent limiting symbols force the integrated idempotence defect to vanish. -/
theorem integratedUnitary_idempotence_defect_tendsto [CompleteSpace H]
    {l : Filter ι} [l.IsCountablyGenerated]
    (U : Euclidean d → H ≃ₗᵢ[ℂ] H)
    (hU : ∀ f, Continuous (fun y => U y f))
    (hadd : ∀ z y f, U z (U y f) = U (z + y) f)
    {a : ι → Euclidean d → ℂ} (ha : ∀ i, Integrable (a i)) (f : H)
    {σ : Measure (Euclidean d)} (hσ : RepresentsCorrelation (unitaryCorrelation U f) σ)
    (hb : ∀ i θ, ‖integratedKernelSymbol (a i) θ‖ ≤ 1)
    {b : Euclidean d → ℂ}
    (ht : ∀ᵐ θ ∂σ, Tendsto (fun i => integratedKernelSymbol (a i) θ) l (𝓝 (b θ)))
    (hi : ∀ᵐ θ ∂σ, b θ * b θ = b θ) :
    Tendsto (fun i => ‖integratedUnitary U (a i) (integratedUnitary U (a i) f) -
      integratedUnitary U (a i) f‖) l (𝓝 0) := by
  letI := hσ.1
  have hs : Tendsto (fun i => ∫ θ,
      ‖integratedKernelSymbol (a i) θ * integratedKernelSymbol (a i) θ -
        integratedKernelSymbol (a i) θ‖ ^ 2 ∂σ) l (𝓝 0) := by
    have hd := tendsto_integral_filter_of_dominated_convergence
      (μ := σ) (l := l)
      (F := fun i θ => ‖integratedKernelSymbol (a i) θ * integratedKernelSymbol (a i) θ -
        integratedKernelSymbol (a i) θ‖ ^ 2)
      (f := fun _ : Euclidean d => (0 : ℝ)) (fun _ => (4 : ℝ))
    apply (by simpa only [integral_zero] using hd) <;> clear hd
    · filter_upwards [] with i
      have hm := (integrable_integratedKernelSymbol_sq
        ((integrable_integratedKernelConvolution (ha i) (ha i)).sub (ha i)) σ)
      simpa only [show integratedKernelConvolution (a i) (a i) - a i =
        (fun y => integratedKernelConvolution (a i) (a i) y - a i y) from rfl,
        integratedKernelSymbol_sub (integrable_integratedKernelConvolution (ha i) (ha i))
          (ha i), integratedKernelSymbol_convolution (ha i) (ha i)]
        using hm.aestronglyMeasurable
    · filter_upwards [] with i
      filter_upwards [] with θ
      change ‖‖integratedKernelSymbol (a i) θ * integratedKernelSymbol (a i) θ -
        integratedKernelSymbol (a i) θ‖ ^ 2‖ ≤ 4
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      have hn := norm_sub_le (integratedKernelSymbol (a i) θ *
        integratedKernelSymbol (a i) θ) (integratedKernelSymbol (a i) θ)
      rw [norm_mul] at hn
      have hx := hb i θ
      have hx0 := norm_nonneg (integratedKernelSymbol (a i) θ)
      have hx2 : ‖integratedKernelSymbol (a i) θ‖ ^ 2 ≤ 1 := by nlinarith
      have hdiff : ‖integratedKernelSymbol (a i) θ * integratedKernelSymbol (a i) θ -
          integratedKernelSymbol (a i) θ‖ ≤ 2 := by nlinarith
      clear hn hx hx0 hx2
      nlinarith [norm_nonneg (integratedKernelSymbol (a i) θ *
        integratedKernelSymbol (a i) θ - integratedKernelSymbol (a i) θ)]
    · exact integrable_const _
    · filter_upwards [ht, hi] with θ hθ hiθ
      simpa only [hiθ, _root_.sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0)] using
        ((hθ.mul hθ).sub hθ).norm.pow 2
  have he (i : ι) := integratedUnitary_spectral_difference_sq U hU hadd
    (integrable_integratedKernelConvolution (ha i) (ha i)) (ha i) f hσ
  simp only [integratedUnitary_convolution U hU hadd (ha _) (ha _),
    integratedKernelSymbol_convolution (ha _) (ha _)] at he
  have hs' := hs.congr' (Filter.Eventually.of_forall fun i => (he i).symm)
  have ht' := Real.continuous_sqrt.continuousAt.tendsto.comp hs'
  simpa only [Function.comp_def, Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using ht'

/-- Supplied spectral measures and bounded idempotent symbol limits assemble an orthogonal cutoff. -/
theorem exists_spectral_cutoff_of_symbol_tendsto [CompleteSpace H]
    {l : Filter ι} [NeBot l] [l.IsCountablyGenerated]
    (U : Euclidean d → H ≃ₗᵢ[ℂ] H)
    (hU : ∀ f, Continuous (fun y => U y f))
    (hadd : ∀ z y f, U z (U y f) = U (z + y) f)
    (h0 : ∀ f, U 0 f = f)
    (σ : H → Measure (Euclidean d))
    (hσ : ∀ f, RepresentsCorrelation (unitaryCorrelation U f) (σ f))
    {a : ι → Euclidean d → ℂ} (ha : ∀ i, Integrable (a i))
    (hb : ∀ i θ, ‖integratedKernelSymbol (a i) θ‖ ≤ 1)
    (hself : ∀ i, IsSelfAdjoint (integratedUnitaryCLM U hU (ha i)))
    {b : Euclidean d → ℂ}
    (ht : ∀ f, ∀ᵐ θ ∂σ f,
      Tendsto (fun i => integratedKernelSymbol (a i) θ) l (𝓝 (b θ)))
    (hi : ∀ f, ∀ᵐ θ ∂σ f, b θ * b θ = b θ) :
    ∃ B : H →L[ℂ] H, ‖B‖ ≤ 1 ∧ IsSelfAdjoint B ∧ B.comp B = B ∧
      (∀ f, Tendsto (fun i => integratedUnitary U (a i) f) l (𝓝 (B f))) ∧
      ∀ f, ‖B f‖ ^ 2 = ∫ θ, ‖b θ‖ ^ 2 ∂σ f := by
  obtain ⟨B, hBn, hBs, hBi, hB⟩ := exists_projection_of_cauchy_contractions
    (fun i => integratedUnitaryCLM U hU (ha i))
    (fun i => norm_integratedUnitaryCLM_le_symbol U hU hadd h0
      (fun f => ⟨σ f, hσ f⟩) (ha i) zero_le_one (hb i)) hself
    (fun f => integratedUnitary_cauchy_of_symbol_tendsto U hU hadd ha f (hσ f) hb (ht f))
    (fun f => integratedUnitary_idempotence_defect_tendsto U hU hadd ha f
      (hσ f) hb (ht f) (hi f))
  exact ⟨B, hBn, hBs, hBi, hB, fun f =>
    strong_limit_spectral_norm_sq U hU hadd ha f (hσ f) hb (ht f) (hB f)⟩

end RieszEuclidean
