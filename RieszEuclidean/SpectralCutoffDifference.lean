import RieszEuclidean.SpectralCutoffLimits

open MeasureTheory Filter Topology

namespace RieszEuclidean

/-- The difference norm identity passes to two strong limits of bounded cutoff symbols. -/
theorem strong_limit_spectral_difference_sq
    {n : ℕ} {ι H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] {l : Filter ι} [NeBot l] [l.IsCountablyGenerated]
    (U : Euclidean n → H ≃ₗᵢ[ℂ] H)
    (hU : ∀ f, Continuous (fun y => U y f))
    (hadd : ∀ z y f, U z (U y f) = U (z + y) f)
    {a c : ι → Euclidean n → ℂ} (ha : ∀ i, Integrable (a i))
    (hc : ∀ i, Integrable (c i)) (f : H)
    {σ : Measure (Euclidean n)} (hσ : RepresentsCorrelation (unitaryCorrelation U f) σ)
    (hab : ∀ i θ, ‖integratedKernelSymbol (a i) θ‖ ≤ 1)
    (hcb : ∀ i θ, ‖integratedKernelSymbol (c i) θ‖ ≤ 1)
    {b d : Euclidean n → ℂ}
    (hat : ∀ᵐ θ ∂σ, Tendsto (fun i => integratedKernelSymbol (a i) θ) l (𝓝 (b θ)))
    (hct : ∀ᵐ θ ∂σ, Tendsto (fun i => integratedKernelSymbol (c i) θ) l (𝓝 (d θ)))
    {u v : H} (hu : Tendsto (fun i => integratedUnitary U (a i) f) l (𝓝 u))
    (hv : Tendsto (fun i => integratedUnitary U (c i) f) l (𝓝 v)) :
    ‖u - v‖ ^ 2 = ∫ θ, ‖b θ - d θ‖ ^ 2 ∂σ := by
  letI := hσ.1
  have hi := tendsto_integral_filter_of_dominated_convergence
    (μ := σ) (l := l)
    (F := fun i θ => ‖integratedKernelSymbol (a i) θ - integratedKernelSymbol (c i) θ‖ ^ 2)
    (f := fun θ => ‖b θ - d θ‖ ^ 2) (fun _ => (4 : ℝ))
  have hlim : Tendsto (fun i => ∫ θ,
      ‖integratedKernelSymbol (a i) θ - integratedKernelSymbol (c i) θ‖ ^ 2 ∂σ)
      l (𝓝 (∫ θ, ‖b θ - d θ‖ ^ 2 ∂σ)) := by
    apply hi <;> clear hi
    · filter_upwards [] with i
      have hm := (integrable_integratedKernelSymbol_sq ((ha i).sub (hc i)) σ)
      simpa only [show a i - c i = (fun y => a i y - c i y) from rfl,
        integratedKernelSymbol_sub (ha i) (hc i)] using hm.aestronglyMeasurable
    · filter_upwards [] with i
      filter_upwards [] with θ
      change ‖‖integratedKernelSymbol (a i) θ - integratedKernelSymbol (c i) θ‖ ^ 2‖ ≤ 4
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      have hn := norm_sub_le (integratedKernelSymbol (a i) θ) (integratedKernelSymbol (c i) θ)
      nlinarith [hab i θ, hcb i θ,
        norm_nonneg (integratedKernelSymbol (a i) θ - integratedKernelSymbol (c i) θ)]
    · exact integrable_const _
    · filter_upwards [hat, hct] with θ haθ hcθ
      exact (haθ.sub hcθ).norm.pow 2
  apply tendsto_nhds_unique ((hu.sub hv).norm.pow 2)
  exact hlim.congr' (Filter.Eventually.of_forall fun i =>
    (integratedUnitary_spectral_difference_sq U hU hadd (ha i) (hc i) f hσ).symm)

end RieszEuclidean
