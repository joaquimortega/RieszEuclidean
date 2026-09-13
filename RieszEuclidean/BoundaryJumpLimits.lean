import RieszEuclidean.BoundaryCutoffLimits

noncomputable section
open MeasureTheory Filter Topology
namespace RieszEuclidean

/-- The interior boundary symbol retains every frequency in the jump set. -/
def boundaryJumpSymbol {d : ℕ} (Ω : Set (Euclidean d)) (t : Euclidean d)
    (J : Set (Euclidean d)) (θ : Euclidean d) : ℂ :=
  cutoffSymbol Ω t θ + J.indicator (fun _ => (1 : ℂ)) θ

/-- Disjointness makes the full boundary jump an idempotent indicator. -/
theorem boundaryJumpSymbol_idempotent {d : ℕ} (Ω : Set (Euclidean d)) (t : Euclidean d)
    (J : Set (Euclidean d)) (hJ : ∀ θ ∈ J, t + θ ∉ Ω) (θ : Euclidean d) :
    boundaryJumpSymbol Ω t J θ * boundaryJumpSymbol Ω t J θ =
      boundaryJumpSymbol Ω t J θ := by
  by_cases h : θ ∈ J
  · simp [boundaryJumpSymbol, cutoffSymbol, h, hJ θ h]
  · simpa [boundaryJumpSymbol, h] using cutoffSymbol_idempotent Ω t θ

/-- The full jump adds exactly the indicator of its frequency set to squared norms. -/
theorem boundaryJumpSymbol_norm_sq {d : ℕ} (Ω : Set (Euclidean d)) (t : Euclidean d)
    (J : Set (Euclidean d)) (hJ : ∀ θ ∈ J, t + θ ∉ Ω) (θ : Euclidean d) :
    ‖boundaryJumpSymbol Ω t J θ‖ ^ 2 = ‖cutoffSymbol Ω t θ‖ ^ 2 +
      J.indicator (fun _ => (1 : ℝ)) θ := by
  by_cases h : θ ∈ J
  · simp [boundaryJumpSymbol, cutoffSymbol, h, hJ θ h]
  · simp [boundaryJumpSymbol, h]

/-- The whole jump gives pointwise ordered squared norms. -/
theorem boundaryJumpSymbol_norm_sq_le {d : ℕ} (Ω : Set (Euclidean d)) (t : Euclidean d)
    (J : Set (Euclidean d)) (hJ : ∀ θ ∈ J, t + θ ∉ Ω) (θ : Euclidean d) :
    ‖cutoffSymbol Ω t θ‖ ^ 2 ≤ ‖boundaryJumpSymbol Ω t J θ‖ ^ 2 := by
  rw [boundaryJumpSymbol_norm_sq Ω t J hJ]
  exact le_add_of_nonneg_right (Set.indicator_nonneg (fun _ _ => zero_le_one) θ)

/-- Squared full-jump symbols are integrable against every finite measure. -/
theorem integrable_boundaryJumpSymbol_norm_sq {d : ℕ} {Ω : Set (Euclidean d)}
    (hΩ : MeasurableSet Ω) (t : Euclidean d) {J : Set (Euclidean d)}
    (hJm : MeasurableSet J) (hJ : ∀ θ ∈ J, t + θ ∉ Ω)
    (σ : Measure (Euclidean d)) [IsFiniteMeasure σ] :
    Integrable (fun θ => ‖boundaryJumpSymbol Ω t J θ‖ ^ 2) σ := by
  simp_rw [boundaryJumpSymbol_norm_sq Ω t J hJ]
  exact (integrable_cutoffSymbol_norm_sq hΩ t σ).add
    ((integrable_const (1 : ℝ)).indicator hJm)

/-- Zero belongs to the full jump and forces the invariant vector's strict norm jump. -/
theorem boundaryJumpSymbol_dirac_norms {d : ℕ} (Ω : Set (Euclidean d))
    (t : Euclidean d) (J : Set (Euclidean d))
    (hJ : ∀ θ ∈ J, t + θ ∉ Ω) (hzero : 0 ∈ J) :
    (∫ θ, ‖cutoffSymbol Ω t θ‖ ^ 2 ∂Measure.dirac 0) = 0 ∧
      (∫ θ, ‖boundaryJumpSymbol Ω t J θ‖ ^ 2 ∂Measure.dirac 0) = 1 := by
  have ht : t ∉ Ω := by simpa only [add_zero] using hJ 0 hzero
  simp [cutoffSymbol, boundaryJumpSymbol, ht, hzero]

/-- Full-jump spectral norm identities force strict inclusion of projection ranges. -/
theorem boundary_jump_cutoff_ranges_strict {d : ℕ} {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {Ω : Set (Euclidean d)} (hΩ : MeasurableSet Ω) (t₀ : Euclidean d)
    {J : Set (Euclidean d)} (hJm : MeasurableSet J)
    (hJ : ∀ θ ∈ J, t₀ + θ ∉ Ω) (hzero : 0 ∈ J)
    (σ : H → Measure (Euclidean d)) (hfinite : ∀ f, IsFiniteMeasure (σ f))
    (Rm Rp : H →L[ℂ] H) (hRms : IsSelfAdjoint Rm) (hRps : IsSelfAdjoint Rp)
    (hRmi : Rm.comp Rm = Rm) (hRpi : Rp.comp Rp = Rp)
    (hRmn : ∀ f, ‖Rm f‖ ^ 2 = ∫ θ, ‖cutoffSymbol Ω t₀ θ‖ ^ 2 ∂σ f)
    (hRpn : ∀ f, ‖Rp f‖ ^ 2 = ∫ θ, ‖boundaryJumpSymbol Ω t₀ J θ‖ ^ 2 ∂σ f)
    (u : H) (hu : ‖u‖ = 1) (hσu : σ u = Measure.dirac 0) :
    Rm u = 0 ∧ Rp u = u ∧
      LinearMap.range Rm.toLinearMap < LinearMap.range Rp.toLinearMap := by
  have horder (f : H) : ‖Rm f‖ ≤ ‖Rp f‖ := by
    letI := hfinite f
    have h := integral_mono (integrable_cutoffSymbol_norm_sq hΩ t₀ (σ f))
      (integrable_boundaryJumpSymbol_norm_sq hΩ t₀ hJm hJ (σ f))
      (boundaryJumpSymbol_norm_sq_le Ω t₀ J hJ)
    rw [← hRmn, ← hRpn] at h
    nlinarith [norm_nonneg (Rm f), norm_nonneg (Rp f)]
  have hm : ‖Rm u‖ ^ 2 = 0 := by
    rw [hRmn, hσu]
    exact (boundaryJumpSymbol_dirac_norms Ω t₀ J hJ hzero).1
  have hp : ‖Rp u‖ ^ 2 = 1 := by
    rw [hRpn, hσu]
    exact (boundaryJumpSymbol_dirac_norms Ω t₀ J hJ hzero).2
  have hmu : Rm u = 0 := norm_eq_zero.mp (sq_eq_zero_iff.mp hm)
  have hpu : ‖Rp u‖ = 1 := by nlinarith [norm_nonneg (Rp u)]
  exact ⟨hmu, projection_range_lt_of_unit_witness Rm Rp hRms hRps hRmi hRpi horder u hu hmu hpu⟩

end RieszEuclidean
