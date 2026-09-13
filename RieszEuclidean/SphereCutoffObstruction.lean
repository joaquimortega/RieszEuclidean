import RieszEuclidean.SphereBoundaryMeasure
import RieszEuclidean.SphereBoundaryApproach
import RieszEuclidean.BoundaryCutoffLimits
open MeasureTheory Filter Topology Metric
namespace RieszEuclidean
/-- The literal sphere geometry selects one boundary point clean for every dominated measure. -/
theorem exists_sphere_clean_point {d : ℕ} (hd : 2 ≤ d)
    (a : Euclidean d) {r : ℝ} (hr : 0 < r)
    (μ : Measure (Euclidean d)) [SFinite μ] :
    ∃ t₀ ∈ sphere a r, μ {θ | θ ≠ 0 ∧ t₀ + θ ∈ frontier (ball a r)} = 0 := by
  obtain ⟨hfin, hpos, _, _, _, hoverlap⟩ := sphere_boundary_measure_properties hd a hr
  letI := hfin
  obtain ⟨t₀, ht₀, hclean⟩ := exists_clean_boundary_point μ (sphereSurfaceMeasure a r)
    isClosed_sphere.measurableSet hpos.ne' hoverlap
  refine ⟨t₀, ht₀, ?_⟩
  simpa only [frontier_ball a hr.ne'] using hclean
/-- For a ball, actual spectral cutoff norm and difference identities are incompatible
with a uniform gap below one to norm-continuous comparison projections.
The construction of those identities from a Riesz basis remains a separate analytic step. -/
theorem sphere_cutoffs_continuous_comparison_obstruction {d : ℕ} {H : Type}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (hd : 2 ≤ d) (a : Euclidean d) {r : ℝ} (hr : 0 < r)
    {G : Set (Euclidean d)} (hG : volume Gᶜ = 0)
    (σ : H → Measure (Euclidean d)) (hfinite : ∀ f, IsFiniteMeasure (σ f))
    (μ : Measure (Euclidean d)) [SFinite μ] (hdom : ∀ f, σ f ≪ μ)
    (P : G → H →L[ℂ] H)
    (hP : ∀ t, ‖P t‖ ≤ 1 ∧ IsSelfAdjoint (P t) ∧ (P t).comp (P t) = P t)
    (hnorm : ∀ t f, ‖P t f‖ ^ 2 = ∫ θ, ‖cutoffSymbol (ball a r) t θ‖ ^ 2 ∂σ f)
    (hdiff : ∀ s t f, ‖P s f - P t f‖ ^ 2 =
      ∫ θ, ‖cutoffSymbol (ball a r) s θ - cutoffSymbol (ball a r) t θ‖ ^ 2 ∂σ f)
    (u : H) (hu : ‖u‖ = 1) (hσu : σ u = Measure.dirac 0)
    (M : Euclidean d → H →L[ℂ] H) (hM : Continuous M)
    (hMs : ∀ t, IsSelfAdjoint (M t)) (hMi : ∀ t, (M t).comp (M t) = M t)
    {γ : ℝ} (hγ : γ < 1) (hgap : ∀ t : G, ‖P t - M t‖ ≤ γ) : False := by
  obtain ⟨t₀, ht₀, hclean⟩ := exists_sphere_clean_point hd a hr μ
  have hside := sphere_point_two_sided_closure a hr ht₀
  exact boundary_cutoffs_continuous_comparison_obstruction Metric.isOpen_ball hG hside.1 hside.2.2
    σ hfinite (fun f => hdom f hclean) P hP hnorm hdiff u hu hσu
    M hM.continuousAt (hMs t₀) (hMi t₀) hγ hgap
end RieszEuclidean
