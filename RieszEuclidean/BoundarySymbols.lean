import RieszEuclidean.StationaryCutoffs
import Mathlib.Topology.Algebra.Indicator
open MeasureTheory Filter Topology
noncomputable section
namespace RieszEuclidean
/-- At the clean boundary point the interior limit adds exactly the zero frequency. -/
def interiorBoundarySymbol {d : ℕ} (Ω : Set (Euclidean d)) (t θ : Euclidean d) : ℂ :=
  cutoffSymbol Ω t θ + ({0} : Set (Euclidean d)).indicator (fun _ => (1 : ℂ)) θ
/-- A translated cutoff is continuous along parameters away from the translated frontier. -/
theorem tendsto_cutoffSymbol_off_frontier {d : ℕ} {Ω : Set (Euclidean d)}
    {t : ℕ → Euclidean d} {t₀ θ : Euclidean d}
    (ht : Tendsto t atTop (𝓝 t₀)) (hθ : t₀ + θ ∉ frontier Ω) :
    Tendsto (fun n => cutoffSymbol Ω (t n) θ) atTop (𝓝 (cutoffSymbol Ω t₀ θ)) := by
  exact (continuousOn_const.continuousAt_indicator hθ).tendsto.comp
    (ht.add_const θ)
/-- Outside parameters converge almost everywhere to the unchanged open-domain symbol. -/
theorem cutoffSymbol_exterior_ae_tendsto {d : ℕ} {Ω : Set (Euclidean d)}
    (hΩ : IsOpen Ω) {t₀ : Euclidean d} (hx : t₀ ∈ frontier Ω)
    (σ : Measure (Euclidean d)) (hclean : σ {θ | θ ≠ 0 ∧ t₀ + θ ∈ frontier Ω} = 0)
    {t : ℕ → Euclidean d} (ht : Tendsto t atTop (𝓝 t₀))
    (hout : ∀ n, t n ∉ closure Ω) :
    ∀ᵐ θ ∂σ, Tendsto (fun n => cutoffSymbol Ω (t n) θ) atTop
      (𝓝 (cutoffSymbol Ω t₀ θ)) := by
  have hxnot : t₀ ∉ Ω := by rw [hΩ.frontier_eq] at hx; exact hx.2
  have hae : ∀ᵐ θ ∂σ, ¬(θ ≠ 0 ∧ t₀ + θ ∈ frontier Ω) := by
    simpa only [ae_iff, not_not] using hclean
  filter_upwards [hae] with θ hθ
  by_cases hz : θ = 0
  · subst θ
    have hn : ∀ n, t n ∉ Ω := fun n h => hout n (subset_closure h)
    simp [cutoffSymbol, hxnot, hn]
  · exact tendsto_cutoffSymbol_off_frontier ht (fun h => hθ ⟨hz, h⟩)
/-- Inside parameters add the zero frequency and agree elsewhere outside one common null set. -/
theorem cutoffSymbol_interior_ae_tendsto {d : ℕ} {Ω : Set (Euclidean d)}
    (hΩ : IsOpen Ω) {t₀ : Euclidean d} (hx : t₀ ∈ frontier Ω)
    (σ : Measure (Euclidean d)) (hclean : σ {θ | θ ≠ 0 ∧ t₀ + θ ∈ frontier Ω} = 0)
    {t : ℕ → Euclidean d} (ht : Tendsto t atTop (𝓝 t₀))
    (hin : ∀ n, t n ∈ Ω) :
    ∀ᵐ θ ∂σ, Tendsto (fun n => cutoffSymbol Ω (t n) θ) atTop
      (𝓝 (interiorBoundarySymbol Ω t₀ θ)) := by
  have hxnot : t₀ ∉ Ω := by rw [hΩ.frontier_eq] at hx; exact hx.2
  have hae : ∀ᵐ θ ∂σ, ¬(θ ≠ 0 ∧ t₀ + θ ∈ frontier Ω) := by
    simpa only [ae_iff, not_not] using hclean
  filter_upwards [hae] with θ hθ
  by_cases hz : θ = 0
  · subst θ
    simp [cutoffSymbol, interiorBoundarySymbol, hxnot, hin]
  · simpa [interiorBoundarySymbol, hz] using
      tendsto_cutoffSymbol_off_frontier ht (fun h => hθ ⟨hz, h⟩)
/-- Both boundary symbols are indicators: the additional zero atom lies outside the open domain. -/
theorem interiorBoundarySymbol_idempotent {d : ℕ} (Ω : Set (Euclidean d))
    {t : Euclidean d} (ht : t ∉ Ω) (θ : Euclidean d) :
    interiorBoundarySymbol Ω t θ * interiorBoundarySymbol Ω t θ =
      interiorBoundarySymbol Ω t θ := by
  by_cases hz : θ = 0
  · subst θ; simp [interiorBoundarySymbol, cutoffSymbol, ht]
  · simpa [interiorBoundarySymbol, hz] using cutoffSymbol_idempotent Ω t θ
/-- Pointwise squared norms record exactly the additional zero-frequency component. -/
theorem interiorBoundarySymbol_norm_sq {d : ℕ} (Ω : Set (Euclidean d))
    {t : Euclidean d} (ht : t ∉ Ω) (θ : Euclidean d) :
    ‖interiorBoundarySymbol Ω t θ‖ ^ 2 = ‖cutoffSymbol Ω t θ‖ ^ 2 +
      ({0} : Set (Euclidean d)).indicator (fun _ => (1 : ℝ)) θ := by
  by_cases hz : θ = 0
  · subst θ; simp [interiorBoundarySymbol, cutoffSymbol, ht]
  · simp [interiorBoundarySymbol, hz]
/-- The two limiting symbols give ordered squared norms. -/
theorem boundarySymbol_norm_sq_le {d : ℕ} (Ω : Set (Euclidean d))
    {t : Euclidean d} (ht : t ∉ Ω) (θ : Euclidean d) :
    ‖cutoffSymbol Ω t θ‖ ^ 2 ≤ ‖interiorBoundarySymbol Ω t θ‖ ^ 2 := by
  rw [interiorBoundarySymbol_norm_sq Ω ht θ]
  exact le_add_of_nonneg_right (Set.indicator_nonneg (fun _ _ => zero_le_one) θ)
/-- The invariant constant's Dirac spectrum detects a strict jump of squared norm. -/
theorem boundarySymbol_dirac_norms {d : ℕ} (Ω : Set (Euclidean d))
    {t : Euclidean d} (ht : t ∉ Ω) :
    (∫ θ, ‖cutoffSymbol Ω t θ‖ ^ 2 ∂Measure.dirac 0) = 0 ∧
      (∫ θ, ‖interiorBoundarySymbol Ω t θ‖ ^ 2 ∂Measure.dirac 0) = 1 := by
  simp [cutoffSymbol, interiorBoundarySymbol, ht]
end RieszEuclidean
