import RieszEuclidean.TitchmarshRegularization
import RieszEuclidean.TitchmarshRegularizationSupport
import RieszEuclidean.TitchmarshFunctionAlgebra
import RieszEuclidean.TitchmarshConvexGeometry

/-!
# Assembly of the distribution Titchmarsh theorem from regularizations

The two analytic inputs are kept explicit: the function support theorem for
compactly supported continuous functions, and support propagation for the
convolution of two regularized distributions. This file handles the remaining
localization, compactness, and convex-geometric argument.
-/

noncomputable section
open MeasureTheory Set SchwartzMap
open scoped SchwartzMap Pointwise CompactlySupported Convolution

namespace RieszEuclidean.CompleteMinimal

variable {d : ℕ}

private abbrev RegularizedFunction (d : ℕ) :=
  RieszEuclidean.TitchmarshFunctionAlgebra.Function d

/-- Package one compactly supported regularization as a compactly supported
continuous function. -/
private noncomputable def regularizedAssemblyFunction
    (u : TemperedDistribution d) (hu : CompactlySupportedDistribution u)
    (ρ : 𝓢(Euclidean d, ℂ)) (hρ : HasCompactSupport (ρ : Euclidean d → ℂ))
    (hcont : Continuous (distributionRegularization u ρ)) : RegularizedFunction d :=
  ⟨⟨distributionRegularization u ρ, hcont⟩,
    distributionRegularization_hasCompactSupport hu hρ⟩

theorem titchmarshLions_of_regularized_support
    (hFunctionTL : ∀ (f g : RegularizedFunction d), f ≠ 0 → g ≠ 0 →
      convexHull ℝ (tsupport
        (RieszEuclidean.TitchmarshFunctionAlgebra.convolution d f g : Euclidean d → ℂ)) =
        convexHull ℝ (tsupport (f : Euclidean d → ℂ)) +
          convexHull ℝ (tsupport (g : Euclidean d → ℂ)))
    (hRegConvSupport : ∀ {u v w : TemperedDistribution d}
      (hu : CompactlySupportedDistribution u) (hv : CompactlySupportedDistribution v)
      (_ : IsDistributionConvolution u v w)
      {ρ σ : 𝓢(Euclidean d, ℂ)},
      (hρ : HasCompactSupport (ρ : Euclidean d → ℂ)) →
      (hσ : HasCompactSupport (σ : Euclidean d → ℂ)) →
      tsupport (RieszEuclidean.TitchmarshFunctionAlgebra.convolution d
        (regularizedAssemblyFunction u hu ρ hρ (continuous_distributionRegularization u ρ))
        (regularizedAssemblyFunction v hv σ hσ (continuous_distributionRegularization v σ)) :
        Euclidean d → ℂ) ⊆
        distributionSupport w + tsupport (ρ : Euclidean d → ℂ) +
          tsupport (σ : Euclidean d → ℂ)) :
    TitchmarshLions d := by
  intro u v w hu hv hu0 hv0 hc
  have hw : CompactlySupportedDistribution w := hc.compactlySupported hu hv
  have hreverse : convexHull ℝ (distributionSupport u) +
      convexHull ℝ (distributionSupport v) ⊆ convexHull ℝ (distributionSupport w) := by
    refine convexHull_add_subset_convexHull_of_approx_of_compact
      (E := Euclidean d) (A := distributionSupport u) (B := distributionSupport v)
      (C := distributionSupport w) hw.support_isCompact ?_
    intro a b ha hb ε hε
    obtain ⟨ρ, hρc, hρloc, hρa⟩ :=
      distributionSupport_regularization_detect_small ha (half_pos hε)
    obtain ⟨σ, hσc, hσloc, hσb⟩ :=
      distributionSupport_regularization_detect_small hb (half_pos hε)
    let hρ : Continuous (distributionRegularization u ρ) := continuous_distributionRegularization u ρ
    let hσ : Continuous (distributionRegularization v σ) := continuous_distributionRegularization v σ
    let f := regularizedAssemblyFunction u hu ρ hρc hρ
    let g := regularizedAssemblyFunction v hv σ hσc hσ
    let k := RieszEuclidean.TitchmarshFunctionAlgebra.convolution d f g
    have hfne : f ≠ 0 := by
      intro hz
      have := congrArg (fun q : RegularizedFunction d => (q : Euclidean d → ℂ) a) hz
      exact hρa (by simpa [f, regularizedAssemblyFunction] using this)
    have hgne : g ≠ 0 := by
      intro hz
      have := congrArg (fun q : RegularizedFunction d => (q : Euclidean d → ℂ) b) hz
      exact hσb (by simpa [g, regularizedAssemblyFunction] using this)
    have hkHull := hFunctionTL f g hfne hgne
    have haF : a ∈ tsupport (f : Euclidean d → ℂ) := subset_tsupport _ hρa
    have hbG : b ∈ tsupport (g : Euclidean d → ℂ) := subset_tsupport _ hσb
    let ε' : ℝ := ε / 2
    have hρball : tsupport (ρ : Euclidean d → ℂ) ⊆ Metric.closedBall 0 ε' := by
      simpa [ε'] using hρloc
    have hσball : tsupport (σ : Euclidean d → ℂ) ⊆ Metric.closedBall 0 ε' := by
      simpa [ε'] using hσloc
    have hksub : tsupport (k : Euclidean d → ℂ) ⊆
        distributionSupport w + Metric.closedBall 0 ε := by
      intro x hx
      have hreg := (hRegConvSupport hu hv hc hρc hσc) hx
      obtain ⟨p, hp, q, hq, hpq⟩ := Set.mem_add.mp hreg
      obtain ⟨p₀, hp₀, z, hz, hp₀z⟩ := Set.mem_add.mp hp
      have hnz : ‖z‖ ≤ ε / 2 := by
        simpa only [Metric.mem_closedBall, dist_zero_right] using hρball hz
      have hnq : ‖q‖ ≤ ε / 2 := by
        simpa only [Metric.mem_closedBall, dist_zero_right] using hσball hq
      have hnorm : ‖z + q‖ ≤ ε := by
        calc
          ‖z + q‖ ≤ ‖z‖ + ‖q‖ := norm_add_le _ _
          _ ≤ ε := by linarith
      have hzz' : z + q ∈ Metric.closedBall (0 : Euclidean d) ε := by
        simpa only [Metric.mem_closedBall, dist_zero_right] using hnorm
      have hpx : p₀ + (z + q) = x := by calc
        p₀ + (z + q) = (p₀ + z) + q := by abel
        _ = p + q := by rw [hp₀z]
        _ = x := hpq
      exact Set.mem_add.mpr ⟨p₀, hp₀, z + q, hzz', hpx⟩
    refine ⟨tsupport (f : Euclidean d → ℂ), tsupport (g : Euclidean d → ℂ),
      tsupport (k : Euclidean d → ℂ), haF, hbG, ?_, ?_⟩
    · simpa [k] using hkHull
    · exact hksub
  exact Set.Subset.antisymm
    (distributionConvolution_convexHull_subset_add hu hv hc) hreverse

end RieszEuclidean.CompleteMinimal
