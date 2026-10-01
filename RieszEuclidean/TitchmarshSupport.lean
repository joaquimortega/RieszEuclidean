import RieszEuclidean.CompleteMinimalConvolutionSupport
import RieszEuclidean.CompleteMinimalSchwartzDensity

noncomputable section
open MeasureTheory Set SchwartzMap
open scoped SchwartzMap Pointwise
namespace RieszEuclidean.CompleteMinimal

variable {d : ℕ}

private theorem translated_tsupport_subset (x : Euclidean d) (φ : 𝓢(Euclidean d, ℂ)) :
    tsupport (schwartzTranslateCLM x φ : Euclidean d → ℂ) ⊆
      (fun y => x + y) ⁻¹' tsupport (φ : Euclidean d → ℂ) := by
  change closure (Function.support (schwartzTranslateCLM x φ : Euclidean d → ℂ)) ⊆
    (fun y => x + y) ⁻¹' tsupport (φ : Euclidean d → ℂ)
  apply IsClosed.closure_subset_iff (isClosed_tsupport _ |>.preimage (continuous_const.add continuous_id)) |>.mpr
  intro y hy
  exact subset_tsupport _ (show φ (x + y) ≠ 0 from hy)

/-- The actual convolution is supported in the sum of the compact factor supports. -/
theorem distributionConvolution_support_subset_add
    {u v w : TemperedDistribution d}
    (hu : CompactlySupportedDistribution u)
    (hv : CompactlySupportedDistribution v)
    (hc : IsDistributionConvolution u v w) :
    distributionSupport w ⊆ distributionSupport u + distributionSupport v := by
  let A := distributionSupport u
  let B := distributionSupport v
  have hAc : IsCompact A := hu.support_isCompact
  have hBc : IsCompact B := hv.support_isCompact
  have hsumc : IsCompact (A + B) := hAc.add hBc
  apply (distributionSupportedIn_iff_support_subset w (A + B) hsumc.isClosed).mp
  intro φ hφ hdisj
  obtain ⟨ψ, hψ, hw⟩ := hc φ
  let C : Set (Euclidean d) :=
    (fun p : Euclidean d × Euclidean d => p.1 - p.2) ''
      (tsupport (φ : Euclidean d → ℂ) ×ˢ B)
  have hCc : IsCompact C := (hφ.prod hBc).image (continuous_fst.sub continuous_snd)
  have hψC : tsupport (ψ : Euclidean d → ℂ) ⊆ C := by
    apply IsClosed.closure_subset_iff hCc.isClosed |>.mpr
    intro x hx
    have hne : v (schwartzTranslateCLM x φ) ≠ 0 := by simpa only [← hψ x] using hx
    by_contra hnot
    apply hne
    apply (distributionSupportedIn_support v).schwartz_test
    apply Set.disjoint_left.mpr
    intro y hy hyB
    have hxy : x + y ∈ tsupport (φ : Euclidean d → ℂ) :=
      translated_tsupport_subset x φ hy
    apply hnot
    exact ⟨(x + y, y), ⟨hxy, hyB⟩, by simp⟩
  have hCA : Disjoint C A := by
    apply Set.disjoint_left.mpr
    intro x hx hxa
    obtain ⟨p, hp, rfl⟩ := hx
    have hp0 : p.1 ∈ tsupport (φ : Euclidean d → ℂ) := hp.1
    have hp1 : p.2 ∈ B := hp.2
    have hmem : p.1 - p.2 + p.2 ∈ A + B :=
      Set.mem_add.mpr ⟨p.1 - p.2, hxa, p.2, hp1, rfl⟩
    have : p.1 ∈ A + B := by simpa using hmem
    exact Set.disjoint_left.mp hdisj hp0 this
  have hzero : u ψ = 0 :=
    (distributionSupportedIn_support u).schwartz_test ψ (hCA.mono_left hψC)
  exact hw.trans hzero

/-- The convex hull of the actual convolution support lies in the sum of factor hulls. -/
theorem distributionConvolution_convexHull_subset_add
    {u v w : TemperedDistribution d}
    (hu : CompactlySupportedDistribution u)
    (hv : CompactlySupportedDistribution v)
    (hc : IsDistributionConvolution u v w) :
    convexHull ℝ (distributionSupport w) ⊆
      convexHull ℝ (distributionSupport u) + convexHull ℝ (distributionSupport v) := by
  rw [← convexHull_add]
  exact convexHull_mono (distributionConvolution_support_subset_add hu hv hc)

/-- Convolution of compactly supported distributions is compactly supported. -/
theorem IsDistributionConvolution.compactlySupported
    {u v w : TemperedDistribution d}
    (hc : IsDistributionConvolution u v w)
    (hu : CompactlySupportedDistribution u)
    (hv : CompactlySupportedDistribution v) :
    CompactlySupportedDistribution w := by
  let K := distributionSupport u + distributionSupport v
  have hK : IsCompact K := hu.support_isCompact.add hv.support_isCompact
  refine ⟨K, hK, ?_⟩
  exact (distributionSupportedIn_iff_support_subset w K hK.isClosed).mpr
    (distributionConvolution_support_subset_add hu hv hc)

end RieszEuclidean.CompleteMinimal
