import RieszEuclidean.CompleteMinimalBessel
import RieszEuclidean.CompleteMinimalDistributionConvolution
import RieszEuclidean.CompleteMinimalRegularSupport

/-!
# Exact support of the normalized ball distribution

The seed is the actual unit-ball indicator divided by its positive volume.
Local distributional vanishing forces a.e. vanishing; positivity of volume on
open sets then identifies its exact support with the closed unit ball.
-/

noncomputable section
open MeasureTheory Set SchwartzMap
open scoped SchwartzMap FourierTransform ENNReal

namespace RieszEuclidean.CompleteMinimal

variable {d : ℕ}

theorem ballIndicator_memLp (d : ℕ) : MemLp (ballIndicator d) 2 volume :=
  memLp_indicator_const 2 (physicalUnitBall_measurable d) 1
    (Or.inr (physicalUnitBall_volume_lt_top d).ne)

/-- The normalized physical-space unit-ball indicator. -/
def normalizedBallIndicator (d : ℕ) : Euclidean d → ℂ :=
  (ballVolume d : ℂ)⁻¹ • ballIndicator d

theorem normalizedBallIndicator_memLp (d : ℕ) :
    MemLp (normalizedBallIndicator d) 2 volume :=
  (ballIndicator_memLp d).const_smul ((ballVolume d : ℂ)⁻¹)

/-- The actual normalized ball vector in full Euclidean L². -/
def normalizedBallL2 (d : ℕ) : FullL2 d :=
  (normalizedBallIndicator_memLp d).toLp (normalizedBallIndicator d)

theorem normalizedBallL2_ae (d : ℕ) :
    (normalizedBallL2 d : Euclidean d → ℂ) =ᵐ[volume] normalizedBallIndicator d :=
  (normalizedBallIndicator_memLp d).coeFn_toLp

theorem normalizedBallL2_integrable (d : ℕ) :
    Integrable (normalizedBallL2 d : Euclidean d → ℂ) :=
  (Integrable.smul ((ballVolume d : ℂ)⁻¹) (ballIndicator_integrable d)).congr
    (normalizedBallL2_ae d).symm

theorem normalizedBallL2_supported (d : ℕ) :
    ∀ᵐ x, x ∉ Metric.closedBall (0 : Euclidean d) 1 → normalizedBallL2 d x = 0 := by
  filter_upwards [normalizedBallL2_ae d] with x hx
  intro hn
  have hb : x ∉ physicalUnitBall d :=
    fun h => hn (Metric.ball_subset_closedBall h)
  simp [hx, normalizedBallIndicator, ballIndicator, hb]

/-- The seed is an actual continuous functional on Schwartz space. -/
def normalizedBallDistribution (d : ℕ) : TemperedDistribution d :=
  l2Distribution (normalizedBallL2 d)

theorem normalizedBallDistribution_supported (d : ℕ) :
    DistributionSupportedIn (normalizedBallDistribution d)
      (Metric.closedBall (0 : Euclidean d) 1) :=
  l2Distribution_supported _ _ (normalizedBallL2_supported d)

theorem normalizedBallDistribution_compactlySupported (d : ℕ) :
    CompactlySupportedDistribution (normalizedBallDistribution d) :=
  ⟨Metric.closedBall (0 : Euclidean d) 1, isCompact_closedBall _ _,
    normalizedBallDistribution_supported d⟩

/-- The exact local-test support is the entire closed unit ball, not merely a subset. -/
theorem normalizedBallDistribution_support (d : ℕ) :
    distributionSupport (normalizedBallDistribution d) =
      Metric.closedBall (0 : Euclidean d) 1 := by
  apply Set.Subset.antisymm
  · exact (normalizedBallDistribution_supported d).support_subset Metric.isClosed_closedBall
  · have hinner : physicalUnitBall d ⊆ distributionSupport (normalizedBallDistribution d) := by
      apply open_subset_l2Distribution_support_of_const Metric.isOpen_ball
        (inv_ne_zero (Complex.ofReal_ne_zero.mpr (ballVolume_pos d).ne'))
      filter_upwards [normalizedBallL2_ae d] with x hx
      intro hmem
      simp [hx, normalizedBallIndicator, ballIndicator, physicalUnitBall, hmem]
    have hclosure := closure_minimal hinner (distributionSupport_isClosed _)
    simpa only [physicalUnitBall, closure_ball _ one_ne_zero] using hclosure

theorem normalizedBallDistribution_ne_zero (d : ℕ) : normalizedBallDistribution d ≠ 0 := by
  intro hz
  have hmem : (0 : Euclidean d) ∈ distributionSupport (normalizedBallDistribution d) := by
    rw [normalizedBallDistribution_support]
    simp
  rw [hz, distributionSupport_zero] at hmem
  exact hmem

theorem normalizedBallDistribution_convexSupport (d : ℕ) :
    convexHull ℝ (distributionSupport (normalizedBallDistribution d)) =
      Metric.closedBall (0 : Euclidean d) 1 := by
  rw [normalizedBallDistribution_support, (convex_closedBall _ _).convexHull_eq]

/-- Its entire integral transform is exactly the actual normalized ball transform. -/
theorem entireFourier_normalizedBallL2 (d : ℕ) :
    entireFourier (normalizedBallL2 d : Euclidean d → ℂ) = normalizedBallFourier d := by
  rw [entireFourier_congr (normalizedBallL2_ae d)]
  change entireFourier ((ballVolume d : ℂ)⁻¹ • ballIndicator d) = _
  rw [entireFourier_smul]
  funext z
  simp [normalizedBallFourier, div_eq_mul_inv, mul_comm]

/-- Pointwise Fourier integral agreement at every real frequency. -/
theorem fourier_normalizedBallL2 (d : ℕ) (ξ : Euclidean d) :
    𝓕 (normalizedBallL2 d : Euclidean d → ℂ) ξ =
      normalizedBallFourier d (realToComplex ξ) := by
  rw [← entireFourier_realToComplex, entireFourier_normalizedBallL2]

/-- The unitary L² Fourier transform has the normalized ball transform as its actual a.e. values. -/
theorem fourierL2_normalizedBallL2_ae (d : ℕ) :
    (fourierL2Equiv d (normalizedBallL2 d) : Euclidean d → ℂ) =ᵐ[volume]
      fun ξ => normalizedBallFourier d (realToComplex ξ) :=
  (fourierL2Equiv_eq_integral _ (normalizedBallL2_integrable d)).trans
    (Filter.Eventually.of_forall (fourier_normalizedBallL2 d))

theorem normalizedBallFourier_real_hasTemperateGrowth (d : ℕ) :
    Function.HasTemperateGrowth (fun ξ => normalizedBallFourier d (realToComplex ξ)) := by
  have he : 𝓕 (normalizedBallL2 d : Euclidean d → ℂ) =
      fun ξ => normalizedBallFourier d (realToComplex ξ) := funext (fourier_normalizedBallL2 d)
  rw [← he]
  exact fourier_hasTemperateGrowth_of_compact_support (normalizedBallL2_integrable d)
    (isCompact_closedBall _ _) (normalizedBallL2_supported d)

/-- The transposed distribution Fourier transform agrees with the regular
distribution of the concrete normalized ball Fourier function. -/
theorem distributionFourier_normalizedBallDistribution (d : ℕ) :
    distributionFourier (normalizedBallDistribution d) =
      polynomialDistribution (fun ξ => normalizedBallFourier d (realToComplex ξ))
        zero_le_one (N := 0)
        (fun ξ => by simpa using normalizedBallFourier_real_norm_le d ξ)
        (normalizedBallFourier_real_hasTemperateGrowth d).1.continuous.aestronglyMeasurable := by
  ext φ
  rw [normalizedBallDistribution, distributionFourier_l2Distribution,
    l2Distribution_apply, polynomialDistribution_apply]
  apply integral_congr_ae
  filter_upwards [fourierL2_normalizedBallL2_ae d] with ξ hξ
  rw [hξ]

/-- With this actual ball seed, Titchmarsh–Lions and John rigidity force the
remaining compact distribution factor to be supported at the origin. -/
theorem normalized_ball_convolution_supported_origin (hTL : TitchmarshLions d)
    {v w : TemperedDistribution d} (hv : CompactlySupportedDistribution v) (hv0 : v ≠ 0)
    (hc : IsDistributionConvolution v (normalizedBallDistribution d) w)
    {K : Set (Euclidean d)} (hK : Convex ℝ K) (hKclosed : IsClosed K)
    (hJ : IsJohnEllipsoid K (Metric.closedBall (0 : Euclidean d) 1))
    (hw : DistributionSupportedIn w K) : DistributionSupportedIn v {0} :=
  hTL.supportedIn_origin_of_john_right (normalizedBallDistribution_compactlySupported d)
    hv (normalizedBallDistribution_ne_zero d) hv0 hc hK hKclosed hJ
    (normalizedBallDistribution_convexSupport d) hw

/-- The same conclusion from the paper's actual Fourier-product identity, using
the proved Fourier-multiplier/convolution bridge. -/
theorem normalized_ball_fourier_product_supported_origin (hTL : TitchmarshLions d)
    {v w : TemperedDistribution d} (hv : CompactlySupportedDistribution v) (hv0 : v ≠ 0)
    (hproduct : distributionFourier w =
      distributionMultiply (fun ξ => normalizedBallFourier d (realToComplex ξ))
        (normalizedBallFourier_real_hasTemperateGrowth d) (distributionFourier v))
    {K : Set (Euclidean d)} (hK : Convex ℝ K) (hKclosed : IsClosed K)
    (hJ : IsJohnEllipsoid K (Metric.closedBall (0 : Euclidean d) 1))
    (hw : DistributionSupportedIn w K) : DistributionSupportedIn v {0} := by
  apply normalized_ball_convolution_supported_origin hTL hv hv0 _ hK hKclosed hJ hw
  change IsDistributionConvolution v (l2Distribution (normalizedBallL2 d)) w
  apply isDistributionConvolution_of_fourier_product (normalizedBallL2 d)
    (normalizedBallL2_integrable d)
    (fourier_hasTemperateGrowth_of_compact_support (normalizedBallL2_integrable d)
      (isCompact_closedBall _ _) (normalizedBallL2_supported d))
  have he : 𝓕 (normalizedBallL2 d : Euclidean d → ℂ) =
      fun ξ => normalizedBallFourier d (realToComplex ξ) := funext (fourier_normalizedBallL2 d)
  simpa only [he] using hproduct

end RieszEuclidean.CompleteMinimal
