import RieszEuclidean.CompleteMinimalBallSupport
import RieszEuclidean.CompleteMinimalPointFourier
import RieszEuclidean.CompleteMinimalDifferentialOperators
import RieszEuclidean.CompleteMinimalInterpolationFunctions

/-!
# The geometric support-to-polynomial step

These composition theorems take an actual compactly supported inverse quotient
and an actual Fourier-product identity. Their conclusion is derived from the
Titchmarsh–Lions proposition, John maximality, and the proved
point-support classification. They do not assert the still separate analytic
division or the sharp polynomial degree estimate.
-/
noncomputable section
open MeasureTheory SchwartzMap
open scoped SchwartzMap FourierTransform
namespace RieszEuclidean.CompleteMinimal
variable {d : ℕ}

/-- Compact Fourier division and the physical support of its ball product force
its inverse distribution to be supported at the origin. -/
theorem normalized_ball_product_supported_origin (hTL : TitchmarshLions d)
    {v w : TemperedDistribution d} (hv : CompactlySupportedDistribution v)
    (hproduct : distributionFourier w =
      distributionMultiply (fun ξ => normalizedBallFourier d (realToComplex ξ))
        (normalizedBallFourier_real_hasTemperateGrowth d) (distributionFourier v))
    {K : Set (Euclidean d)} (hK : Convex ℝ K) (hKclosed : IsClosed K)
    (hJ : IsJohnEllipsoid K (Metric.closedBall (0 : Euclidean d) 1))
    (hw : DistributionSupportedIn w K) : DistributionSupportedIn v {0} := by
  by_cases hv0 : v = 0
  · rw [hv0]
    exact distributionSupportedIn_zero _
  · exact normalized_ball_fourier_product_supported_origin hTL hv hv0 hproduct
      hK hKclosed hJ hw

/-- The quotient's actual Fourier distribution is a polynomial regular
 distribution, with the growth certificates needed by the integral definition. -/
theorem normalized_ball_product_fourier_polynomial (hTL : TitchmarshLions d)
    {v w : TemperedDistribution d} (hv : CompactlySupportedDistribution v)
    (hproduct : distributionFourier w =
      distributionMultiply (fun ξ => normalizedBallFourier d (realToComplex ξ))
        (normalizedBallFourier_real_hasTemperateGrowth d) (distributionFourier v))
    {K : Set (Euclidean d)} (hK : Convex ℝ K) (hKclosed : IsClosed K)
    (hJ : IsJohnEllipsoid K (Metric.closedBall (0 : Euclidean d) 1))
    (hw : DistributionSupportedIn w K) :
    ∃ p : ComplexPolynomial d, ∃ N : ℕ, ∃ C : ℝ, ∃ hC : 0 ≤ C,
      ∃ hp : ∀ x, ‖polynomialEvaluation x p‖ ≤ C * (1 + ‖x‖) ^ N,
      ∃ hm : AEStronglyMeasurable (fun x => polynomialEvaluation x p) volume,
        distributionFourier v = polynomialDistribution (fun x => polynomialEvaluation x p) hC hp hm := by
  exact DistributionSupportedIn.fourier_polynomial
    (normalized_ball_product_supported_origin hTL hv hproduct hK hKclosed hJ hw)

/-- The actual finite sphere denominator gives a physical differential operator
supported in the original closed body whenever the original L² function is. -/
theorem sphereDenominator_l2_operator_supported (radius : ℕ → ℝ) (N : ℕ)
    (f : FullL2 d) (K : Set (Euclidean d))
    (hf : ∀ᵐ x, x ∉ K → f x = 0) :
    DistributionSupportedIn
      (polynomialDifferentialOperator (sphereDenominator d radius N) (l2Distribution f)) K :=
  (l2Distribution_supported f K hf).polynomialDifferentialOperator _

/-- The tail's geometric support step applied to the actual denominator operator.
The remaining input is exactly the Fourier product supplied by analytic division. -/
theorem sphere_tail_inverse_supported_origin (hTL : TitchmarshLions d)
    (radius : ℕ → ℝ) (N : ℕ) (f : FullL2 d) {v : TemperedDistribution d}
    (hv : CompactlySupportedDistribution v)
    (hproduct : distributionFourier
        (polynomialDifferentialOperator (sphereDenominator d radius N) (l2Distribution f)) =
      distributionMultiply (fun ξ => normalizedBallFourier d (realToComplex ξ))
        (normalizedBallFourier_real_hasTemperateGrowth d) (distributionFourier v))
    {K : Set (Euclidean d)} (hK : Convex ℝ K) (hKclosed : IsClosed K)
    (hJ : IsJohnEllipsoid K (Metric.closedBall (0 : Euclidean d) 1))
    (hf : ∀ᵐ x, x ∉ K → f x = 0) : DistributionSupportedIn v {0} :=
  normalized_ball_product_supported_origin hTL hv hproduct hK hKclosed hJ
    (sphereDenominator_l2_operator_supported radius N f K hf)

/-- A continuous integral representative of the Fourier transform of a
point-supported distribution is an actual polynomial on every real frequency. -/
theorem DistributionSupportedIn.continuous_fourier_polynomial
    {v : TemperedDistribution d} (hv : DistributionSupportedIn v {(0 : Euclidean d)})
    (G : Euclidean d → ℂ) (hG : Continuous G)
    (htransform : ∀ φ : 𝓢(Euclidean d, ℂ), distributionFourier v φ = ∫ x, G x * φ x) :
    ∃ m : ℕ, ∃ p : ComplexPolynomial d, p.totalDegree ≤ m ∧
      ∀ x : Euclidean d, G x = polynomialEvaluation x p := by
  obtain ⟨m, p, hdegree, hpoly⟩ := hv.fourier_polynomial_integral
  have hP : Continuous (fun x : Euclidean d => polynomialEvaluation x p) :=
    (MvPolynomial.continuous_eval p).comp
      (continuous_pi (fun j => Complex.continuous_ofReal.comp
        (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin d => ℝ) j).continuous))
  have hae : G =ᵐ[volume] (fun x => polynomialEvaluation x p) := by
    apply ae_eq_of_integral_contDiff_smul_eq hG.locallyIntegrable hP.locallyIntegrable
    intro φ hφ hc
    let ψ : 𝓢(Euclidean d, ℂ) := compactSchwartz (fun x => (φ x : ℂ))
      (Complex.ofRealCLM.contDiff.comp hφ) (hc.comp_left Complex.ofReal_zero)
    have h := (htransform ψ).symm.trans (hpoly ψ)
    change (∫ x, G x * (φ x : ℂ)) = ∫ x, polynomialEvaluation x p * (φ x : ℂ) at h
    simpa only [Complex.real_smul, mul_comm] using h
  have heq := MeasureTheory.Measure.eq_of_ae_eq hae hG hP
  exact ⟨m, p, hdegree, fun x => congrFun heq x⟩

/-- The support-to-polynomial conclusion for the actual tail quotient, once its
compact inverse distribution and Fourier product have been constructed. -/
theorem sphere_tail_quotient_polynomial (hTL : TitchmarshLions d)
    (radius : ℕ → ℝ) (N : ℕ) (f : FullL2 d) {v : TemperedDistribution d}
    (hv : CompactlySupportedDistribution v)
    (hproduct : distributionFourier
        (polynomialDifferentialOperator (sphereDenominator d radius N) (l2Distribution f)) =
      distributionMultiply (fun ξ => normalizedBallFourier d (realToComplex ξ))
        (normalizedBallFourier_real_hasTemperateGrowth d) (distributionFourier v))
    {K : Set (Euclidean d)} (hK : Convex ℝ K) (hKclosed : IsClosed K)
    (hJ : IsJohnEllipsoid K (Metric.closedBall (0 : Euclidean d) 1))
    (hf : ∀ᵐ x, x ∉ K → f x = 0)
    (G : Euclidean d → ℂ) (hG : Continuous G)
    (htransform : ∀ φ : 𝓢(Euclidean d, ℂ), distributionFourier v φ = ∫ x, G x * φ x) :
    ∃ m : ℕ, ∃ p : ComplexPolynomial d, p.totalDegree ≤ m ∧
      ∀ x : Euclidean d, G x = polynomialEvaluation x p :=
  DistributionSupportedIn.continuous_fourier_polynomial
    (sphere_tail_inverse_supported_origin hTL radius N f hv hproduct hK hKclosed hJ hf) G hG htransform


/-- The proved tail support-to-polynomial step with only scalar analytic inputs:
a compact inverse quotient, its integral transform, and `Q_N F = κ G`.
The sharp degree estimate is a separate statement. -/
theorem sphere_tail_fourier_polynomial_product (hTL : TitchmarshLions d)
    (radius : ℕ → ℝ) (N : ℕ) (f : FullL2 d)
    (hfi : Integrable (f : Euclidean d → ℂ)) {v : TemperedDistribution d}
    (hv : CompactlySupportedDistribution v)
    {K : Set (Euclidean d)} (hK : Convex ℝ K) (hKclosed : IsClosed K)
    (hJ : IsJohnEllipsoid K (Metric.closedBall (0 : Euclidean d) 1))
    (hf : ∀ᵐ x, x ∉ K → f x = 0)
    (G : Euclidean d → ℂ) (hG : Continuous G)
    (htransform : ∀ φ : 𝓢(Euclidean d, ℂ), distributionFourier v φ = ∫ x, G x * φ x)
    (hproduct : ∀ x, polynomialEvaluation x (sphereDenominator d radius N) *
        𝓕 (f : Euclidean d → ℂ) x = normalizedBallFourier d (realToComplex x) * G x) :
    ∃ m : ℕ, ∃ p : ComplexPolynomial d, p.totalDegree ≤ m ∧
      (∀ x : Euclidean d, G x = polynomialEvaluation x p) ∧
      (∀ x : Euclidean d, polynomialEvaluation x (sphereDenominator d radius N) *
        𝓕 (f : Euclidean d → ℂ) x = normalizedBallFourier d (realToComplex x) *
          polynomialEvaluation x p) := by
  have hdistribution := fourier_polynomial_product_of_integral_representatives
    (sphereDenominator d radius N) (l2Distribution f) v
    (𝓕 (f : Euclidean d → ℂ)) G
    (fun x => normalizedBallFourier d (realToComplex x))
    (normalizedBallFourier_real_hasTemperateGrowth d)
    (distributionFourier_l2_integral f hfi) htransform hproduct
  obtain ⟨m, p, hdegree, hpoly⟩ := sphere_tail_quotient_polynomial hTL radius N f hv
    hdistribution hK hKclosed hJ hf G hG htransform
  refine ⟨m, p, hdegree, hpoly, fun x => ?_⟩
  rw [hproduct x, hpoly x]

/-- The same support-to-polynomial composition for an arbitrary actual finite
polynomial denominator, including the paper's `sourceSphereDenominator`. -/
theorem polynomial_tail_fourier_polynomial_product (hTL : TitchmarshLions d)
    (q : ComplexPolynomial d) (f : FullL2 d)
    (hfi : Integrable (f : Euclidean d → ℂ)) {v : TemperedDistribution d}
    (hv : CompactlySupportedDistribution v)
    {K : Set (Euclidean d)} (hK : Convex ℝ K) (hKclosed : IsClosed K)
    (hJ : IsJohnEllipsoid K (Metric.closedBall (0 : Euclidean d) 1))
    (hf : ∀ᵐ x, x ∉ K → f x = 0)
    (G : Euclidean d → ℂ) (hG : Continuous G)
    (htransform : ∀ φ : 𝓢(Euclidean d, ℂ), distributionFourier v φ = ∫ x, G x * φ x)
    (hproduct : ∀ x, polynomialEvaluation x q * 𝓕 (f : Euclidean d → ℂ) x =
      normalizedBallFourier d (realToComplex x) * G x) :
    ∃ m : ℕ, ∃ p : ComplexPolynomial d, p.totalDegree ≤ m ∧
      (∀ x : Euclidean d, G x = polynomialEvaluation x p) ∧
      (∀ x : Euclidean d, polynomialEvaluation x q * 𝓕 (f : Euclidean d → ℂ) x =
        normalizedBallFourier d (realToComplex x) * polynomialEvaluation x p) := by
  have hdistribution := fourier_polynomial_product_of_integral_representatives q (l2Distribution f) v
    (𝓕 (f : Euclidean d → ℂ)) G
    (fun x => normalizedBallFourier d (realToComplex x))
    (normalizedBallFourier_real_hasTemperateGrowth d)
    (distributionFourier_l2_integral f hfi) htransform hproduct
  have hs := normalized_ball_product_supported_origin hTL hv hdistribution hK hKclosed hJ
    ((l2Distribution_supported f K hf).polynomialDifferentialOperator q)
  obtain ⟨m, p, hdegree, hpoly⟩ := hs.continuous_fourier_polynomial G hG htransform
  refine ⟨m, p, hdegree, hpoly, fun x => ?_⟩
  rw [hproduct x, hpoly x]

/-- The polynomial product is the paper's rational expression wherever the
finite denominator is nonzero. -/
theorem fourier_eq_polynomial_ball_quotient (f : FullL2 d) (p q : ComplexPolynomial d)
    (hproduct : ∀ x : Euclidean d, polynomialEvaluation x q * 𝓕 (f : Euclidean d → ℂ) x =
      normalizedBallFourier d (realToComplex x) * polynomialEvaluation x p)
    (x : Euclidean d) (hq : polynomialEvaluation x q ≠ 0) :
    𝓕 (f : Euclidean d → ℂ) x =
      polynomialEvaluation x p * normalizedBallFourier d (realToComplex x) /
        polynomialEvaluation x q := by
  apply (eq_div_iff hq).mpr
  simpa only [mul_comm] using hproduct x


end RieszEuclidean.CompleteMinimal
