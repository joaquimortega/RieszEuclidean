import RieszEuclidean.CompleteMinimalDistributionConvolution
import RieszEuclidean.CompleteMinimalPolynomial

/-! Constant-coefficient physical derivatives and their actual Fourier multipliers. -/
noncomputable section
open MeasureTheory SchwartzMap
open scoped SchwartzMap FourierTransform BigOperators
namespace RieszEuclidean.CompleteMinimal
variable {d : ℕ}

/-- The real-frequency symbol of a physical directional derivative. -/
def derivativeSymbolCLM (v : Euclidean d) : Euclidean d →L[ℝ] ℂ :=
  (2 * Real.pi * Complex.I : ℂ) • (Complex.ofRealCLM.comp (innerSL ℝ v))

@[simp] theorem derivativeSymbolCLM_apply (v x : Euclidean d) :
    derivativeSymbolCLM v x = (2 * Real.pi * Complex.I : ℂ) * (inner (𝕜 := ℝ) v x : ℂ) := rfl

/-- A derivative symbol is a genuine smooth multiplier of temperate growth. -/
def derivativeMultiplierCLM (v : Euclidean d) :
    𝓢(Euclidean d, ℂ) →L[ℂ] 𝓢(Euclidean d, ℂ) :=
  schwartzMultiplierCLM (derivativeSymbolCLM v) (derivativeSymbolCLM v).hasTemperateGrowth

/-- Differentiating a transformed test gives the negative derivative symbol. -/
theorem pderiv_fourier_schwartz (v : Euclidean d) (φ : 𝓢(Euclidean d, ℂ)) :
    SchwartzMap.pderivCLM ℂ v (SchwartzMap.fourierTransformCLE ℂ φ) =
      -(SchwartzMap.fourierTransformCLE ℂ (derivativeMultiplierCLM v φ)) := by
  ext x
  change (fderiv ℝ (𝓕 (φ : Euclidean d → ℂ)) x) v =
    -(𝓕 (derivativeMultiplierCLM v φ : Euclidean d → ℂ) x)
  have hi : Integrable (fun y : Euclidean d => ‖y‖ * ‖φ y‖) := by
    simpa only [pow_one] using φ.integrable_pow_mul volume 1
  have hsm : Integrable (VectorFourier.fourierSMulRight (innerSL ℝ) (φ : Euclidean d → ℂ)) := by
    apply (hi.const_mul (2 * Real.pi * ‖(innerSL ℝ : Euclidean d →L[ℝ] Euclidean d →L[ℝ] ℝ)‖)).mono'
      φ.continuous.aestronglyMeasurable.fourierSMulRight
    filter_upwards with y
    simpa only [mul_assoc] using VectorFourier.norm_fourierSMulRight_le (innerSL ℝ) (φ : Euclidean d → ℂ) y
  rw [Real.fderiv_fourierIntegral φ.integrable hi,
    Real.fourierIntegral_continuousLinearMap_apply hsm,
    Real.fourierIntegral_eq, Real.fourierIntegral_eq, ← integral_neg]
  apply integral_congr_ae
  filter_upwards with y
  simp only [VectorFourier.fourierSMulRight_apply, innerSL_apply,
    derivativeMultiplierCLM, schwartzMultiplierCLM_apply, derivativeSymbolCLM_apply,
    Complex.real_smul, smul_eq_mul, Circle.smul_def, real_inner_comm v y]
  rw [show (innerSL ℝ y) v = inner (𝕜 := ℝ) v y by exact (real_inner_comm y v).symm]
  ring

/-- The Fourier transform of a physical derivative is multiplication by its symbol. -/
theorem distributionFourier_derivative (v : Euclidean d) (u : TemperedDistribution d) :
    distributionFourier (distributionDerivative v u) =
      distributionMultiply (derivativeSymbolCLM v) (derivativeSymbolCLM v).hasTemperateGrowth
        (distributionFourier u) := by
  ext φ
  simp only [distributionFourier_apply, distributionDerivative_apply,
    distributionMultiply_apply]
  rw [pderiv_fourier_schwartz, map_neg, neg_neg]
  rfl

/-- Division by the Fourier derivative constant gives the coordinate operator. -/
def normalizedCoordinateDerivative (j : Fin d) (u : TemperedDistribution d) :
    TemperedDistribution d :=
  (2 * Real.pi * Complex.I : ℂ)⁻¹ •
    distributionDerivative (EuclideanSpace.basisFun (Fin d) ℝ j) u

/-- Coordinate multiplication on the actual Schwartz test space. -/
def coordinateTestCLM (j : Fin d) : 𝓢(Euclidean d, ℂ) →L[ℂ] 𝓢(Euclidean d, ℂ) :=
  let c : Euclidean d →L[ℝ] ℂ := Complex.ofRealCLM.comp (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin d => ℝ) j)
  schwartzMultiplierCLM c c.hasTemperateGrowth

@[simp] theorem coordinateTestCLM_apply (j : Fin d) (φ : 𝓢(Euclidean d, ℂ)) (x : Euclidean d) :
    coordinateTestCLM j φ x = φ x * (x j : ℂ) := rfl

theorem distributionFourier_normalizedCoordinateDerivative (j : Fin d) (u : TemperedDistribution d) :
    distributionFourier (normalizedCoordinateDerivative j u) =
      (distributionFourier u).comp (coordinateTestCLM j) := by
  have hc : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
    apply mul_ne_zero
    · exact mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
    · exact Complex.I_ne_zero
  ext φ
  change (2 * Real.pi * Complex.I : ℂ)⁻¹ *
    distributionFourier (distributionDerivative (EuclideanSpace.basisFun (Fin d) ℝ j) u) φ = _
  rw [distributionFourier_derivative]
  have he : derivativeMultiplierCLM (EuclideanSpace.basisFun (Fin d) ℝ j) φ =
      (2 * Real.pi * Complex.I : ℂ) • coordinateTestCLM j φ := by
    ext x
    simp only [derivativeMultiplierCLM, schwartzMultiplierCLM_apply,
      derivativeSymbolCLM_apply, SchwartzMap.smul_apply, coordinateTestCLM_apply,
      EuclideanSpace.basisFun_apply, EuclideanSpace.inner_single_left]
    simp only [conj_trivial, one_mul, smul_eq_mul]
    ring
  change _ * (distributionFourier u) (derivativeMultiplierCLM _ φ) = _
  rw [he, map_smul]
  simp only [smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hc, one_mul,
    ContinuousLinearMap.comp_apply]

/-- A finite word of actual physical coordinate derivatives. -/
def coordinateWordDerivative : List (Fin d) → TemperedDistribution d → TemperedDistribution d
  | [], u => u
  | j :: w, u => normalizedCoordinateDerivative j (coordinateWordDerivative w u)

/-- The matching finite composition of actual coordinate multipliers. -/
def coordinateWordTestCLM : List (Fin d) → 𝓢(Euclidean d, ℂ) →L[ℂ] 𝓢(Euclidean d, ℂ)
  | [] => ContinuousLinearMap.id ℂ _
  | j :: w => (coordinateWordTestCLM w).comp (coordinateTestCLM j)

theorem coordinateWordTestCLM_apply (w : List (Fin d)) (φ : 𝓢(Euclidean d, ℂ)) (x : Euclidean d) :
    coordinateWordTestCLM w φ x = φ x * (w.map (fun j => (x j : ℂ))).prod := by
  induction w generalizing φ with
  | nil => simp [coordinateWordTestCLM]
  | cons j w ih =>
    simp only [coordinateWordTestCLM, ContinuousLinearMap.comp_apply, ih,
      coordinateTestCLM_apply, List.map_cons, List.prod_cons]
    ring

theorem distributionFourier_coordinateWordDerivative (w : List (Fin d)) (u : TemperedDistribution d) :
    distributionFourier (coordinateWordDerivative w u) =
      (distributionFourier u).comp (coordinateWordTestCLM w) := by
  induction w with
  | nil => ext φ; rfl
  | cons j w ih =>
    rw [coordinateWordDerivative, distributionFourier_normalizedCoordinateDerivative, ih]
    ext φ
    rfl

theorem DistributionSupportedIn.coordinateWordDerivative {u : TemperedDistribution d}
    {S : Set (Euclidean d)} (hu : DistributionSupportedIn u S) (w : List (Fin d)) :
    DistributionSupportedIn (coordinateWordDerivative w u) S := by
  induction w with
  | nil => exact hu
  | cons j w ih =>
    exact (ih.derivative _).smul _


/-- A monomial's exponents encoded as a finite coordinate word. -/
def polynomialMonomialWord (a : Fin d →₀ ℕ) : List (Fin d) :=
  (List.ofFn (fun j : Fin d => List.replicate (a j) j)).flatten

theorem polynomialMonomialWord_eval (a : Fin d →₀ ℕ) (x : Euclidean d) :
    ((polynomialMonomialWord a).map (fun j => (x j : ℂ))).prod =
      ∏ j : Fin d, (x j : ℂ) ^ a j := by
  simp [polynomialMonomialWord, List.map_flatten, List.prod_flatten, List.map_map,
    List.map_ofFn, List.prod_ofFn]

/-- The coefficient sum of actual finite physical derivative words representing
an arbitrary complex polynomial Fourier multiplier. -/
def polynomialDifferentialOperator (p : ComplexPolynomial d) (u : TemperedDistribution d) :
    TemperedDistribution d :=
  p.sum (fun a c => c • coordinateWordDerivative (polynomialMonomialWord a) u)

/-- The matching Schwartz multiplier, assembled from finite coordinate products. -/
def polynomialTestCLM (p : ComplexPolynomial d) :
    𝓢(Euclidean d, ℂ) →L[ℂ] 𝓢(Euclidean d, ℂ) :=
  p.sum (fun a c => c • coordinateWordTestCLM (polynomialMonomialWord a))

/-- This finite operator acts by actual pointwise polynomial multiplication. -/
theorem polynomialTestCLM_apply (p : ComplexPolynomial d)
    (φ : 𝓢(Euclidean d, ℂ)) (x : Euclidean d) :
    polynomialTestCLM p φ x = φ x * polynomialEvaluation x p := by
  classical
  change distributionDelta x (polynomialTestCLM p φ) = _
  simp only [polynomialTestCLM, MvPolynomial.sum_def,
    ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply, map_sum, map_smul,
    distributionDelta_apply, smul_eq_mul, coordinateWordTestCLM_apply,
    polynomialMonomialWord_eval, polynomialEvaluation_apply, MvPolynomial.eval_eq',
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  ring

/-- Polynomial Fourier multiplication is exactly the transform of the finite
constant-coefficient physical differential operator above. -/
theorem distributionFourier_polynomialDifferentialOperator (p : ComplexPolynomial d)
    (u : TemperedDistribution d) :
    distributionFourier (polynomialDifferentialOperator p u) =
      (distributionFourier u).comp (polynomialTestCLM p) := by
  classical
  ext φ
  simp only [polynomialDifferentialOperator, polynomialTestCLM, MvPolynomial.sum_def,
    distributionFourier_apply, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
    smul_eq_mul, ContinuousLinearMap.comp_apply, map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro a _
  change _ * distributionFourier (coordinateWordDerivative (polynomialMonomialWord a) u) φ = _
  rw [distributionFourier_coordinateWordDerivative]
  rfl

/-- The operator multiplies an actual Fourier integral representation by its polynomial. -/
theorem distributionFourier_polynomialDifferentialOperator_integral
    (p : ComplexPolynomial d) (u : TemperedDistribution d) (F : Euclidean d → ℂ)
    (hF : ∀ φ : 𝓢(Euclidean d, ℂ), distributionFourier u φ = ∫ x, F x * φ x)
    (φ : 𝓢(Euclidean d, ℂ)) :
    distributionFourier (polynomialDifferentialOperator p u) φ =
      ∫ x, polynomialEvaluation x p * F x * φ x := by
  rw [distributionFourier_polynomialDifferentialOperator, ContinuousLinearMap.comp_apply, hF]
  apply integral_congr_ae
  filter_upwards with x
  rw [polynomialTestCLM_apply]
  ring

/-- The actual Fourier integral of an integrable L² function represents its
transformed tempered distribution. -/
theorem distributionFourier_l2_integral (f : FullL2 d)
    (hf : Integrable (f : Euclidean d → ℂ)) (φ : 𝓢(Euclidean d, ℂ)) :
    distributionFourier (l2Distribution f) φ = ∫ x, 𝓕 (f : Euclidean d → ℂ) x * φ x := by
  rw [distributionFourier_apply, l2Distribution_apply]
  change (∫ x, f x * 𝓕 (φ : Euclidean d → ℂ) x) = _
  exact (integral_fourier_mul hf φ.integrable).symm

/-- A pointwise product of actual Fourier representatives gives the precise
Fourier product of distributions needed by the convolution support theorem. -/
theorem fourier_polynomial_product_of_integral_representatives
    (p : ComplexPolynomial d) (u v : TemperedDistribution d)
    (F G m : Euclidean d → ℂ) (hm : Function.HasTemperateGrowth m)
    (hF : ∀ φ : 𝓢(Euclidean d, ℂ), distributionFourier u φ = ∫ x, F x * φ x)
    (hG : ∀ φ : 𝓢(Euclidean d, ℂ), distributionFourier v φ = ∫ x, G x * φ x)
    (hproduct : ∀ x, polynomialEvaluation x p * F x = m x * G x) :
    distributionFourier (polynomialDifferentialOperator p u) =
      distributionMultiply m hm (distributionFourier v) := by
  ext φ
  rw [distributionFourier_polynomialDifferentialOperator_integral p u F hF,
    distributionMultiply_apply, hG]
  apply integral_congr_ae
  filter_upwards with x
  rw [hproduct, schwartzMultiplierCLM_apply]
  ring


/-- Every finite constant-coefficient differential operator preserves physical support. -/
theorem DistributionSupportedIn.polynomialDifferentialOperator {u : TemperedDistribution d}
    {S : Set (Euclidean d)} (hu : DistributionSupportedIn u S) (p : ComplexPolynomial d) :
    DistributionSupportedIn (polynomialDifferentialOperator p u) S := by
  classical
  intro φ hφ hdisj
  simp only [RieszEuclidean.CompleteMinimal.polynomialDifferentialOperator, MvPolynomial.sum_def,
    ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  apply Finset.sum_eq_zero
  intro a _
  rw [hu.coordinateWordDerivative (polynomialMonomialWord a) φ hφ hdisj, mul_zero]


end RieszEuclidean.CompleteMinimal
