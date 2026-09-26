import RieszEuclidean.CompleteMinimalPointSupport
import RieszEuclidean.CompleteMinimalPolynomial
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Topology.Algebra.MvPolynomial

/-!
# Fourier transforms of point-supported distributions

Actual coordinate jets at the origin transform into regular distributions given
by complex multivariate monomials. The point-support classification therefore
supplies a genuine polynomial Fourier transform.
-/

noncomputable section
open MeasureTheory SchwartzMap
open scoped SchwartzMap FourierTransform

namespace RieszEuclidean.CompleteMinimal

variable {d N : ℕ}

/-- The polynomial corresponding to a coordinate jet under negative Fourier transposition. -/
def pointJetPolynomial (i : PointJetIndex d N) : ComplexPolynomial d :=
  MvPolynomial.C (-(2 * Real.pi * Complex.I)) ^ i.1.val *
    ∏ j, MvPolynomial.X (i.2 j)

/-- A jet of order `n` gives a polynomial of total degree at most `n`. -/
theorem pointJetPolynomial_totalDegree_le (i : PointJetIndex d N) :
    (pointJetPolynomial i).totalDegree ≤ i.1.val := by
  unfold pointJetPolynomial
  rw [← MvPolynomial.C_pow]
  apply (MvPolynomial.totalDegree_mul _ _).trans
  simp only [MvPolynomial.totalDegree_C, zero_add]
  simpa only [MvPolynomial.totalDegree_X, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, smul_eq_mul, mul_one] using
    MvPolynomial.totalDegree_finset_prod Finset.univ
      (fun j => (MvPolynomial.X (i.2 j) : ComplexPolynomial d))

/-- The value of a jet polynomial at a real frequency. -/
theorem pointJetPolynomial_eval (i : PointJetIndex d N) (x : Euclidean d) :
    polynomialEvaluation x (pointJetPolynomial i) =
      (-(2 * Real.pi * Complex.I)) ^ i.1.val * ∏ j, (x (i.2 j) : ℂ) := by
  simp [polynomialEvaluation_apply, pointJetPolynomial, MvPolynomial.eval_prod]

/-- The coordinate directions in the jet recover the corresponding coordinates in the phase. -/
theorem pointJetDirections_inner (i : PointJetIndex d N) (x : Euclidean d) (j : Fin i.1.val) :
    (innerSL ℝ x) (pointJetDirections i j) = x (i.2 j) := by
  rw [innerSL_apply, pointJetDirections, EuclideanSpace.basisFun_apply,
    EuclideanSpace.inner_single_right]
  simp

/-- Every jet monomial has an explicit polynomial growth bound. -/
theorem pointJetPolynomial_norm_le (i : PointJetIndex d N) (x : Euclidean d) :
    ‖polynomialEvaluation x (pointJetPolynomial i)‖ ≤
      (2 * Real.pi) ^ i.1.val * (1 + ‖x‖) ^ N := by
  rw [pointJetPolynomial_eval, norm_mul, norm_pow, norm_neg]
  have hconst : ‖(2 * Real.pi * Complex.I : ℂ)‖ = 2 * Real.pi := by
    rw [norm_mul, Complex.norm_I, mul_one]
    norm_cast
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  rw [hconst, norm_prod]
  have hprod : (∏ j : Fin i.1.val, ‖(x (i.2 j) : ℂ)‖) ≤ (1 + ‖x‖) ^ i.1.val := by
    calc
      _ ≤ ∏ _j : Fin i.1.val, (1 + ‖x‖) := by
        apply Finset.prod_le_prod (fun _ _ => norm_nonneg _)
        intro j _
        simpa only [Complex.norm_real] using (PiLp.norm_apply_le x (i.2 j)).trans
          (by linarith [norm_nonneg x])
      _ = _ := by simp
  exact mul_le_mul_of_nonneg_left
    (hprod.trans (pow_le_pow_right₀ (by linarith [norm_nonneg x]) (by omega))) (by positivity)

/-- Evaluation of an actual Fourier-transformed jet is the monomial integral. -/
theorem distributionFourier_pointJet_apply (i : PointJetIndex d N)
    (φ : 𝓢(Euclidean d, ℂ)) :
    distributionFourier (pointJetDistribution N i) φ =
      ∫ x, polynomialEvaluation x (pointJetPolynomial i) * φ x := by
  rw [distributionFourier_apply, pointJetDistribution_apply]
  change iteratedFDeriv ℝ i.1.val (𝓕 (φ : Euclidean d → ℂ)) 0 (pointJetDirections i) = _
  rw [Real.iteratedFDeriv_fourierIntegral (N := ⊤)
    (fun k _ => φ.integrable_pow_mul volume k) φ.continuous.aestronglyMeasurable (by simp),
    Real.fourierIntegral_continuousMultilinearMap_apply
      (VectorFourier.integrable_fourierPowSMulRight (innerSL ℝ)
        (φ.integrable_pow_mul volume i.1.val) φ.continuous.aestronglyMeasurable),
    Real.fourierIntegral_eq]
  apply integral_congr_ae
  filter_upwards with x
  simp only [inner_zero_right, neg_zero, VectorFourier.fourierPowSMulRight_apply,
    pointJetPolynomial_eval]
  simp_rw [pointJetDirections_inner (N := N) i]
  simp [Circle.smul_def, Complex.real_smul, Complex.ofReal_prod, mul_assoc]

/-- The Fourier transform of a coordinate jet is the regular monomial distribution. -/
theorem distributionFourier_pointJet (i : PointJetIndex d N) :
    distributionFourier (pointJetDistribution N i) =
      polynomialDistribution (fun x => polynomialEvaluation x (pointJetPolynomial i))
        (by positivity : 0 ≤ (2 * Real.pi) ^ i.1.val)
        (pointJetPolynomial_norm_le i)
        (((MvPolynomial.continuous_eval (pointJetPolynomial i)).comp
          (continuous_pi (fun j => Complex.continuous_ofReal.comp (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin d => ℝ) j).continuous))).aestronglyMeasurable) := by
  ext φ
  exact distributionFourier_pointJet_apply i φ

/-- The finite polynomial supplied by the coordinate-jet classification. -/
def pointSupportedFourierPolynomial (c : PointJetIndex d N → ℂ) : ComplexPolynomial d :=
  ∑ i, MvPolynomial.C (c i) * pointJetPolynomial i

/-- The polynomial supplied by jets through order `N` has total degree at most `N`. -/
theorem pointSupportedFourierPolynomial_totalDegree_le (c : PointJetIndex d N → ℂ) :
    (pointSupportedFourierPolynomial c).totalDegree ≤ N := by
  apply MvPolynomial.totalDegree_finsetSum_le
  intro i _
  apply (MvPolynomial.totalDegree_mul _ _).trans
  simp only [MvPolynomial.totalDegree_C, zero_add]
  exact (pointJetPolynomial_totalDegree_le i).trans (by omega)

/-- An explicit nonnegative bound for the finite jet polynomial. -/
def pointSupportedFourierBound (c : PointJetIndex d N → ℂ) : ℝ :=
  ∑ i, ‖c i‖ * (2 * Real.pi) ^ i.1.val

/-- Evaluation commutes with the finite jet polynomial sum. -/
theorem pointSupportedFourierPolynomial_eval (c : PointJetIndex d N → ℂ) (x : Euclidean d) :
    polynomialEvaluation x (pointSupportedFourierPolynomial c) =
      ∑ i, c i * polynomialEvaluation x (pointJetPolynomial i) := by
  simp [polynomialEvaluation_apply, pointSupportedFourierPolynomial]

/-- The finite jet polynomial obeys a genuine degree-`N` growth bound. -/
theorem pointSupportedFourierPolynomial_norm_le (c : PointJetIndex d N → ℂ) (x : Euclidean d) :
    ‖polynomialEvaluation x (pointSupportedFourierPolynomial c)‖ ≤
      pointSupportedFourierBound c * (1 + ‖x‖) ^ N := by
  rw [pointSupportedFourierPolynomial_eval, pointSupportedFourierBound, Finset.sum_mul]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro i _
  rw [norm_mul, mul_assoc]
  exact mul_le_mul_of_nonneg_left (pointJetPolynomial_norm_le i x) (norm_nonneg _)

/-- An actual point-supported distribution has a polynomial Fourier transform,
expressed by its regular distribution and by its integral on every Schwartz test. -/
theorem DistributionSupportedIn.fourier_polynomial {u : TemperedDistribution d}
    (hu : DistributionSupportedIn u {(0 : Euclidean d)}) :
    ∃ p : ComplexPolynomial d, ∃ N : ℕ, ∃ C : ℝ, ∃ hC : 0 ≤ C,
      ∃ hp : ∀ x, ‖polynomialEvaluation x p‖ ≤ C * (1 + ‖x‖) ^ N,
      ∃ hm : AEStronglyMeasurable (fun x => polynomialEvaluation x p) volume,
      distributionFourier u = polynomialDistribution (fun x => polynomialEvaluation x p) hC hp hm := by
  classical
  obtain ⟨N, c, rfl⟩ := hu.eq_sum_pointJets
  let p := pointSupportedFourierPolynomial c
  have hC : 0 ≤ pointSupportedFourierBound c := by
    exact Finset.sum_nonneg fun _ _ => mul_nonneg (norm_nonneg _) (by positivity)
  have hm : AEStronglyMeasurable (fun x => polynomialEvaluation x p) volume :=
    ((MvPolynomial.continuous_eval p).comp
      (continuous_pi (fun j => Complex.continuous_ofReal.comp (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin d => ℝ) j).continuous))).aestronglyMeasurable
  refine ⟨p, N, pointSupportedFourierBound c, hC,
    pointSupportedFourierPolynomial_norm_le c, hm, ?_⟩
  ext φ
  simp only [distributionFourier_apply, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul, polynomialDistribution_apply]
  change (∑ i, c i * distributionFourier (pointJetDistribution N i) φ) = _
  simp_rw [distributionFourier_pointJet_apply, ← integral_const_mul]
  rw [← integral_finset_sum]
  · apply integral_congr_ae
    filter_upwards with x
    rw [pointSupportedFourierPolynomial_eval, Finset.sum_mul]
    simp only [mul_assoc]
  · intro i _
    exact (polynomial_schwartz_integrable (by positivity : 0 ≤ (2 * Real.pi) ^ i.1.val)
      (pointJetPolynomial_norm_le i)
      (((MvPolynomial.continuous_eval (pointJetPolynomial i)).comp
        (continuous_pi (fun j => Complex.continuous_ofReal.comp (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin d => ℝ) j).continuous))).aestronglyMeasurable) φ).const_mul (c i)

/-- Point support gives an actual polynomial integral on the Fourier side, with
the degree bound of the finite-order classification. -/
theorem DistributionSupportedIn.fourier_polynomial_integral {u : TemperedDistribution d}
    (hu : DistributionSupportedIn u {(0 : Euclidean d)}) :
    ∃ N : ℕ, ∃ p : ComplexPolynomial d, p.totalDegree ≤ N ∧
      ∀ φ : 𝓢(Euclidean d, ℂ), distributionFourier u φ =
        ∫ x, polynomialEvaluation x p * φ x := by
  classical
  obtain ⟨N, c, hc⟩ := hu.eq_sum_pointJets
  refine ⟨N, pointSupportedFourierPolynomial c,
    pointSupportedFourierPolynomial_totalDegree_le c, ?_⟩
  intro φ
  rw [hc]
  simp only [distributionFourier_apply, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul]
  change (∑ i, c i * distributionFourier (pointJetDistribution N i) φ) = _
  simp_rw [distributionFourier_pointJet_apply, ← integral_const_mul]
  rw [← integral_finset_sum]
  · apply integral_congr_ae
    filter_upwards with x
    rw [pointSupportedFourierPolynomial_eval, Finset.sum_mul]
    simp only [mul_assoc]
  · intro i _
    exact (polynomial_schwartz_integrable (by positivity : 0 ≤ (2 * Real.pi) ^ i.1.val)
      (pointJetPolynomial_norm_le i)
      (((MvPolynomial.continuous_eval (pointJetPolynomial i)).comp
        (continuous_pi (fun j => Complex.continuous_ofReal.comp
          (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin d => ℝ) j).continuous))).aestronglyMeasurable)
      φ).const_mul (c i)

end RieszEuclidean.CompleteMinimal
