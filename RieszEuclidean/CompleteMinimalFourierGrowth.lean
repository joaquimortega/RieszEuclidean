import RieszEuclidean.CompleteMinimalBessel
import RieszEuclidean.CompleteMinimalQuotientType
import RieszEuclidean.CompleteMinimalPolynomial

/-! # Exponential growth of the actual Fourier quotients' factors -/

noncomputable section

open MeasureTheory

namespace RieszEuclidean.CompleteMinimal

variable {E : Type*} [NormedAddCommGroup E]

/-- Constant functions have finite exponential type. -/
theorem finiteExponentialType_const (c : ℂ) :
    FiniteExponentialType (fun _ : E => c) := by
  apply finiteExponentialType_of_nonnegative_bound (norm_nonneg c) (le_refl (0 : ℝ))
  intro z
  simp

/-- Sums preserve a global finite exponential growth bound. -/
theorem FiniteExponentialType.add {f g : E → ℂ}
    (hf : FiniteExponentialType f) (hg : FiniteExponentialType g) :
    FiniteExponentialType (fun z => f z + g z) := by
  obtain ⟨C, R, hC, hR, hfb⟩ := hf
  obtain ⟨D, S, hD, hS, hgb⟩ := hg
  refine ⟨C + D, max R S, add_pos hC hD, hR.trans (le_max_left _ _), ?_⟩
  intro z
  calc
    ‖f z + g z‖ ≤ ‖f z‖ + ‖g z‖ := norm_add_le _ _
    _ ≤ C * Real.exp (R * ‖z‖) + D * Real.exp (S * ‖z‖) := add_le_add (hfb z) (hgb z)
    _ ≤ C * Real.exp (max R S * ‖z‖) + D * Real.exp (max R S * ‖z‖) := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
          (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))) hC.le
      · exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
          (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _))) hD.le
    _ = (C + D) * Real.exp (max R S * ‖z‖) := by ring

/-- Every complex coordinate is dominated by a global exponential bound. -/
theorem finiteExponentialType_coordinate {d : ℕ} (i : Fin d) :
    FiniteExponentialType (fun z : ComplexEuclidean d => z i) := by
  refine ⟨1, 1, zero_lt_one, zero_le_one, ?_⟩
  intro z
  simp only [one_mul]
  exact (PiLp.norm_apply_le z i).trans
    ((le_add_of_nonneg_right zero_le_one).trans (Real.add_one_le_exp ‖z‖))

/-- Evaluation of a complex multivariate polynomial has finite exponential type. -/
theorem finiteExponentialType_polynomial {d : ℕ} (p : ComplexPolynomial d) :
    FiniteExponentialType (fun z : ComplexEuclidean d => MvPolynomial.eval (fun i => z i) p) := by
  induction p using MvPolynomial.induction_on with
  | C c => simpa using (finiteExponentialType_const (E := ComplexEuclidean d) c)
  | add p q hp hq => simpa only [map_add] using hp.add hq
  | mul_X p i hp =>
    simpa only [map_mul, MvPolynomial.eval_X] using
      hp.mul (finiteExponentialType_coordinate i)

/-- The normalized indicator of the unit ball has an actual entire transform of finite type. -/
theorem finiteExponentialType_normalizedBallFourier (d : ℕ) :
    FiniteExponentialType (normalizedBallFourier d) := by
  have h : FiniteExponentialType (entireFourier (ballIndicator d)) :=
    finiteExponentialType_of_nonnegative_bound (integral_nonneg (fun x => norm_nonneg _))
      (by positivity) (entireFourier_norm_le (ballIndicator_integrable d)
        (ballIndicator_support_bound d))
  exact h.div_const (Complex.ofReal_ne_zero.mpr (ballVolume_pos d).ne')

/-- Polynomial multiples of bounded-domain Fourier transforms have finite type. -/
theorem finiteExponentialType_polynomial_mul_domainEntireFourier {d : ℕ}
    {Ω : Set (Euclidean d)} (hΩ : MeasurableSet Ω) (hbounded : Bornology.IsBounded Ω)
    (p : ComplexPolynomial d) (f : DomainL2 Ω) :
    FiniteExponentialType (fun z => MvPolynomial.eval (fun i => z i) p *
      domainEntireFourier Ω hΩ f z) :=
  (finiteExponentialType_polynomial p).mul
    (finiteExponentialType_domainEntireFourier hΩ hbounded f)

/-- Polynomial bounds for a function and its first complex derivative on the real locus. -/
def RealPolynomialFirstDerivativeBound {d : ℕ} (F : ComplexEuclidean d → ℂ) : Prop :=
  ∃ m : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x : Euclidean d,
    ‖F (realToComplex x)‖ ≤ C * (1 + ‖x‖) ^ m ∧
      ‖fderiv ℂ F (realToComplex x)‖ ≤ C * (1 + ‖x‖) ^ m

theorem norm_complex_smul_clm_le {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    (c : ℂ) (L : V →L[ℂ] ℂ) : ‖c • L‖ ≤ ‖c‖ * ‖L‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  intro v
  change ‖c * L v‖ ≤ _
  rw [norm_mul, mul_assoc]
  exact mul_le_mul_of_nonneg_left (L.le_opNorm v) (norm_nonneg _)

theorem RealPolynomialFirstDerivativeBound.add {d : ℕ} {F G : ComplexEuclidean d → ℂ}
    (hF : Differentiable ℂ F) (hG : Differentiable ℂ G)
    (hf : RealPolynomialFirstDerivativeBound F) (hg : RealPolynomialFirstDerivativeBound G) :
    RealPolynomialFirstDerivativeBound (fun z => F z + G z) := by
  obtain ⟨m, C, hC, hf⟩ := hf
  obtain ⟨n, D, hD, hg⟩ := hg
  refine ⟨m + n, C + D, add_nonneg hC hD, fun x => ?_⟩
  have hr : 1 ≤ 1 + ‖x‖ := le_add_of_nonneg_right (norm_nonneg _)
  have hm : C * (1 + ‖x‖) ^ m ≤ C * (1 + ‖x‖) ^ (m + n) :=
    mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hr (Nat.le_add_right _ _)) hC
  have hn : D * (1 + ‖x‖) ^ n ≤ D * (1 + ‖x‖) ^ (m + n) :=
    mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hr (Nat.le_add_left _ _)) hD
  constructor
  · exact (norm_add_le _ _).trans ((add_le_add ((hf x).1.trans hm) ((hg x).1.trans hn)).trans_eq
      (add_mul C D _).symm)
  · rw [fderiv_add (hF _) (hG _)]
    exact (norm_add_le _ _).trans ((add_le_add ((hf x).2.trans hm) ((hg x).2.trans hn)).trans_eq
      (add_mul C D _).symm)

theorem RealPolynomialFirstDerivativeBound.mul {d : ℕ} {F G : ComplexEuclidean d → ℂ}
    (hF : Differentiable ℂ F) (hG : Differentiable ℂ G)
    (hf : RealPolynomialFirstDerivativeBound F) (hg : RealPolynomialFirstDerivativeBound G) :
    RealPolynomialFirstDerivativeBound (fun z => F z * G z) := by
  obtain ⟨m, C, hC, hf⟩ := hf
  obtain ⟨n, D, hD, hg⟩ := hg
  refine ⟨m + n, 2 * C * D, by positivity, fun x => ?_⟩
  have hfm := hf x
  have hgm := hg x
  have hprod : (C * (1 + ‖x‖) ^ m) * (D * (1 + ‖x‖) ^ n) =
      C * D * (1 + ‖x‖) ^ (m + n) := by rw [pow_add]; ring
  constructor
  · rw [norm_mul]
    apply (mul_le_mul hfm.1 hgm.1 (norm_nonneg _) (by positivity)).trans
    rw [hprod]
    nlinarith [mul_nonneg (mul_nonneg hC hD) (pow_nonneg (by positivity : 0 ≤ 1 + ‖x‖) (m+n))]
  · rw [fderiv_mul (hF _) (hG _)]
    apply (norm_add_le _ _).trans
    have h₁ := mul_le_mul hfm.1 hgm.2 (norm_nonneg _) (by positivity)
    have h₂ := mul_le_mul hgm.1 hfm.2 (norm_nonneg _) (by positivity)
    rw [hprod] at h₁
    have hprod' : (D * (1 + ‖x‖) ^ n) * (C * (1 + ‖x‖) ^ m) =
        C * D * (1 + ‖x‖) ^ (m + n) := by rw [mul_comm, hprod]
    rw [hprod'] at h₂
    exact ((add_le_add (norm_complex_smul_clm_le _ _) (norm_complex_smul_clm_le _ _)).trans
      (add_le_add h₁ h₂)).trans_eq (by ring)

/-- Complex polynomial evaluation and its derivative have polynomial real-axis bounds. -/
theorem polynomial_differentiable_and_real_derivative_bound {d : ℕ} (p : ComplexPolynomial d) :
    Differentiable ℂ (fun z : ComplexEuclidean d => MvPolynomial.eval (fun i => z i) p) ∧
      RealPolynomialFirstDerivativeBound
        (fun z : ComplexEuclidean d => MvPolynomial.eval (fun i => z i) p) := by
  induction p using MvPolynomial.induction_on with
  | C c =>
    simp only [MvPolynomial.eval_C]
    refine ⟨differentiable_const _, 0, ‖c‖, norm_nonneg _, fun x => ?_⟩
    simp
  | add p q hp hq =>
    simp only [map_add]
    exact ⟨hp.1.add hq.1, hp.2.add hp.1 hq.1 hq.2⟩
  | mul_X p i hp =>
    simp only [map_mul, MvPolynomial.eval_X]
    let L : ComplexEuclidean d →L[ℂ] ℂ := PiLp.proj 2 (fun _ : Fin d => ℂ) i
    have hL : Differentiable ℂ (fun z : ComplexEuclidean d => z i) := L.differentiable
    have hLb : RealPolynomialFirstDerivativeBound (fun z : ComplexEuclidean d => z i) := by
      refine ⟨1, 1, zero_le_one, fun x => ?_⟩
      simp only [one_mul, pow_one]
      constructor
      · exact (PiLp.norm_apply_le (realToComplex x) i).trans
          (by rw [realToComplex_norm]; exact le_add_of_nonneg_left zero_le_one)
      · change ‖fderiv ℂ L (realToComplex x)‖ ≤ _
        rw [L.fderiv]
        apply (ContinuousLinearMap.opNorm_le_bound L zero_le_one (fun z => ?_)).trans
          (le_add_of_nonneg_right (norm_nonneg _) : (1 : ℝ) ≤ 1 + ‖x‖)
        simpa only [one_mul] using PiLp.norm_apply_le z i
    exact ⟨hp.1.mul hL, hp.2.mul hp.1 hL hLb⟩

/-- Both a polynomial Fourier numerator and its derivative grow polynomially on real frequencies. -/
theorem polynomial_mul_domainEntireFourier_real_derivative_bound {d : ℕ}
    {Ω : Set (Euclidean d)} (hΩ : MeasurableSet Ω) (hbounded : Bornology.IsBounded Ω)
    (p : ComplexPolynomial d) (f : DomainL2 Ω) :
    RealPolynomialFirstDerivativeBound (fun z => MvPolynomial.eval (fun i => z i) p *
      domainEntireFourier Ω hΩ f z) := by
  have hp := polynomial_differentiable_and_real_derivative_bound p
  have hf := domainEntireFourier_differentiable hΩ hbounded f
  obtain ⟨C, hC⟩ := domainEntireFourier_real_bounds hΩ hbounded f
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0).1
  apply hp.2.mul hp.1 hf
  refine ⟨0, C, hC0, fun x => ?_⟩
  simpa only [pow_zero, mul_one] using hC x

end RieszEuclidean.CompleteMinimal
