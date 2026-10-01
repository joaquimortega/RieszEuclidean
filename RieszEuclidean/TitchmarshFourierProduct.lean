import RieszEuclidean.CompleteMinimalEntireFourier
import Mathlib.Analysis.Convolution

/-! Fourier transforms turn the actual Lebesgue convolution into products. -/

noncomputable section

open MeasureTheory
open scoped Convolution

namespace RieszEuclidean.CompleteMinimal

theorem complexFourierKernel_add {d : ℕ} (x y : Euclidean d)
    (z : ComplexEuclidean d) :
    complexFourierKernel (x + y) z =
      complexFourierKernel x z * complexFourierKernel y z := by
  have hp : complexPairing (x + y) z = complexPairing x z + complexPairing y z := by
    simp [complexPairing, add_mul, Finset.sum_add_distrib]
  simp [complexFourierKernel, fourierPhaseCLM, complexPairingCLM_apply,
    hp, Complex.exp_add, mul_add, mul_assoc]

theorem complexFourierKernel_neg {d : ℕ} (x : Euclidean d)
    (z : ComplexEuclidean d) :
    complexFourierKernel (-x) z = (complexFourierKernel x z)⁻¹ := by
  have hp : complexPairing (-x) z = -complexPairing x z := by
    simp [complexPairing]
  simp [complexFourierKernel, fourierPhaseCLM, complexPairingCLM_apply,
    hp, Complex.exp_neg]

theorem complexFourierKernel_sub {d : ℕ} (x y : Euclidean d)
    (z : ComplexEuclidean d) :
    complexFourierKernel (x - y) z =
      complexFourierKernel x z / complexFourierKernel y z := by
  rw [sub_eq_add_neg, complexFourierKernel_add, complexFourierKernel_neg,
    div_eq_mul_inv]

theorem complexFourierKernel_eq_exp_pairing {d : ℕ} (x : Euclidean d)
    (z : ComplexEuclidean d) :
    complexFourierKernel x z =
      Complex.exp ((-2 * (Real.pi : ℂ) * Complex.I) * complexPairing x z) := by
  simp [complexFourierKernel, fourierPhaseCLM, complexPairingCLM_apply,
    smul_eq_mul, mul_assoc]

/-- Convolution commutes with twisting both inputs by the same Fourier
character, with the output twisted by that character. -/
theorem convolution_complexFourierKernel_twist {d : ℕ}
    (f g : Euclidean d → ℂ) (z : ComplexEuclidean d) :
    ((fun x => f x * complexFourierKernel x z) ⋆[ContinuousLinearMap.mul ℂ ℂ, volume]
        (fun x => g x * complexFourierKernel x z)) =
      fun x => (f ⋆[ContinuousLinearMap.mul ℂ ℂ, volume] g) x *
        complexFourierKernel x z := by
  funext x
  rw [MeasureTheory.convolution_def, MeasureTheory.convolution_def]
  rw [← integral_mul_const]
  apply integral_congr_ae
  filter_upwards [] with y
  calc
    f y * complexFourierKernel y z *
        (g (x - y) * complexFourierKernel (x - y) z) =
        (f y * g (x - y)) *
          (complexFourierKernel y z * complexFourierKernel (x - y) z) := by ring
    _ = (f y * g (x - y)) * complexFourierKernel x z := by
      rw [← complexFourierKernel_add y (x - y) z]
      congr 2
      abel

/-- The complex Fourier transform of Lebesgue convolution is the product of
the two transforms. The support assumptions state bounded support by balls. -/
theorem entireFourier_convolution {d : ℕ} {f g : Euclidean d → ℂ}
    (hf : Integrable f) (hg : Integrable g)
    {R S : ℝ} (hfs : ∀ᵐ x, f x ≠ 0 → ‖x‖ ≤ R)
    (hgs : ∀ᵐ x, g x ≠ 0 → ‖x‖ ≤ S) (z : ComplexEuclidean d) :
    entireFourier (f ⋆[ContinuousLinearMap.mul ℂ ℂ, volume] g) z =
      entireFourier f z * entireFourier g z := by
  let F : Euclidean d → ℂ := fun x => f x * complexFourierKernel x z
  let G : Euclidean d → ℂ := fun x => g x * complexFourierKernel x z
  have hF : Integrable F := entireFourier_integrable hf hfs z
  have hG : Integrable G := entireFourier_integrable hg hgs z
  have htwist := convolution_complexFourierKernel_twist f g z
  have hpoint (x : Euclidean d) :
      (F ⋆[ContinuousLinearMap.mul ℂ ℂ, volume] G) x =
        ((f ⋆[ContinuousLinearMap.mul ℂ ℂ, volume] g) x) *
          complexFourierKernel x z := by
    simpa [F, G] using congrFun htwist x
  have hprod := MeasureTheory.integral_convolution
    (L := ContinuousLinearMap.mul ℂ ℂ) hF hG
  calc
    entireFourier (f ⋆[ContinuousLinearMap.mul ℂ ℂ, volume] g) z
        = ∫ x, ((f ⋆[ContinuousLinearMap.mul ℂ ℂ, volume] g) x) *
            complexFourierKernel x z := rfl
    _ = ∫ x, (F ⋆[ContinuousLinearMap.mul ℂ ℂ, volume] G) x := by
      apply integral_congr_ae
      filter_upwards [] with x
      exact (hpoint x).symm
    _ = (∫ x, F x) * ∫ x, G x := hprod
    _ = entireFourier f z * entireFourier g z := rfl

/-- Moving the complex frequency in the direction `v` encodes the directional
Laplace exponential as a Fourier kernel factor. -/
theorem complexFourierKernel_laplace_shift {d : ℕ} (x v ξ : Euclidean d)
    (T : ℝ) (z : ℂ) :
    Complex.exp (z * ((T - inner (𝕜 := ℝ) v x : ℝ) : ℂ)) *
        complexFourierKernel x (realToComplex ξ) =
      Complex.exp (z * (T : ℂ)) *
        complexFourierKernel x
          (realToComplex ξ + (-(z * Complex.I) / (2 * Real.pi)) • realToComplex v) := by
  let η : ComplexEuclidean d :=
    realToComplex ξ + (-(z * Complex.I) / (2 * Real.pi)) • realToComplex v
  have hp : complexPairing x η =
      (inner (𝕜 := ℝ) x ξ : ℂ) +
        (-(z * Complex.I) / (2 * Real.pi)) *
          (inner (𝕜 := ℝ) x v : ℂ) := by
    calc
      complexPairing x η = complexPairingCLM x η :=
        (complexPairingCLM_apply x η).symm
      _ = complexPairingCLM x (realToComplex ξ) +
          (-(z * Complex.I) / (2 * Real.pi)) *
            complexPairingCLM x (realToComplex v) := by
        change complexPairingCLM x (realToComplex ξ +
          (-(z * Complex.I) / (2 * Real.pi)) • realToComplex v) = _
        rw [ContinuousLinearMap.map_add, ContinuousLinearMap.map_smul]
        simp only [smul_eq_mul]
      _ = _ := by simp [complexPairingCLM_apply, complexPairing_realToComplex]
  rw [complexFourierKernel_realToComplex, complexFourierKernel_eq_exp_pairing]
  rw [← Complex.exp_add, ← Complex.exp_add]
  congr 1
  simp only [η] at hp
  rw [hp]
  push_cast
  have hvx : inner (𝕜 := ℝ) x v = inner (𝕜 := ℝ) v x := real_inner_comm v x
  rw [hvx]
  field_simp [Real.pi_ne_zero]
  ring_nf
  rw [Complex.I_sq]
  ring

/-- The directional Laplace integral is a shifted entire Fourier transform,
including the scalar exponential contributed by the support boundary. -/
theorem integral_directionalLaplace_eq_entireFourier_shift {d : ℕ}
    (f : Euclidean d → ℂ) (v ξ : Euclidean d) (T : ℝ) (z : ℂ) :
    (∫ x, f x * Complex.exp (z * ((T - inner (𝕜 := ℝ) v x : ℝ) : ℂ)) *
        complexFourierKernel x (realToComplex ξ)) =
      Complex.exp (z * (T : ℂ)) *
        entireFourier f
          (realToComplex ξ + (-(z * Complex.I) / (2 * Real.pi)) • realToComplex v) := by
  unfold entireFourier
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with x
  calc
    f x * Complex.exp (z * ((T - inner (𝕜 := ℝ) v x : ℝ) : ℂ)) *
        complexFourierKernel x (realToComplex ξ) =
        f x * (Complex.exp (z * ((T - inner (𝕜 := ℝ) v x : ℝ) : ℂ)) *
          complexFourierKernel x (realToComplex ξ)) := by ring
    _ = f x * (Complex.exp (z * (T : ℂ)) *
        complexFourierKernel x
          (realToComplex ξ + (-(z * Complex.I) / (2 * Real.pi)) • realToComplex v)) := by
      rw [complexFourierKernel_laplace_shift x v ξ T z]
    _ = Complex.exp (z * (T : ℂ)) *
        (f x * complexFourierKernel x
          (realToComplex ξ + (-(z * Complex.I) / (2 * Real.pi)) • realToComplex v)) := by ring

end RieszEuclidean.CompleteMinimal
