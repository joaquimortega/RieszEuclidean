import RieszEuclidean.CutoffProjection
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
open MeasureTheory
namespace RieszEuclidean
/-- Pairing an arbitrary L² function with a Schwartz test function. -/
theorem schwartz_L2_inner {d : ℕ} (g : SchwartzMap (Euclidean d) ℂ) (f : FullL2 d) :
    inner (𝕜 := ℂ) (g.toLp 2 volume) f = ∫ x, f x * starRingEnd ℂ (g x) := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [g.coeFn_toLp 2 volume] with x hx
  simp only [hx, RCLike.inner_apply, mul_comm]
/-- The extended transform satisfies the Fourier pairing identity against Schwartz tests. -/
theorem fourierL2_pairing {d : ℕ} (f : FullL2 d) (g : SchwartzMap (Euclidean d) ℂ) :
    (∫ x, fourierL2Equiv d f x * starRingEnd ℂ (g x)) =
      ∫ x, f x * starRingEnd ℂ (Real.fourierIntegralInv g x) := by
  have h := (fourierL2Equiv d).inner_map_map
    (((SchwartzMap.fourierTransformCLE ℂ).symm g).toLp 2 volume) f
  rw [fourierL2Equiv_schwartz, ContinuousLinearEquiv.apply_symm_apply,
    schwartz_L2_inner, schwartz_L2_inner] at h
  simpa only [SchwartzMap.fourierTransformCLE_symm_apply] using h
/-- The negative-sign unitary transform equals the integral for L¹∩L² inputs. -/
theorem fourierL2Equiv_eq_integral {d : ℕ} (f : FullL2 d)
    (hf : Integrable (f : Euclidean d → ℂ)) :
    (fourierL2Equiv d f : Euclidean d → ℂ) =ᵐ[volume] Real.fourierIntegral f := by
  have hcont : Continuous (Real.fourierIntegral (f : Euclidean d → ℂ)) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (continuous_fst.inner continuous_snd) hf
  apply ae_eq_of_integral_contDiff_smul_eq
    ((Lp.memLp (fourierL2Equiv d f)).locallyIntegrable (by norm_num)) hcont.locallyIntegrable
  intro g hg hgs
  let gC : SchwartzMap (Euclidean d) ℂ := compactSchwartz (fun x => (g x : ℂ))
    (Complex.ofRealCLM.contDiff.comp hg) (hgs.comp_left Complex.ofReal_zero)
  have h := (fourierL2_pairing f gC).trans (integral_fourier_mul_conj hf gC.integrable).symm
  change (∫ x, fourierL2Equiv d f x * starRingEnd ℂ (g x : ℂ)) =
    ∫ x, Real.fourierIntegral f x * starRingEnd ℂ (g x : ℂ) at h
  simpa only [Complex.conj_ofReal, Complex.real_smul, mul_comm] using h
/-- Conjugation exchanges inverse Fourier with forward Fourier. -/
theorem inverseFourier_conj {d : ℕ} (f : Euclidean d → ℂ) (x : Euclidean d) :
    Real.fourierIntegralInv (fun y => starRingEnd ℂ (f y)) x =
      starRingEnd ℂ (Real.fourierIntegral f x) := by
  rw [Real.fourierIntegralInv_eq, Real.fourierIntegral_eq, ← integral_conj]
  congr 1
  ext y
  simp [Circle.smul_def, map_mul]
/-- Transposition for the positive Fourier sign. -/
theorem integral_inverseFourier_mul {d : ℕ} {f g : Euclidean d → ℂ}
    (hf : Integrable f) (hg : Integrable g) :
    (∫ x, Real.fourierIntegralInv f x * g x) = ∫ x, f x * Real.fourierIntegralInv g x := by
  have h := VectorFourier.integral_fourierIntegral_smul_eq_flip
    (L := -innerₗ (Euclidean d)) Real.continuous_fourierChar
    (continuous_fst.inner continuous_snd).neg hf hg
  have hflip : (-innerₗ (Euclidean d)).flip = -innerₗ (Euclidean d) := by
    ext x y
    change -inner (𝕜 := ℝ) y x = -inner (𝕜 := ℝ) x y
    rw [real_inner_comm]
  simpa only [Real.fourierIntegralInv, smul_eq_mul, hflip] using h
/-- Conjugated pairing for the positive Fourier sign. -/
theorem integral_inverseFourier_mul_conj {d : ℕ} {f g : Euclidean d → ℂ}
    (hf : Integrable f) (hg : Integrable g) :
    (∫ x, Real.fourierIntegralInv f x * starRingEnd ℂ (g x)) =
      ∫ x, f x * starRingEnd ℂ (Real.fourierIntegral g x) := by
  have hg' : Integrable (fun x => starRingEnd ℂ (g x)) :=
    Complex.conjCLE.toContinuousLinearMap.integrable_comp hg
  simpa only [inverseFourier_conj] using integral_inverseFourier_mul hf hg'
/-- The positive-sign unitary satisfies the inverse pairing against Schwartz tests. -/
theorem paperFourierL2_pairing {d : ℕ} (f : FullL2 d) (g : SchwartzMap (Euclidean d) ℂ) :
    (∫ x, paperFourierL2 d f x * starRingEnd ℂ (g x)) =
      ∫ x, f x * starRingEnd ℂ (Real.fourierIntegral g x) := by
  have h := (paperFourierL2 d).inner_map_map
    ((SchwartzMap.fourierTransformCLE ℂ g).toLp 2 volume) f
  rw [paperFourierL2, fourierL2Equiv_symm_schwartz,
    ContinuousLinearEquiv.symm_apply_apply, schwartz_L2_inner, schwartz_L2_inner] at h
  simpa only [SchwartzMap.fourierTransformCLE_apply] using h
/-- The paper's positive-sign Fourier map agrees with its integral on L¹∩L². -/
theorem paperFourierL2_eq_integral {d : ℕ} (f : FullL2 d)
    (hf : Integrable (f : Euclidean d → ℂ)) :
    (paperFourierL2 d f : Euclidean d → ℂ) =ᵐ[volume] Real.fourierIntegralInv f := by
  have hcont : Continuous (Real.fourierIntegralInv (f : Euclidean d → ℂ)) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (continuous_fst.inner continuous_snd).neg hf
  apply ae_eq_of_integral_contDiff_smul_eq
    ((Lp.memLp (paperFourierL2 d f)).locallyIntegrable (by norm_num)) hcont.locallyIntegrable
  intro g hg hgs
  let gC : SchwartzMap (Euclidean d) ℂ := compactSchwartz (fun x => (g x : ℂ))
    (Complex.ofRealCLM.contDiff.comp hg) (hgs.comp_left Complex.ofReal_zero)
  have h := (paperFourierL2_pairing f gC).trans (integral_inverseFourier_mul_conj hf gC.integrable).symm
  change (∫ x, paperFourierL2 d f x * starRingEnd ℂ (g x : ℂ)) =
    ∫ x, Real.fourierIntegralInv f x * starRingEnd ℂ (g x : ℂ) at h
  simpa only [Complex.conj_ofReal, Complex.real_smul, mul_comm] using h
end RieszEuclidean
