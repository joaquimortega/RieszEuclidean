import RieszEuclidean.Basic
import Mathlib.Analysis.Distribution.FourierSchwartz

noncomputable section
open MeasureTheory
open scoped FourierTransform
namespace RieszEuclidean

/-- Fourier transposition on integrable Euclidean functions, before conjugation. -/
theorem integral_fourier_mul {d : ℕ} {f g : Euclidean d → ℂ}
    (hf : Integrable f) (hg : Integrable g) :
    (∫ x, 𝓕 f x * g x) = ∫ x, f x * 𝓕 g x := by
  have h := VectorFourier.integral_fourierIntegral_smul_eq_flip
    (L := innerₗ (Euclidean d)) Real.continuous_fourierChar
    (continuous_fst.inner continuous_snd) hf hg
  simpa only [Real.fourierIntegral, smul_eq_mul, flip_innerₗ] using h

/-- Conjugation exchanges the two Fourier signs. -/
theorem fourier_conj_eq_conj_inverse {d : ℕ} (f : Euclidean d → ℂ)
    (x : Euclidean d) :
    𝓕 (fun y => starRingEnd ℂ (f y)) x = starRingEnd ℂ (𝓕⁻ f x) := by
  rw [Real.fourierIntegral_eq, Real.fourierIntegralInv_eq, ← integral_conj]
  congr 1
  ext y
  simp [Circle.smul_def, map_mul]

/-- The Fourier pairing with conjugation uses the inverse transform on the right. -/
theorem integral_fourier_mul_conj {d : ℕ} {f g : Euclidean d → ℂ}
    (hf : Integrable f) (hg : Integrable g) :
    (∫ x, 𝓕 f x * starRingEnd ℂ (g x)) =
      ∫ x, f x * starRingEnd ℂ (𝓕⁻ g x) := by
  have hg' : Integrable (fun x => starRingEnd ℂ (g x)) :=
    Complex.conjCLE.toContinuousLinearMap.integrable_comp hg
  simpa only [fourier_conj_eq_conj_inverse] using integral_fourier_mul hf hg'

/-- Parseval pairing for Euclidean Schwartz functions with the exact Fourier normalization. -/
theorem schwartz_parseval {d : ℕ} (f g : SchwartzMap (Euclidean d) ℂ) :
    (∫ x, 𝓕 f x * starRingEnd ℂ (𝓕 g x)) =
      ∫ x, f x * starRingEnd ℂ (g x) := by
  have h := integral_fourier_mul_conj f.integrable
    (SchwartzMap.fourierTransformCLM ℂ g).integrable
  simpa only [SchwartzMap.fourierTransformCLM_apply,
    Continuous.fourier_inversion g.continuous g.integrable
      (SchwartzMap.fourierTransformCLM ℂ g).integrable] using h


/-- The Schwartz embedding into L² realizes the integral pairing. -/
theorem schwartz_toL2_inner {d : ℕ} (f g : SchwartzMap (Euclidean d) ℂ) :
    inner (𝕜 := ℂ) (f.toLp 2) (g.toLp 2) =
      ∫ x, g x * starRingEnd ℂ (f x) := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [f.coeFn_toLp 2, g.coeFn_toLp 2] with x hf hg
  simp [hf, hg, RCLike.inner_apply, mul_comm]

/-- Fourier preserves the L² inner product of Schwartz functions. -/
theorem schwartz_fourier_inner {d : ℕ} (f g : SchwartzMap (Euclidean d) ℂ) :
    inner (𝕜 := ℂ) ((SchwartzMap.fourierTransformCLM ℂ f).toLp 2)
      ((SchwartzMap.fourierTransformCLM ℂ g).toLp 2) =
      inner (𝕜 := ℂ) (f.toLp 2) (g.toLp 2) := by
  simpa only [schwartz_toL2_inner, SchwartzMap.fourierTransformCLM_apply] using
    schwartz_parseval g f

/-- Parseval in the norm used for the Hilbert-space extension. -/
theorem schwartz_fourier_norm {d : ℕ} (f : SchwartzMap (Euclidean d) ℂ) :
    ‖(SchwartzMap.fourierTransformCLM ℂ f).toLp 2‖ = ‖f.toLp 2‖ := by
  have h := congrArg Complex.re (schwartz_fourier_inner f f)
  change RCLike.re (inner (𝕜 := ℂ) _ _) = RCLike.re (inner (𝕜 := ℂ) _ _) at h
  rw [← norm_sq_eq_re_inner, ← norm_sq_eq_re_inner] at h
  nlinarith [norm_nonneg ((SchwartzMap.fourierTransformCLM ℂ f).toLp 2),
    norm_nonneg (f.toLp 2)]

end RieszEuclidean
