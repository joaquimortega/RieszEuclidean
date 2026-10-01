import RieszEuclidean.TitchmarshKernelDerivatives
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! Differentiating compact-kernel tests through every finite order. -/

noncomputable section
open MeasureTheory SchwartzMap
open scoped SchwartzMap FourierTransform

namespace RieszEuclidean.CompleteMinimal

variable {d : ℕ}

private def curryJet (n : ℕ) :
    Jet d (n + 1) →L[ℝ] Euclidean d →L[ℝ] Jet d n :=
  (continuousMultilinearCurryLeftEquiv ℝ
    (fun _ : Fin (n + 1) => Euclidean d) ℂ).toContinuousLinearEquiv.toContinuousLinearMap

private theorem convolutionJet_fderiv (f : Euclidean d → ℂ) (hf : Continuous f)
    (φ : 𝓢(Euclidean d, ℂ)) (hφ : HasCompactSupport (φ : Euclidean d → ℂ))
    (n : ℕ) (y : Euclidean d) :
    fderiv ℝ (convolutionJet f φ n) y = curryJet n (convolutionJet f φ (n + 1) y) := by
  rw [(convolutionJet_hasFDerivAt f hf φ hφ n y).fderiv]
  have hcont : Continuous (iteratedFDeriv ℝ (n + 1) (φ : Euclidean d → ℂ)) :=
    φ.smooth'.continuous_iteratedFDeriv (by exact_mod_cast le_top)
  have hInt := (hφ.iteratedFDeriv (n + 1)).convolutionExists_left (μ := volume)
    (jetAction (d := d) (n + 1)) hcont (hf.comp continuous_neg).locallyIntegrable y
  simp only [convolutionJet, MeasureTheory.convolution_def]
  trans ∫ z, curryJet n
    (jetAction (d := d) (n + 1) (iteratedFDeriv ℝ (n + 1) (φ : Euclidean d → ℂ) z)
      (reflected f (y - z)))
  · apply integral_congr_ae
    exact Filter.Eventually.of_forall fun z => by
      apply ContinuousLinearMap.ext
      intro v
      apply ContinuousMultilinearMap.ext
      intro m
      rfl
  · exact ContinuousLinearMap.integral_comp_comm (𝕜 := ℝ)
      (E := Jet d (n + 1)) (F := Euclidean d →L[ℝ] Jet d n) (μ := volume)
      (curryJet (d := d) n) hInt

private theorem translatedJet_integrable (f : Euclidean d → ℂ)
    (hf : Continuous f) (hfc : HasCompactSupport f)
    (φ : 𝓢(Euclidean d, ℂ)) (n : ℕ) (y : Euclidean d) :
    Integrable (fun x => f x • iteratedFDeriv ℝ n (φ : Euclidean d → ℂ) (y + x)) := by
  have hcont : Continuous (iteratedFDeriv ℝ n (φ : Euclidean d → ℂ)) :=
    φ.smooth'.continuous_iteratedFDeriv (by exact_mod_cast le_top)
  exact (hf.smul (hcont.comp (continuous_const.add continuous_id))).integrable_of_hasCompactSupport
    hfc.smul_right

/-- Every finite derivative of the compact-kernel test is the integral of
the corresponding derivatives of its translated Schwartz test. -/
theorem iteratedFDeriv_kernelConvolutionTestCLM
    (f : Euclidean d → ℂ) (hf : Continuous f) (hfc : HasCompactSupport f)
    (hm : Function.HasTemperateGrowth (𝓕 f))
    (φ : 𝓢(Euclidean d, ℂ)) (hφ : HasCompactSupport (φ : Euclidean d → ℂ))
    (n : ℕ) (y : Euclidean d) :
    iteratedFDeriv ℝ n (kernelConvolutionTestCLM f hm φ : Euclidean d → ℂ) y =
      ∫ x, f x • iteratedFDeriv ℝ n (φ : Euclidean d → ℂ) (y + x) := by
  let K := (kernelConvolutionTestCLM f hm φ : Euclidean d → ℂ)
  have hjet : ∀ n, iteratedFDeriv ℝ n K = convolutionJet f φ n := by
    intro n
    induction n with
    | zero =>
      funext z
      rw [convolutionJet_apply]
      apply ContinuousMultilinearMap.ext
      intro m
      rw [ContinuousMultilinearMap.integral_apply (translatedJet_integrable f hf hfc φ 0 z)]
      simp only [iteratedFDeriv_zero_apply, ContinuousMultilinearMap.smul_apply]
      exact kernelConvolutionTestCLM_apply f (hf.integrable_of_hasCompactSupport hfc) hm φ z
    | succ n ih =>
      rw [iteratedFDeriv_succ_eq_comp_left, ih]
      funext z
      change (continuousMultilinearCurryLeftEquiv ℝ
        (fun _ : Fin (n + 1) => Euclidean d) ℂ).symm
          (fderiv ℝ (convolutionJet f φ n) z) = _
      rw [convolutionJet_fderiv f hf φ hφ n z]
      change (continuousMultilinearCurryLeftEquiv ℝ
        (fun _ : Fin (n + 1) => Euclidean d) ℂ).symm
          ((continuousMultilinearCurryLeftEquiv ℝ
            (fun _ : Fin (n + 1) => Euclidean d) ℂ) (convolutionJet f φ (n + 1) z)) = _
      exact LinearIsometryEquiv.symm_apply_apply _ _
  rw [hjet n, convolutionJet_apply]

end RieszEuclidean.CompleteMinimal
