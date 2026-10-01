import RieszEuclidean.TitchmarshRegularization
import RieszEuclidean.TitchmarshJetEmbedding
import RieszEuclidean.TitchmarshJetIntegrability
import RieszEuclidean.TitchmarshKernelJets

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 1000000

/-! Distribution/test Fubini through finite weighted jets. -/

noncomputable section
open MeasureTheory SchwartzMap
open scoped SchwartzMap Pointwise FourierTransform

namespace RieszEuclidean.CompleteMinimal

variable {d : ℕ}

/-- The derivative formula needed to identify the finite jet of a kernel test
with the integral of translated test jets. -/
def KernelTestJetFormula (f : Euclidean d → ℂ)
    (hm : Function.HasTemperateGrowth (𝓕 f)) (φ : 𝓢(Euclidean d, ℂ)) : Prop :=
  ∀ n y, iteratedFDeriv ℝ n
      (kernelConvolutionTestCLM f hm φ : Euclidean d → ℂ) y =
    ∫ x, f x • iteratedFDeriv ℝ n (φ : Euclidean d → ℂ) (y + x)

/-- Coordinatewise, the kernel-test derivative formula yields the Bochner
integral identity in the finite jet Banach space. -/
theorem finiteJetMap_kernelTest_eq_integral_of_formula
    (N : ℕ) (f : Euclidean d → ℂ) (hf : Continuous f)
    (hfc : HasCompactSupport f) (hm : Function.HasTemperateGrowth (𝓕 f))
    (φ : 𝓢(Euclidean d, ℂ)) (hformula : KernelTestJetFormula f hm φ) :
    finiteJetMap N (kernelConvolutionTestCLM f hm φ) =
      ∫ x, finiteJetMap N (f x • schwartzTranslateCLM x φ) := by
  let G : Euclidean d → FiniteJetSpace d N :=
    fun x => finiteJetMap N (f x • schwartzTranslateCLM x φ)
  have hG : Integrable G := by
    change Integrable (fun x => finiteJetMap N (f x • schwartzTranslateCLM x φ))
    exact finiteJetMap_smulTranslatedFamily_integrable N f hf hfc φ
  apply finiteJet_eq_integral_of_coordinate_eq
    (finiteJetMap N (kernelConvolutionTestCLM f hm φ)) G hG
  intro i y
  change ‖y‖ ^ i.1.1 •
      iteratedFDeriv ℝ i.1.2
        (kernelConvolutionTestCLM f hm φ : Euclidean d → ℂ) y = _
  rw [hformula i.1.2 y, ← integral_smul]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by
    have hcoord : G x i y = f x •
        (‖y‖ ^ i.1.1 • iteratedFDeriv ℝ i.1.2
          (φ : Euclidean d → ℂ) (y + x)) := by
      change (finiteJetMap N (f x • schwartzTranslateCLM x φ)) i y = _
      rw [(finiteJetMap N).map_smul]
      change f x • (finiteJetMap N (schwartzTranslateCLM x φ) i y) = _
      rw [finiteJetMap_apply]
      have htrans : (schwartzTranslateCLM x φ : Euclidean d → ℂ) =
          fun z => (φ : Euclidean d → ℂ) (x + z) := by
        funext z
        simp [schwartzTranslateCLM_apply]
      rw [htrans, iteratedFDeriv_comp_add_left]
      rw [add_comm x y]
    calc
      ‖y‖ ^ i.1.1 •
          (f x • iteratedFDeriv ℝ i.1.2 (φ : Euclidean d → ℂ) (y + x)) =
        f x • (‖y‖ ^ i.1.1 •
          iteratedFDeriv ℝ i.1.2 (φ : Euclidean d → ℂ) (y + x)) := by
            exact smul_comm _ _ _
      _ = G x i y := hcoord.symm

/-- Once a distribution factors through the finite jet map, the kernel-test
functional integral identity follows from the jet formula and compact support. -/
theorem distribution_apply_kernelConvolutionTest_eq_integral_of_factor
    (N : ℕ) (L : FiniteJetSpace d N →L[ℂ] ℂ)
    (u : TemperedDistribution d)
    (hfactor : L.comp (finiteJetMap N) = u)
    (f : Euclidean d → ℂ) (hf : Continuous f) (hfc : HasCompactSupport f)
    (hm : Function.HasTemperateGrowth (𝓕 f)) (φ : 𝓢(Euclidean d, ℂ))
    (hformula : KernelTestJetFormula f hm φ) :
    u (kernelConvolutionTestCLM f hm φ) =
      ∫ x, f x * u (schwartzTranslateCLM x φ) := by
  apply distribution_apply_kernelConvolutionTest_eq_integral
      (finiteJetMap N) L u hfactor f hm φ
      (finiteJetMap_kernelTest_eq_integral_of_formula N f hf hfc hm φ hformula)
      (finiteJetMap_smulTranslatedFamily_integrable N f hf hfc φ)

/-- Every tempered distribution commutes with the compact-kernel integral once
the kernel-test derivative formula is established. The finite-order estimate
factors the distribution through a finite weighted jet space. -/
theorem distribution_apply_kernelConvolutionTest_eq_integral_of_formula
    (u : TemperedDistribution d) (f : Euclidean d → ℂ) (hf : Continuous f)
    (hfc : HasCompactSupport f) (hm : Function.HasTemperateGrowth (𝓕 f))
    (φ : 𝓢(Euclidean d, ℂ))
    (hformula : KernelTestJetFormula f hm φ) :
    u (kernelConvolutionTestCLM f hm φ) =
      ∫ x, f x * u (schwartzTranslateCLM x φ) := by
  obtain ⟨N, L, hfactor⟩ := temperedDistribution_factors_through_finiteJet u
  exact distribution_apply_kernelConvolutionTest_eq_integral_of_factor
    N L u hfactor f hf hfc hm φ hformula

/-- Distribution actions commute with integration against a compactly supported
continuous kernel when the Schwartz test is compactly supported. -/
theorem distribution_apply_compactKernelConvolutionTest_eq_integral
    (u : TemperedDistribution d) (f : Euclidean d → ℂ) (hf : Continuous f)
    (hfc : HasCompactSupport f) (hm : Function.HasTemperateGrowth (𝓕 f))
    (φ : 𝓢(Euclidean d, ℂ)) (hφ : HasCompactSupport (φ : Euclidean d → ℂ)) :
    u (kernelConvolutionTestCLM f hm φ) =
      ∫ x, f x * u (schwartzTranslateCLM x φ) := by
  apply distribution_apply_kernelConvolutionTest_eq_integral_of_formula
    u f hf hfc hm φ
  intro n y
  exact iteratedFDeriv_kernelConvolutionTestCLM f hf hfc hm φ hφ n y

end RieszEuclidean.CompleteMinimal

end
