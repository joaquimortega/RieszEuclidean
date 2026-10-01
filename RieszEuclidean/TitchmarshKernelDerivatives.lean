import RieszEuclidean.TitchmarshRegularization
import RieszEuclidean.CompleteMinimalDistributionConvolution
import Mathlib.Analysis.Convolution
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries

/-! Exact finite-jet formula for the compact-kernel test action. -/

noncomputable section
open MeasureTheory SchwartzMap Set
open scoped SchwartzMap Pointwise FourierTransform

namespace RieszEuclidean.CompleteMinimal

variable {d : ℕ}

/-- The real multilinear target used for the order `n` differential jet. -/
abbrev Jet (d n : ℕ) :=
  ContinuousMultilinearMap ℝ (fun _ : Fin n => Euclidean d) ℂ

/-- The bilinear action taking a complex scalar and multiplying a jet. -/
def jetAction (n : ℕ) : Jet d n →L[ℝ] ℂ →L[ℝ] Jet d n :=
  ContinuousLinearMap.flip (ContinuousLinearMap.lsmul ℝ (E := Jet d n) ℂ)

/-- Reflection of the integrable factor used in Mathlib convolution. -/
def reflected (f : Euclidean d → ℂ) : Euclidean d → ℂ := fun z => f (-z)

/-- Convolution of the `n`-th kernel jet with the reflected scalar factor. -/
def convolutionJet (f : Euclidean d → ℂ) (φ : 𝓢(Euclidean d, ℂ))
    (n : ℕ) : Euclidean d → Jet d n :=
  MeasureTheory.convolution (iteratedFDeriv ℝ n (φ : Euclidean d → ℂ))
    (reflected f) (jetAction (d := d) n) volume

/-- The jet-valued convolution is the integral of translated kernel jets. -/
theorem convolutionJet_apply (f : Euclidean d → ℂ)
    (φ : 𝓢(Euclidean d, ℂ)) (n : ℕ) (y : Euclidean d) :
    convolutionJet (d := d) f φ n y =
      ∫ x, f x • iteratedFDeriv ℝ n (φ : Euclidean d → ℂ) (y + x) := by
  rw [convolutionJet, MeasureTheory.convolution_def]
  let T : Euclidean d → Euclidean d := fun x => y + x
  have hT : MeasureTheory.MeasurePreserving T volume volume := by
    simpa [T] using MeasureTheory.measurePreserving_add_left volume y
  have heT : MeasurableEmbedding T := by
    simpa [T] using measurableEmbedding_addLeft y
  calc
    (∫ z, jetAction (d := d) n
        (iteratedFDeriv ℝ n (φ : Euclidean d → ℂ) z) (reflected f (y - z))) =
      ∫ x, jetAction (d := d) n
        (iteratedFDeriv ℝ n (φ : Euclidean d → ℂ) (T x))
        (reflected f (y - T x)) := by
          have hcomp := hT.integral_comp heT (fun z =>
            jetAction (d := d) n (iteratedFDeriv ℝ n (φ : Euclidean d → ℂ) z)
              (reflected f (y - z)))
          simpa only [T] using hcomp.symm
    _ = ∫ x, f x • iteratedFDeriv ℝ n (φ : Euclidean d → ℂ) (y + x) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => by
        change f (-(y - (y + x))) • iteratedFDeriv ℝ n
          (φ : Euclidean d → ℂ) (y + x) =
          f x • iteratedFDeriv ℝ n (φ : Euclidean d → ℂ) (y + x)
        congr 1
        congr 1
        all_goals abel

/-- Compact smooth kernel jets can be differentiated through convolution on the
compact, differentiable factor. -/
theorem convolutionJet_hasFDerivAt (f : Euclidean d → ℂ) (hf : Continuous f)
    (φ : 𝓢(Euclidean d, ℂ)) (hφ : HasCompactSupport (φ : Euclidean d → ℂ))
    (n : ℕ) (y : Euclidean d) :
    HasFDerivAt (𝕜 := ℝ) (convolutionJet (d := d) f φ n)
      (MeasureTheory.convolution (𝕜 := ℝ)
        (fderiv ℝ (iteratedFDeriv ℝ n (φ : Euclidean d → ℂ)))
        (reflected f) (ContinuousLinearMap.precompL (𝕜 := ℝ) (Euclidean d)
          (jetAction (d := d) n)) volume y) y := by
  refine HasCompactSupport.hasFDerivAt_convolution_left
    (𝕜 := ℝ) (L := jetAction (d := d) n)
    (hcf := hφ.iteratedFDeriv n)
    (hf := (φ.smooth ⊤).iteratedFDeriv_right (by exact (WithTop.coe_le_coe).2 le_top))
    (hg := (hf.comp continuous_neg).locallyIntegrable) y

end RieszEuclidean.CompleteMinimal
