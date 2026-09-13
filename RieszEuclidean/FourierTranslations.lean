import RieszEuclidean.FourierKernel
noncomputable section
open MeasureTheory
namespace RieszEuclidean
/-- Translation acts isometrically on actual Euclidean L² classes. -/
def translationL2 {d : ℕ} (t : Euclidean d) : FullL2 d →ₗᵢ[ℂ] FullL2 d :=
  Lp.compMeasurePreservingₗᵢ ℂ (fun x => x + t) (measurePreserving_add_right volume t)
/-- The representative of translation is the translated representative almost everywhere. -/
theorem translationL2_coe {d : ℕ} (t : Euclidean d) (f : FullL2 d) :
    (translationL2 t f : Euclidean d → ℂ) =ᵐ[volume] fun x => f (x + t) :=
  Lp.coeFn_compMeasurePreserving f (measurePreserving_add_right volume t)
/-- Translation preserves L¹ integrability when applied to an L² class. -/
theorem translationL2_integrable {d : ℕ} (t : Euclidean d) (f : FullL2 d)
    (hf : Integrable (f : Euclidean d → ℂ)) :
    Integrable (translationL2 t f : Euclidean d → ℂ) := by
  have h := ((measurePreserving_add_right volume t).integrable_comp hf.aestronglyMeasurable).mpr hf
  exact h.congr (translationL2_coe t f).symm
/-- Translation of the input translates convolution by the same vector. -/
theorem domainKernel_integral_translation {d : ℕ} (Ω : Set (Euclidean d))
    (f : Euclidean d → ℂ) (t v : Euclidean d) :
    (∫ w, domainKernel Ω (v - w) * f (w + t)) =
      ∫ w, domainKernel Ω (v + t - w) * f w := by
  have h := integral_add_right_eq_self (μ := volume)
    (fun w => domainKernel Ω (v + t - w) * f w) t
  simpa only [add_sub_add_right_eq_sub] using h
/-- Fourier cutoffs commute with translation on L¹∩L². -/
theorem fourierProjection_translation_integrable {d : ℕ} (Ω : Set (Euclidean d))
    (hΩ : MeasurableSet Ω) (hfin : volume Ω ≠ ⊤) (t : Euclidean d)
    (f : FullL2 d) (hf : Integrable (f : Euclidean d → ℂ)) :
    (fourierProjection Ω hΩ).op (translationL2 t f) =
      translationL2 t ((fourierProjection Ω hΩ).op f) := by
  have ht := (measurePreserving_add_right volume t).quasiMeasurePreserving.ae
    (fourierProjection_kernel Ω hΩ hfin f hf)
  apply Lp.ext
  filter_upwards [fourierProjection_kernel Ω hΩ hfin (translationL2 t f)
    (translationL2_integrable t f hf), translationL2_coe t ((fourierProjection Ω hΩ).op f),
    ht] with v hleft hright hkernel
  rw [hleft, hright, hkernel]
  calc
    _ = ∫ w, domainKernel Ω (v - w) * f (w + t) := by
      apply integral_congr_ae
      filter_upwards [translationL2_coe t f] with w hw
      rw [hw]
    _ = _ := domainKernel_integral_translation Ω (f : Euclidean d → ℂ) t v
/-- The actual Fourier cutoff commutes with every real translation on all of L². -/
theorem fourierProjection_translation {d : ℕ} (Ω : Set (Euclidean d))
    (hΩ : MeasurableSet Ω) (hfin : volume Ω ≠ ⊤) (t : Euclidean d) (f : FullL2 d) :
    (fourierProjection Ω hΩ).op (translationL2 t f) =
      translationL2 t ((fourierProjection Ω hΩ).op f) := by
  refine (schwartz_toL2_denseRange d).induction_on
    (p := fun f => (fourierProjection Ω hΩ).op (translationL2 t f) =
      translationL2 t ((fourierProjection Ω hΩ).op f)) f ?_ ?_
  · exact isClosed_eq ((fourierProjection Ω hΩ).op.continuous.comp (translationL2 t).continuous)
      ((translationL2 t).continuous.comp (fourierProjection Ω hΩ).op.continuous)
  · intro g
    exact fourierProjection_translation_integrable Ω hΩ hfin t _
      (g.integrable.congr (g.coeFn_toLp 2 volume).symm)
end RieszEuclidean
