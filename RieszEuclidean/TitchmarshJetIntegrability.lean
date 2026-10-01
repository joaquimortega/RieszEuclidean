import RieszEuclidean.TitchmarshTranslationContinuity
import RieszEuclidean.TitchmarshJetEmbedding
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 50000

/-! Bochner integrability and coordinate extraction for finite jets of translated tests. -/

noncomputable section

open MeasureTheory SchwartzMap
open scoped BoundedContinuousFunction SchwartzMap

namespace RieszEuclidean.CompleteMinimal

variable {d : ℕ}

/-- A compactly supported continuous scalar weight times the finite jet of a translated
Schwartz test is Bochner integrable. -/
theorem finiteJetMap_smulTranslatedFamily_integrable (N : ℕ) (f : Euclidean d → ℂ)
    (hf : Continuous f) (hfc : HasCompactSupport f) (φ : 𝓢(Euclidean d, ℂ)) :
    Integrable (fun x => finiteJetMap (d := d) N (f x • schwartzTranslateCLM x φ)) := by
  classical
  let G : Euclidean d → FiniteJetSpace d N :=
    fun x => finiteJetMap (d := d) N (f x • schwartzTranslateCLM x φ)
  have htrans : Continuous (fun x : Euclidean d => schwartzTranslateCLM x φ) :=
    continuous_schwartzTranslateCLM_apply φ
  have hG : Continuous G := by
    dsimp [G]
    exact (finiteJetMap (d := d) N).continuous.comp (hf.smul htrans)
  have hsupport : tsupport G ⊆ tsupport f := by
    change closure (Function.support G) ⊆ tsupport f
    apply IsClosed.closure_subset_iff (isClosed_tsupport f) |>.mpr
    intro x hx
    change G x ≠ 0 at hx
    by_cases hxf : x ∈ tsupport f
    · exact hxf
    · exfalso
      have hfx : f x = 0 := image_eq_zero_of_nmem_tsupport hxf
      exact hx (by simp only [G, hfx, zero_smul, map_zero])
  have hGc : HasCompactSupport G := hfc.of_isClosed_subset (isClosed_tsupport G) hsupport
  exact hG.integrable_of_hasCompactSupport hGc

/-- Evaluation of a Bochner integral of finite jets at one coordinate and one spatial point
commutes with integration. -/
theorem finiteJet_integral_coordinate_apply {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {N : ℕ}
    (F : α → FiniteJetSpace d N) (hF : Integrable F μ)
    (i : {i : ℕ × ℕ // i ∈ Finset.Iic (N, N)}) (y : Euclidean d) :
    (∫ x, F x ∂μ) i y = ∫ x, F x i y ∂μ := by
  let proj : FiniteJetSpace d N →L[ℝ]
      (Euclidean d →ᵇ JetValue d i.1.2) := ContinuousLinearMap.proj (R := ℝ) i
  let eval : (Euclidean d →ᵇ JetValue d i.1.2) →L[ℝ] JetValue d i.1.2 :=
    BoundedContinuousFunction.evalCLM ℝ y
  let L : FiniteJetSpace d N →L[ℝ] JetValue d i.1.2 := eval.comp proj
  have hcomm : ∫ x, L (F x) ∂μ = L (∫ x, F x ∂μ) := by
    exact L.integral_comp_comm (μ := μ) hF
  calc
    (∫ x, F x ∂μ) i y = L (∫ x, F x ∂μ) := rfl
    _ = ∫ x, L (F x) ∂μ := hcomm.symm
    _ = ∫ x, F x i y ∂μ := rfl

/-- Coordinatewise scalar integral identities determine an equality in the finite-jet space.
This packages the final step after differentiating a kernel integral under the integral sign. -/
theorem finiteJet_eq_integral_of_coordinate_eq {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {N : ℕ}
    (J : FiniteJetSpace d N)
    (F : α → FiniteJetSpace d N) (hF : Integrable F μ)
    (hcoord : ∀ (i : {i : ℕ × ℕ // i ∈ Finset.Iic (N, N)}) (y : Euclidean d),
      J i y = ∫ x, F x i y ∂μ) :
    J = ∫ x, F x ∂μ := by
  apply funext
  intro i
  apply BoundedContinuousFunction.ext
  intro y
  rw [finiteJet_integral_coordinate_apply F hF i y]
  exact hcoord i y

end RieszEuclidean.CompleteMinimal

end
