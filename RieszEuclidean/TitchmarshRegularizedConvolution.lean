import RieszEuclidean.TitchmarshRegularization
import RieszEuclidean.TitchmarshRegularizationSupport
import RieszEuclidean.TitchmarshFunctionAlgebra
import RieszEuclidean.TitchmarshKernelIntegral
import Mathlib.Analysis.Convolution

/-! Exact convolution identity for two compactly supported distribution
regularizations, followed by the corresponding support bound. -/

noncomputable section
open MeasureTheory Set SchwartzMap
open scoped SchwartzMap CompactlySupported Convolution FourierTransform Pointwise

namespace RieszEuclidean.CompleteMinimal

variable {d : ℕ}

private theorem compact_continuous_fourier_growth (f : Euclidean d → ℂ)
    (hf : Continuous f) (hfc : HasCompactSupport f) :
    Function.HasTemperateGrowth (𝓕 f) :=
  fourier_hasTemperateGrowth_of_compact_support
    (hf.integrable_of_hasCompactSupport hfc) hfc
    (Filter.Eventually.of_forall fun _ hx => image_eq_zero_of_nmem_tsupport hx)

private theorem volume_neg_invariant :
    (volume : Measure (Euclidean d)).IsNegInvariant := by
  refine ⟨?_⟩
  rw [Measure.neg_def]
  exact (LinearIsometryEquiv.measurePreserving
    (LinearIsometryEquiv.neg ℝ : Euclidean d ≃ₗᵢ[ℝ] Euclidean d)).map_eq

private def regularizedKernel (ρ σ : 𝓢(Euclidean d, ℂ))
    (hρ : HasCompactSupport (ρ : Euclidean d → ℂ)) : 𝓢(Euclidean d, ℂ) :=
  kernelConvolutionTestCLM (schwartzReflectCLM ρ)
    (compact_continuous_fourier_growth _ (schwartzReflectCLM ρ).continuous
      (schwartzReflectCLM_hasCompactSupport hρ)) σ

private def regularizedFunction (u : TemperedDistribution d)
    (hu : CompactlySupportedDistribution u) (ρ : 𝓢(Euclidean d, ℂ))
    (hρ : HasCompactSupport (ρ : Euclidean d → ℂ)) :
    RieszEuclidean.TitchmarshFunctionAlgebra.Function d :=
  ⟨⟨distributionRegularization u ρ, continuous_distributionRegularization u ρ⟩,
    distributionRegularization_hasCompactSupport hu hρ⟩

private theorem regularizedKernel_eq_functionConvolution
    (ρ σ : 𝓢(Euclidean d, ℂ))
    (hρ : HasCompactSupport (ρ : Euclidean d → ℂ))
    (hσ : HasCompactSupport (σ : Euclidean d → ℂ)) :
    (regularizedKernel ρ σ hρ : Euclidean d → ℂ) =
      RieszEuclidean.TitchmarshFunctionAlgebra.convolution d
        ⟨ρ, hρ⟩ ⟨σ, hσ⟩ := by
  funext x
  let hm := compact_continuous_fourier_growth (schwartzReflectCLM ρ)
    (schwartzReflectCLM ρ).continuous (schwartzReflectCLM_hasCompactSupport hρ)
  calc
    regularizedKernel ρ σ hρ x =
        MeasureTheory.convolution (σ : Euclidean d → ℂ)
          (fun z => (schwartzReflectCLM ρ) (-z))
          (ContinuousLinearMap.mul ℝ ℂ) volume x := by
      exact kernelConvolutionTestCLM_eq_convolution _ (schwartzReflectCLM ρ).integrable
        hm σ x
    _ = MeasureTheory.convolution (σ : Euclidean d → ℂ) ρ
          (ContinuousLinearMap.mul ℝ ℂ) volume x := by
      congr 1
      funext z
      simp [schwartzReflectCLM_apply]
    _ = MeasureTheory.convolution (ρ : Euclidean d → ℂ) σ
          (ContinuousLinearMap.mul ℝ ℂ) volume x := by
      let ρcc : RieszEuclidean.TitchmarshFunctionAlgebra.Function d := ⟨ρ, hρ⟩
      let σcc : RieszEuclidean.TitchmarshFunctionAlgebra.Function d := ⟨σ, hσ⟩
      have hcomm := RieszEuclidean.TitchmarshFunctionAlgebra.convolution_comm d σcc ρcc
      have hpoint := congrArg (fun f : RieszEuclidean.TitchmarshFunctionAlgebra.Function d => f x) hcomm
      simpa [ρcc, σcc, RieszEuclidean.TitchmarshFunctionAlgebra.convolution,
        MeasureTheory.convolution_def] using hpoint
    _ = RieszEuclidean.TitchmarshFunctionAlgebra.convolution d ⟨ρ, hρ⟩ ⟨σ, hσ⟩ x := by
      rfl

/-- The convolution of two distribution regularizations is the regularization
of their actual distribution convolution, with kernel `ρ ⋆ σ`. -/
theorem IsDistributionConvolution.regularizedConvolution_identity
    {u v w : TemperedDistribution d} (hc : IsDistributionConvolution u v w)
    (hu : CompactlySupportedDistribution u) (hv : CompactlySupportedDistribution v)
    (ρ σ : 𝓢(Euclidean d, ℂ))
    (hρ : HasCompactSupport (ρ : Euclidean d → ℂ))
    (hσ : HasCompactSupport (σ : Euclidean d → ℂ)) (x : Euclidean d) :
    RieszEuclidean.TitchmarshFunctionAlgebra.convolution d
      (regularizedFunction u hu ρ hρ) (regularizedFunction v hv σ hσ) x =
      distributionRegularization w (regularizedKernel ρ σ hρ) x := by
  letI := volume_neg_invariant (d := d)
  let f : Euclidean d → ℂ := fun t => distributionRegularization v σ (x + t)
  have hf : Continuous f :=
    (continuous_distributionRegularization v σ).comp (continuous_const.add continuous_id)
  have hfc : HasCompactSupport f :=
    (distributionRegularization_hasCompactSupport hv hσ).comp_homeomorph
      (Homeomorph.addLeft x)
  let hm := compact_continuous_fourier_growth f hf hfc
  have hout := distribution_apply_compactKernelConvolutionTest_eq_integral
    u f hf hfc hm (schwartzReflectCLM ρ) (schwartzReflectCLM_hasCompactSupport hρ)
  have htrans : ∀ t, schwartzTranslateCLM t (schwartzReflectCLM ρ) =
      regularizationTest ρ (-t) := by
    intro t
    ext z
    simp only [schwartzTranslateCLM_apply, schwartzReflectCLM_apply,
      regularizationTest_apply]
    congr 1
    abel
  have hout' : u (kernelConvolutionTestCLM f hm (schwartzReflectCLM ρ)) =
      ∫ t, f t * distributionRegularization u ρ (-t) := by
    rw [hout]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun t => by
      simp only [htrans t, distributionRegularization_apply]
  let κ := regularizedKernel ρ σ hρ
  obtain ⟨ψ, hψ, hw⟩ := hc.regularization_formula κ x
  have hκρ := compact_continuous_fourier_growth (schwartzReflectCLM ρ)
    (schwartzReflectCLM ρ).continuous (schwartzReflectCLM_hasCompactSupport hρ)
  let φx := regularizationTest σ x
  have hφxc : HasCompactSupport (φx : Euclidean d → ℂ) :=
    regularizationTest_hasCompactSupport hσ x
  have hkernel_identity (z : Euclidean d) :
      kernelConvolutionTestCLM (fun a => ρ (a - z))
        (compact_continuous_fourier_growth (fun a => ρ (a - z))
          (ρ.continuous.comp (continuous_id.sub continuous_const))
          (hρ.comp_homeomorph (Homeomorph.subRight z))) φx =
      regularizationTest κ (x - z) := by
    ext t
    let fz : Euclidean d → ℂ := fun a => ρ (a - z)
    let hmz := compact_continuous_fourier_growth fz
      (ρ.continuous.comp (continuous_id.sub continuous_const))
      (hρ.comp_homeomorph (Homeomorph.subRight z))
    let T : Euclidean d → Euclidean d := fun a => z - a
    have hT : MeasurePreserving T volume volume := by
      simpa [T, sub_eq_add_neg] using
        (MeasureTheory.measurePreserving_add_left volume z).comp
          (MeasureTheory.Measure.measurePreserving_neg volume)
    have heT : MeasurableEmbedding T := by
      let e : Euclidean d ≃ₜ Euclidean d :=
        (Homeomorph.neg (Euclidean d)).trans (Homeomorph.addLeft z)
      simpa [T, e, sub_eq_add_neg] using e.measurableEmbedding
    calc
      kernelConvolutionTestCLM fz hmz φx t =
          ∫ a, fz a * φx (t + a) :=
        kernelConvolutionTestCLM_apply fz
          ((ρ.continuous.comp (continuous_id.sub continuous_const)).integrable_of_hasCompactSupport
            (hρ.comp_homeomorph (Homeomorph.subRight z))) hmz φx t
      _ = ∫ a, ρ (a - z) * σ (x - t - a) := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun a => by
          simp only [fz, φx, regularizationTest_apply]
          congr 1
          abel
      _ = ∫ a, (schwartzReflectCLM ρ) (z - a) * σ (x - z - t + (z - a)) := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun a => by
          simp [T, schwartzReflectCLM_apply, sub_eq_add_neg, add_assoc,
            add_left_comm, add_comm]
      _ = ∫ a, (schwartzReflectCLM ρ) a * σ (x - z - t + a) :=
        hT.integral_comp heT
          (fun b => (schwartzReflectCLM ρ) b * σ (x - z - t + b))
      _ = κ (x - z - t) := by
        dsimp [κ, regularizedKernel]
        rw [kernelConvolutionTestCLM_apply _ (schwartzReflectCLM ρ).integrable hκρ]
      _ = regularizationTest κ (x - z) t := by
        simp [regularizationTest_apply]
  have hpoint (z : Euclidean d) :
      kernelConvolutionTestCLM f hm (schwartzReflectCLM ρ) z =
        distributionRegularization v κ (x - z) := by
    let fz : Euclidean d → ℂ := fun a => ρ (a - z)
    let hmz := compact_continuous_fourier_growth fz
      (ρ.continuous.comp (continuous_id.sub continuous_const))
      (hρ.comp_homeomorph (Homeomorph.subRight z))
    have hinter := distribution_apply_compactKernelConvolutionTest_eq_integral v fz
      (ρ.continuous.comp (continuous_id.sub continuous_const))
      (hρ.comp_homeomorph (Homeomorph.subRight z)) hmz φx hφxc
    have htest := hkernel_identity z
    have htranslation : ∀ a,
        schwartzTranslateCLM a φx = regularizationTest σ (x - a) := by
      intro a
      ext t
      simp [φx, regularizationTest_apply, schwartzTranslateCLM_apply,
        sub_eq_add_neg, add_assoc, add_comm, add_left_comm]
    have hreg : distributionRegularization v κ (x - z) =
        ∫ a, ρ (a - z) * distributionRegularization v σ (x - a) := by
      rw [distributionRegularization_apply]
      rw [← htest]
      rw [hinter]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun a => by
        simp only [htranslation a, distributionRegularization_apply, fz]
    have hchange :
        (∫ a, ρ (a - z) * distributionRegularization v σ (x - a)) =
          ∫ t, f t * (schwartzReflectCLM ρ) (z + t) := by
      let q : Euclidean d → ℂ := fun a =>
        ρ (a - z) * distributionRegularization v σ (x - a)
      calc
        ∫ a, q a = ∫ t, q (-t) := (integral_neg_eq_self q volume).symm
        _ = ∫ t, f t * (schwartzReflectCLM ρ) (z + t) := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall fun t => by
            simp [q, f, schwartzReflectCLM_apply, sub_eq_add_neg,
              add_assoc, add_left_comm, add_comm, mul_comm]
    calc
      kernelConvolutionTestCLM f hm (schwartzReflectCLM ρ) z =
          ∫ t, f t * (schwartzReflectCLM ρ) (z + t) := by
        rw [kernelConvolutionTestCLM_apply f
          (hf.integrable_of_hasCompactSupport hfc) hm]
      _ = distributionRegularization v κ (x - z) := by
        rw [← hchange, ← hreg]

  have hψeq : ψ = kernelConvolutionTestCLM f hm (schwartzReflectCLM ρ) := by
    ext z
    rw [hψ z, hpoint z]
  have houter : u ψ = distributionRegularization w κ x := by
    rw [hψeq]
    exact (congrArg u hψeq).symm.trans hw.symm
  have hconvint :
      RieszEuclidean.TitchmarshFunctionAlgebra.convolution d
        (regularizedFunction u hu ρ hρ) (regularizedFunction v hv σ hσ) x =
      ∫ t, f t * distributionRegularization u ρ (-t) := by
    rw [RieszEuclidean.TitchmarshFunctionAlgebra.coe_convolution]
    let g : Euclidean d → ℂ := fun y =>
      distributionRegularization u ρ y * distributionRegularization v σ (x - y)
    calc
      ∫ y, g y = ∫ y, g (-y) := (integral_neg_eq_self g volume).symm
      _ = ∫ t, f t * distributionRegularization u ρ (-t) := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun t => by
          simp [g, f, mul_comm]
  calc
    _ = ∫ t, f t * distributionRegularization u ρ (-t) := hconvint
    _ = u ψ := hout'.symm.trans (congrArg u hψeq).symm
    _ = distributionRegularization w κ x := houter

/-- The support of the convolution of two regularizations is bounded by the
support of the distribution convolution and the two kernel supports. -/
theorem IsDistributionConvolution.regularizedConvolution_support_subset
    {u v w : TemperedDistribution d} (hc : IsDistributionConvolution u v w)
    (hu : CompactlySupportedDistribution u) (hv : CompactlySupportedDistribution v)
    {ρ σ : 𝓢(Euclidean d, ℂ)}
    (hρ : HasCompactSupport (ρ : Euclidean d → ℂ))
    (hσ : HasCompactSupport (σ : Euclidean d → ℂ)) :
    tsupport (distributionRegularization u ρ ⋆[ContinuousLinearMap.mul ℂ ℂ, volume]
      distributionRegularization v σ) ⊆
      distributionSupport w + tsupport (ρ : Euclidean d → ℂ) +
        tsupport (σ : Euclidean d → ℂ) := by
  let κ := regularizedKernel ρ σ hρ
  let ρcc : RieszEuclidean.TitchmarshFunctionAlgebra.Function d := ⟨ρ, hρ⟩
  let σcc : RieszEuclidean.TitchmarshFunctionAlgebra.Function d := ⟨σ, hσ⟩
  have hκeq : (κ : Euclidean d → ℂ) =
      RieszEuclidean.TitchmarshFunctionAlgebra.convolution d ρcc σcc := by
    exact regularizedKernel_eq_functionConvolution ρ σ hρ hσ
  have hκcompact : HasCompactSupport (κ : Euclidean d → ℂ) := by
    rw [hκeq]
    exact hρ.convolution (L := ContinuousLinearMap.mul ℂ ℂ) hσ
  have hκsupport : tsupport (κ : Euclidean d → ℂ) ⊆
      tsupport (ρ : Euclidean d → ℂ) + tsupport (σ : Euclidean d → ℂ) := by
    rw [hκeq]
    apply closure_minimal
    · exact (MeasureTheory.support_convolution_subset
        (L := ContinuousLinearMap.mul ℂ ℂ) (μ := volume)).trans
        (Set.add_subset_add (subset_tsupport (ρ : Euclidean d → ℂ))
          (subset_tsupport (σ : Euclidean d → ℂ)))
    · exact (IsCompact.add hρ hσ).isClosed
  have hidentity (y : Euclidean d) :
      (distributionRegularization u ρ ⋆[ContinuousLinearMap.mul ℂ ℂ, volume]
        distributionRegularization v σ) y =
      distributionRegularization w κ y := by
    simpa [regularizedFunction, RieszEuclidean.TitchmarshFunctionAlgebra.coe_convolution,
      RieszEuclidean.TitchmarshFunctionAlgebra.convolution] using
      (hc.regularizedConvolution_identity hu hv ρ σ hρ hσ y)
  have hw : CompactlySupportedDistribution w := hc.compactlySupported hu hv
  rw [show (distributionRegularization u ρ ⋆[ContinuousLinearMap.mul ℂ ℂ, volume]
      distributionRegularization v σ) = distributionRegularization w κ from funext hidentity]
  exact (distributionRegularization_tsupport_subset hw hκcompact).trans
    (by simpa [add_assoc] using Set.add_subset_add_left hκsupport)

end RieszEuclidean.CompleteMinimal
