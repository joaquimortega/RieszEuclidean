import RieszEuclidean.CompleteMinimalEntireFourier

/-! Fourier uniqueness for the low part of the directional support argument. -/

noncomputable section
open MeasureTheory Filter Topology

namespace RieszEuclidean.CompleteMinimal

/-- An integrable L² function with zero Fourier integral vanishes almost everywhere. -/
theorem ae_eq_zero_of_fourierIntegral_eq_zero {d : ℕ}
    {f : Euclidean d → ℂ} (hf : Integrable f) (h₂ : MemLp f 2 volume)
    (hF : ∀ ξ, Real.fourierIntegral f ξ = 0) : f =ᵐ[volume] 0 := by
  let u : FullL2 d := h₂.toLp f
  have hu : (u : Euclidean d → ℂ) =ᵐ[volume] f := h₂.coeFn_toLp
  have hui : Integrable (u : Euclidean d → ℂ) := hf.congr hu.symm
  have hFu : ∀ ξ, entireFourier u (realToComplex ξ) = 0 := by
    intro ξ
    rw [entireFourier_congr hu, entireFourier_realToComplex]
    exact hF ξ
  have hzero : fourierL2Equiv d u = 0 := by
    apply Lp.ext
    filter_upwards [entireFourier_eq_fourierL2 u hui, Lp.coeFn_zero ℂ 2 volume]
      with ξ hξ h0
    exact hξ.symm.trans ((hFu ξ).trans h0.symm)
  have huz : u = 0 := by
    apply (fourierL2Equiv d).injective
    simpa using hzero
  exact hu.symm.trans (huz ▸ Lp.coeFn_zero ℂ 2 volume)

/-- Fourier uniqueness upgrades to pointwise uniqueness for continuous compact tests. -/
theorem eq_zero_of_fourierIntegral_eq_zero {d : ℕ}
    {f : Euclidean d → ℂ} (hf : Continuous f) (hc : HasCompactSupport f)
    (hF : ∀ ξ, Real.fourierIntegral f ξ = 0) : f = 0 := by
  exact MeasureTheory.Measure.eq_of_ae_eq
    (ae_eq_zero_of_fourierIntegral_eq_zero (hf.integrable_of_hasCompactSupport hc)
      (hf.memLp_of_hasCompactSupport (p := 2) hc) hF) hf continuous_const

/-- An almost-everywhere vanishing low part forces vanishing on the open halfspace. -/
theorem eq_zero_on_halfspace_of_indicator_ae_eq_zero {d : ℕ}
    {f : Euclidean d → ℂ} (hf : Continuous f)
    (ℓ : Euclidean d →L[ℝ] ℝ) (T : ℝ)
    (hzero : {x | ℓ x < T}.indicator f =ᵐ[volume] 0) :
    ∀ x, ℓ x < T → f x = 0 := by
  have hU : IsOpen {x | ℓ x < T} := isOpen_lt ℓ.continuous continuous_const
  have hae : f =ᵐ[volume.restrict {x | ℓ x < T}] 0 := by
    apply (ae_restrict_iff' hU.measurableSet).mpr
    filter_upwards [hzero] with x hx hmem
    change {x | ℓ x < T}.indicator f x = 0 at hx
    rw [Set.indicator_of_mem (show x ∈ {x | ℓ x < T} from hmem)] at hx
    exact hx
  exact MeasureTheory.Measure.eqOn_open_of_ae_eq hae hU hf.continuousOn
    continuous_const.continuousOn

end RieszEuclidean.CompleteMinimal
