import RieszEuclidean.CompleteMinimalConvolutionSupport

/-! Local tests and exact support of regular L² distributions. -/

noncomputable section
open MeasureTheory Set SchwartzMap
open scoped SchwartzMap ENNReal

namespace RieszEuclidean.CompleteMinimal

variable {d : ℕ}

set_option maxHeartbeats 800000 in
/-- Distributional local vanishing of an L² function implies actual a.e. vanishing. -/
theorem l2Distribution_ae_zero_on_open {f : FullL2 d} {U : Set (Euclidean d)}
    (hU : IsOpen U)
    (hz : ∀ φ : 𝓢(Euclidean d, ℂ), HasCompactSupport (φ : Euclidean d → ℂ) →
      tsupport (φ : Euclidean d → ℂ) ⊆ U → l2Distribution f φ = 0) :
    ∀ᵐ x, x ∈ U → f x = 0 := by
  refine hU.ae_eq_zero_of_integral_contDiff_smul_eq_zero
    (f := (f : Euclidean d → ℂ))
    (((Lp.memLp f).locallyIntegrable (by norm_num)).locallyIntegrableOn U) ?_
  intro g hg hc hs
  let φ := compactSchwartz (fun x => (g x : ℂ))
    (Complex.ofRealCLM.contDiff.comp hg) (hc.comp_left Complex.ofReal_zero)
  have hsup : tsupport (φ : Euclidean d → ℂ) = tsupport g := by
    change closure (Function.support (fun x => (g x : ℂ))) = closure (Function.support g)
    apply congrArg closure
    exact Set.ext fun x => Complex.ofReal_ne_zero
  have hh := hz φ (hc.comp_left Complex.ofReal_zero) (hsup.symm ▸ hs)
  rw [l2Distribution_apply] at hh
  change (∫ x, f x * (g x : ℂ)) = 0 at hh
  simpa only [Complex.real_smul, mul_comm] using hh

/-- A nonzero a.e. constant on an open set makes every point of that set belong
to the exact distribution support. -/
theorem open_subset_l2Distribution_support_of_const {f : FullL2 d}
    {V : Set (Euclidean d)} (hV : IsOpen V) {c : ℂ} (hc : c ≠ 0)
    (hf : ∀ᵐ x, x ∈ V → f x = c) : V ⊆ distributionSupport (l2Distribution f) := by
  intro x hx
  by_contra hn
  change ¬ ∀ U : Set (Euclidean d), IsOpen U → x ∈ U →
    ∃ φ : 𝓢(Euclidean d, ℂ), HasCompactSupport (φ : Euclidean d → ℂ) ∧
      tsupport (φ : Euclidean d → ℂ) ⊆ U ∧ l2Distribution f φ ≠ 0 at hn
  push_neg at hn
  obtain ⟨U, hU, hxU, hzero⟩ := hn
  have hfae := l2Distribution_ae_zero_on_open hU hzero
  have hmeasure : volume (U ∩ V) = 0 := by
    apply compl_mem_ae_iff.mp
    filter_upwards [hfae, hf] with y hy hconst
    intro hmem
    exact hc ((hconst hmem.2).symm.trans (hy hmem.1))
  exact (hU.inter hV).measure_ne_zero volume ⟨x, hxU, hx⟩ hmeasure

/-- For a closed set, distributional support of an L² function is equivalent to
its actual a.e. vanishing outside the set. -/
theorem l2Distribution_supported_iff {f : FullL2 d} {S : Set (Euclidean d)}
    (hS : IsClosed S) : DistributionSupportedIn (l2Distribution f) S ↔
      ∀ᵐ x, x ∉ S → f x = 0 := by
  constructor
  · intro h
    apply l2Distribution_ae_zero_on_open hS.isOpen_compl
    intro φ hc hs
    apply h φ hc
    exact Set.disjoint_left.mpr fun x hx hxS => (hs hx) hxS
  · exact l2Distribution_supported f S

end RieszEuclidean.CompleteMinimal
