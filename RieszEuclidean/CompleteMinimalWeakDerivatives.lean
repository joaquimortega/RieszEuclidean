import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.MeasureTheory.Integral.DivergenceTheorem

noncomputable section

open MeasureTheory Measure Module Topology Filter Set

namespace RieszEuclidean.CompleteMinimal

/-- The integral of an integrable derivative of an integrable continuous function
vanishes even when the derivative has countably many exceptional points. -/
theorem integral_eq_zero_of_hasDerivAt_off_countable
    {f f' : ℝ → ℂ} {S : Set ℝ} (hS : S.Countable) (hf : Continuous f)
    (hderiv : ∀ x ∉ S, HasDerivAt f (f' x) x)
    (hf' : Integrable f') (hfi : Integrable f) : ∫ x, f' x = 0 := by
  have hFTC (a b : ℝ) : ∫ x in a..b, f' x = f b - f a :=
    integral_eq_of_hasDerivWithinAt_off_countable f f' hS hf.continuousOn
      (fun x hx => hderiv x hx.2) hf'.intervalIntegrable
  let T : ℂ := (∫ x in Ioi (0 : ℝ), f' x) + f 0
  let B : ℂ := f 0 - (∫ x in Iic (0 : ℝ), f' x)
  have htop : Tendsto f atTop (𝓝 T) := by
    have h := (intervalIntegral_tendsto_integral_Ioi 0 hf'.integrableOn
      (tendsto_id : Tendsto (id : ℝ → ℝ) atTop atTop)).add_const (f 0)
    apply h.congr
    intro x
    rw [hFTC]
    simp
  have hbot : Tendsto f atBot (𝓝 B) := by
    have h := (intervalIntegral_tendsto_integral_Iic 0 hf'.integrableOn
      (tendsto_id : Tendsto (id : ℝ → ℝ) atBot atBot)).const_sub (f 0)
    apply h.congr
    intro x
    rw [hFTC]
    abel
  have hT : T = 0 := by
    apply IntegrableAtFilter.eq_zero_of_tendsto
      (show IntegrableAtFilter f atTop volume from ⟨univ, univ_mem, hfi.integrableOn⟩) ?_ htop
    intro s hs
    obtain ⟨b, hb⟩ := mem_atTop_sets.mp hs
    rw [← top_le_iff, ← Real.volume_Ici (a := b)]
    exact measure_mono hb
  have hB : B = 0 := by
    apply IntegrableAtFilter.eq_zero_of_tendsto
      (show IntegrableAtFilter f atBot volume from ⟨univ, univ_mem, hfi.integrableOn⟩) ?_ hbot
    intro s hs
    obtain ⟨b, hb⟩ := mem_atBot_sets.mp hs
    rw [← top_le_iff, ← Real.volume_Iic (a := b)]
    exact measure_mono hb
  have hwhole := intervalIntegral_tendsto_integral hf'
    (tendsto_neg_atTop_atBot : Tendsto (fun x : ℝ => -x) atTop atBot)
    (tendsto_id : Tendsto (id : ℝ → ℝ) atTop atTop)
  have hzero : Tendsto (fun x : ℝ => ∫ t in (-x)..x, f' t) atTop (𝓝 (0 : ℂ)) := by
    have h := htop.sub (hbot.comp tendsto_neg_atTop_atBot)
    rw [hT, hB, sub_zero] at h
    exact h.congr (fun x => (hFTC (-x) x).symm)
  exact tendsto_nhds_unique hwhole hzero

/-- One-dimensional integration by parts with countably many exceptional derivative
points. Continuity excludes jumps at those points. -/
theorem integral_mul_hasDerivAt_off_countable_eq_neg_left
    {f f' g g' : ℝ → ℂ} {S : Set ℝ} (hS : S.Countable)
    (hf : Continuous f) (hg : Continuous g)
    (hderiv : ∀ x ∉ S, HasDerivAt f (f' x) x)
    (hgderiv : ∀ x, HasDerivAt g (g' x) x)
    (hfg' : Integrable (fun x => f x * g' x))
    (hf'g : Integrable (fun x => f' x * g x))
    (hfg : Integrable (fun x => f x * g x)) :
    ∫ x, f x * g' x = - ∫ x, f' x * g x := by
  have hzero := integral_eq_zero_of_hasDerivAt_off_countable hS (hf.mul hg)
    (fun x hx => (hderiv x hx).mul (hgderiv x)) (hf'g.add hfg') hfg
  rw [integral_add hf'g hfg'] at hzero
  exact eq_neg_of_add_eq_zero_right hzero

/-- The product-space Fubini step for the exceptional-line integration by parts. -/
theorem integral_mul_hasDerivAt_off_countable_prod
    {E : Type*} [MeasurableSpace E] {μ : Measure E} [SigmaFinite μ]
    {f f' g g' : E × ℝ → ℂ}
    (hf'g : Integrable (fun x => f' x * g x) (μ.prod volume))
    (hfg' : Integrable (fun x => f x * g' x) (μ.prod volume))
    (hfg : Integrable (fun x => f x * g x) (μ.prod volume))
    (hf : ∀ x, Continuous (fun t => f (x, t)))
    (hg : ∀ x, Continuous (fun t => g (x, t)))
    (hderiv : ∀ x, ∃ S : Set ℝ, S.Countable ∧
      ∀ t ∉ S, HasDerivAt (fun t => f (x, t)) (f' (x, t)) t)
    (hgderiv : ∀ x t, HasDerivAt (fun t => g (x, t)) (g' (x, t)) t) :
    ∫ x, f x * g' x ∂μ.prod volume = - ∫ x, f' x * g x ∂μ.prod volume := by
  rw [integral_prod _ hfg', integral_prod _ hf'g, ← integral_neg]
  apply integral_congr_ae
  filter_upwards [hf'g.prod_right_ae, hfg'.prod_right_ae, hfg.prod_right_ae]
    with x hf'gx hfg'x hfgx
  obtain ⟨S, hS, hderivx⟩ := hderiv x
  exact integral_mul_hasDerivAt_off_countable_eq_neg_left hS (hf x) (hg x)
    hderivx (hgderiv x) hfg'x hf'gx hfgx

/-- Product-space integration by parts for an arbitrary Haar measure, allowing
countable exceptional points on every vertical line. -/
theorem integral_mul_hasLineDerivAt_off_countable_prod_haar
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    {μ : Measure (E × ℝ)} [IsAddHaarMeasure μ]
    {f f' g g' : E × ℝ → ℂ} {S : Set (E × ℝ)}
    (hf'g : Integrable (fun x => f' x * g x) μ)
    (hfg' : Integrable (fun x => f x * g' x) μ)
    (hfg : Integrable (fun x => f x * g x) μ)
    (hf : Continuous f) (hg : Continuous g)
    (hS : ∀ x : E × ℝ, {t : ℝ | x + t • (0, 1) ∈ S}.Countable)
    (hderiv : ∀ x ∉ S, HasLineDerivAt ℝ f (f' x) x (0, 1))
    (hgderiv : ∀ x, HasLineDerivAt ℝ g (g' x) x (0, 1)) :
    ∫ x, f x * g' x ∂μ = - ∫ x, f' x * g x ∂μ := by
  let ν : Measure E := addHaar
  have A : ν.prod volume = (addHaarScalarFactor (ν.prod volume) μ) • μ :=
    isAddLeftInvariant_eq_smul _ _
  have Hf'g : Integrable (fun x => f' x * g x) (ν.prod volume) := by
    rw [A]; exact hf'g.smul_measure_nnreal
  have Hfg' : Integrable (fun x => f x * g' x) (ν.prod volume) := by
    rw [A]; exact hfg'.smul_measure_nnreal
  have Hfg : Integrable (fun x => f x * g x) (ν.prod volume) := by
    rw [A]; exact hfg.smul_measure_nnreal
  have H := integral_mul_hasDerivAt_off_countable_prod Hf'g Hfg' Hfg
    (fun x => hf.comp (continuous_const.prodMk continuous_id))
    (fun x => hg.comp (continuous_const.prodMk continuous_id))
    (fun x => ?_) (fun x t => ?_)
  · rw [isAddLeftInvariant_eq_smul μ (ν.prod volume)]
    simp [H]
  · refine ⟨{t : ℝ | (x, (0 : ℝ)) + t • (0, 1) ∈ S}, hS (x, 0), ?_⟩
    intro t ht
    have hnot : (x, t) ∉ S := by simpa using ht
    convert (hderiv (x, t) hnot).scomp_of_eq t
      ((hasDerivAt_id t).add (hasDerivAt_const t (-t))) (by simp) using 1 <;>
      simp [Function.comp_def, add_comm, add_left_comm]
  · convert (hgderiv (x, t)).scomp_of_eq t
      ((hasDerivAt_id t).add (hasDerivAt_const t (-t))) (by simp) using 1 <;>
      simp [Function.comp_def, add_comm, add_left_comm]

/-- Integration by parts along a nonzero direction with countable exceptional points
on each affine line. The differentiated function remains continuous across the
exceptional set, so no boundary distribution is introduced. -/
theorem integral_mul_hasLineDerivAt_off_countable_eq_neg_left
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    {μ : Measure E} [IsAddHaarMeasure μ]
    {f f' g g' : E → ℂ} {S : Set E} {v : E} (hv : v ≠ 0)
    (hf'g : Integrable (fun x => f' x * g x) μ)
    (hfg' : Integrable (fun x => f x * g' x) μ)
    (hfg : Integrable (fun x => f x * g x) μ)
    (hf : Continuous f) (hg : Continuous g)
    (hS : ∀ x : E, {t : ℝ | x + t • v ∈ S}.Countable)
    (hderiv : ∀ x ∉ S, HasLineDerivAt ℝ f (f' x) x v)
    (hgderiv : ∀ x, HasLineDerivAt ℝ g (g' x) x v) :
    ∫ x, f x * g' x ∂μ = - ∫ x, f' x * g x ∂μ := by
  haveI : Nontrivial E := nontrivial_iff.mpr ⟨v, 0, hv⟩
  let n := finrank ℝ E
  let E' := Fin (n - 1) → ℝ
  obtain ⟨L, hLv⟩ : ∃ L : E ≃L[ℝ] (E' × ℝ), L v = (0, 1) := by
    have hdim : finrank ℝ (E' × ℝ) = n := by
      simpa [E'] using Nat.sub_add_cancel (finrank_pos (R := ℝ) (M := E))
    let L₀ : E ≃L[ℝ] (E' × ℝ) := (ContinuousLinearEquiv.ofFinrankEq hdim).symm
    obtain ⟨M, hM⟩ : ∃ M : (E' × ℝ) ≃L[ℝ] (E' × ℝ), M (L₀ v) = (0, 1) := by
      apply SeparatingDual.exists_continuousLinearEquiv_apply_eq
      · simpa using hv
      · simp
    exact ⟨L₀.trans M, by simp [hM]⟩
  let ν := Measure.map L μ
  suffices H : ∫ x : E' × ℝ, f (L.symm x) * g' (L.symm x) ∂ν =
      - ∫ x : E' × ℝ, f' (L.symm x) * g (L.symm x) ∂ν by
    have hmap : μ = Measure.map L.symm ν := by
      simp [ν, Measure.map_map L.symm.continuous.measurable L.continuous.measurable]
    have hemb : IsClosedEmbedding L.symm := L.symm.toHomeomorph.isClosedEmbedding
    simpa [hmap, hemb.integral_map] using H
  have Lemb : MeasurableEmbedding L := L.toHomeomorph.measurableEmbedding
  apply integral_mul_hasLineDerivAt_off_countable_prod_haar
    (S := L.symm ⁻¹' S)
  · simpa [ν, Lemb.integrable_map_iff, Function.comp_def] using hf'g
  · simpa [ν, Lemb.integrable_map_iff, Function.comp_def] using hfg'
  · simpa [ν, Lemb.integrable_map_iff, Function.comp_def] using hfg
  · exact hf.comp L.symm.continuous
  · exact hg.comp L.symm.continuous
  · intro x
    have heq : {t : ℝ | x + t • (0, 1) ∈ L.symm ⁻¹' S} =
        {t : ℝ | L.symm x + t • v ∈ S} := by
      ext t
      simp [← hLv]
    rw [heq]
    exact hS (L.symm x)
  · intro x hx
    have heq : f = (f ∘ L.symm) ∘ (L : E →ₗ[ℝ] (E' × ℝ)) := by ext y; simp
    have h := hderiv (L.symm x) hx
    rw [heq] at h
    convert h.of_comp using 1
    · simp
    · simp [← hLv]
  · intro x
    have heq : g = (g ∘ L.symm) ∘ (L : E →ₗ[ℝ] (E' × ℝ)) := by ext y; simp
    have h := hgderiv (L.symm x)
    rw [heq] at h
    convert h.of_comp using 1
    · simp
    · simp [← hLv]

/-- A smooth test function against a continuous function whose directional derivative
is defined off a set meeting every line in countably many points. -/
theorem integral_mul_fderiv_off_countable_eq_neg_left
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    {μ : Measure E} [IsAddHaarMeasure μ]
    {f f' ψ : E → ℂ} {S : Set E} {v : E} (hv : v ≠ 0)
    (hf'ψ : Integrable (fun x => f' x * ψ x) μ)
    (hfψ' : Integrable (fun x => f x * fderiv ℝ ψ x v) μ)
    (hfψ : Integrable (fun x => f x * ψ x) μ)
    (hf : Continuous f) (hψ : Differentiable ℝ ψ)
    (hS : ∀ x : E, {t : ℝ | x + t • v ∈ S}.Countable)
    (hderiv : ∀ x ∉ S, HasLineDerivAt ℝ f (f' x) x v) :
    ∫ x, f x * fderiv ℝ ψ x v ∂μ = - ∫ x, f' x * ψ x ∂μ :=
  integral_mul_hasLineDerivAt_off_countable_eq_neg_left hv hf'ψ hfψ' hfψ hf hψ.continuous
    hS hderiv (fun x => (hψ x).hasFDerivAt.hasLineDerivAt v)

end RieszEuclidean.CompleteMinimal
