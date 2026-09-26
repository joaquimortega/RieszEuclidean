import RieszEuclidean.CompleteMinimalSpherePolynomial
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.Analysis.NormedSpace.Real

noncomputable section

open Classical MeasureTheory
open scoped ENNReal

namespace RieszEuclidean.CompleteMinimal

open MvPolynomial

/-- The highest-degree homogeneous part of a complex polynomial. -/
def leadingHomogeneousPart {d : ℕ} (p : ComplexPolynomial d) : ComplexPolynomial d :=
  homogeneousComponent p.totalDegree p

/-- A nonzero polynomial has a nonzero leading homogeneous part. -/
theorem leadingHomogeneousPart_ne_zero {d : ℕ} {p : ComplexPolynomial d} (hp : p ≠ 0) :
    leadingHomogeneousPart p ≠ 0 := by
  have hsupport : p.support.Nonempty := Finset.nonempty_iff_ne_empty.mpr
    (fun h => hp (Finsupp.support_eq_empty.mp h))
  obtain ⟨s, hs, hdegree⟩ := Finset.exists_mem_eq_sup p.support hsupport Finsupp.degree
  have hdegree' : s.degree = p.totalDegree := hdegree.symm
  intro hzero
  have hc := congrArg (MvPolynomial.coeff s) hzero
  rw [leadingHomogeneousPart, coeff_homogeneousComponent, if_pos hdegree', coeff_zero] at hc
  exact (mem_support_iff.mp hs) hc

/-- Radial evaluation separates the scalar power of each monomial. -/
theorem polynomialEvaluation_radial_expansion {d : ℕ} (p : ComplexPolynomial d)
    (r : ℝ) (θ : RealPoint d) :
    polynomialEvaluation (r • θ) p =
      ∑ s ∈ p.support, (p.coeff s * ∏ i ∈ s.support, (θ i : ℂ) ^ s i) * (r : ℂ) ^ s.degree := by
  rw [polynomialEvaluation_apply, eval_eq]
  apply Finset.sum_congr rfl
  intro s _
  simp only [PiLp.smul_apply, smul_eq_mul, Complex.ofReal_mul, mul_pow,
    Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, Finsupp.degree]
  ring

/-- A homogeneous polynomial scales by its homogeneous degree on a real ray. -/
theorem polynomialEvaluation_homogeneous_smul {d m : ℕ} (p : ComplexPolynomial d)
    (hp : p.IsHomogeneous m) (r : ℝ) (θ : RealPoint d) :
    polynomialEvaluation (r • θ) p = (r : ℂ) ^ m * polynomialEvaluation θ p := by
  rw [polynomialEvaluation_radial_expansion, polynomialEvaluation_apply, eval_eq, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s hs
  have hdegree : s.degree = m := by
    by_contra hn
    exact (mem_support_iff.mp hs) (hp.coeff_eq_zero hn)
  rw [hdegree]
  ring

/-- Remove the leading homogeneous part and the degree decreases by at least one. -/
theorem remainder_totalDegree_le {d : ℕ} (p : ComplexPolynomial d) :
    (p - leadingHomogeneousPart p).totalDegree ≤ p.totalDegree - 1 := by
  rw [totalDegree, Finset.sup_le_iff]
  intro s hs
  have hcoeff : (p - leadingHomogeneousPart p).coeff s ≠ 0 := mem_support_iff.mp hs
  have hdegree : s.degree ≠ p.totalDegree := by
    intro hd
    apply hcoeff
    simp [leadingHomogeneousPart, coeff_homogeneousComponent, hd]
  have hcoeffp : p.coeff s ≠ 0 := by
    simpa only [coeff_sub, leadingHomogeneousPart, coeff_homogeneousComponent,
      if_neg hdegree, sub_zero] using hcoeff
  have hle : s.degree ≤ p.totalDegree := le_totalDegree (mem_support_iff.mpr hcoeffp)
  change s.degree ≤ p.totalDegree - 1
  omega

/-- The sum of coefficient norms controls polynomial growth on the unit sphere. -/
def coefficientNormSum {d : ℕ} (p : ComplexPolynomial d) : ℝ :=
  ∑ s ∈ p.support, ‖p.coeff s‖

theorem coefficientNormSum_nonneg {d : ℕ} (p : ComplexPolynomial d) :
    0 ≤ coefficientNormSum p := Finset.sum_nonneg fun _ _ => norm_nonneg _

/-- A uniform upper bound on real rays with bounded coordinates. -/
theorem polynomialEvaluation_radial_norm_le {d : ℕ} (p : ComplexPolynomial d)
    {r : ℝ} (hr : 1 ≤ r) (θ : RealPoint d) (hθ : ∀ i, ‖θ i‖ ≤ 1) :
    ‖polynomialEvaluation (r • θ) p‖ ≤ coefficientNormSum p * r ^ p.totalDegree := by
  rw [polynomialEvaluation_radial_expansion]
  calc
    _ ≤ ∑ s ∈ p.support,
        ‖(p.coeff s * ∏ i ∈ s.support, (θ i : ℂ) ^ s i) * (r : ℂ) ^ s.degree‖ :=
      norm_sum_le _ _
    _ ≤ ∑ s ∈ p.support, ‖p.coeff s‖ * r ^ p.totalDegree := by
      apply Finset.sum_le_sum
      intro s hs
      have hprod : ‖∏ i ∈ s.support, (θ i : ℂ) ^ s i‖ ≤ 1 := by
        rw [norm_prod]
        apply Finset.prod_le_one (fun _ _ => norm_nonneg _)
        intro i _
        simpa only [norm_pow, Complex.norm_real, Real.norm_eq_abs] using
          pow_le_one₀ (n := s i) (norm_nonneg (θ i)) (hθ i)
      simp only [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (zero_le_one.trans hr)]
      have hpow : r ^ s.degree ≤ r ^ p.totalDegree :=
        pow_le_pow_right₀ hr (le_totalDegree hs)
      exact mul_le_mul (mul_le_of_le_one_right (norm_nonneg _) hprod) hpow
        (pow_nonneg (zero_le_one.trans hr) _) (norm_nonneg _)
    _ = coefficientNormSum p * r ^ p.totalDegree := by rw [coefficientNormSum, Finset.sum_mul]

/-- Evaluation of a complex polynomial on the real Euclidean coordinates is continuous. -/
theorem polynomialEvaluation_continuous {d : ℕ} (p : ComplexPolynomial d) :
    Continuous (fun x : RealPoint d => polynomialEvaluation x p) := by
  apply p.continuous_eval.comp
  apply continuous_pi
  intro i
  exact Complex.continuous_ofReal.comp
    ((continuous_apply i).comp (PiLp.continuous_equiv 2 (fun _ : Fin d => ℝ)))

/-- A nonzero real-evaluated homogeneous complex polynomial is nonzero somewhere
on the real unit sphere. -/
theorem homogeneous_exists_unit_evaluation_ne_zero {d m : ℕ} (hd : 1 ≤ d)
    (p : ComplexPolynomial d) (hp : p.IsHomogeneous m) (hpn : p ≠ 0) :
    ∃ θ : RealPoint d, ‖θ‖ = 1 ∧ polynomialEvaluation θ p ≠ 0 := by
  haveI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  obtain ⟨θ₀, hθ₀⟩ := exists_norm_eq (RealPoint d) (by norm_num : (0 : ℝ) ≤ 1)
  by_contra hn
  push_neg at hn
  have hreal : ∀ x : RealPoint d, polynomialEvaluation x p = 0 := by
    intro x
    by_cases hx : x = 0
    · subst x
      simpa using polynomialEvaluation_homogeneous_smul p hp 0 θ₀
        |>.trans (by rw [hn θ₀ hθ₀, mul_zero])
    · have hnorm : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
      let θ : RealPoint d := ‖x‖⁻¹ • x
      have hθ : ‖θ‖ = 1 := norm_smul_inv_norm (𝕜 := ℝ) hx
      have hxθ : ‖x‖ • θ = x := by
        dsimp [θ]
        rw [smul_smul, mul_inv_cancel₀ hnorm, one_smul]
      rw [← hxθ, polynomialEvaluation_homogeneous_smul p hp, hn θ hθ, mul_zero]
  apply hpn
  apply polynomial_eq_zero_of_real_box p (fun _ => -1) (fun _ => 1) (by intro i; norm_num)
  intro x _hx
  exact hreal ((WithLp.equiv 2 _).symm x)

/-- Uniform leading-term polynomial growth on a nonempty open patch of the real
unit sphere. Both the patch and the constants are produced from the polynomial. -/
theorem polynomial_growth_on_open_sphere_patch {d : ℕ} (hd : 1 ≤ d)
    (p : ComplexPolynomial d) (hp : p ≠ 0) :
    ∃ (U : Set ↥(Metric.sphere (0 : RealPoint d) 1)) (c R : ℝ),
      IsOpen U ∧ U.Nonempty ∧ 0 < c ∧ 1 ≤ R ∧
      ∀ θ ∈ U, ∀ r : ℝ, R ≤ r → c * r ^ p.totalDegree ≤
        ‖polynomialEvaluation (r • θ.val) p‖ := by
  let H := leadingHomogeneousPart p
  have hH : H.IsHomogeneous p.totalDegree := homogeneousComponent_isHomogeneous _ _
  obtain ⟨θ₀, hθ₀, hHθ₀⟩ := homogeneous_exists_unit_evaluation_ne_zero hd H hH
    (leadingHomogeneousPart_ne_zero hp)
  let a := ‖polynomialEvaluation θ₀ H‖
  have ha : 0 < a := norm_pos_iff.mpr hHθ₀
  let U : Set ↥(Metric.sphere (0 : RealPoint d) 1) :=
    {θ | a / 2 < ‖polynomialEvaluation θ.val H‖}
  have hU : IsOpen U := isOpen_lt continuous_const
    (((polynomialEvaluation_continuous H).comp continuous_subtype_val).norm)
  have hUne : U.Nonempty := ⟨⟨θ₀, mem_sphere_zero_iff_norm.mpr hθ₀⟩, by
    change a / 2 < a
    linarith⟩
  let q := p - H
  let B := coefficientNormSum q
  let R := max 1 (4 * B / a)
  refine ⟨U, a / 4, R, hU, hUne, by positivity, le_max_left _ _, ?_⟩
  intro θ hθ r hr
  have hrone : 1 ≤ r := (le_max_left _ _).trans hr
  have hrzero : 0 ≤ r := zero_le_one.trans hrone
  have hθnorm : ‖θ.val‖ = 1 := mem_sphere_zero_iff_norm.mp θ.property
  have hleadnorm : ‖polynomialEvaluation (r • θ.val) H‖ =
      r ^ p.totalDegree * ‖polynomialEvaluation θ.val H‖ := by
    rw [polynomialEvaluation_homogeneous_smul H hH, norm_mul, norm_pow,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hrzero]
  have hlead : (a / 2) * r ^ p.totalDegree ≤ ‖polynomialEvaluation (r • θ.val) H‖ := by
    rw [hleadnorm]
    rw [mul_comm (a / 2)]
    exact mul_le_mul_of_nonneg_left hθ.le (pow_nonneg hrzero _)
  by_cases hm : p.totalDegree = 0
  · have hpeq : p = H := by
      dsimp [H, leadingHomogeneousPart]
      rw [hm, homogeneousComponent_zero]
      exact totalDegree_eq_zero_iff_eq_C.mp hm
    rw [hpeq] at hlead ⊢
    have hpow : r ^ H.totalDegree ≥ 0 := pow_nonneg hrzero _
    nlinarith
  · have hcoords : ∀ i, ‖θ.val i‖ ≤ 1 := fun i =>
      (PiLp.norm_apply_le θ.val i).trans_eq hθnorm
    have hqnorm := polynomialEvaluation_radial_norm_le q hrone θ.val hcoords
    have hqdegree : q.totalDegree ≤ p.totalDegree - 1 := remainder_totalDegree_le p
    have hqnorm' : ‖polynomialEvaluation (r • θ.val) q‖ ≤ B * r ^ (p.totalDegree - 1) :=
      hqnorm.trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hrone hqdegree)
        (coefficientNormSum_nonneg q))
    have hBr : B ≤ (a / 4) * r := by
      have hRr : 4 * B / a ≤ r := (le_max_right _ _).trans hr
      have hmul := (div_le_iff₀ ha).mp hRr
      nlinarith
    have hpow : r ^ p.totalDegree = r ^ (p.totalDegree - 1) * r := by
      rw [← pow_succ]
      congr 1
      omega
    have hqsmall : ‖polynomialEvaluation (r • θ.val) q‖ ≤ (a / 4) * r ^ p.totalDegree := by
      rw [hpow]
      have hh := mul_le_mul_of_nonneg_right hBr (pow_nonneg hrzero (p.totalDegree - 1))
      nlinarith [hqnorm']
    have htriangle : ‖polynomialEvaluation (r • θ.val) H‖ -
        ‖polynomialEvaluation (r • θ.val) p‖ ≤ ‖polynomialEvaluation (r • θ.val) q‖ := by
      simpa only [q, polynomialEvaluation_apply, map_sub, norm_sub_rev] using
        norm_sub_norm_le (polynomialEvaluation (r • θ.val) H) (polynomialEvaluation (r • θ.val) p)
    linarith

/-- Every nonempty open real sphere patch has positive polar surface measure. -/
theorem open_sphere_patch_measure_pos {d : ℕ} (hd : 1 ≤ d)
    (U : Set ↥(Metric.sphere (0 : RealPoint d) 1)) (hU : IsOpen U) (hne : U.Nonempty) :
    0 < (volume : Measure (RealPoint d)).toSphere U := by
  haveI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  let oneRadius : Set.Ioi (0 : ℝ) := ⟨(1 : ℝ), by norm_num⟩
  let W := (homeomorphUnitSphereProd (RealPoint d)) ⁻¹' (U ×ˢ Set.Iio oneRadius)
  have hW : IsOpen W := (hU.prod isOpen_Iio).preimage (homeomorphUnitSphereProd _).continuous
  have hcone : IsOpen (((↑) : ({0}ᶜ : Set (RealPoint d)) → RealPoint d) '' W) :=
    (isClosed_singleton.isOpen_compl.isOpenMap_subtype_val _ hW)
  obtain ⟨θ, hθ⟩ := hne
  let halfRadius : Set.Ioi (0 : ℝ) := ⟨1 / 2, by norm_num⟩
  have hconene : (((↑) : ({0}ᶜ : Set (RealPoint d)) → RealPoint d) '' W).Nonempty := by
    refine ⟨((homeomorphUnitSphereProd (RealPoint d)).symm (θ, halfRadius)).val, ?_⟩
    refine ⟨_, ?_, rfl⟩
    change homeomorphUnitSphereProd _ ((homeomorphUnitSphereProd _).symm (θ, halfRadius)) ∈
      U ×ˢ Set.Iio oneRadius
    rw [Homeomorph.apply_symm_apply]
    exact ⟨hθ, by norm_num [halfRadius, oneRadius]⟩
  have hvol := hcone.measure_pos volume hconene
  rw [(volume : Measure (RealPoint d)).toSphere_apply' hU.measurableSet]
  have haux := (volume : Measure (RealPoint d)).toSphere_apply_aux U oneRadius
  change volume (((↑) : ({0}ᶜ : Set (RealPoint d)) → RealPoint d) '' W) = _ at haux
  rw [← haux]
  exact ENNReal.mul_pos (by simpa using
    (Nat.cast_ne_zero.mpr (by omega : d ≠ 0) : (d : ENNReal) ≠ 0)) hvol.ne'

/-- A continuous function cannot belong to L² if its polar squared norm, including
the Jacobian, stays positive on a positive-measure angular patch and infinitely
much radial Lebesgue measure. -/
theorem not_memLp_of_polar_square_lower_bound {d : ℕ}
    (F : RealPoint d → ℂ) (hF : Continuous F)
    (U : Set ↥(Metric.sphere (0 : RealPoint d) 1))
    (hUpos : 0 < (volume : Measure (RealPoint d)).toSphere U)
    (G : Set ℝ) (hG : MeasurableSet G) (hGpositive : G ⊆ Set.Ioi 0)
    (hGinfinite : volume G = ⊤) (c : ℝ) (hc : 0 < c)
    (hlower : ∀ θ ∈ U, ∀ r ∈ G,
      c ≤ ‖F (r • θ.val)‖ ^ 2 * r ^ (d - 1)) : ¬ MemLp F 2 volume := by
  intro hmem
  let μθ := (volume : Measure (RealPoint d)).toSphere
  let μr := (volume : Measure ℝ).comap (Subtype.val : Set.Ioi (0 : ℝ) → ℝ)
  let f : ↥(Metric.sphere (0 : RealPoint d) 1) × Set.Ioi (0 : ℝ) → ℝ≥0∞ :=
    fun z => ENNReal.ofReal (‖F (z.2.val • z.1.val)‖ ^ 2)
  have hf : Measurable f := by dsimp [f]; fun_prop
  have hsquare : Integrable (fun x => ‖F x‖ ^ 2) volume :=
    hmem.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
  have hfull : (∫⁻ x, ENNReal.ofReal (‖F x‖ ^ 2) ∂volume) < ⊤ := by
    simpa only [HasFiniteIntegral, Real.enorm_eq_ofReal_abs, abs_sq] using hsquare.hasFiniteIntegral
  have hpolar : (∫⁻ z, f z ∂μθ.prod (Measure.volumeIoiPow (d - 1))) =
      ∫⁻ x : ({0}ᶜ : Set (RealPoint d)), ENNReal.ofReal (‖F x.val‖ ^ 2)
        ∂(volume.comap Subtype.val) := by
    have h := (volume : Measure (RealPoint d)).measurePreserving_homeomorphUnitSphereProd
      |>.lintegral_comp_emb (homeomorphUnitSphereProd _).measurableEmbedding f
    rw [finrank_euclideanSpace_fin] at h
    rw [← h]
    apply lintegral_congr
    intro x
    change ENNReal.ofReal (‖F ((homeomorphUnitSphereProd _).symm
      (homeomorphUnitSphereProd _ x)).val‖ ^ 2) = _
    rw [Homeomorph.symm_apply_apply]
  have htotal : (∫⁻ z, f z ∂μθ.prod (Measure.volumeIoiPow (d - 1))) < ⊤ := by
    rw [hpolar, lintegral_subtype_comap (measurableSet_singleton _).compl
      (fun x => ENNReal.ofReal (‖F x‖ ^ 2))]
    exact (lintegral_mono' Measure.restrict_le_self le_rfl).trans_lt hfull
  have hiter : (∫⁻ θ, ∫⁻ r, f (θ, r) ∂Measure.volumeIoiPow (d - 1) ∂μθ) < ⊤ := by
    rw [← lintegral_prod _ hf.aemeasurable]
    exact htotal
  have hae := ae_lt_top hf.lintegral_prod_right' hiter.ne
  obtain ⟨θ, hθ, hθfinite⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hUpos.ne'
    (hae.filter_mono (ae_mono (Measure.restrict_le_self (s := U))))
  let G' : Set (Set.Ioi (0 : ℝ)) := Subtype.val ⁻¹' G
  have hG' : MeasurableSet G' := hG.preimage measurable_subtype_coe
  have hG'infinite : μr G' = ⊤ := by
    dsimp [μr]
    rw [comap_subtype_coe_apply measurableSet_Ioi]
    have himage : Subtype.val '' G' = G := by
      ext r
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact hx
      · intro hr
        exact ⟨⟨r, hGpositive hr⟩, hr, rfl⟩
    rw [himage, hGinfinite]
  have hradial : (∫⁻ r, f (θ, r) ∂Measure.volumeIoiPow (d - 1)) = ⊤ := by
    rw [Measure.volumeIoiPow]
    rw [lintegral_withDensity_eq_lintegral_mul _ (by fun_prop)
      (show Measurable (fun r => f (θ, r)) from hf.comp measurable_prodMk_left)]
    have hbound : (∫⁻ r, G'.indicator (fun _ => ENNReal.ofReal c) r ∂μr) ≤
        ∫⁻ r, ENNReal.ofReal (r.val ^ (d - 1)) * f (θ, r) ∂μr := by
      apply lintegral_mono
      intro r
      by_cases hr : r ∈ G'
      · rw [Set.indicator_of_mem hr]
        change ENNReal.ofReal c ≤ ENNReal.ofReal (r.val ^ (d - 1)) *
          ENNReal.ofReal (‖F (r.val • θ.val)‖ ^ 2)
        rw [← ENNReal.ofReal_mul (pow_nonneg r.property.le _)]
        apply ENNReal.ofReal_le_ofReal
        simpa only [mul_comm] using hlower θ hθ r.val hr
      · rw [Set.indicator_of_not_mem hr]
        exact zero_le _
    have hleft : (∫⁻ r, G'.indicator (fun _ => ENNReal.ofReal c) r ∂μr) = ⊤ := by
      rw [lintegral_indicator_const hG', hG'infinite, ENNReal.mul_top]
      exact (ENNReal.ofReal_pos.mpr hc).ne'
    exact top_unique (hleft ▸ hbound)
  exact hθfinite.ne hradial

/-- A radial square lower bound recurring arbitrarily far out on a set of infinite
radial Lebesgue measure. This is the explicit analytic input for the L² obstruction. -/
def RecurringRadialSquareLowerBound {d : ℕ} (M : RealPoint d → ℂ) (exponent : ℕ) : Prop :=
  ∃ a : ℝ, 0 < a ∧ ∀ R : ℝ, ∃ G : Set ℝ,
    MeasurableSet G ∧ volume G = ⊤ ∧
    (∀ r ∈ G, R ≤ r ∧ 1 ≤ r) ∧
    ∀ θ : ↥(Metric.sphere (0 : RealPoint d) 1), ∀ r ∈ G,
      a ≤ ‖M (r • θ.val)‖ ^ 2 * r ^ exponent

/-- Multiplying a polynomial of excessive degree by a multiplier with the stated
recurring radial decay prevents L² integrability, by the genuine polar measure. -/
theorem polynomial_totalDegree_le_of_memLp_multiplier {d : ℕ} (hd : 1 ≤ d)
    (N : ℕ) (p : ComplexPolynomial d) (F M : RealPoint d → ℂ)
    (hF : Continuous F) (hfactor : ∀ x, F x = polynomialEvaluation x p * M x)
    (hlower : RecurringRadialSquareLowerBound M (4 * N + d + 1))
    (hmem : MemLp F 2 volume) : p.totalDegree ≤ 2 * N := by
  by_contra hdegree
  have hm : 2 * N < p.totalDegree := by omega
  have hp : p ≠ 0 := by intro hp; simp [hp] at hm
  obtain ⟨U, c, R, hU, hUne, hc, hR, hgrowth⟩ :=
    polynomial_growth_on_open_sphere_patch hd p hp
  obtain ⟨a, ha, hrec⟩ := hlower
  obtain ⟨G, hG, hGinf, hGr, hrad⟩ := hrec R
  apply not_memLp_of_polar_square_lower_bound F hF U
    (open_sphere_patch_measure_pos hd U hU hUne) G hG
    (fun r hr => lt_of_lt_of_le zero_lt_one (hGr r hr).2) hGinf (c ^ 2 * a)
    (mul_pos (sq_pos_of_pos hc) ha) ?_ hmem
  intro θ hθ r hr
  have hr1 := (hGr r hr).2
  have hpbound := hgrowth θ hθ r (hGr r hr).1
  have hpow : r ^ (4 * N + d + 1) ≤ r ^ (p.totalDegree + p.totalDegree + (d - 1)) :=
    pow_le_pow_right₀ hr1 (by omega)
  calc
    c ^ 2 * a ≤ c ^ 2 * (‖M (r • θ.val)‖ ^ 2 * r ^ (4 * N + d + 1)) :=
      mul_le_mul_of_nonneg_left (hrad θ r hr) (sq_nonneg c)
    _ ≤ c ^ 2 * (‖M (r • θ.val)‖ ^ 2 *
        r ^ (p.totalDegree + p.totalDegree + (d - 1))) := by gcongr
    _ = ‖M (r • θ.val)‖ ^ 2 * (c * r ^ p.totalDegree) ^ 2 * r ^ (d - 1) := by
      simp only [pow_add, mul_pow, pow_two]
      ring
    _ ≤ ‖M (r • θ.val)‖ ^ 2 * ‖polynomialEvaluation (r • θ.val) p‖ ^ 2 *
        r ^ (d - 1) := by gcongr
    _ = ‖F (r • θ.val)‖ ^ 2 * r ^ (d - 1) := by
      rw [hfactor, norm_mul, mul_pow]
      ring

/-- A kernel lower bound and the polynomial denominator upper bound imply the
radial multiplier estimate used in the degree obstruction. -/
theorem recurringRadialSquareLowerBound_of_kernel_denominator {d : ℕ} (N : ℕ)
    (M κ Q : RealPoint d → ℂ) (hfactor : ∀ x, M x * Q x = κ x)
    (hκ : RecurringRadialSquareLowerBound κ (d + 1))
    (C : ℝ) (hC : 0 < C)
    (hQ : ∀ θ : ↥(Metric.sphere (0 : RealPoint d) 1), ∀ r : ℝ,
      1 ≤ r → ‖Q (r • θ.val)‖ ^ 2 ≤ C * r ^ (4 * N)) :
    RecurringRadialSquareLowerBound M (4 * N + d + 1) := by
  obtain ⟨a, ha, hrec⟩ := hκ
  refine ⟨a / C, div_pos ha hC, fun R => ?_⟩
  obtain ⟨G, hG, hGinf, hGr, hrad⟩ := hrec R
  refine ⟨G, hG, hGinf, hGr, ?_⟩
  intro θ r hr
  apply (div_le_iff₀ hC).mpr
  have hr0 : 0 ≤ r := le_trans zero_le_one (hGr r hr).2
  calc
    a ≤ ‖κ (r • θ.val)‖ ^ 2 * r ^ (d + 1) := hrad θ r hr
    _ = ‖M (r • θ.val)‖ ^ 2 * ‖Q (r • θ.val)‖ ^ 2 * r ^ (d + 1) := by
      rw [← hfactor, norm_mul, mul_pow]
    _ ≤ ‖M (r • θ.val)‖ ^ 2 * (C * r ^ (4 * N)) * r ^ (d + 1) := by
      gcongr
      exact hQ θ r (hGr r hr).2
    _ = ‖M (r • θ.val)‖ ^ 2 * r ^ (4 * N + d + 1) * C := by
      rw [show 4 * N + d + 1 = 4 * N + (d + 1) by omega, pow_add]
      ring

/-- Fixed positive-length separated intervals give the infinite radial measure
in the lower-bound interface; no radial divergence is assumed. -/
theorem recurringRadialSquareLowerBound_of_intervals {d : ℕ}
    (M : RealPoint d → ℂ) (exponent : ℕ) (a δ : ℝ) (ha : 0 < a) (hδ : 0 < δ)
    (s : ℕ → ℝ) (hgap : ∀ k, s k + δ ≤ s (k + 1))
    (hunbounded : ∀ R : ℝ, ∃ k, R ≤ s k)
    (hlower : ∀ k, ∀ θ : ↥(Metric.sphere (0 : RealPoint d) 1), ∀ r,
      r ∈ Set.Ioc (s k) (s k + δ) → a ≤ ‖M (r • θ.val)‖ ^ 2 * r ^ exponent) :
    RecurringRadialSquareLowerBound M exponent := by
  have hsmono : Monotone s := monotone_nat_of_le_succ fun k => by linarith [hgap k]
  refine ⟨a, ha, fun R => ?_⟩
  obtain ⟨K, hK⟩ := hunbounded (max R 1)
  let G := ⋃ k : ℕ, Set.Ioc (s (k + K)) (s (k + K) + δ)
  have hdisjoint : Pairwise (fun i j : ℕ =>
      Disjoint (Set.Ioc (s (i + K)) (s (i + K) + δ))
        (Set.Ioc (s (j + K)) (s (j + K) + δ))) := by
    intro i j hij
    rcases lt_or_gt_of_ne hij with h | h
    · exact Set.Ioc_disjoint_Ioc_of_le
        ((hgap (i + K)).trans (hsmono (by omega)))
    · exact (Set.Ioc_disjoint_Ioc_of_le
        ((hgap (j + K)).trans (hsmono (by omega)))).symm
  have hGinf : volume G = ⊤ := by
    rw [show G = ⋃ k : ℕ, Set.Ioc (s (k + K)) (s (k + K) + δ) from rfl,
      measure_iUnion hdisjoint (fun _ => measurableSet_Ioc)]
    simp only [Real.volume_Ioc, add_sub_cancel_left]
    exact ENNReal.tsum_const_eq_top_of_ne_zero (ENNReal.ofReal_pos.mpr hδ).ne'
  refine ⟨G, MeasurableSet.iUnion (fun _ => measurableSet_Ioc), hGinf, ?_, ?_⟩
  · intro r hr
    obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hr
    have hkr : max R 1 ≤ r := hK.trans ((hsmono (by omega : K ≤ k + K)).trans hk.1.le)
    exact ⟨(le_max_left R 1).trans hkr, (le_max_right R 1).trans hkr⟩
  · intro θ r hr
    obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hr
    exact hlower (k + K) θ r hk

/-- Every denominator polynomial of degree at most `2N` has the required uniform
square upper bound along all unit rays. -/
theorem polynomial_denominator_radial_square_bound {d : ℕ} (N : ℕ)
    (q : ComplexPolynomial d) (hdegree : q.totalDegree ≤ 2 * N) :
    ∃ C : ℝ, 0 < C ∧ ∀ θ : ↥(Metric.sphere (0 : RealPoint d) 1), ∀ r : ℝ,
      1 ≤ r → ‖polynomialEvaluation (r • θ.val) q‖ ^ 2 ≤ C * r ^ (4 * N) := by
  let B := coefficientNormSum q
  have hB : 0 ≤ B := coefficientNormSum_nonneg q
  refine ⟨(B + 1) ^ 2, sq_pos_of_pos (by linarith), ?_⟩
  intro θ r hr
  have hθnorm : ‖θ.val‖ = 1 := mem_sphere_zero_iff_norm.mp θ.property
  have hbound := polynomialEvaluation_radial_norm_le q hr θ.val
    (fun i => (PiLp.norm_apply_le θ.val i).trans_eq hθnorm)
  have hbound' : ‖polynomialEvaluation (r • θ.val) q‖ ≤ (B + 1) * r ^ (2 * N) := by
    calc
      _ ≤ B * r ^ q.totalDegree := hbound
      _ ≤ B * r ^ (2 * N) :=
        mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hr hdegree) hB
      _ ≤ (B + 1) * r ^ (2 * N) := by gcongr; linarith
  calc
    _ ≤ ((B + 1) * r ^ (2 * N)) ^ 2 := by gcongr
    _ = (B + 1) ^ 2 * r ^ (4 * N) := by
      rw [mul_pow, ← pow_mul, show 2 * N * 2 = 4 * N by omega]

/-- The cross-multiplied quotient identity, a recurring kernel lower bound, and
an actual polynomial denominator of degree at most `2N` force the numerator degree
bound. Zeros of the denominator require no pointwise division. -/
theorem polynomial_totalDegree_le_of_memLp_quotient {d : ℕ} (hd : 1 ≤ d)
    (N : ℕ) (p q : ComplexPolynomial d) (hqdegree : q.totalDegree ≤ 2 * N)
    (F κ : RealPoint d → ℂ) (hF : Continuous F)
    (hfactor : ∀ x, F x * polynomialEvaluation x q = polynomialEvaluation x p * κ x)
    (hκ : RecurringRadialSquareLowerBound κ (d + 1))
    (hmem : MemLp F 2 volume) : p.totalDegree ≤ 2 * N := by
  by_contra hdegree
  have hm : 2 * N < p.totalDegree := by omega
  have hp : p ≠ 0 := by intro hp; simp [hp] at hm
  obtain ⟨U, c, R, hU, hUne, hc, hR, hgrowth⟩ :=
    polynomial_growth_on_open_sphere_patch hd p hp
  obtain ⟨a, ha, hrec⟩ := hκ
  obtain ⟨G, hG, hGinf, hGr, hrad⟩ := hrec R
  obtain ⟨C, hC, hQ⟩ := polynomial_denominator_radial_square_bound N q hqdegree
  apply not_memLp_of_polar_square_lower_bound F hF U
    (open_sphere_patch_measure_pos hd U hU hUne) G hG
    (fun r hr => lt_of_lt_of_le zero_lt_one (hGr r hr).2) hGinf (c ^ 2 * a / C)
    (div_pos (mul_pos (sq_pos_of_pos hc) ha) hC) ?_ hmem
  intro θ hθ r hr
  have hr1 := (hGr r hr).2
  have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hr1
  have hpbound := hgrowth θ hθ r (hGr r hr).1
  have hpow : r ^ (4 * N + d + 1) ≤ r ^ (p.totalDegree + p.totalDegree + (d - 1)) :=
    pow_le_pow_right₀ hr1 (by omega)
  have hid : ‖F (r • θ.val)‖ ^ 2 * ‖polynomialEvaluation (r • θ.val) q‖ ^ 2 =
      ‖polynomialEvaluation (r • θ.val) p‖ ^ 2 * ‖κ (r • θ.val)‖ ^ 2 := by
    have h := congrArg (fun z : ℂ => ‖z‖) (hfactor (r • θ.val))
    simp only [norm_mul] at h
    calc
      _ = (‖F (r • θ.val)‖ * ‖polynomialEvaluation (r • θ.val) q‖) ^ 2 := by ring
      _ = (‖polynomialEvaluation (r • θ.val) p‖ * ‖κ (r • θ.val)‖) ^ 2 := by rw [h]
      _ = _ := by ring
  have hbound : (c ^ 2 * a) * r ^ (p.totalDegree + p.totalDegree) ≤
      (‖F (r • θ.val)‖ ^ 2 * r ^ (d - 1) * C) *
        r ^ (p.totalDegree + p.totalDegree) := by
    calc
      _ = (c * r ^ p.totalDegree) ^ 2 * a := by
        simp only [pow_add, mul_pow, pow_two]; ring
      _ ≤ (c * r ^ p.totalDegree) ^ 2 * (‖κ (r • θ.val)‖ ^ 2 * r ^ (d + 1)) := by
        gcongr
        exact hrad θ r hr
      _ ≤ ‖polynomialEvaluation (r • θ.val) p‖ ^ 2 *
          (‖κ (r • θ.val)‖ ^ 2 * r ^ (d + 1)) := by gcongr
      _ = (‖F (r • θ.val)‖ ^ 2 * ‖polynomialEvaluation (r • θ.val) q‖ ^ 2) *
          r ^ (d + 1) := by rw [hid]; ring
      _ ≤ (‖F (r • θ.val)‖ ^ 2 * (C * r ^ (4 * N))) * r ^ (d + 1) := by
        gcongr
        exact hQ θ r hr1
      _ = ‖F (r • θ.val)‖ ^ 2 * C * r ^ (4 * N + d + 1) := by
        rw [show 4 * N + d + 1 = 4 * N + (d + 1) by omega, pow_add]; ring
      _ ≤ ‖F (r • θ.val)‖ ^ 2 * C * r ^ (p.totalDegree + p.totalDegree + (d - 1)) := by
        gcongr
      _ = _ := by rw [pow_add]; ring
  exact (div_le_iff₀ hC).mpr ((mul_le_mul_right (pow_pos hrpos _)).mp hbound)

end RieszEuclidean.CompleteMinimal
