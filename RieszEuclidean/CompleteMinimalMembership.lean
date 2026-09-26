import RieszEuclidean.CompleteMinimalRegularSupport
import RieszEuclidean.CompleteMinimalRestriction
import RieszEuclidean.CompleteMinimalDifferentialOperators
import RieszEuclidean.CompleteMinimalPolynomialGrowth
import RieszEuclidean.CompleteMinimalInterpolationFunctions
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.LinearAlgebra.Lagrange

/-!
# Supported L² synthesis from actual tempered distributions

This file converts physical distribution support and quantitative Fourier decay
into actual domain L² vectors. The hypotheses concern an inverse distribution
and its Fourier action on tests, rather than Paley–Wiener membership.
-/

noncomputable section
open MeasureTheory Set SchwartzMap
open scoped SchwartzMap FourierTransform ENNReal

namespace RieszEuclidean.CompleteMinimal

variable {d : ℕ}

/-- Actual polynomial evaluation has a global bound with its total degree and
the explicit sum of its coefficient norms. -/
theorem polynomialEvaluation_norm_le (p : ComplexPolynomial d) (x : Euclidean d) :
    ‖polynomialEvaluation x p‖ ≤ coefficientNormSum p * (1 + ‖x‖) ^ p.totalDegree := by
  let r : ℝ := 1 + ‖x‖
  have hr : 0 < r := by dsimp [r]; positivity
  let θ : Euclidean d := r⁻¹ • x
  have hθ : ∀ i, ‖θ i‖ ≤ 1 := by
    intro i
    calc
      ‖θ i‖ ≤ ‖θ‖ := PiLp.norm_apply_le θ i
      _ = ‖x‖ / r := by
        simp only [θ, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hr,
          div_eq_mul_inv]
        ring
      _ ≤ 1 := (div_le_one hr).mpr (by dsimp [r]; linarith)
  have hx : r • θ = x := by simp [θ, smul_smul, mul_inv_cancel₀ hr.ne']
  have hrone : 1 ≤ r := by dsimp [r]; linarith [norm_nonneg x]
  have h := polynomialEvaluation_radial_norm_le p hrone θ hθ
  simpa only [hx, r] using h

/-- Polynomial numerators consume exactly their degree of decay, leaving the
sharp ball-transform bound when the denominator supplies enough decay. -/
theorem polynomial_mul_ball_decay {M : ℕ} (p : ComplexPolynomial d)
    (hp : p.totalDegree ≤ M) (G : Euclidean d → ℂ) {C : ℝ}
    (hG : ∀ x, ‖G x‖ ≤ C * (1 + ‖x‖) ^ (-(M : ℝ) - ((d : ℝ) + 1) / 2)) :
    ∀ x, ‖polynomialEvaluation x p * G x‖ ≤
      (coefficientNormSum p * C) * (1 + ‖x‖) ^ (-((d : ℝ) + 1) / 2) := by
  intro x
  have hrone : 1 ≤ 1 + ‖x‖ := by linarith [norm_nonneg x]
  have hpoly : ‖polynomialEvaluation x p‖ ≤ coefficientNormSum p * (1 + ‖x‖) ^ M :=
    (polynomialEvaluation_norm_le p x).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hrone hp)
        (coefficientNormSum_nonneg p))
  calc
    _ = ‖polynomialEvaluation x p‖ * ‖G x‖ := norm_mul _ _
    _ ≤ (coefficientNormSum p * (1 + ‖x‖) ^ M) *
        (C * (1 + ‖x‖) ^ (-(M : ℝ) - ((d : ℝ) + 1) / 2)) :=
      mul_le_mul hpoly (hG x) (norm_nonneg _)
        (mul_nonneg (coefficientNormSum_nonneg p) (by positivity))
    _ = _ := by
      rw [← Real.rpow_natCast]
      calc
        _ = (coefficientNormSum p * C) * ((1 + ‖x‖) ^ (M : ℝ) *
            (1 + ‖x‖) ^ (-(M : ℝ) - ((d : ℝ) + 1) / 2)) := by ring
        _ = _ := by rw [← Real.rpow_add (by positivity)]; congr 2; ring

/-- An actual supported inverse distribution whose Fourier transform is an L²
distribution is the distribution of the Plancherel inverse, with the same support. -/
theorem supported_inverse_of_l2_fourier {S : Set (Euclidean d)} (hS : IsClosed S)
    (u : TemperedDistribution d) (hu : DistributionSupportedIn u S)
    (F : FullL2 d) (hF : distributionFourier u = l2Distribution F) :
    u = l2Distribution ((fourierL2Equiv d).symm F) ∧
      ∀ᵐ x, x ∉ S → ((fourierL2Equiv d).symm F) x = 0 := by
  have heq : u = l2Distribution ((fourierL2Equiv d).symm F) := by
    apply distributionFourier_injective
    rw [hF, distributionFourier_l2Distribution, LinearIsometryEquiv.apply_symm_apply]
  exact ⟨heq, (l2Distribution_supported_iff hS).mp (heq ▸ hu)⟩

/-- A measurable Fourier representative is square integrable if its squared
norm has an integrable radial majorant with exponent greater than the dimension. -/
theorem memLp_two_of_radial_sq_bound {F : Euclidean d → ℂ}
    (hF : AEStronglyMeasurable F volume) {C s : ℝ}
    (hs : (d : ℝ) < s)
    (hbound : ∀ᵐ x, ‖F x‖ ^ 2 ≤ C * (1 + ‖x‖) ^ (-s)) :
    MemLp F 2 volume := by
  apply (memLp_two_iff_integrable_sq_norm hF).mpr
  have hint : Integrable (fun x : Euclidean d => (1 + ‖x‖) ^ (-s)) volume :=
    integrable_one_add_norm (by simpa [Euclidean, finrank_euclideanSpace] using hs)
  apply (hint.const_mul C).mono' (hF.norm.pow 2)
  filter_upwards [hbound] with x hx
  change |‖F x‖ ^ 2| ≤ _
  rwa [abs_of_nonneg (sq_nonneg _)]

/-- The usual Fourier decay estimate of order strictly greater than half the
dimension supplies the square-integrability needed by Plancherel synthesis. -/
theorem memLp_two_of_radial_bound {F : Euclidean d → ℂ}
    (hF : AEStronglyMeasurable F volume) {C s : ℝ} (hC : 0 ≤ C)
    (hs : (d : ℝ) < 2 * s)
    (hbound : ∀ᵐ x, ‖F x‖ ≤ C * (1 + ‖x‖) ^ (-s)) :
    MemLp F 2 volume := by
  apply memLp_two_of_radial_sq_bound hF hs (C := C ^ 2)
  filter_upwards [hbound] with x hx
  calc
    ‖F x‖ ^ 2 ≤ (C * (1 + ‖x‖) ^ (-s)) ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hC (Real.rpow_nonneg (by positivity) _))).2 hx
    _ = C ^ 2 * (1 + ‖x‖) ^ (-(2 * s)) := by
      rw [mul_pow, ← Real.rpow_mul_natCast (by positivity : 0 ≤ 1 + ‖x‖)]
      congr 2
      ring

/-- The sharp ball-transform decay left after multiplying by a numerator of
the allowed degree is sufficient in every Euclidean dimension. -/
theorem memLp_two_of_ball_decay {F : Euclidean d → ℂ}
    (hF : AEStronglyMeasurable F volume) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ᵐ x, ‖F x‖ ≤ C * (1 + ‖x‖) ^ (-((d : ℝ) + 1) / 2)) :
    MemLp F 2 volume := by
  apply memLp_two_of_radial_bound hF hC (s := ((d : ℝ) + 1) / 2) (by linarith)
  simpa only [neg_div] using hbound

/-- Continuity absorbs the bounded-frequency region into a global radial
bound, so an asymptotic decay estimate is enough for synthesis. -/
theorem radial_bound_of_tail {F : Euclidean d → ℂ} (hF : Continuous F)
    {C s R : ℝ} (hbound : ∀ x, R ≤ ‖x‖ → ‖F x‖ ≤ C * (1 + ‖x‖) ^ (-s)) :
    ∃ C' : ℝ, 0 ≤ C' ∧ ∀ x, ‖F x‖ ≤ C' * (1 + ‖x‖) ^ (-s) := by
  have hg : Continuous (fun x : Euclidean d => ‖F x‖ * (1 + ‖x‖) ^ s) :=
    hF.norm.mul ((continuous_const.add continuous_norm).rpow_const
      (fun x => Or.inl (by positivity)))
  obtain ⟨B, hB⟩ := (isCompact_closedBall (0 : Euclidean d) R).exists_bound_of_continuousOn
    hg.continuousOn
  refine ⟨max (max B C) 0, le_max_right _ _, fun x => ?_⟩
  by_cases hx : ‖x‖ ≤ R
  · have hb := hB x (by simpa only [Metric.mem_closedBall, dist_zero_right] using hx)
    have hnonneg : 0 ≤ ‖F x‖ * (1 + ‖x‖) ^ s :=
      mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (by positivity) _)
    rw [Real.norm_eq_abs, abs_of_nonneg hnonneg] at hb
    have hmul : ‖F x‖ * (1 + ‖x‖) ^ s ≤ max (max B C) 0 := by
      exact hb.trans ((le_max_left B C).trans (le_max_left _ 0))
    rw [Real.rpow_neg (by positivity : 0 ≤ 1 + ‖x‖), ← div_eq_mul_inv]
    exact (le_div_iff₀ (Real.rpow_pos_of_pos (by positivity) s)).mpr hmul
  · exact (hbound x (le_of_lt (lt_of_not_ge hx))).trans
      (mul_le_mul_of_nonneg_right ((le_max_right B C).trans (le_max_left _ 0))
        (Real.rpow_nonneg (by positivity) _))

/-- An actual continuous Fourier representative with sharp decay at infinity
is square integrable; no bound near its removable poles is required as input. -/
theorem memLp_two_of_ball_decay_tail {F : Euclidean d → ℂ} (hF : Continuous F)
    {C R : ℝ}
    (hbound : ∀ x, R ≤ ‖x‖ → ‖F x‖ ≤ C * (1 + ‖x‖) ^ (-((d : ℝ) + 1) / 2)) :
    MemLp F 2 volume := by
  obtain ⟨C', hC', hb⟩ := radial_bound_of_tail (s := ((d : ℝ) + 1) / 2) hF (by
    simpa only [neg_div] using hbound)
  apply memLp_two_of_ball_decay hF.aestronglyMeasurable hC'
  simpa only [neg_div] using (Filter.Eventually.of_forall hb : ∀ᵐ x ∂volume,
    ‖F x‖ ≤ C' * (1 + ‖x‖) ^ (-(((d : ℝ) + 1) / 2)))

/-- A regular polynomial-growth distribution agrees with its L² embedding
whenever the underlying actual function is also square integrable. -/
theorem polynomialDistribution_eq_l2Distribution {N : ℕ} (F : Euclidean d → ℂ)
    {C : ℝ} (hC : 0 ≤ C) (hbound : ∀ x, ‖F x‖ ≤ C * (1 + ‖x‖) ^ N)
    (hm : AEStronglyMeasurable F volume) (hF : MemLp F 2 volume) :
    polynomialDistribution F hC hbound hm = l2Distribution (hF.toLp F) := by
  ext φ
  rw [polynomialDistribution_apply, l2Distribution_apply]
  apply integral_congr_ae
  filter_upwards [hF.coeFn_toLp] with x hx
  rw [hx]

/-- Restricting an actual supported full-space vector to a measurable domain
containing its support up to a null set preserves its zero extension. -/
theorem domainExtension_restriction_of_supported {S Ω : Set (Euclidean d)}
    (hΩ : MeasurableSet Ω) (hSΩ : S ≤ᵐ[volume] Ω) (f : FullL2 d)
    (hf : ∀ᵐ x, x ∉ S → f x = 0) :
    domainExtension Ω hΩ (domainRestriction Ω f) = f := by
  rw [domainExtension_restriction]
  apply (domainCutoff_eq_self_iff Ω hΩ f).mpr
  filter_upwards [hf, hSΩ] with x hx hinc
  intro hn
  exact hx (fun hs => hn (hinc hs))

/-- Actual supported domain-L² synthesis from a distributional Fourier identity.
The domain may differ from the closed physical support by null sets. -/
theorem exists_domainL2_of_supported_fourier {S Ω : Set (Euclidean d)}
    (hS : IsClosed S) (hΩ : MeasurableSet Ω) (hSΩ : S ≤ᵐ[volume] Ω)
    (u : TemperedDistribution d) (hu : DistributionSupportedIn u S)
    (F : Euclidean d → ℂ) (hF : MemLp F 2 volume)
    (htransform : distributionFourier u = l2Distribution (hF.toLp F)) :
    ∃ f : DomainL2 Ω, SupportedOn Ω f S ∧
      l2Distribution (domainExtension Ω hΩ f) = u ∧
      (fourierL2Equiv d (domainExtension Ω hΩ f) : Euclidean d → ℂ) =ᵐ[volume] F := by
  obtain ⟨huEq, hs⟩ := supported_inverse_of_l2_fourier hS u hu (hF.toLp F) htransform
  let g := (fourierL2Equiv d).symm (hF.toLp F)
  have hext := domainExtension_restriction_of_supported hΩ hSΩ g hs
  refine ⟨domainRestriction Ω g, ?_, ?_, ?_⟩
  · have hsr := hs.filter_mono (ae_mono (Measure.restrict_le_self (s := Ω)))
    filter_upwards [domainRestriction_coe Ω g, hsr] with x hx hz
    intro hn
    exact hx.trans (hz hn)
  · rw [hext]
    exact huEq.symm
  · rw [hext]
    exact ((fourierL2Equiv d).apply_symm_apply (hF.toLp F)) ▸ hF.coeFn_toLp

/-- Quantitative decay and an actual inverse-distribution identity yield a
supported domain vector without any Paley–Wiener membership hypothesis. -/
theorem exists_domainL2_of_supported_fourier_decay {S Ω : Set (Euclidean d)}
    (hS : IsClosed S) (hΩ : MeasurableSet Ω) (hSΩ : S ≤ᵐ[volume] Ω)
    (u : TemperedDistribution d) (hu : DistributionSupportedIn u S)
    (F : Euclidean d → ℂ) (hm : AEStronglyMeasurable F volume)
    {C : ℝ} (hC : 0 ≤ C)
    (hdecay : ∀ᵐ x, ‖F x‖ ≤ C * (1 + ‖x‖) ^ (-((d : ℝ) + 1) / 2))
    (htransform : ∀ φ : 𝓢(Euclidean d, ℂ),
      distributionFourier u φ = ∫ x, F x * φ x) :
    ∃ f : DomainL2 Ω, SupportedOn Ω f S ∧
      l2Distribution (domainExtension Ω hΩ f) = u ∧
      (fourierL2Equiv d (domainExtension Ω hΩ f) : Euclidean d → ℂ) =ᵐ[volume] F := by
  have hF := memLp_two_of_ball_decay hm hC hdecay
  apply exists_domainL2_of_supported_fourier hS hΩ hSΩ u hu F hF
  ext φ
  rw [htransform, l2Distribution_apply]
  apply integral_congr_ae
  filter_upwards [hF.coeFn_toLp] with x hx
  rw [hx]

/-- On a bounded domain the synthesized vector's entire Fourier transform
agrees with any continuous representative at every real frequency. -/
theorem exists_domainL2_of_supported_fourier_continuous {S Ω : Set (Euclidean d)}
    (hS : IsClosed S) (hΩ : MeasurableSet Ω) (hbounded : Bornology.IsBounded Ω)
    (hSΩ : S ≤ᵐ[volume] Ω) (u : TemperedDistribution d)
    (hu : DistributionSupportedIn u S) (F : Euclidean d → ℂ) (hcont : Continuous F)
    (hF : MemLp F 2 volume)
    (htransform : distributionFourier u = l2Distribution (hF.toLp F)) :
    ∃ f : DomainL2 Ω, SupportedOn Ω f S ∧
      l2Distribution (domainExtension Ω hΩ f) = u ∧
      ∀ ξ, domainEntireFourier Ω hΩ f (realToComplex ξ) = F ξ := by
  obtain ⟨f, hs, heq, hFourier⟩ :=
    exists_domainL2_of_supported_fourier hS hΩ hSΩ u hu F hF htransform
  refine ⟨f, hs, heq, fun ξ => congrFun (MeasureTheory.Measure.eq_of_ae_eq
    ((domainEntireFourier_eq_fourierL2 hΩ hbounded f).trans hFourier) ?_ hcont) ξ⟩
  have hemb : Continuous (realToComplex : Euclidean d → ComplexEuclidean d) :=
    (PiLp.continuous_equiv_symm 2 _).comp (continuous_pi fun j => by
      change Continuous (fun x : Euclidean d => (x j : ℂ))
      fun_prop)
  exact (domainEntireFourier_differentiable hΩ hbounded f).continuous.comp hemb

/-- Actual polynomial differentiation of a supported inverse distribution
realizes every numerator whose degree is covered by the denominator decay. -/
theorem exists_domainL2_polynomial_numerator {S Ω : Set (Euclidean d)}
    (hS : IsClosed S) (hΩ : MeasurableSet Ω) (hbounded : Bornology.IsBounded Ω)
    (hSΩ : S ≤ᵐ[volume] Ω) (u : TemperedDistribution d)
    (hu : DistributionSupportedIn u S) (G : Euclidean d → ℂ) (hG : Continuous G)
    {M : ℕ} {C : ℝ} (hC : 0 ≤ C)
    (hdecay : ∀ x, ‖G x‖ ≤ C * (1 + ‖x‖) ^ (-(M : ℝ) - ((d : ℝ) + 1) / 2))
    (htransform : ∀ φ : 𝓢(Euclidean d, ℂ), distributionFourier u φ = ∫ x, G x * φ x)
    (p : ComplexPolynomial d) (hp : p.totalDegree ≤ M) :
    ∃ f : DomainL2 Ω, SupportedOn Ω f S ∧
      l2Distribution (domainExtension Ω hΩ f) = polynomialDifferentialOperator p u ∧
      ∀ ξ, domainEntireFourier Ω hΩ f (realToComplex ξ) = polynomialEvaluation ξ p * G ξ := by
  let F := fun x => polynomialEvaluation x p * G x
  have hcF : Continuous F := (polynomialEvaluation_continuous p).mul hG
  have hmem : MemLp F 2 volume := memLp_two_of_ball_decay hcF.aestronglyMeasurable
    (mul_nonneg (coefficientNormSum_nonneg p) hC)
    (Filter.Eventually.of_forall (polynomial_mul_ball_decay p hp G hdecay))
  apply exists_domainL2_of_supported_fourier_continuous hS hΩ hbounded hSΩ
    (polynomialDifferentialOperator p u) (hu.polynomialDifferentialOperator p) F hcF hmem
  ext φ
  rw [distributionFourier_polynomialDifferentialOperator_integral p u G htransform,
    l2Distribution_apply]
  apply integral_congr_ae
  filter_upwards [hmem.coeFn_toLp] with x hx
  rw [hx]

/-- The numerator synthesis theorem needs denominator decay only outside a
bounded frequency region, because its actual representative is continuous. -/
theorem exists_domainL2_polynomial_numerator_tail {S Ω : Set (Euclidean d)}
    (hS : IsClosed S) (hΩ : MeasurableSet Ω) (hbounded : Bornology.IsBounded Ω)
    (hSΩ : S ≤ᵐ[volume] Ω) (u : TemperedDistribution d)
    (hu : DistributionSupportedIn u S) (G : Euclidean d → ℂ) (hG : Continuous G)
    {M : ℕ} {C R : ℝ}
    (hdecay : ∀ x, R ≤ ‖x‖ →
      ‖G x‖ ≤ C * (1 + ‖x‖) ^ (-(M : ℝ) - ((d : ℝ) + 1) / 2))
    (htransform : ∀ φ : 𝓢(Euclidean d, ℂ), distributionFourier u φ = ∫ x, G x * φ x)
    (p : ComplexPolynomial d) (hp : p.totalDegree ≤ M) :
    ∃ f : DomainL2 Ω, SupportedOn Ω f S ∧
      l2Distribution (domainExtension Ω hΩ f) = polynomialDifferentialOperator p u ∧
      ∀ ξ, domainEntireFourier Ω hΩ f (realToComplex ξ) = polynomialEvaluation ξ p * G ξ := by
  obtain ⟨C', hC', hb⟩ := radial_bound_of_tail
    (s := (M : ℝ) + ((d : ℝ) + 1) / 2) hG (by
      simpa only [neg_add, sub_eq_add_neg] using hdecay)
  apply exists_domainL2_polynomial_numerator hS hΩ hbounded hSΩ u hu G hG hC' _ htransform p hp
  simpa only [neg_add, sub_eq_add_neg] using hb

/-- The coefficient of a simple resolvent in the partial fraction expansion. -/
def resolventWeight {ι : Type*} [DecidableEq ι] (s : Finset ι) (a : ι → ℂ) (i : ι) : ℂ :=
  ∏ j ∈ s.erase i, (a i - a j)⁻¹

/-- The interpolation identity behind partial fractions, proved from the
sum of the actual Lagrange basis polynomials. -/
theorem resolventWeight_identity {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (a : ι → ℂ) (ha : Set.InjOn a s) (hs : s.Nonempty) (q : ℂ) :
    ∑ i ∈ s, resolventWeight s a i * (∏ j ∈ s.erase i, (q - a j)) = 1 := by
  have h := congrArg (Polynomial.eval q) (Lagrange.sum_basis ha hs)
  simpa only [Polynomial.eval_finset_sum, Polynomial.eval_one, Lagrange.basis,
    Polynomial.eval_prod, Lagrange.basisDivisor, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_sub, Polynomial.eval_X,
    resolventWeight, Finset.prod_mul_distrib] using h

/-- Simple distinct poles give the actual scalar partial fraction formula,
at every point away from those poles. -/
theorem resolvent_partial_fractions {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (a : ι → ℂ) (ha : Set.InjOn a s) (hs : s.Nonempty) (q k : ℂ)
    (hq : ∀ i ∈ s, q ≠ a i) :
    k / (∏ i ∈ s, (q - a i)) = ∑ i ∈ s, resolventWeight s a i * (k / (q - a i)) := by
  have hid := resolventWeight_identity s a ha hs q
  calc
    k / (∏ i ∈ s, (q - a i)) =
        (∑ i ∈ s, resolventWeight s a i * (∏ j ∈ s.erase i, (q - a j))) *
          (k / (∏ i ∈ s, (q - a i))) := by rw [hid, one_mul]
    _ = ∑ i ∈ s, resolventWeight s a i * (k / (q - a i)) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      have hex : (∏ j ∈ s.erase i, (q - a j)) ≠ 0 :=
        Finset.prod_ne_zero_iff.mpr fun j hj => sub_ne_zero.mpr (hq j (Finset.mem_of_mem_erase hj))
      rw [← Finset.mul_prod_erase s (fun j => q - a j) hi]
      rw [div_eq_mul_inv, div_eq_mul_inv, mul_inv_rev]
      calc
        _ = resolventWeight s a i * (k * (q - a i)⁻¹) *
            ((∏ j ∈ s.erase i, (q - a j)) * (∏ j ∈ s.erase i, (q - a j))⁻¹) := by ring
        _ = _ := by rw [mul_inv_cancel₀ hex, mul_one]

/-- The canonical spherical denominator has the explicit simple-resolvent
expansion at every real frequency off the finitely many selected spheres. -/
theorem sphereDenominator_partial_fractions (radius : ℕ → ℝ)
    (hstrict : StrictMono radius) (hpositive : ∀ j, 0 < j → 0 < radius j)
    {N : ℕ} (hN : 0 < N) (x : Euclidean d) (k : ℂ)
    (hx : ∀ j ∈ Finset.range N, ‖x‖ ≠ radius (j + 1)) :
    k / MvPolynomial.eval (fun j => (x j : ℂ)) (sphereDenominator d radius N) =
      ∑ j ∈ Finset.range N,
        resolventWeight (Finset.range N) (fun i => ((radius (i + 1) ^ 2 : ℝ) : ℂ)) j *
          (k / ((‖x‖ ^ 2 - radius (j + 1) ^ 2 : ℝ) : ℂ)) := by
  have ha : Set.InjOn (fun i => ((radius (i + 1) ^ 2 : ℝ) : ℂ)) (Finset.range N) := by
    intro i _ j _ hij
    have hs : radius (i + 1) ^ 2 = radius (j + 1) ^ 2 := Complex.ofReal_injective hij
    have hr := (sq_eq_sq₀ (hpositive _ (by omega)).le (hpositive _ (by omega)).le).mp hs
    exact Nat.add_right_cancel (hstrict.injective hr)
  have hq : ∀ j ∈ Finset.range N,
      ((‖x‖ ^ 2 : ℝ) : ℂ) ≠ ((radius (j + 1) ^ 2 : ℝ) : ℂ) := by
    intro j hj heq
    exact hx j hj ((sq_eq_sq₀ (norm_nonneg _) (hpositive _ (by omega)).le).mp
      (Complex.ofReal_injective heq))
  rw [sphereDenominator_eval_real]
  simp_rw [Complex.ofReal_sub]
  exact resolvent_partial_fractions (Finset.range N) _ ha
    (Finset.nonempty_range_iff.mpr (Nat.ne_of_gt hN)) _ k hq

/-- Finite sums of actual inverse-resolvent distributions have the expected
Fourier integral representative, including almost-everywhere scalar identities. -/
theorem distributionFourier_resolvent_sum_integral {ι : Type*}
    (s : Finset ι) (c : ι → ℂ) (u : ι → TemperedDistribution d)
    (R : ι → Euclidean d → ℂ)
    (hR : ∀ i ∈ s, ∀ φ : 𝓢(Euclidean d, ℂ), Integrable (fun x => R i x * φ x))
    (htransform : ∀ i ∈ s, ∀ φ : 𝓢(Euclidean d, ℂ),
      distributionFourier (u i) φ = ∫ x, R i x * φ x)
    (F : Euclidean d → ℂ) (hF : F =ᵐ[volume] fun x => ∑ i ∈ s, c i * R i x)
    (φ : 𝓢(Euclidean d, ℂ)) :
    distributionFourier (∑ i ∈ s, c i • u i) φ = ∫ x, F x * φ x := by
  calc
    distributionFourier (∑ i ∈ s, c i • u i) φ =
        ∑ i ∈ s, c i * (∫ x, R i x * φ x) := by
      simp only [distributionFourier, map_sum, map_smul, ContinuousLinearMap.sum_apply,
        ContinuousLinearMap.smul_apply, smul_eq_mul]
      exact Finset.sum_congr rfl fun i hi => congrArg (fun z => c i * z) (htransform i hi φ)
    _ = ∫ x, (∑ i ∈ s, c i * R i x) * φ x := by
      simp_rw [Finset.sum_mul, mul_assoc]
      rw [integral_finset_sum s (fun i hi => (hR i hi φ).const_mul (c i))]
      simp only [integral_const_mul]
    _ = ∫ x, F x * φ x := integral_congr_ae (hF.symm.mul Filter.EventuallyEq.rfl)

/-- Finite supported inverse resolvents synthesize an actual supported domain
vector once their explicit scalar sum has the ball-transform decay. -/
theorem exists_domainL2_of_resolvent_sum {ι : Type*}
    (s : Finset ι) (c : ι → ℂ) {S Ω : Set (Euclidean d)}
    (hS : IsClosed S) (hΩ : MeasurableSet Ω) (hSΩ : S ≤ᵐ[volume] Ω)
    (u : ι → TemperedDistribution d) (hu : ∀ i ∈ s, DistributionSupportedIn (u i) S)
    (R : ι → Euclidean d → ℂ)
    (hR : ∀ i ∈ s, ∀ φ : 𝓢(Euclidean d, ℂ), Integrable (fun x => R i x * φ x))
    (htransform : ∀ i ∈ s, ∀ φ : 𝓢(Euclidean d, ℂ),
      distributionFourier (u i) φ = ∫ x, R i x * φ x)
    (F : Euclidean d → ℂ) (hm : AEStronglyMeasurable F volume)
    (hF : F =ᵐ[volume] fun x => ∑ i ∈ s, c i * R i x)
    {C : ℝ} (hC : 0 ≤ C)
    (hdecay : ∀ᵐ x, ‖F x‖ ≤ C * (1 + ‖x‖) ^ (-((d : ℝ) + 1) / 2)) :
    ∃ f : DomainL2 Ω, SupportedOn Ω f S ∧
      l2Distribution (domainExtension Ω hΩ f) = ∑ i ∈ s, c i • u i ∧
      (fourierL2Equiv d (domainExtension Ω hΩ f) : Euclidean d → ℂ) =ᵐ[volume] F := by
  have hsupport : DistributionSupportedIn (∑ i ∈ s, c i • u i) S := by
    intro φ hc hd
    simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply]
    exact Finset.sum_eq_zero fun i hi => by rw [hu i hi φ hc hd, smul_zero]
  apply exists_domainL2_of_supported_fourier_decay hS hΩ hSΩ
    (∑ i ∈ s, c i • u i) hsupport F hm hC hdecay
  exact distributionFourier_resolvent_sum_integral s c u R hR htransform F hF

/-- Simple physical inverse resolvents and their explicit scalar sum realize
all bounded-degree polynomial numerators as actual supported domain vectors. -/
theorem exists_domainL2_polynomial_resolvent_sum {ι : Type*}
    (s : Finset ι) (c : ι → ℂ) {S Ω : Set (Euclidean d)}
    (hS : IsClosed S) (hΩ : MeasurableSet Ω) (hbounded : Bornology.IsBounded Ω)
    (hSΩ : S ≤ᵐ[volume] Ω) (u : ι → TemperedDistribution d)
    (hu : ∀ i ∈ s, DistributionSupportedIn (u i) S) (R : ι → Euclidean d → ℂ)
    (hR : ∀ i ∈ s, ∀ φ : 𝓢(Euclidean d, ℂ), Integrable (fun x => R i x * φ x))
    (htransform : ∀ i ∈ s, ∀ φ : 𝓢(Euclidean d, ℂ),
      distributionFourier (u i) φ = ∫ x, R i x * φ x)
    (G : Euclidean d → ℂ) (hG : Continuous G)
    (hGsum : G =ᵐ[volume] fun x => ∑ i ∈ s, c i * R i x) {M : ℕ} {C T : ℝ}
    (hdecay : ∀ x, T ≤ ‖x‖ →
      ‖G x‖ ≤ C * (1 + ‖x‖) ^ (-(M : ℝ) - ((d : ℝ) + 1) / 2))
    (p : ComplexPolynomial d) (hp : p.totalDegree ≤ M) :
    ∃ f : DomainL2 Ω, SupportedOn Ω f S ∧
      l2Distribution (domainExtension Ω hΩ f) =
        polynomialDifferentialOperator p (∑ i ∈ s, c i • u i) ∧
      ∀ ξ, domainEntireFourier Ω hΩ f (realToComplex ξ) = polynomialEvaluation ξ p * G ξ := by
  have hsupport : DistributionSupportedIn (∑ i ∈ s, c i • u i) S := by
    intro φ hc hd
    simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply]
    exact Finset.sum_eq_zero fun i hi => by rw [hu i hi φ hc hd, smul_zero]
  exact exists_domainL2_polynomial_numerator_tail hS hΩ hbounded hSΩ
    (∑ i ∈ s, c i • u i) hsupport G hG hdecay
    (distributionFourier_resolvent_sum_integral s c u R hR htransform G hGsum) p hp

end RieszEuclidean.CompleteMinimal
