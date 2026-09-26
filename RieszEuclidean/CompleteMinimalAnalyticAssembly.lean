import RieszEuclidean.CompleteMinimalAssembly
import RieszEuclidean.CompleteMinimalDivision
import RieszEuclidean.CompleteMinimalQuotientType
import RieszEuclidean.CompleteMinimalTail
import RieszEuclidean.CompleteMinimalMembership
import RieszEuclidean.CompleteMinimalPolynomialGrowth
import RieszEuclidean.CompleteMinimalRealUniqueness
import RieszEuclidean.CompleteMinimalSphereMembership
import RieszEuclidean.CompleteMinimalBesselZeros
import RieszEuclidean.CompleteMinimalFourierDivision
import Mathlib.Analysis.Analytic.Polynomial
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-! Analytic integration for the normalized spherical construction. -/
noncomputable section
open MeasureTheory Set SchwartzMap Filter Topology
open scoped SchwartzMap FourierTransform BigOperators
namespace RieszEuclidean.CompleteMinimal
variable {d : ℕ}

/-- Evaluation of an actual complex multivariate polynomial on complex Euclidean space. -/
def complexPolynomialValue (p : ComplexPolynomial d) (z : ComplexEuclidean d) : ℂ :=
  MvPolynomial.eval (fun j => z j) p

theorem complexPolynomialValue_analytic (p : ComplexPolynomial d) :
    AnalyticOnNhd ℂ (complexPolynomialValue p) univ :=
  AnalyticOnNhd.eval_continuousLinearMap'
    (fun j => PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin d => ℂ) j) p

/-- The finite sphere denominator as an actual entire function. -/
def sphereDenominatorFunction (radius : ℕ → ℝ) (N : ℕ) : ComplexEuclidean d → ℂ :=
  complexPolynomialValue (sphereDenominator d radius N)

theorem sphereDenominatorFunction_eq_prod (radius : ℕ → ℝ) (N : ℕ) (z : ComplexEuclidean d) :
    sphereDenominatorFunction radius N z =
      ∏ j ∈ Finset.range N, (squareSum (fun k => z k) - (radius (j + 1) : ℂ) ^ 2) := by
  simp [sphereDenominatorFunction, complexPolynomialValue, sphereDenominator, spherePolynomial,
    squareSum]

theorem sphereDenominatorFunction_zero_ne_zero (radius : ℕ → ℝ)
    (hr : ∀ j, 0 < j → 0 < radius j) (N : ℕ) :
    sphereDenominatorFunction (d := d) radius N 0 ≠ 0 := by
  change MvPolynomial.eval (fun j => (0 : ComplexEuclidean d) j) _ ≠ 0
  simpa using sphereDenominator_eval_zero_ne_zero (d := d) (N := N) radius hr

/-- Distinct positive-radius factors make the finite denominator's zeros simple. -/
theorem sphereDenominatorFunction_simple_quadric_zeros (radius : ℕ → ℝ)
    (hr : ∀ j, 0 < j → 0 < radius j) (hstrict : StrictMono radius) (N : ℕ) :
    HasSimpleQuadricZeros (sphereDenominatorFunction (d := d) radius N)
      (fun j : Fin N => radius (j.val + 1)) := by
  classical
  intro z hz
  rw [sphereDenominatorFunction_eq_prod] at hz
  obtain ⟨j, hj, hzero⟩ := Finset.prod_eq_zero_iff.mp hz
  let q := fun (k : ℕ) (w : ComplexEuclidean d) =>
    squareSum (fun i => w i) - (radius (k + 1) : ℂ) ^ 2
  let u := fun w : ComplexEuclidean d => ∏ k ∈ (Finset.range N).erase j, q k w
  have hanalytic (k : ℕ) : AnalyticOnNhd ℂ (q k) univ := by
    have h := complexPolynomialValue_analytic (spherePolynomial d (radius (k + 1)))
    change AnalyticOnNhd ℂ (fun w : ComplexEuclidean d =>
      MvPolynomial.eval (fun i => w i) (spherePolynomial d (radius (k + 1)))) univ at h
    simpa [q, spherePolynomial, squareSum] using h
  have hprod (s : Finset ℕ) : AnalyticOnNhd ℂ (fun w => ∏ k ∈ s, q k w) univ := by
    induction s using Finset.induction_on with
    | empty => simpa only [Finset.prod_empty] using (analyticOnNhd_const : AnalyticOnNhd ℂ (fun _ : ComplexEuclidean d => (1 : ℂ)) univ)
    | @insert k s hks ih =>
      simpa only [Finset.prod_insert hks] using (hanalytic k).mul ih
  have hu : AnalyticOnNhd ℂ u univ := hprod _
  have hunit : u z ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro k hk
    rcases Finset.mem_erase.mp hk with ⟨hkj, _⟩
    intro hkzero
    have heq : (radius (k + 1) : ℂ) ^ 2 = (radius (j + 1) : ℂ) ^ 2 :=
      (sub_eq_zero.mp hkzero).symm.trans (sub_eq_zero.mp hzero)
    have heqR : radius (k + 1) ^ 2 = radius (j + 1) ^ 2 := by exact_mod_cast heq
    have hrad : radius (k + 1) = radius (j + 1) :=
      (sq_eq_sq₀ (hr _ (by omega)).le (hr _ (by omega)).le).mp heqR
    exact hkj (by have hh := hstrict.injective hrad; omega)
  refine ⟨⟨j, Finset.mem_range.mp hj⟩, sub_eq_zero.mp hzero, u, hu z (mem_univ z), hunit, ?_⟩
  apply Eventually.of_forall
  intro w
  rw [sphereDenominatorFunction_eq_prod]
  exact (Finset.mul_prod_erase (Finset.range N) (fun k => q k w) hj).symm

/-- Finite analytic removal is proved from actual polynomial denominator geometry. -/
theorem exists_analytic_finite_sphere_quotient (radius : ℕ → ℝ)
    (hr : ∀ j, 0 < j → 0 < radius j) (hstrict : StrictMono radius) (N : ℕ)
    (κ : ComplexEuclidean d → ℂ) (hκ : AnalyticOnNhd ℂ κ univ)
    (hzero : ∀ j, 0 < j → j ≤ N → ∀ z : ComplexEuclidean d,
      squareSum (fun i => z i) = (radius j : ℂ) ^ 2 → κ z = 0) :
    ∃ χ : ComplexEuclidean d → ℂ, AnalyticOnNhd ℂ χ univ ∧
      (∀ z, κ z = sphereDenominatorFunction radius N z * χ z) ∧
      ∀ z, sphereDenominatorFunction radius N z ≠ 0 →
        χ z = κ z / sphereDenominatorFunction radius N z := by
  exact global_analytic_division_of_simple_quadric_zeros κ (sphereDenominatorFunction radius N)
    (fun j : Fin N => radius (j.val + 1)) hκ (complexPolynomialValue_analytic _)
    (sphereDenominatorFunction_zero_ne_zero radius hr N)
    (fun j => hr _ (by omega)) (sphereDenominatorFunction_simple_quadric_zeros radius hr hstrict N)
    (fun j z hz => hzero _ (by omega) (by omega) z hz)

/-- Entire finite quotients with the same product are unique, including at zeros. -/
theorem finite_sphere_quotient_unique (radius : ℕ → ℝ)
    (hr : ∀ j, 0 < j → 0 < radius j) (N : ℕ)
    (κ χ ψ : ComplexEuclidean d → ℂ) (hχ : Continuous χ) (hψ : Continuous ψ)
    (hχprod : ∀ z, κ z = sphereDenominatorFunction radius N z * χ z)
    (hψprod : ∀ z, κ z = sphereDenominatorFunction radius N z * ψ z) : χ = ψ := by
  funext z
  exact local_quotient_value_unique κ (sphereDenominatorFunction radius N) χ ψ z
    (entire_not_eventually_zero _ (complexPolynomialValue_analytic _)
      ⟨0, sphereDenominatorFunction_zero_ne_zero radius hr N⟩ z)
    (hχ.continuousAt) (hψ.continuousAt)
    (Eventually.of_forall hχprod) (Eventually.of_forall hψprod)

/-- A continuous physical quotient agrees with the analytically removed
quotient, including on every removed quadric. -/
theorem finite_sphere_quotient_analytic (radius : ℕ → ℝ)
    (hr : ∀ j, 0 < j → 0 < radius j) (hstrict : StrictMono radius) (N : ℕ)
    (κ χ : ComplexEuclidean d → ℂ) (hκ : AnalyticOnNhd ℂ κ univ)
    (hχ : Continuous χ)
    (hproduct : ∀ z, κ z = sphereDenominatorFunction radius N z * χ z) :
    AnalyticOnNhd ℂ χ univ := by
  have hzero : ∀ j, 0 < j → j ≤ N → ∀ z : ComplexEuclidean d,
      squareSum (fun i => z i) = (radius j : ℂ) ^ 2 → κ z = 0 := by
    intro j hj hjN z hz
    rw [hproduct]
    have hQ : sphereDenominatorFunction radius N z = 0 := by
      rw [sphereDenominatorFunction_eq_prod]
      apply Finset.prod_eq_zero_iff.mpr
      refine ⟨j - 1, Finset.mem_range.mpr (by omega), ?_⟩
      rw [show j - 1 + 1 = j by omega, hz, sub_self]
    rw [hQ, zero_mul]
  obtain ⟨ψ, hψ, hψprod, _⟩ := exists_analytic_finite_sphere_quotient
    radius hr hstrict N κ hκ hzero
  have heq := finite_sphere_quotient_unique radius hr N κ χ ψ hχ
    (differentiableOn_univ.mp hψ.differentiableOn).continuous hproduct hψprod
  exact heq.symm ▸ hψ

private theorem squareSum_realToComplex (x : Euclidean d) :
    squareSum (fun j => realToComplex x j) = ((‖x‖ ^ 2 : ℝ) : ℂ) := by
  have h : ‖x‖ ^ 2 = ∑ j : Fin d, (x j) ^ 2 := by
    simpa only [Real.norm_eq_abs, sq_abs] using PiLp.norm_sq_eq_of_L2 (fun _ : Fin d => ℝ) x
  rw [h]
  simp [squareSum, realToComplex_apply]

set_option maxHeartbeats 800000 in
/-- Removal of the first `N` simple zeros leaves no zero in the closed frequency ball. -/
theorem finite_sphere_quotient_nonzero (radius : ℕ → ℝ)
    (hr : ∀ j, 0 < j → 0 < radius j) (hstrict : StrictMono radius) (N : ℕ)
    (κ χ : ComplexEuclidean d → ℂ) (hχ : Continuous χ)
    (hκsimple : HasSimpleQuadricZeros κ (fun i : ℕ => radius (i + 1)))
    (hproduct : ∀ z, κ z = sphereDenominatorFunction radius N z * χ z)
    (x : Euclidean d) (hx : ‖x‖ ≤ radius N) : χ (realToComplex x) ≠ 0 := by
  intro hχzero
  have hκzero : κ (realToComplex x) = 0 := by rw [hproduct, hχzero, mul_zero]
  obtain ⟨i, hi, uκ, huκ, hunit, hκfactor⟩ := hκsimple _ hκzero
  have hsquare : ‖x‖ ^ 2 = radius (i + 1) ^ 2 := by
    exact_mod_cast ((squareSum_realToComplex x).symm.trans hi)
  have hnorm : ‖x‖ = radius (i + 1) :=
    (sq_eq_sq₀ (norm_nonneg x) (hr _ (by omega)).le).mp hsquare
  have hiN : i + 1 ≤ N := hstrict.le_iff_le.mp (hnorm ▸ hx)
  have hQzero : sphereDenominatorFunction radius N (realToComplex x) = 0 := by
    exact sphereDenominator_eval_eq_zero_on_sphere radius (by omega) hiN x hnorm
  obtain ⟨j, hj, uQ, huQ, _huQunit, hQfactor⟩ :=
    sphereDenominatorFunction_simple_quadric_zeros radius hr hstrict N _ hQzero
  have hradsq : radius (j.val + 1) ^ 2 = radius (i + 1) ^ 2 := by
    exact_mod_cast (hj.symm.trans hi)
  have hrad : radius (j.val + 1) = radius (i + 1) :=
    (sq_eq_sq₀ (hr _ (by omega)).le (hr _ (by omega)).le).mp hradsq
  change ∀ᶠ z in 𝓝 (realToComplex x), sphereDenominatorFunction radius N z =
    (squareSum (fun k => z k) - (radius (j.val + 1) : ℂ) ^ 2) * uQ z at hQfactor
  rw [hrad] at hQfactor
  let q : ComplexEuclidean d → ℂ := fun z =>
    squareSum (fun j => z j) - (radius (i + 1) : ℂ) ^ 2
  have hq : AnalyticOnNhd ℂ q univ := by
    have h := complexPolynomialValue_analytic (spherePolynomial d (radius (i + 1)))
    change AnalyticOnNhd ℂ (fun w : ComplexEuclidean d =>
      MvPolynomial.eval (fun j => w j) (spherePolynomial d (radius (i + 1)))) univ at h
    simpa [q, spherePolynomial, squareSum] using h
  have hq0 : q 0 ≠ 0 := by
    change (∑ j : Fin d, (0 : ℂ) ^ 2) - (radius (i + 1) : ℂ) ^ 2 ≠ 0
    simp only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), Finset.sum_const_zero,
      zero_sub, neg_ne_zero]
    exact pow_ne_zero _ (Complex.ofReal_ne_zero.mpr (hr _ (by omega)).ne')
  have hsecond : ∀ᶠ z in 𝓝 (realToComplex x), κ z = q z * (uQ z * χ z) := by
    filter_upwards [hQfactor] with z hz
    rw [hproduct, hz]
    ring
  have he := local_quotient_value_unique κ q uκ (fun z => uQ z * χ z) (realToComplex x)
    (entire_not_eventually_zero q hq ⟨0, hq0⟩ _)
    huκ.continuousAt (huQ.continuousAt.mul hχ.continuousAt) hκfactor hsecond
  exact hunit (he.trans (by change uQ (realToComplex x) * χ (realToComplex x) = 0; rw [hχzero, mul_zero]))

/-- A later kernel zero remains a zero after division by the first finite factors. -/
theorem finite_sphere_quotient_zero (radius : ℕ → ℝ)
    (hr : ∀ j, 0 < j → 0 < radius j) (hstrict : StrictMono radius) (N j : ℕ)
    (κ χ : ComplexEuclidean d → ℂ)
    (hzero : ∀ x : Euclidean d, ‖x‖ = radius j → κ (realToComplex x) = 0)
    (hproduct : ∀ z, κ z = sphereDenominatorFunction radius N z * χ z)
    (hj : N < j) (x : Euclidean d) (hx : ‖x‖ = radius j) : χ (realToComplex x) = 0 := by
  have hQ : sphereDenominatorFunction radius N (realToComplex x) ≠ 0 := by
    apply sphereDenominator_eval_ne_zero radius hr x
    intro k _hk hkN hknorm
    have he : radius j = radius k := hx.symm.trans hknorm
    have heindex := hstrict.injective he
    omega
  exact (mul_eq_zero.mp ((hproduct _).symm.trans (hzero x hx))).resolve_left hQ


/-- The exact analytic division interface: an actual compact inverse quotient,
its real Fourier representative, and the scalar denominator product. -/
def CompactSphereTailDivision (Ω : Set (Euclidean d)) (hΩ : MeasurableSet Ω)
    (hfinite : volume Ω ≠ ⊤) (radius : ℕ → ℝ) (N : ℕ) : Prop :=
  ∀ f : DomainL2 Ω,
    (∀ ξ ∈ laterSpheres radius N, inner (𝕜 := ℂ) f (exponentialL2 Ω hfinite ξ) = 0) →
    ∃ v : TemperedDistribution d, ∃ G : Euclidean d → ℂ,
      CompactlySupportedDistribution v ∧ Continuous G ∧
      (∀ φ : 𝓢(Euclidean d, ℂ), distributionFourier v φ = ∫ x, G x * φ x) ∧
      ∀ x, polynomialEvaluation x (sphereDenominator d radius N) *
        𝓕 (domainExtension Ω hΩ f : Euclidean d → ℂ) x =
          normalizedBallFourier d (realToComplex x) * G x

/-- Compact inverse division, John rigidity, and the proved L² obstruction give
exactly the bounded-degree entire representation needed by sphere selection. -/
theorem tailPolynomialRepresentation_of_compact_division
    (hd : 1 ≤ d) (hTL : TitchmarshLions d)
    (Ω : Set (Euclidean d)) (hΩ : MeasurableSet Ω) (hbounded : Bornology.IsBounded Ω)
    (hfinite : volume Ω ≠ ⊤) (hconvex : Convex ℝ (closure Ω))
    (hJ : IsJohnEllipsoid (closure Ω) (Metric.closedBall (0 : Euclidean d) 1))
    (radius : ℕ → ℝ) (hr : ∀ j, 0 < j → 0 < radius j) (N : ℕ)
    (χ : ComplexEuclidean d → ℂ) (hχ : Differentiable ℂ χ)
    (hχproduct : ∀ z, normalizedBallFourier d z = sphereDenominatorFunction radius N z * χ z)
    (hκlower : RecurringRadialSquareLowerBound
      (fun x => normalizedBallFourier d (realToComplex x)) (d + 1))
    (hdivision : CompactSphereTailDivision Ω hΩ hfinite radius N) :
    TailPolynomialRepresentation Ω hΩ hfinite (laterSpheres radius N) (2 * N) χ := by
  intro f hf
  obtain ⟨v, G, hv, hG, htransform, hproduct⟩ := hdivision f hf
  have hfsupport : ∀ᵐ x, x ∉ closure Ω → domainExtension Ω hΩ f x = 0 := by
    filter_upwards [domainExtension_coe Ω hΩ f] with x hx hn
    rw [hx, Set.indicator_of_not_mem (fun hxΩ => hn (subset_closure hxΩ))]
  obtain ⟨m, p, _hm, _hGp, hpF⟩ := sphere_tail_fourier_polynomial_product hTL radius N
    (domainExtension Ω hΩ f) (domainExtension_integrable hΩ hbounded f) hv hconvex
    isClosed_closure hJ hfsupport G hG htransform hproduct
  let F := fun x => domainEntireFourier Ω hΩ f (realToComplex x)
  have hemb : Continuous (realToComplex : Euclidean d → ComplexEuclidean d) :=
    (PiLp.continuous_equiv_symm 2 _).comp (continuous_pi fun j => by
      change Continuous (fun x : Euclidean d => (x j : ℂ)); fun_prop)
  have hcF : Continuous F := (domainEntireFourier_differentiable hΩ hbounded f).continuous.comp hemb
  have hmF : MemLp F 2 volume :=
    (memLp_congr_ae (domainEntireFourier_eq_fourierL2 hΩ hbounded f)).mpr
      (Lp.memLp (fourierL2Equiv d (domainExtension Ω hΩ f)))
  have hrealprod : ∀ x, F x * polynomialEvaluation x (sphereDenominator d radius N) =
      polynomialEvaluation x p * normalizedBallFourier d (realToComplex x) := by
    intro x
    simpa only [F, domainEntireFourier, entireFourier_realToComplex, mul_comm] using hpF x
  have hdegree : p.totalDegree ≤ 2 * N := polynomial_totalDegree_le_of_memLp_quotient hd N p
    (sphereDenominator d radius N) (by rw [sphereDenominator_totalDegree hd]) F _ hcF hrealprod
    hκlower hmF
  let p' : MvPolynomial.restrictTotalDegree (Fin d) ℂ (2 * N) :=
    ⟨p, (MvPolynomial.mem_restrictTotalDegree _ _ _).mpr hdegree⟩
  have hpwhole : (fun z => sphereDenominatorFunction radius N z * domainEntireFourier Ω hΩ f z) =
      fun z => normalizedBallFourier d z * complexPolynomialValue p z := by
    apply entire_eq_of_eq_on_real
    · exact (differentiableOn_univ.mp (complexPolynomialValue_analytic _).differentiableOn).mul
        (domainEntireFourier_differentiable hΩ hbounded f)
    · exact (normalizedBallFourier_differentiable d).mul
        (differentiableOn_univ.mp (complexPolynomialValue_analytic p).differentiableOn)
    · intro x
      simpa only [sphereDenominatorFunction, complexPolynomialValue, realToComplex_apply,
        polynomialEvaluation_apply, F, mul_comm] using hrealprod x
  have hwhole : domainEntireFourier Ω hΩ f = fun z => χ z * complexPolynomialValue p z := by
    apply finite_sphere_quotient_unique radius hr N
      (fun z => normalizedBallFourier d z * complexPolynomialValue p z)
      (domainEntireFourier Ω hΩ f) (fun z => χ z * complexPolynomialValue p z)
      (domainEntireFourier_differentiable hΩ hbounded f).continuous
      (hχ.continuous.mul ((differentiableOn_univ.mp (complexPolynomialValue_analytic p).differentiableOn).continuous))
    · intro z
      exact (congrFun hpwhole z).symm
    · intro z
      rw [hχproduct]
      ring
  refine ⟨p', fun z => ?_⟩
  exact congrFun hwhole z


/-- The boundary of the unit ball is null, so open-ball inclusion is sufficient
for actual L² synthesis supported in the closed ball. -/
theorem closedBall_ae_subset_of_ball_subset {Ω : Set (Euclidean d)}
    (hB : Metric.ball (0 : Euclidean d) 1 ⊆ Ω) :
    Metric.closedBall (0 : Euclidean d) 1 ≤ᵐ[volume] Ω := by
  have hnull : volume (Metric.sphere (0 : Euclidean d) 1) = 0 :=
    Measure.addHaar_sphere_of_ne_zero volume _ (by norm_num)
  filter_upwards [measure_zero_iff_ae_nmem.mp hnull] with x hx hclosed
  change x ∈ Metric.closedBall (0 : Euclidean d) 1 at hclosed
  apply hB
  have hn : ‖x‖ ≤ 1 := by simpa only [Metric.mem_closedBall, dist_zero_right] using hclosed
  have hne : ‖x‖ ≠ 1 := by simpa only [Metric.mem_sphere, dist_zero_right] using hx
  simpa only [Metric.mem_ball, dist_zero_right] using lt_of_le_of_ne hn hne

/-- The enumerated Bessel zeros supply all actual resolvent normalization
constants required by the finite physical kernel. -/
theorem ballZeroRadius_resolvent_normalization (n : ℕ) {j : ℕ} (hj : 0 < j) :
    ballHelmholtzSquare n ((((2 * Real.pi * ballZeroRadius n j) ^ 2 : ℝ) : ℂ)) ≠ 0 := by
  have ha : 0 < 2 * Real.pi * ballZeroRadius n j :=
    mul_pos (mul_pos (by norm_num) Real.pi_pos) (ballZeroRadius_pos n hj)
  have hz : radialBallFourier n ((2 * Real.pi * ballZeroRadius n j : ℝ) : ℂ) = 0 := by
    rw [radialBallFourier_ofReal_eq, ballZeroRadius_isZero n hj, Complex.ofReal_zero]
  apply ballHelmholtzSquare_ne_zero_of_simple_zero n ha hz
  intro hd
  apply realRadialBallFourier_deriv_ne_zero_at_zero n ha (ballZeroRadius_isZero n hj)
  rw [realRadialBallFourier_deriv, hd, Complex.zero_re]

/-- The concrete spherical package reduces only to the two analytic identities
produced by physical resolvents and compact inverse division. All radius,
simple-zero, support, degree, synthesis, and nonvanishing facts are proved. -/
def sphereAnalyticInputs_of_resolvent_and_compact_division
    (n : ℕ) (hTL : TitchmarshLions (n + 1))
    (Ω : Set (Euclidean (n + 1))) (hΩ : MeasurableSet Ω)
    (hbounded : Bornology.IsBounded Ω) (hfinite : volume Ω ≠ ⊤)
    (hconvex : Convex ℝ Ω)
    (hJ : IsJohnEllipsoid (closure Ω) (Metric.closedBall (0 : Euclidean (n + 1)) 1))
    (hB : Metric.ball (0 : Euclidean (n + 1)) 1 ⊆ Ω)
    (hproduct : ∀ N z, normalizedBallFourier (n + 1) z =
      MvPolynomial.eval (fun j => z j) (sphereDenominator (n + 1) (ballZeroRadius n) N) *
        sphereKernelMultiplier n (ballZeroRadius n) N z)
    (hdivision : ∀ N, CompactSphereTailDivision Ω hΩ hfinite (ballZeroRadius n) N) :
    SphereAnalyticInputs Ω hΩ hfinite (ballZeroRadius n)
      (Metric.closedBall (0 : Euclidean (n + 1)) 1) := by
  let hb := fun (N j : ℕ) (hj : 0 < j) (_ : j ≤ N) =>
    ballZeroRadius_resolvent_normalization n hj
  have hr : ∀ j, 0 < j → 0 < ballZeroRadius n j := fun _ hj => ballZeroRadius_pos n hj
  refine ⟨sphereKernelMultiplier n (ballZeroRadius n), ?_, ?_, ?_, ?_⟩
  · intro N p
    exact sphereKernelMultiplier_synthesize n (ballZeroRadius n) N (hb N) (hproduct N)
      Ω hΩ hbounded (closedBall_ae_subset_of_ball_subset hB) p.val
      ((MvPolynomial.mem_restrictTotalDegree _ _ _).mp p.property)
  · intro N
    exact tailPolynomialRepresentation_of_compact_division (by omega) hTL Ω hΩ hbounded
      hfinite hconvex.closure hJ (ballZeroRadius n) hr N _
      (sphereKernelMultiplier_differentiable n (ballZeroRadius n) N (hb N))
      (hproduct N) (normalizedBallFourier_recurringSquareLowerBound n) (hdivision N)
  · intro N x hx
    exact finite_sphere_quotient_nonzero (ballZeroRadius n) hr (ballZeroRadius_strictMono n)
      N _ _ (sphereKernelMultiplier_differentiable n (ballZeroRadius n) N (hb N)).continuous
      (normalizedBallFourier_hasSimpleQuadricZeros_positive n) (hproduct N) x hx
  · intro N j hj x hx
    exact finite_sphere_quotient_zero (ballZeroRadius n) hr (ballZeroRadius_strictMono n)
      N j _ _ (fun x hx => (normalizedBallFourier_real_zero_iff n x).mpr ⟨j, by omega, hx⟩)
      (hproduct N) hj x hx

/-- The compact quotient required by the tail argument is constructed from
the actual entire Fourier transform and actual Bessel division. -/
theorem compactSphereTailDivision (n : ℕ) {Ω : Set (Euclidean (n + 1))}
    (hΩ : MeasurableSet Ω) (hbounded : Bornology.IsBounded Ω)
    (hfinite : volume Ω ≠ ⊤) (N : ℕ) :
    CompactSphereTailDivision Ω hΩ hfinite (ballZeroRadius n) N := by
  intro f hf
  obtain ⟨G, u, hG, hproduct, hu, hFourier⟩ :=
    normalized_ball_tail_compact_inverse n hΩ hfinite hbounded N f hf
  have hc : Continuous G := (differentiableOn_univ.mp hG.differentiableOn).continuous
  have hemb : Continuous (realToComplex : Euclidean (n + 1) → ComplexEuclidean (n + 1)) :=
    (PiLp.continuous_equiv_symm 2 _).comp (continuous_pi fun j => by
      change Continuous (fun x : Euclidean (n + 1) => (x j : ℂ)); fun_prop)
  refine ⟨u, fun x => G (realToComplex x), hu, hc.comp hemb, hFourier, ?_⟩
  intro x
  simpa only [realToComplex_apply, polynomialEvaluation_apply, domainEntireFourier,
    entireFourier_realToComplex] using hproduct (realToComplex x)

/-- The actual normalized spherical analytic package. Its only external
analytic theorem is the explicitly named Titchmarsh–Lions hypothesis. -/
def sphereAnalyticInputs (n : ℕ) (hTL : TitchmarshLions (n + 1))
    (Ω : Set (Euclidean (n + 1))) (hΩ : MeasurableSet Ω)
    (hbounded : Bornology.IsBounded Ω) (hfinite : volume Ω ≠ ⊤)
    (hconvex : Convex ℝ Ω)
    (hJ : IsJohnEllipsoid (closure Ω) (Metric.closedBall (0 : Euclidean (n + 1)) 1))
    (hB : Metric.ball (0 : Euclidean (n + 1)) 1 ⊆ Ω) :
    SphereAnalyticInputs Ω hΩ hfinite (ballZeroRadius n)
      (Metric.closedBall (0 : Euclidean (n + 1)) 1) := by
  apply sphereAnalyticInputs_of_resolvent_and_compact_division
    n hTL Ω hΩ hbounded hfinite hconvex hJ hB
  · intro N
    apply sphereKernelMultiplier_product n (ballZeroRadius n) N (ballZeroRadius_strictMono n)
      (fun _ hj => ballZeroRadius_pos n hj)
    intro j hj _
    rw [radialBallFourier_ofReal_eq, ballZeroRadius_isZero n hj, Complex.ofReal_zero]
  · exact compactSphereTailDivision n hΩ hbounded hfinite

end RieszEuclidean.CompleteMinimal
