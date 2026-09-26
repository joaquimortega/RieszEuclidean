import RieszEuclidean.CompleteMinimalDivision
import RieszEuclidean.CompleteMinimalFourierGrowth
import RieszEuclidean.CompleteMinimalFourierAnalytic
import RieszEuclidean.CompleteMinimalPaleyWiener
import RieszEuclidean.CompleteMinimalMembership
import RieszEuclidean.CompleteMinimalAssembly
import RieszEuclidean.CompleteMinimalBesselZeros
import RieszEuclidean.CompleteMinimalBesselAsymptotic
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Analytic.Polynomial

/-!
Analytic division of a domain Fourier transform by the normalized spherical denominator,
followed by construction of its compactly supported inverse Fourier distribution.
-/

noncomputable section
open MeasureTheory Set Filter Topology
open scoped BigOperators

namespace RieszEuclidean.CompleteMinimal

/-- The real-frequency restriction of an entire function to a unit radial line. -/
def realRadialRestriction {d : ℕ} (A : ComplexEuclidean d → ℂ) (θ : Euclidean d) (s : ℝ) : ℂ :=
  A (realToComplex (s • θ))

/-- The actual derivative of the restriction, expressed through the complex Fréchet derivative. -/
theorem realRadialRestriction_hasDerivAt {d : ℕ} {A : ComplexEuclidean d → ℂ}
    (hA : Differentiable ℂ A) (θ : Euclidean d) (s : ℝ) :
    HasDerivAt (realRadialRestriction A θ)
      ((fderiv ℂ A (realToComplex (s • θ))) (realToComplex θ)) s := by
  unfold realRadialRestriction
  have hline := (hA ((s : ℂ) • realToComplex θ)).hasFDerivAt.comp_hasDerivAt (s : ℂ)
    ((hasDerivAt_id (s : ℂ)).smul_const (realToComplex θ))
  simpa only [realRadialRestriction, realToComplex_real_smul, one_smul,
    Function.comp_def, id_eq] using hline.comp_ofReal

/-- A polynomial bound outside a bounded real-frequency region extends to a global
polynomial bound by continuity on the compact remainder. -/
theorem real_polynomial_bound_of_tail {d : ℕ} {G : ComplexEuclidean d → ℂ}
    (hG : Continuous G) {C R : ℝ} (hC : 0 ≤ C) (m : ℕ)
    (hbound : ∀ x : Euclidean d, R < ‖x‖ →
      ‖G (realToComplex x)‖ ≤ C * (1 + ‖x‖) ^ m) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ x : Euclidean d,
      ‖G (realToComplex x)‖ ≤ D * (1 + ‖x‖) ^ m := by
  have hemb : Continuous (realToComplex : Euclidean d → ComplexEuclidean d) :=
    (PiLp.continuous_equiv_symm 2 _).comp (continuous_pi fun j => by
      change Continuous (fun x : Euclidean d => (x j : ℂ))
      fun_prop)
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : Euclidean d) (max R 1)).bddAbove_image
    (hG.comp hemb).norm.continuousOn
  refine ⟨max C (max M 0), le_trans hC (le_max_left _ _), fun x => ?_⟩
  by_cases hx : R < ‖x‖
  · exact (hbound x hx).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
  · have hxball : x ∈ Metric.closedBall (0 : Euclidean d) (max R 1) := by
      simp only [Metric.mem_closedBall, dist_zero_right]
      exact (le_of_not_gt hx).trans (le_max_left _ _)
    calc
      _ ≤ M := hM ⟨x, hxball, rfl⟩
      _ ≤ max C (max M 0) := (le_max_left M 0).trans (le_max_right _ _)
      _ ≤ max C (max M 0) * (1 + ‖x‖) ^ m :=
        le_mul_of_one_le_right (by positivity) (one_le_pow₀ (by linarith [norm_nonneg x]))

/-- The scalar distance-to-zero estimate and the actual numerator derivative bound imply
a real polynomial growth bound for the multivariate entire quotient. -/
theorem entire_quotient_real_polynomial_bound {d : ℕ}
    {A κ G : ComplexEuclidean d → ℂ} (hA : Differentiable ℂ A) (hG : Continuous G)
    (hprod : ∀ z, A z = κ z * G z) (k : ℝ → ℂ) (Z : Set ℝ)
    (hZ : IsClosed Z) (hZne : Z.Nonempty) (hdense : Dense Zᶜ)
    (hradial : ∀ θ : Euclidean d, ‖θ‖ = 1 → ∀ s : ℝ,
      κ (realToComplex (s • θ)) = k s) (hzero : ∀ s ∈ Z, k s = 0)
    {C c R : ℝ} (hC : 0 ≤ C) (hc : 0 < c) (m b : ℕ)
    (hAnorm : ∀ x : Euclidean d, ‖A (realToComplex x)‖ ≤ C * (1 + ‖x‖) ^ m)
    (hAderiv : ∀ x : Euclidean d, ‖fderiv ℂ A (realToComplex x)‖ ≤ C * (1 + ‖x‖) ^ m)
    (hlower : ∀ s : ℝ, R < s →
      c / (1 + ‖s‖) ^ b * min 1 (Metric.infDist s Z) ≤ ‖k s‖) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ x : Euclidean d,
      ‖G (realToComplex x)‖ ≤ D * (1 + ‖x‖) ^ (m + b) := by
  apply real_polynomial_bound_of_tail hG (C := C * 2 ^ m / c) (R := max R 0) (by positivity) (m + b)
  intro x hx
  have hxpos : 0 < ‖x‖ := lt_of_le_of_lt (le_max_right R 0) hx
  let θ : Euclidean d := ‖x‖⁻¹ • x
  have hθ : ‖θ‖ = 1 := by simp [θ, norm_smul, Real.norm_eq_abs, abs_of_pos hxpos, hxpos.ne']
  have hnorm (s : ℝ) : ‖s • θ‖ = ‖s‖ := by rw [norm_smul, hθ, mul_one]
  let H := realRadialRestriction A θ
  let H' := fun s : ℝ => (fderiv ℂ A (realToComplex (s • θ))) (realToComplex θ)
  let K := realRadialRestriction G θ
  have hH (s : ℝ) : ‖H s‖ ≤ C * (1 + ‖s‖) ^ m := by
    simpa only [H, realRadialRestriction, hnorm] using hAnorm (s • θ)
  have hH' (s : ℝ) : ‖H' s‖ ≤ C * (1 + ‖s‖) ^ m := by
    calc
      _ ≤ ‖fderiv ℂ A (realToComplex (s • θ))‖ * ‖realToComplex θ‖ :=
        ContinuousLinearMap.le_opNorm _ _
      _ = ‖fderiv ℂ A (realToComplex (s • θ))‖ := by rw [realToComplex_norm, hθ, mul_one]
      _ ≤ _ := by simpa only [hnorm] using hAderiv (s • θ)
  have hHK (s : ℝ) : H s = k s * K s := by
    dsimp only [H, K, realRadialRestriction]
    rw [hprod, hradial θ hθ s]
  have hHzero (s : ℝ) (hs : s ∈ Z) : H s = 0 := by rw [hHK s, hzero s hs, zero_mul]
  have hK : Continuous K := by
    have hemb : Continuous (realToComplex : Euclidean d → ComplexEuclidean d) :=
      (PiLp.continuous_equiv_symm 2 _).comp (continuous_pi fun j => by
        change Continuous (fun x : Euclidean d => (x j : ℂ))
        fun_prop)
    exact hG.comp (hemb.comp (continuous_id.smul continuous_const))
  have hbound := radial_quotient_polynomial_bound H H' k K Z hZ hZne hdense C c R hC hc m b
    hH (realRadialRestriction_hasDerivAt hA θ) hH' hHzero hHK hK hlower ‖x‖
    (lt_of_le_of_lt (le_max_left R 0) hx)
  have hrad : ‖x‖ • θ = x := by
    dsimp only [θ]
    rw [smul_smul, mul_inv_cancel₀ hxpos.ne', one_smul]
  simpa only [K, realRadialRestriction, hrad, norm_norm] using hbound

/-- Simple quadric division, quotient exponential type, radial cancellation, and
Paley–Wiener–Schwartz combine to construct the compact inverse of an actual numerator. -/
theorem simple_quadric_division_compact_inverse {d : ℕ} {ι : Type*}
    (A κ : ComplexEuclidean d → ℂ) (radius : ι → ℝ)
    (hA : AnalyticOnNhd ℂ A univ) (hκ : AnalyticOnNhd ℂ κ univ) (hκ0 : κ 0 ≠ 0)
    (hradius : ∀ j, 0 < radius j) (hgeometry : HasSimpleQuadricZeros κ radius)
    (hAzero : ∀ j z, squareSum (fun k => z k) = (radius j : ℂ) ^ 2 → A z = 0)
    (hAtype : FiniteExponentialType A) (hκtype : FiniteExponentialType κ)
    (k : ℝ → ℂ) (Z : Set ℝ) (hZ : IsClosed Z) (hZne : Z.Nonempty) (hdense : Dense Zᶜ)
    (hradial : ∀ θ : Euclidean d, ‖θ‖ = 1 → ∀ s : ℝ,
      κ (realToComplex (s • θ)) = k s) (hkzero : ∀ s ∈ Z, k s = 0)
    {C c R : ℝ} (hC : 0 ≤ C) (hc : 0 < c) (m b : ℕ)
    (hAnorm : ∀ x : Euclidean d, ‖A (realToComplex x)‖ ≤ C * (1 + ‖x‖) ^ m)
    (hAderiv : ∀ x : Euclidean d, ‖fderiv ℂ A (realToComplex x)‖ ≤ C * (1 + ‖x‖) ^ m)
    (hlower : ∀ s : ℝ, R < s →
      c / (1 + ‖s‖) ^ b * min 1 (Metric.infDist s Z) ≤ ‖k s‖) :
    ∃ G : ComplexEuclidean d → ℂ, ∃ u : TemperedDistribution d,
      AnalyticOnNhd ℂ G univ ∧ (∀ z, A z = κ z * G z) ∧
      FiniteExponentialType G ∧
      (∃ D : ℝ, 0 ≤ D ∧ ∀ x : Euclidean d,
        ‖G (realToComplex x)‖ ≤ D * (1 + ‖x‖) ^ (m + b)) ∧
      CompactlySupportedDistribution u ∧
      ∀ φ : SchwartzMap (Euclidean d) ℂ,
        distributionFourier u φ = ∫ x, G (realToComplex x) * φ x := by
  obtain ⟨G, hG, hprod, _⟩ := global_analytic_division_of_simple_quadric_zeros A κ radius
    hA hκ hκ0 hradius hgeometry hAzero
  have hAdiff : Differentiable ℂ A := fun z => (hA z (mem_univ z)).differentiableAt
  have hκdiff : Differentiable ℂ κ := fun z => (hκ z (mem_univ z)).differentiableAt
  have hGdiff : Differentiable ℂ G := fun z => (hG z (mem_univ z)).differentiableAt
  have hGtype := finiteExponentialType_entire_quotient hAdiff hκdiff hGdiff hprod hκ0 hAtype hκtype
  obtain ⟨D, hD, hGreal⟩ := entire_quotient_real_polynomial_bound hAdiff hGdiff.continuous
    hprod k Z hZ hZne hdense hradial hkzero hC hc m b hAnorm hAderiv hlower
  obtain ⟨u, hu, hFourier⟩ := paleyWienerSchwartz hGdiff hGtype ⟨m + b, D, hD, hGreal⟩
  exact ⟨G, u, hG, hprod, hGtype, ⟨D, hD, hGreal⟩, hu, hFourier⟩

/-- The finite spherical polynomial evaluated at a complex frequency. -/
theorem sphereDenominator_eval_complex {d : ℕ} (radius : ℕ → ℝ) (N : ℕ) (z : ComplexEuclidean d) :
    MvPolynomial.eval (fun k => z k) (sphereDenominator d radius N) =
      ∏ j ∈ Finset.range N, (squareSum (fun k => z k) - (radius (j + 1) : ℂ) ^ 2) := by
  simp [sphereDenominator, spherePolynomial, squareSum]

/-- Any one of the first positive-radius quadrics is a zero of the finite numerator polynomial. -/
theorem sphereDenominator_eval_complex_zero {d : ℕ} (radius : ℕ → ℝ) (N j : ℕ)
    (hj : 0 < j) (hjN : j ≤ N) (z : ComplexEuclidean d)
    (hz : squareSum (fun k => z k) = (radius j : ℂ) ^ 2) :
    MvPolynomial.eval (fun k => z k) (sphereDenominator d radius N) = 0 := by
  rw [sphereDenominator_eval_complex]
  apply Finset.prod_eq_zero_iff.mpr
  refine ⟨j - 1, Finset.mem_range.mpr (by omega), ?_⟩
  rw [show j - 1 + 1 = j by omega, hz, sub_self]

/-- Vanishing on the later real spheres cancels all remaining complex quadric factors
of the denominator, by analytic continuation along the complex sphere. -/
theorem polynomial_domainFourier_zero_on_all_quadrics {d : ℕ} {Ω : Set (Euclidean d)}
    (hΩ : MeasurableSet Ω) (hfinite : volume Ω ≠ ⊤) (hbounded : Bornology.IsBounded Ω)
    (radius : ℕ → ℝ) (hradius : ∀ j, 0 < j → 0 < radius j) (N : ℕ) (f : DomainL2 Ω)
    (hvanish : ∀ ξ : Euclidean d, ξ ∈ laterSpheres radius N →
      inner (𝕜 := ℂ) (exponentialL2 Ω hfinite ξ) f = 0) (j : ℕ) (hj : 0 < j)
    (z : ComplexEuclidean d) (hz : squareSum (fun k => z k) = (radius j : ℂ) ^ 2) :
    MvPolynomial.eval (fun k => z k) (sphereDenominator d radius N) *
      domainEntireFourier Ω hΩ f z = 0 := by
  by_cases hjN : j ≤ N
  · rw [sphereDenominator_eval_complex_zero radius N j hj hjN z hz, zero_mul]
  · have hFzero := entire_zero_on_quadric (domainEntireFourier Ω hΩ f)
      (domainEntireFourier_differentiable hΩ hbounded f) (radius j) (hradius j hj)
      (fun ξ hξ => by
        rw [domainEntireFourier_real_inner hΩ hfinite f ξ]
        exact hvanish ξ ⟨j, by omega, hξ⟩) z hz
    rw [hFzero, mul_zero]

/-- The scalar radial denominator in physical Fourier-frequency normalization. -/
def physicalRadialBallFourier (n : ℕ) (s : ℝ) : ℂ :=
  radialBallFourier n ((2 * Real.pi * s : ℝ) : ℂ)

/-- Its actual real zero set, including the negative radii. -/
def physicalBallZeroSet (n : ℕ) : Set ℝ := {s | physicalRadialBallFourier n s = 0}

/-- The scalar denominator agrees with the actual ball transform along every real unit direction. -/
theorem physicalRadialBallFourier_eq (n : ℕ) (θ : Euclidean (n + 1)) (hθ : ‖θ‖ = 1) (s : ℝ) :
    normalizedBallFourier (n + 1) (realToComplex (s • θ)) = physicalRadialBallFourier n s := by
  rw [normalizedBallFourier_real_radial, norm_smul, hθ, mul_one, Real.norm_eq_abs]
  by_cases hs : 0 ≤ s
  · simp only [abs_of_nonneg hs, physicalRadialBallFourier]
  · rw [abs_of_neg (lt_of_not_ge hs)]
    have heq : ((2 * Real.pi * -s : ℝ) : ℂ) = -((2 * Real.pi * s : ℝ) : ℂ) := by push_cast; ring
    rw [heq, radialBallFourier_even]
    rfl

/-- The physical radial zeros form a closed real set. -/
theorem physicalBallZeroSet_isClosed (n : ℕ) : IsClosed (physicalBallZeroSet n) := by
  apply isClosed_eq _ continuous_const
  have hr := (radialBallFourier_analytic n).continuous
  exact hr.comp (Complex.continuous_ofReal.comp (continuous_const.mul continuous_id))

/-- Positive Bessel zeros provide an actual point of the physical radial zero set. -/
theorem physicalBallZeroSet_nonempty (n : ℕ) : (physicalBallZeroSet n).Nonempty := by
  refine ⟨positiveBallZero n 0 / (2 * Real.pi), ?_⟩
  change radialBallFourier n ((2 * Real.pi * (positiveBallZero n 0 / (2 * Real.pi)) : ℝ) : ℂ) = 0
  rw [mul_div_cancel₀ _ (show 2 * Real.pi ≠ 0 by positivity), radialBallFourier_ofReal_eq,
    positiveBallZero_isZero, Complex.ofReal_zero]

/-- Local finiteness of entire radial zeros survives physical-frequency scaling. -/
theorem physicalBallZeroSet_locallyFinite (n : ℕ) (s : ℝ) :
    ∃ U ∈ 𝓝 s, (U ∩ physicalBallZeroSet n).Finite := by
  let e : ℝ → ℂ := fun t => ((2 * Real.pi * t : ℝ) : ℂ)
  have he : Continuous e := Complex.continuous_ofReal.comp (continuous_const.mul continuous_id)
  have hinj : Function.Injective e := by
    intro t u h
    have hr : 2 * Real.pi * t = 2 * Real.pi * u := Complex.ofReal_injective h
    nlinarith [Real.pi_pos]
  obtain ⟨U, hU, hfinite⟩ := radialBallFourier_zeros_locallyFinite n (e s)
  refine ⟨e ⁻¹' U, he.continuousAt.preimage_mem_nhds hU, ?_⟩
  simpa only [preimage_inter, e, physicalBallZeroSet, physicalRadialBallFourier] using
    hfinite.preimage hinj.injOn

/-- A locally finite real set has dense complement. -/
theorem dense_complement_of_real_locallyFinite (Z : Set ℝ)
    (hZ : ∀ s : ℝ, ∃ U ∈ 𝓝 s, (U ∩ Z).Finite) : Dense Zᶜ := by
  intro s
  obtain ⟨U, hU, hfinite⟩ := hZ s
  have hdense : Dense (U ∩ Z)ᶜ := by
    simpa only [Set.diff_eq, univ_inter] using dense_univ.diff_finite hfinite
  have hfreq := mem_closure_iff_frequently.mp (hdense s)
  apply mem_closure_iff_frequently.mpr
  exact (hfreq.and_eventually hU).mono fun t ht => by
    exact fun htZ => ht.1 ⟨ht.2, htZ⟩

/-- No interval of real frequencies consists of physical radial zeros. -/
theorem physicalBallZeroSet_dense_complement (n : ℕ) : Dense (physicalBallZeroSet n)ᶜ :=
  dense_complement_of_real_locallyFinite _ (physicalBallZeroSet_locallyFinite n)

/-- The bounded-domain transform is analytic on the whole complex frequency space. -/
theorem domainEntireFourier_analyticOnNhd {d : ℕ} {Ω : Set (Euclidean d)}
    (hΩ : MeasurableSet Ω) (hbounded : Bornology.IsBounded Ω) (f : DomainL2 Ω) :
    AnalyticOnNhd ℂ (domainEntireFourier Ω hΩ f) univ := by
  obtain ⟨R, hR, hbound⟩ := hbounded.exists_pos_norm_le
  exact entireFourier_analyticOnNhd (domainExtension_integrable hΩ hbounded f) hR.le
    (domainExtension_supported_in_radius hΩ f hbound)

/-- Later-sphere annihilation gives an actual entire quotient by the normalized ball
transform and a compactly supported inverse distribution, without analytic hypotheses. -/
theorem normalized_ball_tail_compact_inverse (n : ℕ) {Ω : Set (Euclidean (n + 1))}
    (hΩ : MeasurableSet Ω) (hfinite : volume Ω ≠ ⊤) (hbounded : Bornology.IsBounded Ω)
    (N : ℕ) (f : DomainL2 Ω)
    (hvanish : ∀ ξ ∈ laterSpheres (ballZeroRadius n) N,
      inner (𝕜 := ℂ) f (exponentialL2 Ω hfinite ξ) = 0) :
    ∃ G : ComplexEuclidean (n + 1) → ℂ, ∃ u : TemperedDistribution (n + 1),
      AnalyticOnNhd ℂ G univ ∧
      (∀ z, MvPolynomial.eval (fun k => z k)
        (sphereDenominator (n + 1) (ballZeroRadius n) N) * domainEntireFourier Ω hΩ f z =
          normalizedBallFourier (n + 1) z * G z) ∧
      CompactlySupportedDistribution u ∧
      ∀ φ : SchwartzMap (Euclidean (n + 1)) ℂ,
        distributionFourier u φ = ∫ x, G (realToComplex x) * φ x := by
  let p := sphereDenominator (n + 1) (ballZeroRadius n) N
  let A : ComplexEuclidean (n + 1) → ℂ := fun z =>
    MvPolynomial.eval (fun k => z k) p * domainEntireFourier Ω hΩ f z
  have hp : AnalyticOnNhd ℂ (fun z : ComplexEuclidean (n + 1) =>
      MvPolynomial.eval (fun k => z k) p) univ :=
    AnalyticOnNhd.eval_continuousLinearMap'
      (fun k => PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin (n + 1) => ℂ) k) p
  have hA : AnalyticOnNhd ℂ A univ := hp.mul (domainEntireFourier_analyticOnNhd hΩ hbounded f)
  have hAzero : ∀ j z, squareSum (fun k => z k) = (ballZeroRadius n (j + 1) : ℂ) ^ 2 →
      A z = 0 := by
    intro j z hz
    apply polynomial_domainFourier_zero_on_all_quadrics hΩ hfinite hbounded
      (ballZeroRadius n) (fun j hj => ballZeroRadius_pos n hj) N f _ (j + 1) (by omega) z hz
    intro ξ hξ
    rw [← inner_conj_symm, hvanish ξ hξ, map_zero]
  obtain ⟨m, C, hC, hAbound⟩ :=
    polynomial_mul_domainEntireFourier_real_derivative_bound hΩ hbounded p f
  obtain ⟨c, R, hc, hlower⟩ := radialBallFourier_physical_distance_lower n
  obtain ⟨G, u, hG, hproduct, _htype, _hreal, hu, hFourier⟩ :=
    simple_quadric_division_compact_inverse A (normalizedBallFourier (n + 1))
      (fun j => ballZeroRadius n (j + 1)) hA (normalizedBallFourier_analytic n)
      (by rw [normalizedBallFourier_zero]; exact one_ne_zero)
      (ballZeroRadius_positive_indices n) (normalizedBallFourier_hasSimpleQuadricZeros_positive n)
      hAzero (finiteExponentialType_polynomial_mul_domainEntireFourier hΩ hbounded p f)
      (finiteExponentialType_normalizedBallFourier (n + 1))
      (physicalRadialBallFourier n) (physicalBallZeroSet n)
      (physicalBallZeroSet_isClosed n) (physicalBallZeroSet_nonempty n)
      (physicalBallZeroSet_dense_complement n) (physicalRadialBallFourier_eq n)
      (fun _ hs => hs) hC hc m (n + 2)
      (fun x => (hAbound x).1) (fun x => (hAbound x).2) hlower
  exact ⟨G, u, hG, hproduct, hu, hFourier⟩

end RieszEuclidean.CompleteMinimal
