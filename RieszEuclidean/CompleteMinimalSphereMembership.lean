import RieszEuclidean.CompleteMinimalMembership
import RieszEuclidean.CompleteMinimalBesselAsymptotic
import RieszEuclidean.CompleteMinimalRealUniqueness
import RieszEuclidean.CompleteMinimalResolvent
import RieszEuclidean.CompleteMinimalBallSupport

/-!
# Decay and actual supported synthesis of spherical quotients

The denominator estimates are algebraic. The numerator decay is proved for
the actual normalized ball transform, using its real radial ODE estimate.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators SchwartzMap FourierTransform

namespace RieszEuclidean.CompleteMinimal

/-- Every positive real ball-transform zero has the nonzero adjacent Bessel
normalization required by its actual physical resolvent. -/
theorem ballHelmholtzSquare_ne_zero_of_positive_zero (n : ℕ) {a : ℝ} (ha : 0 < a)
    (hz : radialBallFourier n (a : ℂ) = 0) :
    ballHelmholtzSquare n ((a ^ 2 : ℝ) : ℂ) ≠ 0 := by
  apply ballHelmholtzSquare_ne_zero_of_simple_zero n ha hz
  intro hd
  have hreal : realRadialBallFourier n a = 0 := by
    simp only [realRadialBallFourier, hz, Complex.zero_re]
  apply realRadialBallFourier_deriv_ne_zero_at_zero n ha hreal
  rw [realRadialBallFourier_deriv, hd, Complex.zero_re]

/-- Evaluation of the manuscript denominator is the product of its actual
Helmholtz Fourier symbols. -/
theorem sourceSphereDenominator_eval_quadratic {d : ℕ} (radius : ℕ → ℝ) (N : ℕ)
    (z : ComplexEuclidean d) :
    MvPolynomial.eval (fun j => z j) (sourceSphereDenominator d radius N) =
      ∏ j ∈ Finset.range N,
        (ballQuadraticForm d z - (((2 * Real.pi * radius (j + 1)) ^ 2 : ℝ) : ℂ)) := by
  simp only [sourceSphereDenominator, map_prod, sourceSphereFactor_eval]
  apply Finset.prod_congr rfl
  intro j _
  rw [ballQuadraticForm]
  push_cast
  ring

/-- The physical finite resolvent kernel in the canonical frequency-radius
normalization. Its zero-stage seed is the normalized ball L² function. -/
def sphereKernelPhysical (n : ℕ) (radius : ℕ → ℝ) (N : ℕ) : Euclidean (n + 1) → ℂ :=
  if N = 0 then normalizedBallL2 (n + 1) else fun x =>
    (((4 * Real.pi ^ 2) ^ N : ℝ) : ℂ) *
      ∑ j ∈ Finset.range N,
        resolventWeight (Finset.range N)
          (fun i => (((2 * Real.pi * radius (i + 1)) ^ 2 : ℝ) : ℂ)) j *
            ballResolvent n (2 * Real.pi * radius (j + 1)) x

/-- The canonical entire spherical multiplier is the actual Fourier integral
of its physical finite resolvent kernel. -/
def sphereKernelMultiplier (n : ℕ) (radius : ℕ → ℝ) (N : ℕ) :
    ComplexEuclidean (n + 1) → ℂ := entireFourier (sphereKernelPhysical n radius N)

@[simp] theorem sphereKernelMultiplier_zero (n : ℕ) (radius : ℕ → ℝ) :
    sphereKernelMultiplier n radius 0 = normalizedBallFourier (n + 1) := by
  simp only [sphereKernelMultiplier, sphereKernelPhysical, if_pos rfl]
  exact entireFourier_normalizedBallL2 (n + 1)

/-- The physical resolvent sum is integrable whenever each actual radial
resolvent has its nonzero boundary normalization. -/
theorem sphereKernelPhysical_integrable (n : ℕ) (radius : ℕ → ℝ) (N : ℕ)
    (hb : ∀ j, 0 < j → j ≤ N →
      ballHelmholtzSquare n ((((2 * Real.pi * radius j) ^ 2 : ℝ) : ℂ)) ≠ 0) :
    Integrable (sphereKernelPhysical n radius N) := by
  classical
  by_cases hN : N = 0
  · simpa only [sphereKernelPhysical, if_pos hN] using normalizedBallL2_integrable (n + 1)
  · simp only [sphereKernelPhysical, if_neg hN]
    apply Integrable.const_mul
    apply integrable_finset_sum
    intro j hj
    exact (ballResolvent_integrable n _ (hb (j + 1) (by omega)
      (by simpa using Finset.mem_range.mp hj))).const_mul _

/-- The actual physical finite sum vanishes almost everywhere off the closed
unit ball, independently of its Fourier quotient identity. -/
theorem sphereKernelPhysical_supported (n : ℕ) (radius : ℕ → ℝ) (N : ℕ) :
    ∀ᵐ x, x ∉ Metric.closedBall (0 : Euclidean (n + 1)) 1 →
      sphereKernelPhysical n radius N x = 0 := by
  classical
  by_cases hN : N = 0
  · simpa only [sphereKernelPhysical, if_pos hN] using normalizedBallL2_supported (n + 1)
  · apply Filter.Eventually.of_forall
    intro x hx
    simp only [sphereKernelPhysical, if_neg hN]
    have hzero : ∀ j, ballResolvent n (2 * Real.pi * radius (j + 1)) x = 0 := by
      intro j
      exact image_eq_zero_of_nmem_tsupport
        (fun h => hx (ballResolvent_tsupport_subset n _ h))
    simp only [hzero, mul_zero, Finset.sum_const_zero]

/-- The Fourier integral of the actual finite physical resolvent sum is entire. -/
theorem sphereKernelMultiplier_differentiable (n : ℕ) (radius : ℕ → ℝ) (N : ℕ)
    (hb : ∀ j, 0 < j → j ≤ N →
      ballHelmholtzSquare n ((((2 * Real.pi * radius j) ^ 2 : ℝ) : ℂ)) ≠ 0) :
    Differentiable ℂ (sphereKernelMultiplier n radius N) := by
  apply entireFourier_differentiable (sphereKernelPhysical_integrable n radius N hb) zero_le_one
  filter_upwards [sphereKernelPhysical_supported n radius N] with x hx
  intro hne
  by_contra hn
  apply hne
  apply hx
  simpa only [Metric.mem_closedBall, dist_zero_right] using hn

/-- The concrete finite physical kernel is square integrable. -/
theorem sphereKernelPhysical_memLp (n : ℕ) (radius : ℕ → ℝ) (N : ℕ)
    (hb : ∀ j, 0 < j → j ≤ N →
      ballHelmholtzSquare n ((((2 * Real.pi * radius j) ^ 2 : ℝ) : ℂ)) ≠ 0) :
    MemLp (sphereKernelPhysical n radius N) 2 volume := by
  classical
  by_cases hN : N = 0
  · simpa only [sphereKernelPhysical, if_pos hN] using Lp.memLp (normalizedBallL2 (n + 1))
  · simp only [sphereKernelPhysical, if_neg hN]
    apply MemLp.const_mul
    apply memLp_finset_sum
    intro j hj
    exact (ballResolvent_memLp n _ (hb (j + 1) (by omega)
      (by simpa using Finset.mem_range.mp hj))).const_mul _

/-- The actual L² inverse of the spherical multiplier. -/
def sphereKernelL2 (n : ℕ) (radius : ℕ → ℝ) (N : ℕ)
    (hb : ∀ j, 0 < j → j ≤ N →
      ballHelmholtzSquare n ((((2 * Real.pi * radius j) ^ 2 : ℝ) : ℂ)) ≠ 0) : FullL2 (n + 1) :=
  (sphereKernelPhysical_memLp n radius N hb).toLp (sphereKernelPhysical n radius N)

/-- The concrete L² inverse has the explicit physical kernel as representative. -/
theorem sphereKernelL2_ae (n : ℕ) (radius : ℕ → ℝ) (N : ℕ)
    (hb : ∀ j, 0 < j → j ≤ N →
      ballHelmholtzSquare n ((((2 * Real.pi * radius j) ^ 2 : ℝ) : ℂ)) ≠ 0) :
    (sphereKernelL2 n radius N hb : Euclidean (n + 1) → ℂ) =ᵐ[volume]
      sphereKernelPhysical n radius N :=
  (sphereKernelPhysical_memLp n radius N hb).coeFn_toLp

/-- The actual distribution inverse of the spherical multiplier. -/
def sphereKernelDistribution (n : ℕ) (radius : ℕ → ℝ) (N : ℕ)
    (hb : ∀ j, 0 < j → j ≤ N →
      ballHelmholtzSquare n ((((2 * Real.pi * radius j) ^ 2 : ℝ) : ℂ)) ≠ 0) :
    TemperedDistribution (n + 1) := l2Distribution (sphereKernelL2 n radius N hb)

/-- The physical inverse distribution is supported in the closed unit ball. -/
theorem sphereKernelDistribution_supported (n : ℕ) (radius : ℕ → ℝ) (N : ℕ)
    (hb : ∀ j, 0 < j → j ≤ N →
      ballHelmholtzSquare n ((((2 * Real.pi * radius j) ^ 2 : ℝ) : ℂ)) ≠ 0) :
    DistributionSupportedIn (sphereKernelDistribution n radius N hb)
      (Metric.closedBall (0 : Euclidean (n + 1)) 1) := by
  apply l2Distribution_supported
  filter_upwards [sphereKernelL2_ae n radius N hb, sphereKernelPhysical_supported n radius N]
    with x hx hs
  intro hn
  exact hx.trans (hs hn)

/-- The canonical entire multiplier is the actual Fourier distribution of its
supported physical inverse, expressed on arbitrary Schwartz tests. -/
theorem sphereKernelDistribution_fourier_integral (n : ℕ) (radius : ℕ → ℝ) (N : ℕ)
    (hb : ∀ j, 0 < j → j ≤ N →
      ballHelmholtzSquare n ((((2 * Real.pi * radius j) ^ 2 : ℝ) : ℂ)) ≠ 0)
    (φ : 𝓢(Euclidean (n + 1), ℂ)) :
    distributionFourier (sphereKernelDistribution n radius N hb) φ =
      ∫ x, sphereKernelMultiplier n radius N (realToComplex x) * φ x := by
  have hint : Integrable (sphereKernelL2 n radius N hb : Euclidean (n + 1) → ℂ) :=
    (sphereKernelPhysical_integrable n radius N hb).congr (sphereKernelL2_ae n radius N hb).symm
  rw [sphereKernelDistribution, distributionFourier_l2_integral _ hint]
  have heq : 𝓕 (sphereKernelL2 n radius N hb : Euclidean (n + 1) → ℂ) =
      fun x => sphereKernelMultiplier n radius N (realToComplex x) := by
    funext x
    rw [sphereKernelMultiplier, ← entireFourier_realToComplex]
    rw [entireFourier_congr (sphereKernelL2_ae n radius N hb)]
  rw [heq]

/-- The canonical multiplier is the explicit finite sum of entire physical
resolvent transforms at every nonzero stage. -/
theorem sphereKernelMultiplier_sum (n : ℕ) (radius : ℕ → ℝ) {N : ℕ} (hN : N ≠ 0)
    (hb : ∀ j, 0 < j → j ≤ N →
      ballHelmholtzSquare n ((((2 * Real.pi * radius j) ^ 2 : ℝ) : ℂ)) ≠ 0)
    (z : ComplexEuclidean (n + 1)) :
    sphereKernelMultiplier n radius N z = (((4 * Real.pi ^ 2) ^ N : ℝ) : ℂ) *
      ∑ j ∈ Finset.range N,
        resolventWeight (Finset.range N)
          (fun i => (((2 * Real.pi * radius (i + 1)) ^ 2 : ℝ) : ℂ)) j *
            entireFourier (ballResolvent n (2 * Real.pi * radius (j + 1))) z := by
  have hint : ∀ j ∈ Finset.range N, Integrable (fun x : Euclidean (n + 1) =>
      ballResolvent n (2 * Real.pi * radius (j + 1)) x * complexFourierKernel x z) := by
    intro j hj
    apply entireFourier_integrable (ballResolvent_integrable n _
      (hb (j + 1) (by omega) (by simpa using Finset.mem_range.mp hj)))
    apply Filter.Eventually.of_forall
    intro x hx
    have hs : x ∈ Metric.closedBall (0 : Euclidean (n + 1)) 1 :=
      ballResolvent_tsupport_subset n _ (subset_closure hx)
    simpa only [Metric.mem_closedBall, dist_zero_right] using hs
  simp only [sphereKernelMultiplier, sphereKernelPhysical, if_neg hN, entireFourier]
  let c : ℂ := (((4 * Real.pi ^ 2) ^ N : ℝ) : ℂ)
  let w : ℕ → ℂ := resolventWeight (Finset.range N)
    (fun i => (((2 * Real.pi * radius (i + 1)) ^ 2 : ℝ) : ℂ))
  let f : ℕ → Euclidean (n + 1) → ℂ := fun j => ballResolvent n (2 * Real.pi * radius (j + 1))
  change (∫ x, c * (∑ j ∈ Finset.range N, w j * f j x) * complexFourierKernel x z) =
    c * ∑ j ∈ Finset.range N, w j * ∫ x, f j x * complexFourierKernel x z
  have heq : (fun x => c * (∑ j ∈ Finset.range N, w j * f j x) * complexFourierKernel x z) =
      fun x => c * ∑ j ∈ Finset.range N, w j * (f j x * complexFourierKernel x z) := by
    funext x
    rw [mul_assoc, Finset.sum_mul]
    congr 1
    exact Finset.sum_congr rfl fun j _ => mul_assoc _ _ _
  rw [heq, integral_const_mul, integral_finset_sum (Finset.range N)
    (fun j hj => (hint j hj).const_mul (w j))]
  simp only [integral_const_mul]
  rfl

/-- The Lagrange partial-fraction coefficients multiply actual resolvent
identities into their finite denominator identity, including at the poles. -/
theorem resolvent_sum_product_identity {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (a : ι → ℂ) (ha : Set.InjOn a s) (hs : s.Nonempty)
    (q k : ℂ) (F : ι → ℂ) (hF : ∀ i ∈ s, (q - a i) * F i = k) :
    (∏ i ∈ s, (q - a i)) * (∑ i ∈ s, resolventWeight s a i * F i) = k := by
  rw [Finset.mul_sum]
  calc
    _ = ∑ i ∈ s, k * (resolventWeight s a i * ∏ j ∈ s.erase i, (q - a j)) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [← Finset.mul_prod_erase s (fun j => q - a j) hi]
      calc
        _ = ((q - a i) * F i) * (resolventWeight s a i * ∏ j ∈ s.erase i, (q - a j)) := by ring
        _ = _ := by rw [hF i hi]
    _ = k * (∑ i ∈ s, resolventWeight s a i * ∏ j ∈ s.erase i, (q - a j)) :=
      (Finset.mul_sum _ _ _).symm
    _ = k := by rw [resolventWeight_identity s a ha hs q, mul_one]

/-- Replacing a positive radial power by the Japanese-bracket power loses only
the explicit factor `2^s` outside the unit ball. -/
theorem radial_rpow_le_bracket {r s : ℝ} (hr : 1 ≤ r) (hs : 0 ≤ s) :
    r ^ (-s) ≤ 2 ^ s * (1 + r) ^ (-s) := by
  have hp : 0 < (1 + r) / 2 := by linarith
  have hle := Real.rpow_le_rpow_of_nonpos hp (by linarith : (1 + r) / 2 ≤ r)
    (neg_nonpos.mpr hs)
  calc
    _ ≤ ((1 + r) / 2) ^ (-s) := hle
    _ = _ := by
      rw [Real.div_rpow (by linarith) (by norm_num),
        Real.rpow_neg (x := 2) (by norm_num)]
      simp only [div_inv_eq_mul, mul_comm]

/-- The actual normalized unit-ball transform has the required radial decay
in the physical frequency variable, including its `2π` normalization. -/
theorem normalizedBallFourier_ball_decay (n : ℕ) :
    ∃ C R : ℝ, 0 ≤ C ∧ ∀ x : Euclidean (n + 1), R ≤ ‖x‖ →
      ‖normalizedBallFourier (n + 1) (realToComplex x)‖ ≤
        C * (1 + ‖x‖) ^ (-((n + 1 : ℕ) + 1 : ℝ) / 2) := by
  let b : ℝ := ((n + 2 : ℕ) : ℝ) / 2
  obtain ⟨M, hM, hb⟩ := realRadialBallFourier_decay n (a := 1) zero_lt_one
  refine ⟨M * (2 * Real.pi) ^ (-b) * 2 ^ b, max 1 ((2 * Real.pi)⁻¹), by positivity, ?_⟩
  intro x hx
  have hunit : 1 ≤ ‖x‖ := (le_max_left _ _).trans hx
  have hscale : 1 ≤ 2 * Real.pi * ‖x‖ := by
    have h := (le_max_right 1 ((2 * Real.pi)⁻¹)).trans hx
    have h' : 1 / (2 * Real.pi) ≤ ‖x‖ := by simpa only [one_div] using h
    simpa only [mul_comm] using (div_le_iff₀ (by positivity : 0 < 2 * Real.pi)).mp h'
  rw [normalizedBallFourier_real_radial, radialBallFourier_ofReal_eq, Complex.norm_real,
    Real.norm_eq_abs]
  have hbracket := radial_rpow_le_bracket hunit (show 0 ≤ b by dsimp [b]; positivity)
  calc
    _ ≤ M * (2 * Real.pi * ‖x‖) ^ (-b) := hb _ hscale
    _ = (M * (2 * Real.pi) ^ (-b)) * ‖x‖ ^ (-b) := by
      rw [Real.mul_rpow (by positivity) (norm_nonneg _)]; ring
    _ ≤ (M * (2 * Real.pi) ^ (-b)) * (2 ^ b * (1 + ‖x‖) ^ (-b)) :=
      mul_le_mul_of_nonneg_left hbracket (by positivity)
    _ = _ := by dsimp [b]; push_cast; ring

/-- Every finite spherical denominator is uniformly bounded below by its full
degree power outside an explicitly bounded frequency region. -/
theorem sphereDenominator_norm_lower_bound {d : ℕ} (radius : ℕ → ℝ) (N : ℕ) :
    ∃ R : ℝ, 1 ≤ R ∧ ∀ x : Euclidean d, R ≤ ‖x‖ →
      (1 + ‖x‖) ^ (2 * N) / 8 ^ N ≤
        ‖MvPolynomial.eval (fun j => (x j : ℂ)) (sphereDenominator d radius N)‖ := by
  let A : ℝ := ∑ j ∈ Finset.range N, |radius (j + 1)|
  have hA : 0 ≤ A := Finset.sum_nonneg fun _ _ => abs_nonneg _
  refine ⟨1 + 2 * A, by linarith, fun x hx => ?_⟩
  have hr : 1 ≤ ‖x‖ := by linarith
  have hfactor : ∀ j ∈ Finset.range N,
      (1 + ‖x‖) ^ 2 / 8 ≤ ‖((‖x‖ ^ 2 - radius (j + 1) ^ 2 : ℝ) : ℂ)‖ := by
    intro j hj
    have hjA : |radius (j + 1)| ≤ A :=
      Finset.single_le_sum (fun k _ => abs_nonneg (radius (k + 1))) hj
    have hhalf : 2 * |radius (j + 1)| ≤ ‖x‖ := by linarith
    have hsq := sq_le_sq₀ (by positivity : 0 ≤ 2 * |radius (j + 1)|) (norm_nonneg x)
    have hrad : 4 * radius (j + 1) ^ 2 ≤ ‖x‖ ^ 2 := by
      have h := hsq.mpr hhalf
      rw [mul_pow, sq_abs] at h
      norm_num at h ⊢
      exact h
    have hpos : 0 ≤ ‖x‖ ^ 2 - radius (j + 1) ^ 2 := by nlinarith [sq_nonneg (radius (j + 1))]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hpos]
    nlinarith [sq_nonneg (‖x‖ - 1)]
  rw [sphereDenominator_eval_real, norm_prod]
  have hprod := Finset.prod_le_prod (s := Finset.range N)
    (fun _ _ => by positivity : ∀ j ∈ Finset.range N, 0 ≤ (1 + ‖x‖) ^ 2 / 8) hfactor
  simpa only [Finset.prod_const, Finset.card_range, div_pow, ← pow_mul] using hprod

/-- Every actual spherical quotient of the ball transform has the sharp
denominator decay. The estimate is derived from its product identity. -/
theorem sphere_quotient_ball_decay (n : ℕ) (radius : ℕ → ℝ) (N : ℕ)
    (χ : ComplexEuclidean (n + 1) → ℂ)
    (hχ : ∀ x : Euclidean (n + 1), normalizedBallFourier (n + 1) (realToComplex x) =
      MvPolynomial.eval (fun j => (x j : ℂ)) (sphereDenominator (n + 1) radius N) *
        χ (realToComplex x)) :
    ∃ C R : ℝ, 0 ≤ C ∧ ∀ x : Euclidean (n + 1), R ≤ ‖x‖ →
      ‖χ (realToComplex x)‖ ≤ C * (1 + ‖x‖) ^
        (-(2 * N : ℕ) - ((n + 1 : ℕ) + 1 : ℝ) / 2) := by
  obtain ⟨C, R, hC, hk⟩ := normalizedBallFourier_ball_decay n
  obtain ⟨T, _, hQ⟩ := sphereDenominator_norm_lower_bound (d := n + 1) radius N
  refine ⟨C * 8 ^ N, max R T, by positivity, fun x hx => ?_⟩
  have ht := (le_max_right R T).trans hx
  have hr : 0 < 1 + ‖x‖ := by positivity
  have hlo : 0 < (1 + ‖x‖) ^ (2 * N) / 8 ^ N := by positivity
  have hid : ‖MvPolynomial.eval (fun j => (x j : ℂ))
      (sphereDenominator (n + 1) radius N)‖ * ‖χ (realToComplex x)‖ =
      ‖normalizedBallFourier (n + 1) (realToComplex x)‖ := by
    rw [← norm_mul, ← hχ]
  have hdiv : ‖χ (realToComplex x)‖ ≤
      ‖normalizedBallFourier (n + 1) (realToComplex x)‖ /
        ((1 + ‖x‖) ^ (2 * N) / 8 ^ N) := by
    apply (le_div_iff₀ hlo).mpr
    calc
      _ ≤ ‖χ (realToComplex x)‖ *
          ‖MvPolynomial.eval (fun j => (x j : ℂ)) (sphereDenominator (n + 1) radius N)‖ :=
        mul_le_mul_of_nonneg_left (hQ x ht) (norm_nonneg _)
      _ = _ := by rw [mul_comm, hid]
  calc
    _ ≤ ‖normalizedBallFourier (n + 1) (realToComplex x)‖ /
        ((1 + ‖x‖) ^ (2 * N) / 8 ^ N) := hdiv
    _ ≤ (C * (1 + ‖x‖) ^ (-((n + 1 : ℕ) + 1 : ℝ) / 2)) /
        ((1 + ‖x‖) ^ (2 * N) / 8 ^ N) :=
      div_le_div_of_nonneg_right (hk x ((le_max_left R T).trans hx)) hlo.le
    _ = _ := by
      rw [div_div_eq_mul_div, div_eq_mul_inv]
      calc
        _ = (C * 8 ^ N) * ((1 + ‖x‖) ^ (-((n + 1 : ℕ) + 1 : ℝ) / 2) *
            (1 + ‖x‖) ^ (-((2 * N : ℕ) : ℝ))) := by
          rw [Real.rpow_neg hr.le, Real.rpow_natCast]; ring
        _ = _ := by rw [← Real.rpow_add hr]; congr 2; ring

/-- Polynomial evaluation on complex Euclidean space is complex differentiable. -/
theorem complexPolynomialEvaluation_differentiable {d : ℕ} (p : ComplexPolynomial d) :
    Differentiable ℂ (fun z : ComplexEuclidean d => MvPolynomial.eval (fun j => z j) p) := by
  induction p using MvPolynomial.induction_on with
  | C c => simpa only [MvPolynomial.eval_C] using differentiable_const c
  | add p q hp hq => simpa only [map_add] using hp.add hq
  | mul_X p i hp =>
    have hi : Differentiable ℂ (fun z : ComplexEuclidean d => z i) :=
      (PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin d => ℂ) i).differentiable
    simpa only [map_mul, MvPolynomial.eval_X] using hp.mul hi

/-- The physical finite sum satisfies the entire denominator identity when
its individual actual resolvents satisfy the real divisor identities. -/
theorem sphereKernelMultiplier_product_of_resolvent_identities (n : ℕ) (radius : ℕ → ℝ)
    (N : ℕ) (hstrict : StrictMono radius) (hpositive : ∀ j, 0 < j → 0 < radius j)
    (hb : ∀ j, 0 < j → j ≤ N →
      ballHelmholtzSquare n ((((2 * Real.pi * radius j) ^ 2 : ℝ) : ℂ)) ≠ 0)
    (hdivisor : ∀ j, 0 < j → j ≤ N → ∀ x : Euclidean (n + 1),
      (ballQuadraticForm (n + 1) (realToComplex x) -
          (((2 * Real.pi * radius j) ^ 2 : ℝ) : ℂ)) *
        entireFourier (ballResolvent n (2 * Real.pi * radius j)) (realToComplex x) =
          normalizedBallFourier (n + 1) (realToComplex x)) :
    ∀ z, normalizedBallFourier (n + 1) z =
      MvPolynomial.eval (fun j => z j) (sphereDenominator (n + 1) radius N) *
        sphereKernelMultiplier n radius N z := by
  by_cases hN : N = 0
  · subst N
    simp only [sphereDenominator_zero, map_one, sphereKernelMultiplier_zero, one_mul, implies_true]
  · have ha : Set.InjOn (fun i => (((2 * Real.pi * radius (i + 1)) ^ 2 : ℝ) : ℂ))
        (Finset.range N) := by
      intro i _ j _ hij
      have hi : 0 < 2 * Real.pi * radius (i + 1) := mul_pos (by positivity) (hpositive _ (by omega))
      have hj : 0 < 2 * Real.pi * radius (j + 1) := mul_pos (by positivity) (hpositive _ (by omega))
      have hr := (sq_eq_sq₀ hi.le hj.le).mp (Complex.ofReal_injective hij)
      have hri := mul_left_cancel₀ (show 2 * Real.pi ≠ 0 by positivity) hr
      exact Nat.add_right_cancel (hstrict.injective hri)
    have hreal : ∀ x : Euclidean (n + 1), normalizedBallFourier (n + 1) (realToComplex x) =
        MvPolynomial.eval (fun j => (x j : ℂ)) (sphereDenominator (n + 1) radius N) *
          sphereKernelMultiplier n radius N (realToComplex x) := by
      intro x
      have hraw := resolvent_sum_product_identity (Finset.range N)
        (fun i => (((2 * Real.pi * radius (i + 1)) ^ 2 : ℝ) : ℂ)) ha
        (Finset.nonempty_range_iff.mpr hN) (ballQuadraticForm (n + 1) (realToComplex x))
        (normalizedBallFourier (n + 1) (realToComplex x))
        (fun j => entireFourier (ballResolvent n (2 * Real.pi * radius (j + 1))) (realToComplex x))
        (fun j hj => hdivisor (j + 1) (by omega) (by simpa using Finset.mem_range.mp hj) x)
      have hscale : (((4 * Real.pi ^ 2) ^ N : ℝ) : ℂ) *
          MvPolynomial.eval (fun j => (x j : ℂ)) (sphereDenominator (n + 1) radius N) =
          ∏ j ∈ Finset.range N, (ballQuadraticForm (n + 1) (realToComplex x) -
            (((2 * Real.pi * radius (j + 1)) ^ 2 : ℝ) : ℂ)) := by
        rw [← sourceSphereDenominator_eval_quadratic radius N (realToComplex x),
          sourceSphereDenominator_eq]
        simp only [map_mul, MvPolynomial.eval_C, realToComplex_apply]
      rw [sphereKernelMultiplier_sum n radius hN hb]
      rw [← hscale] at hraw
      calc
        _ = _ := hraw.symm
        _ = _ := by ring
    have hEq := entire_eq_of_eq_on_real (normalizedBallFourier_differentiable (n + 1))
      ((complexPolynomialEvaluation_differentiable (sphereDenominator (n + 1) radius N)).mul
        (sphereKernelMultiplier_differentiable n radius N hb)) hreal
    exact fun z => congrFun hEq z

/-- A spherical quotient with an actual supported inverse distribution
realizes all allowed polynomial numerators on every complex frequency. -/
theorem sphere_quotient_synthesize (n : ℕ) (radius : ℕ → ℝ) (N : ℕ)
    (χ : ComplexEuclidean (n + 1) → ℂ) (hdiff : Differentiable ℂ χ)
    (hproduct : ∀ z, normalizedBallFourier (n + 1) z =
      MvPolynomial.eval (fun j => z j) (sphereDenominator (n + 1) radius N) * χ z)
    (u : TemperedDistribution (n + 1))
    (hu : DistributionSupportedIn u (Metric.closedBall (0 : Euclidean (n + 1)) 1))
    (htransform : ∀ φ : 𝓢(Euclidean (n + 1), ℂ),
      distributionFourier u φ = ∫ x, χ (realToComplex x) * φ x)
    (Ω : Set (Euclidean (n + 1))) (hΩ : MeasurableSet Ω) (hbounded : Bornology.IsBounded Ω)
    (hBΩ : Metric.closedBall (0 : Euclidean (n + 1)) 1 ≤ᵐ[volume] Ω)
    (p : ComplexPolynomial (n + 1)) (hp : p.totalDegree ≤ 2 * N) :
    ∃ f : DomainL2 Ω, SupportedOn Ω f (Metric.closedBall (0 : Euclidean (n + 1)) 1) ∧
      domainEntireFourier Ω hΩ f = fun z => χ z * MvPolynomial.eval (fun j => z j) p := by
  have hemb : Continuous (realToComplex : Euclidean (n + 1) → ComplexEuclidean (n + 1)) :=
    (PiLp.continuous_equiv_symm 2 _).comp (continuous_pi fun j => by
      change Continuous (fun x : Euclidean (n + 1) => (x j : ℂ))
      fun_prop)
  have hcont : Continuous (fun x : Euclidean (n + 1) => χ (realToComplex x)) :=
    hdiff.continuous.comp hemb
  obtain ⟨C, R, _, hdecay⟩ := sphere_quotient_ball_decay n radius N χ
    (fun x => hproduct (realToComplex x))
  obtain ⟨f, hs, _, heq⟩ := exists_domainL2_polynomial_numerator_tail
    Metric.isClosed_closedBall hΩ hbounded hBΩ u hu (fun x => χ (realToComplex x))
    hcont hdecay htransform p hp
  refine ⟨f, hs, entire_eq_of_eq_on_real (domainEntireFourier_differentiable hΩ hbounded f)
    (hdiff.mul (complexPolynomialEvaluation_differentiable p)) fun x => ?_⟩
  simpa only [polynomialEvaluation_apply, mul_comm] using heq x

/-- The canonical multiplier's actual physical inverse supplies numerator
synthesis as soon as its explicit denominator product identity is established. -/
theorem sphereKernelMultiplier_synthesize (n : ℕ) (radius : ℕ → ℝ) (N : ℕ)
    (hb : ∀ j, 0 < j → j ≤ N →
      ballHelmholtzSquare n ((((2 * Real.pi * radius j) ^ 2 : ℝ) : ℂ)) ≠ 0)
    (hproduct : ∀ z, normalizedBallFourier (n + 1) z =
      MvPolynomial.eval (fun j => z j) (sphereDenominator (n + 1) radius N) *
        sphereKernelMultiplier n radius N z)
    (Ω : Set (Euclidean (n + 1))) (hΩ : MeasurableSet Ω) (hbounded : Bornology.IsBounded Ω)
    (hBΩ : Metric.closedBall (0 : Euclidean (n + 1)) 1 ≤ᵐ[volume] Ω)
    (p : ComplexPolynomial (n + 1)) (hp : p.totalDegree ≤ 2 * N) :
    ∃ f : DomainL2 Ω, SupportedOn Ω f (Metric.closedBall (0 : Euclidean (n + 1)) 1) ∧
      domainEntireFourier Ω hΩ f = fun z =>
        sphereKernelMultiplier n radius N z * MvPolynomial.eval (fun j => z j) p :=
  sphere_quotient_synthesize n radius N (sphereKernelMultiplier n radius N)
    (sphereKernelMultiplier_differentiable n radius N hb) hproduct
    (sphereKernelDistribution n radius N hb) (sphereKernelDistribution_supported n radius N hb)
    (sphereKernelDistribution_fourier_integral n radius N hb) Ω hΩ hbounded hBΩ p hp

/-- At genuine positive ball-transform zero radii, the canonical physical
multiplier is an entire quotient of the ball transform by the finite denominator. -/
theorem sphereKernelMultiplier_product (n : ℕ) (radius : ℕ → ℝ) (N : ℕ)
    (hstrict : StrictMono radius) (hpositive : ∀ j, 0 < j → 0 < radius j)
    (hzero : ∀ j, 0 < j → j ≤ N → radialBallFourier n (2 * Real.pi * radius j : ℝ) = 0) :
    ∀ z, normalizedBallFourier (n + 1) z =
      MvPolynomial.eval (fun j => z j) (sphereDenominator (n + 1) radius N) *
        sphereKernelMultiplier n radius N z := by
  have hb : ∀ j, 0 < j → j ≤ N →
      ballHelmholtzSquare n ((((2 * Real.pi * radius j) ^ 2 : ℝ) : ℂ)) ≠ 0 := by
    intro j hj hJ
    exact ballHelmholtzSquare_ne_zero_of_positive_zero n
      (mul_pos (by positivity) (hpositive j hj)) (hzero j hj hJ)
  apply sphereKernelMultiplier_product_of_resolvent_identities n radius N hstrict hpositive hb
  intro j hj hJ x
  rw [entireFourier_realToComplex]
  exact fourier_ballResolvent_divisor n
    (ne_of_gt (mul_pos (by positivity) (hpositive j hj))) (hzero j hj hJ) (hb j hj hJ) x

/-- Every allowed polynomial numerator over the canonical spherical quotient
is the entire Fourier transform of an actual ball-supported domain-L² vector.
Only actual positive ball-transform zero radii are required. -/
theorem sphereKernelMultiplier_synthesize_of_zeros (n : ℕ) (radius : ℕ → ℝ) (N : ℕ)
    (hstrict : StrictMono radius) (hpositive : ∀ j, 0 < j → 0 < radius j)
    (hzero : ∀ j, 0 < j → j ≤ N → radialBallFourier n (2 * Real.pi * radius j : ℝ) = 0)
    (Ω : Set (Euclidean (n + 1))) (hΩ : MeasurableSet Ω) (hbounded : Bornology.IsBounded Ω)
    (hBΩ : Metric.closedBall (0 : Euclidean (n + 1)) 1 ≤ᵐ[volume] Ω)
    (p : ComplexPolynomial (n + 1)) (hp : p.totalDegree ≤ 2 * N) :
    ∃ f : DomainL2 Ω, SupportedOn Ω f (Metric.closedBall (0 : Euclidean (n + 1)) 1) ∧
      domainEntireFourier Ω hΩ f = fun z =>
        sphereKernelMultiplier n radius N z * MvPolynomial.eval (fun j => z j) p := by
  have hb : ∀ j, 0 < j → j ≤ N →
      ballHelmholtzSquare n ((((2 * Real.pi * radius j) ^ 2 : ℝ) : ℂ)) ≠ 0 := by
    intro j hj hJ
    exact ballHelmholtzSquare_ne_zero_of_positive_zero n
      (mul_pos (by positivity) (hpositive j hj)) (hzero j hj hJ)
  exact sphereKernelMultiplier_synthesize n radius N hb
    (sphereKernelMultiplier_product n radius N hstrict hpositive hzero) Ω hΩ hbounded hBΩ p hp

end RieszEuclidean.CompleteMinimal
