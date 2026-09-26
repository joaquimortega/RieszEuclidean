import RieszEuclidean.CompleteMinimalBallSupport
import RieszEuclidean.CompleteMinimalWeakDerivatives
import RieszEuclidean.CompleteMinimalDifferentialOperators
import RieszEuclidean.CompleteMinimalRealUniqueness
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.MeasureTheory.Integral.DivergenceTheorem

/-!
# A genuine compactly supported ball Helmholtz resolvent

The adjacent radial solution is constructed from the actual ball Fourier series.
Its squared-radius formula is smooth at the origin and has zero value and first
normal derivative at the chosen boundary zero. Off-countable-line integration
by parts proves the zero-extended distributional equation. The Fourier quotient
then follows from actual Fourier derivative symbols and test-function uniqueness.
-/

noncomputable section
open MeasureTheory Set SchwartzMap
open scoped SchwartzMap FourierTransform ENNReal Topology

namespace RieszEuclidean.CompleteMinimal

/-- Zero extension preserves a zero derivative at a zero of the original
function, independently of the geometry of the extension set. -/
theorem hasFDerivAt_indicator_zero {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {S : Set E} {f : E → F} {x : E} (hf : HasFDerivAt f (0 : E →L[ℝ] F) x)
    (hx : f x = 0) : HasFDerivAt (S.indicator f) (0 : E →L[ℝ] F) x := by
  classical
  rw [hasFDerivAt_iff_isLittleO_nhds_zero] at hf ⊢
  have hix : S.indicator f x = 0 := by simp [Set.indicator_apply, hx]
  simp only [hx, hix, ContinuousLinearMap.zero_apply, sub_zero] at hf ⊢
  apply Asymptotics.IsLittleO.of_bound
  intro ε hε
  filter_upwards [hf.bound hε] with y hy
  by_cases hxy : x + y ∈ S
  · simpa only [Set.indicator_of_mem hxy] using hy
  · simp only [Set.indicator_of_not_mem hxy, norm_zero]
    exact mul_nonneg hε.le (norm_nonneg y)

/-- The primitive spherical radial solution, in the squared variable. This
representation is smooth at the spatial origin. -/
def ballHelmholtzSquare (n : ℕ) (z : ℂ) : ℂ :=
  ballSquareFunction n z + (2 / (n + 1 : ℕ) : ℂ) * z * deriv (ballSquareFunction n) z

theorem ballHelmholtzSquare_analytic (n : ℕ) :
    AnalyticOnNhd ℂ (ballHelmholtzSquare n) Set.univ := by
  exact (ballSquareFunction_analytic n).add
    ((analyticOnNhd_const.mul analyticOnNhd_id).mul (ballSquareFunction_analytic n).deriv)

/-- The ball equation differentiates to the adjacent spherical solution. -/
theorem ballHelmholtzSquare_hasDerivAt (n : ℕ) (z : ℂ) :
    HasDerivAt (ballHelmholtzSquare n)
      (-ballSquareFunction n z / (2 * (n + 1 : ℕ))) z := by
  have hF := ((ballSquareFunction_analytic n) z (mem_univ _)).differentiableAt.hasDerivAt
  have hF' := ((ballSquareFunction_analytic n).deriv z (mem_univ _)).differentiableAt.hasDerivAt
  have h := hF.add (((hasDerivAt_id z).const_mul (2 / (n + 1 : ℕ) : ℂ)).mul hF')
  convert h using 1
  have hd : (n + 1 : ℂ) ≠ 0 := by exact_mod_cast (by omega : n + 1 ≠ 0)
  have ho := ballSquareFunction_ode n z
  dsimp only [id]
  push_cast at ho ⊢
  field_simp [hd]
  linear_combination -(n + 1 : ℂ) * ho

theorem ballHelmholtzSquare_deriv (n : ℕ) (z : ℂ) :
    deriv (ballHelmholtzSquare n) z =
      -ballSquareFunction n z / (2 * (n + 1 : ℕ)) :=
  (ballHelmholtzSquare_hasDerivAt n z).deriv

/-- The adjacent spherical solution satisfies its own squared radial equation. -/
theorem ballHelmholtzSquare_ode (n : ℕ) (z : ℂ) :
    4 * z * deriv (deriv (ballHelmholtzSquare n)) z +
      2 * (n + 1 : ℕ) * deriv (ballHelmholtzSquare n) z +
      ballHelmholtzSquare n z = 0 := by
  have hF := ((ballSquareFunction_analytic n) z (mem_univ _)).differentiableAt.hasDerivAt
  have hd : (n + 1 : ℂ) ≠ 0 := by exact_mod_cast (by omega : n + 1 ≠ 0)
  have hsecond : deriv (deriv (ballHelmholtzSquare n)) z =
      -deriv (ballSquareFunction n) z / (2 * (n + 1 : ℕ)) := by
    have h := hF.neg.div_const (2 * (n + 1 : ℕ) : ℂ)
    have he : deriv (ballHelmholtzSquare n) =
        fun w => -ballSquareFunction n w / (2 * (n + 1 : ℕ)) :=
      funext (ballHelmholtzSquare_deriv n)
    rw [he]
    exact h.deriv
  rw [hsecond, ballHelmholtzSquare_deriv, ballHelmholtzSquare]
  push_cast
  field_simp [hd]
  ring

/-- The interior physical-space formula, expressed in a smooth squared radius. -/
def ballResolventInterior (n : ℕ) (a : ℝ) (x : Euclidean (n + 1)) : ℂ :=
  (ballHelmholtzSquare n ((a ^ 2 * ‖x‖ ^ 2 : ℝ) : ℂ) /
      ballHelmholtzSquare n ((a ^ 2 : ℝ) : ℂ) - 1) /
    ((ballVolume (n + 1) : ℂ) * (a ^ 2 : ℝ))

/-- The actual physical resolvent formula with zero extension outside the ball. -/
def ballResolvent (n : ℕ) (a : ℝ) : Euclidean (n + 1) → ℂ :=
  (physicalUnitBall (n + 1)).indicator (ballResolventInterior n a)

theorem ballResolventInterior_contDiff (n : ℕ) (a : ℝ) :
    ContDiff ℝ ⊤ (ballResolventInterior n a) := by
  have hB : ContDiff ℝ ⊤ (ballHelmholtzSquare n) :=
    (ballHelmholtzSquare_analytic n).restrictScalars.contDiff
  have hr : ContDiff ℝ ⊤ (fun x : Euclidean (n + 1) =>
      ((a ^ 2 * ‖x‖ ^ 2 : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (contDiff_const.mul (contDiff_norm_sq ℝ))
  exact (((hB.comp hr).div_const _).sub contDiff_const).div_const _

/-- The physical expression vanishes at the unit sphere. -/
theorem ballResolventInterior_boundary (n : ℕ) (a : ℝ)
    (hb : ballHelmholtzSquare n ((a ^ 2 : ℝ) : ℂ) ≠ 0)
    {x : Euclidean (n + 1)} (hx : ‖x‖ = 1) : ballResolventInterior n a x = 0 := by
  unfold ballResolventInterior
  simp only [hx, one_pow, mul_one, div_self hb, sub_self, zero_div]

theorem ballResolvent_tsupport_subset (n : ℕ) (a : ℝ) :
    tsupport (ballResolvent n a) ⊆ Metric.closedBall (0 : Euclidean (n + 1)) 1 := by
  apply closure_minimal _ Metric.isClosed_closedBall
  intro x hx
  exact Metric.ball_subset_closedBall (Set.mem_of_indicator_ne_zero hx)

theorem ballResolvent_hasCompactSupport (n : ℕ) (a : ℝ) :
    HasCompactSupport (ballResolvent n a) :=
  (isCompact_closedBall (0 : Euclidean (n + 1)) 1).of_isClosed_subset
    isClosed_closure (ballResolvent_tsupport_subset n a)

/-- The adjacent solution equals the original solution plus its radial derivative. -/
theorem ballHelmholtzSquare_at_radius (n : ℕ) (s : ℂ) :
    ballHelmholtzSquare n (s ^ 2) = radialBallFourier n s +
      s / (n + 1 : ℕ) * deriv (radialBallFourier n) s := by
  rw [radialBallFourier_deriv, radialBallFourier_eq_squareFunction]
  unfold ballHelmholtzSquare
  simp only [div_eq_mul_inv]
  ring

/-- A positive simple ball-transform zero has a nonzero adjacent solution. -/
theorem ballHelmholtzSquare_ne_zero_of_simple_zero (n : ℕ) {a : ℝ} (ha : 0 < a)
    (hz : radialBallFourier n (a : ℂ) = 0)
    (hd : deriv (radialBallFourier n) (a : ℂ) ≠ 0) :
    ballHelmholtzSquare n ((a ^ 2 : ℝ) : ℂ) ≠ 0 := by
  rw [Complex.ofReal_pow, ballHelmholtzSquare_at_radius, hz, zero_add]
  apply mul_ne_zero _ hd
  exact div_ne_zero (Complex.ofReal_ne_zero.mpr ha.ne') (by exact_mod_cast (by omega : n + 1 ≠ 0))

/-- At a ball-transform zero, the full interior derivative vanishes on the sphere. -/
theorem ballResolventInterior_boundary_hasFDerivAt (n : ℕ) (a : ℝ)
    (hz : radialBallFourier n (a : ℂ) = 0) {x : Euclidean (n + 1)} (hx : ‖x‖ = 1) :
    HasFDerivAt (ballResolventInterior n a) (0 : Euclidean (n + 1) →L[ℝ] ℂ) x := by
  have hF : ballSquareFunction n ((a ^ 2 : ℝ) : ℂ) = 0 := by
    rw [radialBallFourier_eq_squareFunction] at hz
    simpa only [Complex.ofReal_pow] using hz
  have harg : ((a ^ 2 * ‖x‖ ^ 2 : ℝ) : ℂ) = ((a ^ 2 : ℝ) : ℂ) := by
    rw [hx]
    simp
  have hB := ballHelmholtzSquare_hasDerivAt n ((a ^ 2 : ℝ) : ℂ)
  rw [hF, neg_zero, zero_div, ← harg] at hB
  have hBR : HasFDerivAt (ballHelmholtzSquare n) (0 : ℂ →L[ℝ] ℂ)
      ((a ^ 2 * ‖x‖ ^ 2 : ℝ) : ℂ) := by
    have he : (ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (0 : ℂ)) = 0 := by
      ext
      simp
    simpa only [he, ContinuousLinearMap.restrictScalars_zero] using hB.hasFDerivAt.restrictScalars ℝ
  have hr : ContDiff ℝ ⊤ (fun y : Euclidean (n + 1) =>
      ((a ^ 2 * ‖y‖ ^ 2 : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (contDiff_const.mul (contDiff_norm_sq ℝ))
  have h := ((hBR.comp x (hr.differentiable (by simp) x).hasFDerivAt).mul_const
    (ballHelmholtzSquare n ((a ^ 2 : ℝ) : ℂ))⁻¹).sub_const 1
  have hfinal := h.mul_const ((ballVolume (n + 1) : ℂ) * (a ^ 2 : ℝ))⁻¹
  have he : ((ballVolume (n + 1) : ℂ) * (a ^ 2 : ℝ))⁻¹ •
      (ballHelmholtzSquare n ((a ^ 2 : ℝ) : ℂ))⁻¹ •
      (0 : Euclidean (n + 1) →L[ℝ] ℂ) = 0 := by
    ext
    simp
  simpa only [ballResolventInterior, div_eq_mul_inv, Function.comp_apply,
    ContinuousLinearMap.zero_comp, he] using hfinal

/-- The zero-extended physical formula is continuous because its boundary value is zero. -/
theorem ballResolvent_continuous (n : ℕ) (a : ℝ)
    (hb : ballHelmholtzSquare n ((a ^ 2 : ℝ) : ℂ) ≠ 0) :
    Continuous (ballResolvent n a) := by
  classical
  change Continuous ((physicalUnitBall (n + 1)).piecewise
    (ballResolventInterior n a) (fun _ => 0))
  apply (ballResolventInterior_contDiff n a).continuous.piecewise _ continuous_const
  intro x hx
  apply ballResolventInterior_boundary n a hb
  have hxs := Metric.frontier_ball_subset_sphere hx
  simpa only [Metric.mem_sphere, dist_zero_right] using hxs

theorem ballResolvent_integrable (n : ℕ) (a : ℝ)
    (hb : ballHelmholtzSquare n ((a ^ 2 : ℝ) : ℂ) ≠ 0) :
    Integrable (ballResolvent n a) volume :=
  (ballResolvent_continuous n a hb).integrable_of_hasCompactSupport (ballResolvent_hasCompactSupport n a)

theorem ballResolvent_memLp (n : ℕ) (a : ℝ)
    (hb : ballHelmholtzSquare n ((a ^ 2 : ℝ) : ℂ) ≠ 0) :
    MemLp (ballResolvent n a) 2 volume :=
  (ballResolvent_continuous n a hb).memLp_of_hasCompactSupport (ballResolvent_hasCompactSupport n a)

/-- The genuine physical-space L² resolvent vector. -/
def ballResolventL2 (n : ℕ) (a : ℝ)
    (hb : ballHelmholtzSquare n ((a ^ 2 : ℝ) : ℂ) ≠ 0) : FullL2 (n + 1) :=
  (ballResolvent_memLp n a hb).toLp (ballResolvent n a)

theorem ballResolventL2_ae (n : ℕ) (a : ℝ)
    (hb : ballHelmholtzSquare n ((a ^ 2 : ℝ) : ℂ) ≠ 0) :
    (ballResolventL2 n a hb : Euclidean (n + 1) → ℂ) =ᵐ[volume] ballResolvent n a :=
  (ballResolvent_memLp n a hb).coeFn_toLp

/-- The actual zero extension has zero full derivative at each boundary point. -/
theorem ballResolvent_boundary_hasFDerivAt (n : ℕ) (a : ℝ)
    (hz : radialBallFourier n (a : ℂ) = 0)
    (hb : ballHelmholtzSquare n ((a ^ 2 : ℝ) : ℂ) ≠ 0)
    {x : Euclidean (n + 1)} (hx : ‖x‖ = 1) :
    HasFDerivAt (ballResolvent n a) (0 : Euclidean (n + 1) →L[ℝ] ℂ) x :=
  hasFDerivAt_indicator_zero (ballResolventInterior_boundary_hasFDerivAt n a hz hx)
    (ballResolventInterior_boundary n a hb hx)

/-- The zero-extended derivative is the indicator of the interior derivative. -/
theorem ballResolvent_hasFDerivAt (n : ℕ) (a : ℝ)
    (hz : radialBallFourier n (a : ℂ) = 0)
    (hb : ballHelmholtzSquare n ((a ^ 2 : ℝ) : ℂ) ≠ 0)
    (x : Euclidean (n + 1)) :
    HasFDerivAt (ballResolvent n a)
      ((physicalUnitBall (n + 1)).indicator (fderiv ℝ (ballResolventInterior n a)) x) x := by
  classical
  by_cases hx : ‖x‖ = 1
  · have hn : x ∉ physicalUnitBall (n + 1) := by simp [physicalUnitBall, Metric.mem_ball, hx]
    rw [Set.indicator_of_not_mem hn]
    exact ballResolvent_boundary_hasFDerivAt n a hz hb hx
  · rcases lt_or_gt_of_ne hx with hxlt | hxgt
    · have hmem : x ∈ physicalUnitBall (n + 1) := by
        simpa only [physicalUnitBall, Metric.mem_ball, dist_zero_right] using hxlt
      rw [Set.indicator_of_mem hmem]
      apply ((ballResolventInterior_contDiff n a).differentiable (by simp) x).hasFDerivAt.congr_of_eventuallyEq
      filter_upwards [Metric.isOpen_ball.mem_nhds hmem] with y hy
      exact Set.indicator_of_mem hy _
    · have hn : x ∉ physicalUnitBall (n + 1) := by
        simp [physicalUnitBall, Metric.mem_ball, hxgt.not_lt]
      rw [Set.indicator_of_not_mem hn]
      apply (hasFDerivAt_const (𝕜 := ℝ) (0 : ℂ) x).congr_of_eventuallyEq
      have hnh : {y : Euclidean (n + 1) | 1 < ‖y‖} ∈ 𝓝 x :=
        (isOpen_lt continuous_const continuous_norm).mem_nhds hxgt
      filter_upwards [hnh] with y hy
      exact Set.indicator_of_not_mem (by
        simpa only [physicalUnitBall, Metric.mem_ball, dist_zero_right] using hy.not_lt) _

/-- There is no jump in the first derivative: the actual zero extension is C¹. -/
theorem ballResolvent_contDiff_one (n : ℕ) (a : ℝ)
    (hz : radialBallFourier n (a : ℂ) = 0)
    (hb : ballHelmholtzSquare n ((a ^ 2 : ℝ) : ℂ) ≠ 0) :
    ContDiff ℝ 1 (ballResolvent n a) := by
  classical
  apply contDiff_one_iff_hasFDerivAt.mpr
  refine ⟨(physicalUnitBall (n + 1)).indicator (fderiv ℝ (ballResolventInterior n a)), ?_,
    ballResolvent_hasFDerivAt n a hz hb⟩
  change Continuous ((physicalUnitBall (n + 1)).piecewise
    (fderiv ℝ (ballResolventInterior n a)) (fun _ => 0))
  apply ((ballResolventInterior_contDiff n a).continuous_fderiv (by simp)).piecewise _ continuous_const
  intro x hx
  apply (ballResolventInterior_boundary_hasFDerivAt n a hz _).fderiv
  have hxs := Metric.frontier_ball_subset_sphere hx
  simpa only [Metric.mem_sphere, dist_zero_right] using hxs

/-- Each affine line in a nonzero direction meets the exceptional boundary in
finitely many points. This permits genuine integration by parts across it. -/
theorem unitSphere_line_finite {d : ℕ} (x v : Euclidean d) (hv : v ≠ 0) :
    {t : ℝ | x + t • v ∈ Metric.sphere (0 : Euclidean d) 1}.Finite := by
  let p : Polynomial ℝ := Polynomial.C (‖v‖ ^ 2) * Polynomial.X ^ 2 +
    Polynomial.C (2 * inner (𝕜 := ℝ) x v) * Polynomial.X + Polynomial.C (‖x‖ ^ 2 - 1)
  have hp : p ≠ 0 := by
    intro h
    have hc := congrArg (fun q : Polynomial ℝ => q.coeff 2) h
    have hnorm : ‖v‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hv)
    norm_num only [p, Polynomial.coeff_add, Polynomial.coeff_C_mul_X_pow,
      Polynomial.coeff_C_mul_X, Polynomial.coeff_C, Polynomial.coeff_zero] at hc
    exact hnorm (by simpa only [ite_true, ite_false, add_zero] using hc)
  apply (Polynomial.finite_setOf_isRoot hp).subset
  intro t ht
  have hn : ‖x + t • v‖ = 1 := by
    simpa only [Metric.mem_sphere, dist_zero_right] using ht
  change Polynomial.eval t p = 0
  have he : Polynomial.eval t p = ‖x + t • v‖ ^ 2 - 1 := by
    simp only [p, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_pow, Polynomial.eval_X, norm_add_sq_real, real_inner_smul_right,
      norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    ring
  rw [he, hn]
  norm_num

/-- Chain rule for an entire function of the squared physical radius. -/
theorem hasLineDerivAt_squared_radius {d : ℕ} {F : ℂ → ℂ} {F' : ℂ}
    (a : ℝ) (x v : Euclidean d)
    (hF : HasDerivAt F F' ((a ^ 2 * ‖x‖ ^ 2 : ℝ) : ℂ)) :
    HasLineDerivAt ℝ (fun y : Euclidean d => F ((a ^ 2 * ‖y‖ ^ 2 : ℝ) : ℂ))
      (F' * ((2 * a ^ 2 * inner (𝕜 := ℝ) x v : ℝ) : ℂ)) x v := by
  have hr := (((hasDerivAt_const (0 : ℝ) x).add
    ((hasDerivAt_id (0 : ℝ)).smul_const v)).norm_sq).const_mul (a ^ 2)
  have hc := Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hr
  have h := (hF.hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt_of_eq (0 : ℝ) hc (by simp)
  change HasDerivAt (fun t : ℝ => F ((a ^ 2 * ‖x + t • v‖ ^ 2 : ℝ) : ℂ)) _ 0
  convert h using 1
  simp
  ring

/-- The actual first directional derivative in the interior. -/
def ballResolventFirstInterior (n : ℕ) (a : ℝ) (v x : Euclidean (n + 1)) : ℂ :=
  (deriv (ballHelmholtzSquare n) ((a ^ 2 * ‖x‖ ^ 2 : ℝ) : ℂ) *
    ((2 * a ^ 2 * inner (𝕜 := ℝ) x v : ℝ) : ℂ) /
      ballHelmholtzSquare n ((a ^ 2 : ℝ) : ℂ)) /
    ((ballVolume (n + 1) : ℂ) * (a ^ 2 : ℝ))

theorem ballResolventInterior_hasLineDerivAt (n : ℕ) (a : ℝ) (x v : Euclidean (n + 1)) :
    HasLineDerivAt ℝ (ballResolventInterior n a) (ballResolventFirstInterior n a v x) x v := by
  have hF := ((ballHelmholtzSquare_analytic n) ((a ^ 2 * ‖x‖ ^ 2 : ℝ) : ℂ)
    (mem_univ _)).differentiableAt.hasDerivAt
  have h := hasLineDerivAt_squared_radius a x v hF
  change HasDerivAt (fun t : ℝ => ballResolventInterior n a (x + t • v)) _ 0
  change HasDerivAt (fun t : ℝ => ballHelmholtzSquare n
    ((a ^ 2 * ‖x + t • v‖ ^ 2 : ℝ) : ℂ)) _ 0 at h
  exact ((h.div_const _).sub_const 1).div_const _

/-- The smooth first derivative in the interior is continuous even at the origin. -/
theorem ballResolventFirstInterior_continuous (n : ℕ) (a : ℝ) (v : Euclidean (n + 1)) :
    Continuous (ballResolventFirstInterior n a v) := by
  have hB := (ballHelmholtzSquare_analytic n).deriv.contDiff (n := 0) |>.continuous
  have hr : Continuous (fun x : Euclidean (n + 1) => ((a ^ 2 * ‖x‖ ^ 2 : ℝ) : ℂ)) := by
    fun_prop
  have hi : Continuous (fun x : Euclidean (n + 1) => ((2 * a ^ 2 * inner (𝕜 := ℝ) x v : ℝ) : ℂ)) := by
    fun_prop
  exact (((hB.comp hr).mul hi).div_const _).div_const _

/-- The first interior derivative has zero trace at a selected ball-transform zero. -/
theorem ballResolventFirstInterior_boundary (n : ℕ) (a : ℝ)
    (hz : radialBallFourier n (a : ℂ) = 0) (v : Euclidean (n + 1))
    {x : Euclidean (n + 1)} (hx : ‖x‖ = 1) : ballResolventFirstInterior n a v x = 0 := by
  have h := (ballResolventInterior_hasLineDerivAt n a x v).lineDeriv
  rw [((ballResolventInterior_boundary_hasFDerivAt n a hz hx).hasLineDerivAt v).lineDeriv] at h
  simpa using h.symm

/-- Simplified interior first derivative, with the nonzero spectral radius cancelled. -/
theorem ballResolventFirstInterior_eq (n : ℕ) {a : ℝ} (ha : a ≠ 0)
    (hb : ballHelmholtzSquare n ((a ^ 2 : ℝ) : ℂ) ≠ 0) (v x : Euclidean (n + 1)) :
    ballResolventFirstInterior n a v x =
      (2 / ((ballVolume (n + 1) : ℂ) * ballHelmholtzSquare n ((a ^ 2 : ℝ) : ℂ))) *
      deriv (ballHelmholtzSquare n) ((a ^ 2 * ‖x‖ ^ 2 : ℝ) : ℂ) *
      (inner (𝕜 := ℝ) x v : ℂ) := by
  have hV : (ballVolume (n + 1) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ballVolume_pos _).ne'
  have hA : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha
  unfold ballResolventFirstInterior
  push_cast at hb ⊢
  field_simp [hV, hA, hb]
  ring

/-- The actual second directional derivative in the interior. -/
def ballResolventSecondInterior (n : ℕ) (a : ℝ) (v x : Euclidean (n + 1)) : ℂ :=
  (2 / ((ballVolume (n + 1) : ℂ) * ballHelmholtzSquare n ((a ^ 2 : ℝ) : ℂ))) *
    (deriv (deriv (ballHelmholtzSquare n)) ((a ^ 2 * ‖x‖ ^ 2 : ℝ) : ℂ) *
      ((2 * a ^ 2 * inner (𝕜 := ℝ) x v : ℝ) : ℂ) * (inner (𝕜 := ℝ) x v : ℂ) +
      deriv (ballHelmholtzSquare n) ((a ^ 2 * ‖x‖ ^ 2 : ℝ) : ℂ) * (‖v‖ ^ 2 : ℝ))

theorem ballResolventFirstInterior_hasLineDerivAt (n : ℕ) {a : ℝ} (ha : a ≠ 0)
    (hb : ballHelmholtzSquare n ((a ^ 2 : ℝ) : ℂ) ≠ 0) (x v : Euclidean (n + 1)) :
    HasLineDerivAt ℝ (ballResolventFirstInterior n a v)
      (ballResolventSecondInterior n a v x) x v := by
  have hG := hasLineDerivAt_squared_radius a x v
    (((ballHelmholtzSquare_analytic n).deriv ((a ^ 2 * ‖x‖ ^ 2 : ℝ) : ℂ)
      (mem_univ _)).differentiableAt.hasDerivAt)
  change HasDerivAt (fun t : ℝ => deriv (ballHelmholtzSquare n)
    ((a ^ 2 * ‖x + t • v‖ ^ 2 : ℝ) : ℂ)) _ 0 at hG
  have hr := ((hasDerivAt_const (0 : ℝ) x).add
    ((hasDerivAt_id (0 : ℝ)).smul_const v)).inner ℝ (hasDerivAt_const (0 : ℝ) v)
  have hL := Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hr
  have h := (hG.mul hL).const_mul
    (2 / ((ballVolume (n + 1) : ℂ) * ballHelmholtzSquare n ((a ^ 2 : ℝ) : ℂ)))
  change HasDerivAt (fun t : ℝ => ballResolventFirstInterior n a v (x + t • v)) _ 0
  convert h using 1
  · funext t
    simpa only [Function.comp_apply, id_eq, Complex.ofRealCLM_apply, mul_assoc] using
      ballResolventFirstInterior_eq n ha hb v (x + t • v)
  · simp only [ballResolventSecondInterior, Function.comp_apply, Complex.ofRealCLM_apply,
      zero_smul, add_zero, id_eq, one_smul, zero_add, inner_zero_right, zero_add,
      real_inner_self_eq_norm_sq]

theorem ballResolventSecondInterior_continuous (n : ℕ) (a : ℝ) (v : Euclidean (n + 1)) :
    Continuous (ballResolventSecondInterior n a v) := by
  have hB : Continuous (deriv (ballHelmholtzSquare n)) :=
    (ballHelmholtzSquare_analytic n).deriv.contDiff (n := 0) |>.continuous
  have hB2 : Continuous (deriv (deriv (ballHelmholtzSquare n))) :=
    (ballHelmholtzSquare_analytic n).deriv.deriv.contDiff (n := 0) |>.continuous
  unfold ballResolventSecondInterior
  fun_prop

/-- The classical interior Laplace identity is an actual sum of directional second derivatives. -/
theorem ballResolventInterior_helmholtz (n : ℕ) {a : ℝ} (ha : a ≠ 0)
    (hb : ballHelmholtzSquare n ((a ^ 2 : ℝ) : ℂ) ≠ 0) (x : Euclidean (n + 1)) :
    -(∑ j : Fin (n + 1), ballResolventSecondInterior n a
      (EuclideanSpace.basisFun (Fin (n + 1)) ℝ j) x) -
      (a ^ 2 : ℝ) * ballResolventInterior n a x = (ballVolume (n + 1) : ℂ)⁻¹ := by
  let C : ℂ := 2 / ((ballVolume (n + 1) : ℂ) * ballHelmholtzSquare n ((a ^ 2 : ℝ) : ℂ))
  let z : ℂ := ((a ^ 2 * ‖x‖ ^ 2 : ℝ) : ℂ)
  have hs : (∑ j : Fin (n + 1), (x j : ℂ) ^ 2) = ((‖x‖ ^ 2 : ℝ) : ℂ) := by
    have hr : (∑ j : Fin (n + 1), (x j) ^ 2) = ‖x‖ ^ 2 := by
      simpa only [Real.norm_eq_abs, sq_abs] using
        (PiLp.norm_sq_eq_of_L2 (fun _ : Fin (n + 1) => ℝ) x).symm
    exact_mod_cast hr
  have hsum : (∑ j : Fin (n + 1), ballResolventSecondInterior n a
      (EuclideanSpace.basisFun (Fin (n + 1)) ℝ j) x) =
      C * (2 * (a ^ 2 : ℝ) * deriv (deriv (ballHelmholtzSquare n)) z * ((‖x‖ ^ 2 : ℝ) : ℂ) +
        (n + 1 : ℕ) * deriv (ballHelmholtzSquare n) z) := by
    have ht (j : Fin (n + 1)) : ballResolventSecondInterior n a
        (EuclideanSpace.basisFun (Fin (n + 1)) ℝ j) x =
        C * (2 * (a ^ 2 : ℝ) * deriv (deriv (ballHelmholtzSquare n)) z * (x j : ℂ) ^ 2 +
          deriv (ballHelmholtzSquare n) z) := by
      simp only [ballResolventSecondInterior, EuclideanSpace.basisFun_apply,
        EuclideanSpace.inner_single_right, conj_trivial, one_mul, EuclideanSpace.norm_single,
        norm_one, one_pow, Complex.ofReal_one, mul_one, Complex.ofReal_mul, Complex.ofReal_ofNat]
      dsimp only [C, z]
      push_cast
      ring
    simp_rw [ht]
    rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum, hs]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [hsum]
  have hode := ballHelmholtzSquare_ode n z
  have hV : (ballVolume (n + 1) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ballVolume_pos _).ne'
  have hA : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha
  dsimp only [C, z] at hode ⊢
  unfold ballResolventInterior
  push_cast at hb hode ⊢
  field_simp [hV, hA, hb]
  linear_combination -(a : ℂ) ^ 2 * ballHelmholtzSquare n ((a : ℂ) ^ 2) *
    (ballVolume (n + 1) : ℂ) ^ 2 * hode

/-- Compact support for any indicator of the physical unit ball. -/
theorem physicalUnitBall_indicator_hasCompactSupport {d : ℕ} (f : Euclidean d → ℂ) :
    HasCompactSupport ((physicalUnitBall d).indicator f) := by
  apply (isCompact_closedBall (0 : Euclidean d) 1).of_isClosed_subset isClosed_closure
  apply closure_minimal _ Metric.isClosed_closedBall
  intro x hx
  exact Metric.ball_subset_closedBall (Set.mem_of_indicator_ne_zero hx)

theorem integrable_physicalUnitBall_indicator {d : ℕ} {f : Euclidean d → ℂ}
    (hf : Continuous f) : Integrable ((physicalUnitBall d).indicator f) volume :=
  ((hf.locallyIntegrable.integrableOn_isCompact (isCompact_closedBall (0 : Euclidean d) 1)).mono_set
    Metric.ball_subset_closedBall).integrable_indicator (physicalUnitBall_measurable d)

/-- The actual zero extension of the resolvent's first directional derivative. -/
def ballResolventFirst (n : ℕ) (a : ℝ) (v : Euclidean (n + 1)) : Euclidean (n + 1) → ℂ :=
  (physicalUnitBall (n + 1)).indicator (ballResolventFirstInterior n a v)

/-- The actual zero extension of the classical interior second directional derivative. -/
def ballResolventSecond (n : ℕ) (a : ℝ) (v : Euclidean (n + 1)) : Euclidean (n + 1) → ℂ :=
  (physicalUnitBall (n + 1)).indicator (ballResolventSecondInterior n a v)

theorem ballResolventFirst_continuous (n : ℕ) (a : ℝ)
    (hz : radialBallFourier n (a : ℂ) = 0) (v : Euclidean (n + 1)) :
    Continuous (ballResolventFirst n a v) := by
  classical
  change Continuous ((physicalUnitBall (n + 1)).piecewise
    (ballResolventFirstInterior n a v) (fun _ => 0))
  apply (ballResolventFirstInterior_continuous n a v).piecewise _ continuous_const
  intro x hx
  apply ballResolventFirstInterior_boundary n a hz v
  have hxs := Metric.frontier_ball_subset_sphere hx
  simpa only [Metric.mem_sphere, dist_zero_right] using hxs

theorem ballResolvent_hasLineDerivAt (n : ℕ) (a : ℝ)
    (hz : radialBallFourier n (a : ℂ) = 0)
    (hb : ballHelmholtzSquare n ((a ^ 2 : ℝ) : ℂ) ≠ 0) (x v : Euclidean (n + 1)) :
    HasLineDerivAt ℝ (ballResolvent n a) (ballResolventFirst n a v x) x v := by
  have h := (ballResolvent_hasFDerivAt n a hz hb x).hasLineDerivAt v
  have he : ballResolventFirstInterior n a v x = fderiv ℝ (ballResolventInterior n a) x v :=
    (ballResolventInterior_hasLineDerivAt n a x v).lineDeriv.symm.trans
      (((ballResolventInterior_contDiff n a).differentiable (by simp) x).lineDeriv_eq_fderiv)
  classical
  by_cases hx : x ∈ physicalUnitBall (n + 1)
  · simpa only [ballResolventFirst, Set.indicator_of_mem hx, he] using h
  · simpa only [ballResolventFirst, Set.indicator_of_not_mem hx,
      ContinuousLinearMap.zero_apply] using h

/-- Away from the boundary, the indicator has its classical interior derivative. -/
theorem hasLineDerivAt_physicalUnitBall_indicator_off_sphere {d : ℕ} {f g : Euclidean d → ℂ}
    (v : Euclidean d) (h : ∀ x, HasLineDerivAt ℝ f (g x) x v)
    {x : Euclidean d} (hx : x ∉ Metric.sphere (0 : Euclidean d) 1) :
    HasLineDerivAt ℝ ((physicalUnitBall d).indicator f) ((physicalUnitBall d).indicator g x) x v := by
  classical
  have hn : ‖x‖ ≠ 1 := by simpa only [Metric.mem_sphere, dist_zero_right] using hx
  rcases lt_or_gt_of_ne hn with hxlt | hxgt
  · have hmem : x ∈ physicalUnitBall d := by
      simpa only [physicalUnitBall, Metric.mem_ball, dist_zero_right] using hxlt
    rw [Set.indicator_of_mem hmem]
    have he : (physicalUnitBall d).indicator f =ᶠ[𝓝 x] f := by
      filter_upwards [Metric.isOpen_ball.mem_nhds hmem] with y hy
      exact Set.indicator_of_mem hy _
    exact he.hasLineDerivAt_iff.mpr (h x)
  · have hnot : x ∉ physicalUnitBall d := by
      simpa only [physicalUnitBall, Metric.mem_ball, dist_zero_right] using hxgt.not_lt
    rw [Set.indicator_of_not_mem hnot]
    have he : (physicalUnitBall d).indicator f =ᶠ[𝓝 x] (fun _ => 0) := by
      have hnh : {y : Euclidean d | 1 < ‖y‖} ∈ 𝓝 x :=
        (isOpen_lt continuous_const continuous_norm).mem_nhds hxgt
      filter_upwards [hnh] with y hy
      exact Set.indicator_of_not_mem (by
        simpa only [physicalUnitBall, Metric.mem_ball, dist_zero_right] using hy.not_lt) _
    exact he.hasLineDerivAt_iff.mpr ((hasFDerivAt_const (𝕜 := ℝ) (0 : ℂ) x).hasLineDerivAt v)

theorem ballResolventFirst_hasLineDerivAt_off_sphere (n : ℕ) {a : ℝ} (ha : a ≠ 0)
    (hb : ballHelmholtzSquare n ((a ^ 2 : ℝ) : ℂ) ≠ 0) (v : Euclidean (n + 1))
    {x : Euclidean (n + 1)} (hx : x ∉ Metric.sphere (0 : Euclidean (n + 1)) 1) :
    HasLineDerivAt ℝ (ballResolventFirst n a v) (ballResolventSecond n a v x) x v :=
  hasLineDerivAt_physicalUnitBall_indicator_off_sphere v
    (fun y => ballResolventFirstInterior_hasLineDerivAt n ha hb y v) hx

theorem ballResolventSecond_mul_schwartz_integrable (n : ℕ) (a : ℝ)
    (v : Euclidean (n + 1)) (ψ : 𝓢(Euclidean (n + 1), ℂ)) :
    Integrable (fun x => ballResolventSecond n a v x * ψ x) volume := by
  have h := integrable_physicalUnitBall_indicator
    ((ballResolventSecondInterior_continuous n a v).mul ψ.continuous)
  change Integrable (fun x => (physicalUnitBall (n + 1)).indicator
    (fun y => ballResolventSecondInterior n a v y * ψ y) x) volume at h
  simpa only [ballResolventSecond, Set.indicator_mul_left] using h

/-- The two actual integrations by parts produce no boundary functional. -/
theorem ballResolvent_weak_second_derivative (n : ℕ) {a : ℝ} (ha : a ≠ 0)
    (hz : radialBallFourier n (a : ℂ) = 0)
    (hb : ballHelmholtzSquare n ((a ^ 2 : ℝ) : ℂ) ≠ 0)
    (v : Euclidean (n + 1)) (hv : v ≠ 0) (ψ : 𝓢(Euclidean (n + 1), ℂ)) :
    (∫ x, ballResolvent n a x *
      (SchwartzMap.pderivCLM ℂ v (SchwartzMap.pderivCLM ℂ v ψ)) x) =
      ∫ x, ballResolventSecond n a v x * ψ x := by
  have hc := ballResolventFirst_continuous n a hz v
  have hs := physicalUnitBall_indicator_hasCompactSupport (ballResolventFirstInterior n a v)
  have hint (θ : 𝓢(Euclidean (n + 1), ℂ)) :
      Integrable (fun x => ballResolventFirst n a v x * θ x) volume :=
    (hc.mul θ.continuous).integrable_of_hasCompactSupport hs.mul_right
  have h2 := integral_mul_fderiv_off_countable_eq_neg_left hv
    (ballResolventSecond_mul_schwartz_integrable n a v ψ)
    (by simpa only [SchwartzMap.pderivCLM_apply] using hint (SchwartzMap.pderivCLM ℂ v ψ))
    (hint ψ) hc ψ.differentiable
    (fun x => (unitSphere_line_finite x v hv).countable)
    (fun x hx => ballResolventFirst_hasLineDerivAt_off_sphere n ha hb v hx)
  have hφ := ballResolvent_continuous n a hb
  have hsφ := ballResolvent_hasCompactSupport n a
  have hintφ (θ : 𝓢(Euclidean (n + 1), ℂ)) :
      Integrable (fun x => ballResolvent n a x * θ x) volume :=
    (hφ.mul θ.continuous).integrable_of_hasCompactSupport hsφ.mul_right
  have h1 := integral_mul_fderiv_off_countable_eq_neg_left (S := Metric.sphere (0 : Euclidean (n + 1)) 1) hv
    (hint (SchwartzMap.pderivCLM ℂ v ψ))
    (by simpa only [SchwartzMap.pderivCLM_apply] using
      (hintφ (SchwartzMap.pderivCLM ℂ v (SchwartzMap.pderivCLM ℂ v ψ))))
    (hintφ (SchwartzMap.pderivCLM ℂ v ψ)) hφ (SchwartzMap.pderivCLM ℂ v ψ).differentiable
    (fun x => (unitSphere_line_finite x v hv).countable)
    (fun x _ => ballResolvent_hasLineDerivAt n a hz hb x v)
  simp only [SchwartzMap.pderivCLM_apply] at h1 h2 ⊢
  rw [h1, h2, neg_neg]

/-- The genuine tempered distribution of the physical resolvent. -/
def ballResolventDistribution (n : ℕ) (a : ℝ)
    (hb : ballHelmholtzSquare n ((a ^ 2 : ℝ) : ℂ) ≠ 0) : TemperedDistribution (n + 1) :=
  l2Distribution (ballResolventL2 n a hb)

theorem ballResolventDistribution_apply (n : ℕ) (a : ℝ)
    (hb : ballHelmholtzSquare n ((a ^ 2 : ℝ) : ℂ) ≠ 0) (ψ : 𝓢(Euclidean (n + 1), ℂ)) :
    ballResolventDistribution n a hb ψ = ∫ x, ballResolvent n a x * ψ x := by
  rw [ballResolventDistribution, l2Distribution_apply]
  apply integral_congr_ae
  filter_upwards [ballResolventL2_ae n a hb] with x hx
  rw [hx]

theorem ballResolventDistribution_supported (n : ℕ) (a : ℝ)
    (hb : ballHelmholtzSquare n ((a ^ 2 : ℝ) : ℂ) ≠ 0) :
    DistributionSupportedIn (ballResolventDistribution n a hb)
      (Metric.closedBall (0 : Euclidean (n + 1)) 1) := by
  apply l2Distribution_supported
  filter_upwards [ballResolventL2_ae n a hb] with x hx
  intro hn
  rw [hx]
  exact Set.indicator_of_not_mem (fun hm => hn (Metric.ball_subset_closedBall hm)) _

/-- The actual physical constant-coefficient operator, using ordinary directional derivatives. -/
def ballHelmholtzOperator (n : ℕ) (a : ℝ) (u : TemperedDistribution (n + 1)) :
    TemperedDistribution (n + 1) :=
  -(∑ j : Fin (n + 1), distributionDerivative (EuclideanSpace.basisFun (Fin (n + 1)) ℝ j)
      (distributionDerivative (EuclideanSpace.basisFun (Fin (n + 1)) ℝ j) u)) -
    ((a ^ 2 : ℝ) : ℂ) • u

/-- The actual distributional Helmholtz identity, including the zero extension.
Its proof uses two real integrations by parts, so no boundary distributions are assumed away. -/
theorem ballResolventDistribution_helmholtz (n : ℕ) {a : ℝ} (ha : a ≠ 0)
    (hz : radialBallFourier n (a : ℂ) = 0)
    (hb : ballHelmholtzSquare n ((a ^ 2 : ℝ) : ℂ) ≠ 0) :
    ballHelmholtzOperator n a (ballResolventDistribution n a hb) = normalizedBallDistribution (n + 1) := by
  have hD (v : Euclidean (n + 1)) (hv : v ≠ 0) (ψ : 𝓢(Euclidean (n + 1), ℂ)) :
      distributionDerivative v (distributionDerivative v (ballResolventDistribution n a hb)) ψ =
        ∫ x, ballResolventSecond n a v x * ψ x := by
    simp only [distributionDerivative_apply, neg_neg]
    rw [ballResolventDistribution_apply]
    exact ballResolvent_weak_second_derivative n ha hz hb v hv ψ
  ext ψ
  have hv (j : Fin (n + 1)) : EuclideanSpace.basisFun (Fin (n + 1)) ℝ j ≠ 0 := by
    apply norm_ne_zero_iff.mp
    simp
  simp only [ballHelmholtzOperator, ContinuousLinearMap.sub_apply, ContinuousLinearMap.neg_apply,
    ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  simp_rw [hD _ (hv _), ballResolventDistribution_apply]
  have hi (j : Fin (n + 1)) : Integrable (fun x => ballResolventSecond n a
      (EuclideanSpace.basisFun (Fin (n + 1)) ℝ j) x * ψ x) volume :=
    ballResolventSecond_mul_schwartz_integrable n a _ ψ
  have hsum := integrable_finset_sum Finset.univ (fun j _ => hi j)
  have hφ : Integrable (fun x => ballResolvent n a x * ψ x) volume :=
    ((ballResolvent_continuous n a hb).mul ψ.continuous).integrable_of_hasCompactSupport
      (ballResolvent_hasCompactSupport n a).mul_right
  have hpoint (x : Euclidean (n + 1)) :
      -(∑ j : Fin (n + 1), ballResolventSecond n a
        (EuclideanSpace.basisFun (Fin (n + 1)) ℝ j) x * ψ x) -
        ((a ^ 2 : ℝ) : ℂ) * (ballResolvent n a x * ψ x) = normalizedBallIndicator (n + 1) x * ψ x := by
    by_cases hx : x ∈ physicalUnitBall (n + 1)
    · simp only [ballResolventSecond, ballResolvent, normalizedBallIndicator, ballIndicator,
        Set.indicator_of_mem hx, Pi.smul_apply, smul_eq_mul, mul_one]
      have h := congrArg (fun z : ℂ => z * ψ x) (ballResolventInterior_helmholtz n ha hb x)
      simpa only [sub_mul, neg_mul, Finset.sum_mul, mul_assoc] using h
    · simp [ballResolventSecond, ballResolvent, normalizedBallIndicator, ballIndicator, hx]
  calc
    _ = ∫ x, -(∑ j : Fin (n + 1), ballResolventSecond n a
        (EuclideanSpace.basisFun (Fin (n + 1)) ℝ j) x * ψ x) -
        ((a ^ 2 : ℝ) : ℂ) * (ballResolvent n a x * ψ x) := by
      rw [integral_sub (by exact hsum.neg) (by exact hφ.const_mul (((a ^ 2 : ℝ) : ℂ))), integral_neg,
        integral_finset_sum _ (fun j _ => hi j), integral_const_mul]
    _ = ∫ x, normalizedBallIndicator (n + 1) x * ψ x :=
      integral_congr_ae (Filter.Eventually.of_forall hpoint)
    _ = normalizedBallDistribution (n + 1) ψ := by
      rw [normalizedBallDistribution, l2Distribution_apply]
      apply integral_congr_ae
      filter_upwards [normalizedBallL2_ae (n + 1)] with x hx
      rw [hx]

/-- The Fourier transform of the physical resolvent is its actual Fourier integral. -/
theorem distributionFourier_ballResolventDistribution_apply (n : ℕ) (a : ℝ)
    (hb : ballHelmholtzSquare n ((a ^ 2 : ℝ) : ℂ) ≠ 0) (ψ : 𝓢(Euclidean (n + 1), ℂ)) :
    distributionFourier (ballResolventDistribution n a hb) ψ =
      ∫ ξ, 𝓕 (ballResolvent n a) ξ * ψ ξ := by
  rw [distributionFourier_apply, ballResolventDistribution_apply]
  exact (integral_fourier_mul (ballResolvent_integrable n a hb) ψ.integrable).symm

theorem ballResolvent_fourier_hasTemperateGrowth (n : ℕ) (a : ℝ)
    (hb : ballHelmholtzSquare n ((a ^ 2 : ℝ) : ℂ) ≠ 0) :
    Function.HasTemperateGrowth (𝓕 (ballResolvent n a)) := by
  apply fourier_hasTemperateGrowth_of_compact_support (ballResolvent_integrable n a hb)
    (isCompact_closedBall (0 : Euclidean (n + 1)) 1)
  filter_upwards with x
  intro hn
  exact Set.indicator_of_not_mem (fun hm => hn (Metric.ball_subset_closedBall hm)) _

/-- Ordinary physical second derivatives have their actual squared Fourier symbols. -/
theorem distributionFourier_second_derivative_integral {d : ℕ}
    (v : Euclidean d) (u : TemperedDistribution d) (F : Euclidean d → ℂ)
    (hF : ∀ θ : 𝓢(Euclidean d, ℂ), distributionFourier u θ = ∫ ξ, F ξ * θ ξ)
    (ψ : 𝓢(Euclidean d, ℂ)) :
    distributionFourier (distributionDerivative v (distributionDerivative v u)) ψ =
      ∫ ξ, (derivativeSymbolCLM v ξ) ^ 2 * F ξ * ψ ξ := by
  rw [distributionFourier_derivative, distributionMultiply_apply,
    distributionFourier_derivative, distributionMultiply_apply, hF]
  apply integral_congr_ae
  filter_upwards with ξ
  simp only [schwartzMultiplierCLM_apply]
  ring

theorem sum_derivativeSymbol_sq (d : ℕ) (ξ : Euclidean d) :
    -(∑ j : Fin d, (derivativeSymbolCLM (EuclideanSpace.basisFun (Fin d) ℝ j) ξ) ^ 2) =
      ballQuadraticForm d (realToComplex ξ) := by
  have ht (j : Fin d) : (derivativeSymbolCLM (EuclideanSpace.basisFun (Fin d) ℝ j) ξ) ^ 2 =
      -((2 * Real.pi : ℂ) ^ 2) * (ξ j : ℂ) ^ 2 := by
    simp only [derivativeSymbolCLM_apply, EuclideanSpace.basisFun_apply,
      EuclideanSpace.inner_single_left, conj_trivial, one_mul, mul_pow,
      Complex.I_sq, Complex.ofReal_mul, Complex.ofReal_ofNat]
    ring
  simp_rw [ht]
  rw [← Finset.mul_sum]
  simp only [ballQuadraticForm, realToComplex_apply]
  ring

/-- Fourier transformation of the proved physical equation gives the actual
regular-distribution divisor identity, including frequencies on its zero set. -/
theorem ballResolvent_fourier_divisor_integral (n : ℕ) {a : ℝ} (ha : a ≠ 0)
    (hz : radialBallFourier n (a : ℂ) = 0)
    (hb : ballHelmholtzSquare n ((a ^ 2 : ℝ) : ℂ) ≠ 0) (ψ : 𝓢(Euclidean (n + 1), ℂ)) :
    (∫ ξ, (ballQuadraticForm (n + 1) (realToComplex ξ) - ((a ^ 2 : ℝ) : ℂ)) *
      𝓕 (ballResolvent n a) ξ * ψ ξ) =
      ∫ ξ, normalizedBallFourier (n + 1) (realToComplex ξ) * ψ ξ := by
  let F : Euclidean (n + 1) → ℂ := 𝓕 (ballResolvent n a)
  let u := ballResolventDistribution n a hb
  have hF : ∀ θ : 𝓢(Euclidean (n + 1), ℂ), distributionFourier u θ = ∫ ξ, F ξ * θ ξ :=
    distributionFourier_ballResolventDistribution_apply n a hb
  have hFi (θ : 𝓢(Euclidean (n + 1), ℂ)) : Integrable (fun ξ => F ξ * θ ξ) volume := by
    have h : Integrable (schwartzMultiplierCLM F (ballResolvent_fourier_hasTemperateGrowth n a hb) θ :
        Euclidean (n + 1) → ℂ) volume :=
      (schwartzMultiplierCLM F (ballResolvent_fourier_hasTemperateGrowth n a hb) θ).integrable
    change Integrable (fun ξ => θ ξ * F ξ) volume at h
    simpa only [mul_comm] using h
  have hi (j : Fin (n + 1)) : Integrable (fun ξ =>
      (derivativeSymbolCLM (EuclideanSpace.basisFun (Fin (n + 1)) ℝ j) ξ) ^ 2 * F ξ * ψ ξ) volume := by
    have h := hFi (derivativeMultiplierCLM (EuclideanSpace.basisFun (Fin (n + 1)) ℝ j)
      (derivativeMultiplierCLM (EuclideanSpace.basisFun (Fin (n + 1)) ℝ j) ψ))
    simpa only [derivativeMultiplierCLM, schwartzMultiplierCLM_apply, pow_two,
      mul_assoc, mul_comm, mul_left_comm] using h
  have hsum := integrable_finset_sum Finset.univ (fun j _ => hi j)
  have hpde := congrArg (fun w : TemperedDistribution (n + 1) => distributionFourier w ψ)
    (ballResolventDistribution_helmholtz n ha hz hb)
  have hlinear : distributionFourier (ballHelmholtzOperator n a u) ψ =
      -(∑ j : Fin (n + 1), distributionFourier
        (distributionDerivative (EuclideanSpace.basisFun (Fin (n + 1)) ℝ j)
          (distributionDerivative (EuclideanSpace.basisFun (Fin (n + 1)) ℝ j) u)) ψ) -
        ((a ^ 2 : ℝ) : ℂ) * distributionFourier u ψ := by
    simp [ballHelmholtzOperator, distributionFourier, map_sum]
  change distributionFourier (ballHelmholtzOperator n a u) ψ =
    distributionFourier (normalizedBallDistribution (n + 1)) ψ at hpde
  rw [hlinear] at hpde
  simp_rw [distributionFourier_second_derivative_integral _ u F hF, hF] at hpde
  rw [distributionFourier_normalizedBallDistribution, polynomialDistribution_apply] at hpde
  calc
    _ = ∫ ξ, -(∑ j : Fin (n + 1),
        (derivativeSymbolCLM (EuclideanSpace.basisFun (Fin (n + 1)) ℝ j) ξ) ^ 2 * F ξ * ψ ξ) -
        ((a ^ 2 : ℝ) : ℂ) * (F ξ * ψ ξ) := by
      apply integral_congr_ae
      filter_upwards with ξ
      rw [← sum_derivativeSymbol_sq]
      dsimp only [F]
      simp only [sub_mul, neg_mul, Finset.sum_mul, mul_assoc]
    _ = -(∑ j : Fin (n + 1), ∫ ξ,
        (derivativeSymbolCLM (EuclideanSpace.basisFun (Fin (n + 1)) ℝ j) ξ) ^ 2 * F ξ * ψ ξ) -
        ((a ^ 2 : ℝ) : ℂ) * (∫ ξ, F ξ * ψ ξ) := by
      rw [integral_sub (by exact hsum.neg) (by exact (hFi ψ).const_mul (((a ^ 2 : ℝ) : ℂ))),
        integral_neg, integral_finset_sum _ (fun j _ => hi j), integral_const_mul]
    _ = _ := hpde

/-- The physical resolvent solves the divisor identity at every real frequency,
including the removable sphere. -/
theorem fourier_ballResolvent_divisor (n : ℕ) {a : ℝ} (ha : a ≠ 0)
    (hz : radialBallFourier n (a : ℂ) = 0)
    (hb : ballHelmholtzSquare n ((a ^ 2 : ℝ) : ℂ) ≠ 0) (ξ : Euclidean (n + 1)) :
    (ballQuadraticForm (n + 1) (realToComplex ξ) - ((a ^ 2 : ℝ) : ℂ)) *
      𝓕 (ballResolvent n a) ξ = normalizedBallFourier (n + 1) (realToComplex ξ) := by
  let F : Euclidean (n + 1) → ℂ := fun ξ =>
    (ballQuadraticForm (n + 1) (realToComplex ξ) - ((a ^ 2 : ℝ) : ℂ)) * 𝓕 (ballResolvent n a) ξ
  let G : Euclidean (n + 1) → ℂ := fun ξ => normalizedBallFourier (n + 1) (realToComplex ξ)
  have hF : Continuous F := by
    have hf := (ballResolvent_fourier_hasTemperateGrowth n a hb).1.continuous
    have hq : Continuous (fun ξ : Euclidean (n + 1) =>
        ballQuadraticForm (n + 1) (realToComplex ξ)) := by
      simp_rw [ballQuadraticForm_realToComplex]
      fun_prop
    exact (hq.sub continuous_const).mul hf
  have hG : Continuous G := (normalizedBallFourier_real_hasTemperateGrowth (n + 1)).1.continuous
  have hae : F =ᵐ[volume] G := by
    apply ae_eq_of_integral_contDiff_smul_eq hF.locallyIntegrable hG.locallyIntegrable
    intro g hg hc
    let θ := compactSchwartz (fun x => (g x : ℂ))
      (Complex.ofRealCLM.contDiff.comp hg) (hc.comp_left Complex.ofReal_zero)
    have h := ballResolvent_fourier_divisor_integral n ha hz hb θ
    change (∫ x, F x * (g x : ℂ)) = ∫ x, G x * (g x : ℂ) at h
    simpa only [Complex.real_smul, mul_comm] using h
  exact congrFun ((hF.ae_eq_iff_eq volume hG).mp hae) ξ

theorem ballResolventDistribution_compactlySupported (n : ℕ) (a : ℝ)
    (hb : ballHelmholtzSquare n ((a ^ 2 : ℝ) : ℂ) ≠ 0) :
    CompactlySupportedDistribution (ballResolventDistribution n a hb) :=
  ⟨Metric.closedBall (0 : Euclidean (n + 1)) 1, isCompact_closedBall _ _,
    ballResolventDistribution_supported n a hb⟩

theorem ballResolventDistribution_ne_zero (n : ℕ) {a : ℝ} (ha : a ≠ 0)
    (hz : radialBallFourier n (a : ℂ) = 0)
    (hb : ballHelmholtzSquare n ((a ^ 2 : ℝ) : ℂ) ≠ 0) :
    ballResolventDistribution n a hb ≠ 0 := by
  intro hu
  have h := ballResolventDistribution_helmholtz n ha hz hb
  rw [hu] at h
  have hop : ballHelmholtzOperator n a 0 = 0 := by
    ext ψ
    simp only [ballHelmholtzOperator, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.neg_apply, ContinuousLinearMap.sum_apply,
      ContinuousLinearMap.smul_apply, smul_eq_mul, distributionDerivative_apply,
      ContinuousLinearMap.zero_apply, neg_zero, Finset.sum_const_zero, mul_zero, sub_self]
  rw [hop] at h
  exact normalizedBallDistribution_ne_zero (n + 1) h.symm

theorem entireFourier_ballResolvent_differentiable (n : ℕ) (a : ℝ)
    (hb : ballHelmholtzSquare n ((a ^ 2 : ℝ) : ℂ) ≠ 0) :
    Differentiable ℂ (entireFourier (ballResolvent n a)) := by
  apply entireFourier_differentiable (ballResolvent_integrable n a hb) (R := 1) zero_le_one
  filter_upwards with x
  intro hx
  have hm : x ∈ physicalUnitBall (n + 1) := Set.mem_of_indicator_ne_zero hx
  exact (mem_ball_zero_iff.mp hm).le

/-- The compact physical inverse has the entire Fourier divisor identity everywhere. -/
theorem entireFourier_ballResolvent_divisor (n : ℕ) {a : ℝ} (ha : a ≠ 0)
    (hz : radialBallFourier n (a : ℂ) = 0)
    (hb : ballHelmholtzSquare n ((a ^ 2 : ℝ) : ℂ) ≠ 0) (z : ComplexEuclidean (n + 1)) :
    (ballQuadraticForm (n + 1) z - ((a ^ 2 : ℝ) : ℂ)) * entireFourier (ballResolvent n a) z =
      normalizedBallFourier (n + 1) z := by
  have he : (fun z : ComplexEuclidean (n + 1) =>
      (ballQuadraticForm (n + 1) z - ((a ^ 2 : ℝ) : ℂ)) * entireFourier (ballResolvent n a) z) =
      normalizedBallFourier (n + 1) := by
    apply entire_eq_of_eq_on_real
      (((ballQuadraticForm_differentiable (n + 1)).sub (differentiable_const _)).mul
        (entireFourier_ballResolvent_differentiable n a hb))
      (normalizedBallFourier_differentiable (n + 1))
    intro ξ
    rw [entireFourier_realToComplex]
    exact fourier_ballResolvent_divisor n ha hz hb ξ
  exact congrFun he z

/-- Away from the characteristic quadric this actual entire Fourier transform
is the paper's resolvent quotient; on the quadric the same transform supplies its removable values. -/
theorem entireFourier_ballResolvent_eq_quotient (n : ℕ) {a : ℝ} (ha : a ≠ 0)
    (hz : radialBallFourier n (a : ℂ) = 0)
    (hb : ballHelmholtzSquare n ((a ^ 2 : ℝ) : ℂ) ≠ 0) (z : ComplexEuclidean (n + 1))
    (hq : ballQuadraticForm (n + 1) z - ((a ^ 2 : ℝ) : ℂ) ≠ 0) :
    entireFourier (ballResolvent n a) z =
      normalizedBallFourier (n + 1) z / (ballQuadraticForm (n + 1) z - ((a ^ 2 : ℝ) : ℂ)) := by
  apply (eq_div_iff hq).mpr
  rw [mul_comm]
  exact entireFourier_ballResolvent_divisor n ha hz hb z

theorem fourier_ballResolvent_eq_quotient (n : ℕ) {a : ℝ} (ha : a ≠ 0)
    (hz : radialBallFourier n (a : ℂ) = 0)
    (hb : ballHelmholtzSquare n ((a ^ 2 : ℝ) : ℂ) ≠ 0) (ξ : Euclidean (n + 1))
    (hq : ballQuadraticForm (n + 1) (realToComplex ξ) - ((a ^ 2 : ℝ) : ℂ) ≠ 0) :
    𝓕 (ballResolvent n a) ξ = normalizedBallFourier (n + 1) (realToComplex ξ) /
      (ballQuadraticForm (n + 1) (realToComplex ξ) - ((a ^ 2 : ℝ) : ℂ)) := by
  rw [← entireFourier_realToComplex]
  exact entireFourier_ballResolvent_eq_quotient n ha hz hb (realToComplex ξ) hq

end RieszEuclidean.CompleteMinimal
