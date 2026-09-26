import RieszEuclidean.CompleteMinimalEntireFourier
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Real spheres and their complex quadrics

The coordinate algebra uses `Fin n → ℂ`, canonically continuously linearly equivalent
to complex Euclidean space. Squares in this file are complex squares, without conjugation.
-/

noncomputable section
open scoped Topology
open Filter Set

namespace RieszEuclidean.CompleteMinimal

/-- The complex quadratic form without conjugation. -/
def squareSum {n : ℕ} (z : Fin n → ℂ) : ℂ := ∑ i, z i ^ 2

/-- The squared Euclidean norm written in real coordinates. -/
def realSquareSum {n : ℕ} (x : Fin n → ℝ) : ℝ := ∑ i, x i ^ 2

/-- The real coordinate dot product. -/
def realDot {n : ℕ} (x y : Fin n → ℝ) : ℝ := ∑ i, x i * y i

/-- Coordinatewise embedding of real vectors into complex vectors. -/
def realCoords {n : ℕ} (x : Fin n → ℝ) : Fin n → ℂ := fun i => (x i : ℂ)

theorem squareSum_re {n : ℕ} (z : Fin n → ℂ) :
    (squareSum z).re = realSquareSum (fun i => (z i).re) -
      realSquareSum (fun i => (z i).im) := by
  simp only [squareSum, realSquareSum, Complex.re_sum, pow_two, Complex.mul_re,
    ← Finset.sum_sub_distrib]

theorem squareSum_im {n : ℕ} (z : Fin n → ℂ) :
    (squareSum z).im = 2 * realDot (fun i => (z i).re) (fun i => (z i).im) := by
  simp only [squareSum, realDot, Complex.im_sum, pow_two, Complex.mul_im,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem quadric_real_imag {n : ℕ} (z : Fin n → ℂ) (r : ℝ)
    (hz : squareSum z = (r : ℂ) ^ 2) :
    realSquareSum (fun i => (z i).re) - realSquareSum (fun i => (z i).im) = r ^ 2 ∧
      realDot (fun i => (z i).re) (fun i => (z i).im) = 0 := by
  have hre := congrArg Complex.re hz
  have him := congrArg Complex.im hz
  rw [squareSum_re] at hre
  rw [squareSum_im] at him
  simp only [pow_two, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, zero_mul, sub_zero, add_zero] at hre him
  exact ⟨by simpa only [pow_two] using hre, by linarith⟩

/-- First coordinate of the complex parametrization of a circle. -/
def circleFirst (r : ℂ) (w : ℂ) : ℂ := r / 2 * (w + w⁻¹)

/-- Second coordinate of the complex parametrization of a circle. -/
def circleSecond (r : ℂ) (w : ℂ) : ℂ := r / (2 * Complex.I) * (w - w⁻¹)

theorem circle_coordinates_square (r w : ℂ) (hw : w ≠ 0) :
    circleFirst r w ^ 2 + circleSecond r w ^ 2 = r ^ 2 := by
  unfold circleFirst circleSecond
  field_simp [hw]
  ring_nf
  simp only [Complex.I_sq]
  ring

theorem circle_parameter_nonzero (r z₁ z₂ : ℂ) (hr : r ≠ 0)
    (hz : z₁ ^ 2 + z₂ ^ 2 = r ^ 2) : (z₁ + Complex.I * z₂) / r ≠ 0 := by
  apply div_ne_zero _ hr
  intro h
  have hprod : (z₁ + Complex.I * z₂) * (z₁ - Complex.I * z₂) = r ^ 2 := by
    linear_combination hz - z₂ ^ 2 * Complex.I_sq
  rw [h, zero_mul] at hprod
  exact pow_ne_zero 2 hr hprod.symm

theorem circle_parameter_inverse (r z₁ z₂ : ℂ) (hr : r ≠ 0)
    (hz : z₁ ^ 2 + z₂ ^ 2 = r ^ 2) :
    circleFirst r ((z₁ + Complex.I * z₂) / r) = z₁ ∧
      circleSecond r ((z₁ + Complex.I * z₂) / r) = z₂ := by
  have hprod : (z₁ + Complex.I * z₂) * (z₁ - Complex.I * z₂) = r ^ 2 := by
    linear_combination hz - z₂ ^ 2 * Complex.I_sq
  have hinv : ((z₁ + Complex.I * z₂) / r)⁻¹ = (z₁ - Complex.I * z₂) / r := by
    apply inv_eq_of_mul_eq_one_right
    rw [div_mul_div_comm, hprod, pow_two, div_self (mul_ne_zero hr hr)]
  constructor
  · unfold circleFirst
    rw [hinv]
    field_simp
    ring
  · unfold circleSecond
    rw [hinv]
    field_simp
    ring

theorem circle_coordinates_real (r : ℝ) (w : ℂ) (hw : ‖w‖ = 1) :
    circleFirst r w = (r * w.re : ℝ) ∧
      circleSecond r w = (r * w.im : ℝ) := by
  rw [circleFirst, circleSecond, Complex.inv_eq_conj hw]
  constructor
  · apply Complex.ext
    · simp
      ring
    · simp
  · rw [div_mul_eq_mul_div]
    apply (div_eq_iff (mul_ne_zero (by norm_num) Complex.I_ne_zero)).mpr
    apply Complex.ext
    · simp
    · simp
      ring

theorem realSquareSum_nonneg {n : ℕ} (x : Fin n → ℝ) : 0 ≤ realSquareSum x := by
  exact Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem realSquareSum_eq_zero {n : ℕ} (x : Fin n → ℝ)
    (hx : realSquareSum x = 0) : x = 0 := by
  funext i
  have hi : x i ^ 2 ≤ realSquareSum x :=
    Finset.single_le_sum (fun j _ => sq_nonneg (x j)) (Finset.mem_univ i)
  have : x i ^ 2 = 0 := le_antisymm (hx ▸ hi) (sq_nonneg _)
  exact (sq_eq_zero_iff.mp this)

theorem realSquareSum_linear {n : ℕ} (x y : Fin n → ℝ) (u v : ℝ) :
    realSquareSum (fun i => u * x i + v * y i) =
      u ^ 2 * realSquareSum x + 2 * u * v * realDot x y + v ^ 2 * realSquareSum y := by
  simp only [realSquareSum, realDot, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem realSquareSum_div {n : ℕ} (x : Fin n → ℝ) (a : ℝ) :
    realSquareSum (fun i => x i / a) = realSquareSum x / a ^ 2 := by
  simp only [realSquareSum, div_pow, Finset.sum_div]

theorem realDot_div {n : ℕ} (x y : Fin n → ℝ) (a b : ℝ) :
    realDot (fun i => x i / a) (fun i => y i / b) = realDot x y / (a * b) := by
  simp only [realDot, div_mul_div_comm, Finset.sum_div]

/-- The one-variable identity principle applied to the embedded real line. -/
theorem entire_zero_of_real_zero (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (hreal : ∀ t : ℝ, f t = 0) : ∀ z, f z = 0 := by
  have ht : Tendsto (fun t : ℝ => (t : ℂ)) (𝓝[≠] 0) (𝓝[≠] 0) := by
    apply Complex.continuous_ofReal.continuousWithinAt.tendsto_nhdsWithin
    intro t ht
    simpa using ht
  have hfreq : ∃ᶠ z in 𝓝[≠] (0 : ℂ), f z = 0 :=
    ht.frequently (Filter.Eventually.frequently (Filter.Eventually.of_forall hreal))
  have ha : AnalyticOnNhd ℂ f univ := fun z _ => hf.analyticAt z
  exact fun z => ha.eqOn_zero_of_preconnected_of_frequently_eq_zero
    isPreconnected_univ (mem_univ 0) hfreq (mem_univ z)

/-- The circle parametrization in a real plane spanned by two vectors. -/
def circlePlane {n : ℕ} (r : ℝ) (a b : Fin n → ℝ) (w : ℂ) : Fin n → ℂ :=
  fun i => circleFirst r w * (a i : ℂ) + circleSecond r w * (b i : ℂ)

theorem circlePlane_real {n : ℕ} (r : ℝ) (a b : Fin n → ℝ) (w : ℂ)
    (hw : ‖w‖ = 1) : circlePlane r a b w =
      realCoords (fun i => r * w.re * a i + r * w.im * b i) := by
  obtain ⟨h₁, h₂⟩ := circle_coordinates_real r w hw
  funext i
  simp only [circlePlane, realCoords, h₁, h₂, Complex.ofReal_add, Complex.ofReal_mul]

theorem circlePlane_real_sphere {n : ℕ} (r : ℝ) (a b : Fin n → ℝ)
    (ha : realSquareSum a = 1) (hb : realSquareSum b = 1) (hab : realDot a b = 0)
    (w : ℂ) (hw : ‖w‖ = 1) :
    realSquareSum (fun i => r * w.re * a i + r * w.im * b i) = r ^ 2 := by
  rw [realSquareSum_linear, ha, hb, hab]
  have hnorm : w.re ^ 2 + w.im ^ 2 = 1 := by
    have := Complex.normSq_eq_norm_sq w
    simp only [Complex.normSq_apply, hw, one_pow] at this
    nlinarith
  nlinarith [sq_nonneg r]

/-- Analytic continuation of the real circle through the entire exponential parameter. -/
theorem entire_zero_on_circlePlane {n : ℕ} (F : (Fin n → ℂ) → ℂ)
    (hF : Differentiable ℂ F) (r : ℝ)
    (hreal : ∀ x : Fin n → ℝ, realSquareSum x = r ^ 2 → F (realCoords x) = 0)
    (a b : Fin n → ℝ) (ha : realSquareSum a = 1) (hb : realSquareSum b = 1)
    (hab : realDot a b = 0) (w : ℂ) (hw : w ≠ 0) : F (circlePlane r a b w) = 0 := by
  let c : ℂ → Fin n → ℂ := fun t => circlePlane r a b (Complex.exp (Complex.I * t))
  have hexp : Differentiable ℂ (fun t : ℂ => Complex.exp (Complex.I * t)) :=
    Complex.differentiable_exp.comp ((differentiable_const _).mul differentiable_id)
  have hc : Differentiable ℂ c := by
    apply differentiable_pi.mpr
    intro i
    exact (((differentiable_const _).mul (hexp.add (hexp.inv (fun _ => Complex.exp_ne_zero _)))).mul
      (differentiable_const _)).add
      (((differentiable_const _).mul (hexp.sub (hexp.inv (fun _ => Complex.exp_ne_zero _)))).mul
        (differentiable_const _))
  have hzero : ∀ t : ℝ, F (c t) = 0 := by
    intro t
    have hn : ‖Complex.exp (Complex.I * (t : ℂ))‖ = 1 := by
      simp [Complex.norm_exp]
    rw [show c t = realCoords (fun i => r * (Complex.exp (Complex.I * (t : ℂ))).re * a i +
        r * (Complex.exp (Complex.I * (t : ℂ))).im * b i) from
      circlePlane_real r a b _ hn]
    exact hreal _ (circlePlane_real_sphere r a b ha hb hab _ hn)
  have h := entire_zero_of_real_zero (fun t => F (c t)) (hF.comp hc) hzero
    (-Complex.I * Complex.log w)
  have hparam : Complex.exp (Complex.I * (-Complex.I * Complex.log w)) = w := by
    have ht : Complex.I * (-Complex.I * Complex.log w) = Complex.log w := by
      linear_combination -Complex.log w * Complex.I_sq
    rw [ht, Complex.exp_log hw]
  simpa only [c, hparam] using h

theorem entire_zero_on_complex_circle {n : ℕ} (F : (Fin n → ℂ) → ℂ)
    (hF : Differentiable ℂ F) (r : ℝ) (hr : r ≠ 0)
    (hreal : ∀ x : Fin n → ℝ, realSquareSum x = r ^ 2 → F (realCoords x) = 0)
    (a b : Fin n → ℝ) (ha : realSquareSum a = 1) (hb : realSquareSum b = 1)
    (hab : realDot a b = 0) (z₁ z₂ : ℂ) (hz : z₁ ^ 2 + z₂ ^ 2 = (r : ℂ) ^ 2) :
    F (fun i => z₁ * (a i : ℂ) + z₂ * (b i : ℂ)) = 0 := by
  have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hr
  obtain ⟨h₁, h₂⟩ := circle_parameter_inverse r z₁ z₂ hrC hz
  have h := entire_zero_on_circlePlane F hF r hreal a b ha hb hab
    ((z₁ + Complex.I * z₂) / r) (circle_parameter_nonzero r z₁ z₂ hrC hz)
  change F (fun i => circleFirst r ((z₁ + Complex.I * z₂) / r) * (a i : ℂ) +
    circleSecond r ((z₁ + Complex.I * z₂) / r) * (b i : ℂ)) = 0 at h
  rwa [h₁, h₂] at h

/-- An entire function vanishing on a real sphere vanishes on its complex quadric.

The argument works in every finite dimension: if the imaginary part is nonzero,
the real and imaginary parts themselves supply a real orthonormal two-plane.
-/
theorem entire_zero_on_quadric_coords {n : ℕ} (F : (Fin n → ℂ) → ℂ)
    (hF : Differentiable ℂ F) (r : ℝ) (hr : 0 < r)
    (hreal : ∀ x : Fin n → ℝ, realSquareSum x = r ^ 2 → F (realCoords x) = 0)
    (z : Fin n → ℂ) (hz : squareSum z = (r : ℂ) ^ 2) : F z = 0 := by
  let x : Fin n → ℝ := fun i => (z i).re
  let y : Fin n → ℝ := fun i => (z i).im
  obtain ⟨hxy, hdot⟩ := quadric_real_imag z r hz
  change realSquareSum x - realSquareSum y = r ^ 2 at hxy
  change realDot x y = 0 at hdot
  by_cases hy : realSquareSum y = 0
  · have hyzero := realSquareSum_eq_zero y hy
    have hcoords : realCoords x = z := by
      funext i
      apply Complex.ext
      · rfl
      · have hi := congrFun hyzero i
        simpa only [realCoords, Complex.ofReal_im, Pi.zero_apply] using hi.symm
    rw [← hcoords]
    exact hreal x (by linarith)
  · let α := Real.sqrt (realSquareSum x)
    let β := Real.sqrt (realSquareSum y)
    have hxsq : α ^ 2 = realSquareSum x := Real.sq_sqrt (realSquareSum_nonneg x)
    have hysq : β ^ 2 = realSquareSum y := Real.sq_sqrt (realSquareSum_nonneg y)
    have hβ : 0 < β := Real.sqrt_pos.mpr
      (lt_of_le_of_ne (realSquareSum_nonneg y) (Ne.symm hy))
    have hα : 0 < α := Real.sqrt_pos.mpr (by
      nlinarith [sq_pos_of_pos hr])
    let a : Fin n → ℝ := fun i => x i / α
    let b : Fin n → ℝ := fun i => y i / β
    have ha : realSquareSum a = 1 := by
      rw [realSquareSum_div, ← hxsq, div_self (pow_ne_zero 2 hα.ne')]
    have hb : realSquareSum b = 1 := by
      rw [realSquareSum_div, ← hysq, div_self (pow_ne_zero 2 hβ.ne')]
    have hab : realDot a b = 0 := by rw [realDot_div, hdot, zero_div]
    have heq : α ^ 2 - β ^ 2 = r ^ 2 := by rw [hxsq, hysq]; exact hxy
    have hcircle : (α : ℂ) ^ 2 + (Complex.I * (β : ℂ)) ^ 2 = (r : ℂ) ^ 2 := by
      calc
        (α : ℂ) ^ 2 + (Complex.I * (β : ℂ)) ^ 2 = ((α ^ 2 - β ^ 2 : ℝ) : ℂ) := by
          push_cast
          linear_combination (β : ℂ) ^ 2 * Complex.I_sq
        _ = (r : ℂ) ^ 2 := by rw [heq, Complex.ofReal_pow]
    have h := entire_zero_on_complex_circle F hF r hr.ne' hreal a b ha hb hab
      α (Complex.I * β) hcircle
    have hcoords : (fun i => (α : ℂ) * (a i : ℂ) +
        (Complex.I * (β : ℂ)) * (b i : ℂ)) = z := by
      funext i
      simp only [a, b, Complex.ofReal_div]
      have hαC : (α : ℂ) ≠ 0 := by exact_mod_cast hα.ne'
      have hβC : (β : ℂ) ≠ 0 := by exact_mod_cast hβ.ne'
      calc
        (α : ℂ) * ((x i : ℂ) / α) + (Complex.I * β) * ((y i : ℂ) / β) =
            (x i : ℂ) + (y i : ℂ) * Complex.I := by field_simp; ring
        _ = z i := Complex.re_add_im (z i)
    rwa [hcoords] at h

/-- The coordinate result transported through the canonical continuous linear equivalence.
Its real-sphere hypothesis uses the actual Euclidean norm and the Fourier module's embedding. -/
theorem entire_zero_on_quadric {n : ℕ} (F : ComplexEuclidean n → ℂ)
    (hF : Differentiable ℂ F) (r : ℝ) (hr : 0 < r)
    (hreal : ∀ x : Euclidean n, ‖x‖ = r → F (realToComplex x) = 0)
    (z : ComplexEuclidean n) (hz : squareSum (fun i => z i) = (r : ℂ) ^ 2) :
    F z = 0 := by
  let e := EuclideanSpace.equiv (Fin n) ℂ
  apply entire_zero_on_quadric_coords (F ∘ e.symm) (hF.comp e.symm.differentiable) r hr
    (fun x hx => ?_) (fun i => z i) hz
  let u : Euclidean n := (WithLp.equiv 2 (Fin n → ℝ)).symm x
  have hnorm : ‖u‖ ^ 2 = r ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2]
    simpa only [u, WithLp.equiv_symm_pi_apply, Real.norm_eq_abs, sq_abs] using hx
  have hu : ‖u‖ = r := (sq_eq_sq₀ (norm_nonneg u) hr.le).mp hnorm
  exact hreal u hu

/-- Every positive-radius quadric point has a nonzero coordinate. -/
theorem quadric_exists_nonzero_coordinate {n : ℕ} (z : Fin n → ℂ) (r : ℝ)
    (hr : 0 < r) (hz : squareSum z = (r : ℂ) ^ 2) : ∃ i, z i ≠ 0 := by
  by_contra h
  push_neg at h
  have hzero : squareSum z = 0 := by simp [squareSum, h]
  have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  exact pow_ne_zero 2 hrC (hz.symm.trans hzero)

theorem squareSum_coordinate_shift {n : ℕ} (z : Fin n → ℂ) (j : Fin n) (t : ℂ) :
    squareSum (fun i => z i + if i = j then t else 0) =
      squareSum z + 2 * z j * t + t ^ 2 := by
  classical
  have hterm : ∀ i : Fin n, (z i + if i = j then t else 0) ^ 2 =
      z i ^ 2 + if i = j then 2 * z j * t + t ^ 2 else 0 := by
    intro i
    by_cases hi : i = j
    · simp only [hi, ↓reduceIte]
      ring
    · simp only [hi, if_false, add_zero]
  simp only [squareSum, hterm, Finset.sum_add_distrib]
  simp
  ring

/-- The defining quadratic has a nonzero derivative in some coordinate direction.
This is the nonsingularity input for a subsequent local analytic division theorem. -/
theorem quadric_exists_nonzero_normal_derivative {n : ℕ} (z : Fin n → ℂ) (r : ℝ)
    (hr : 0 < r) (hz : squareSum z = (r : ℂ) ^ 2) :
    ∃ j, 2 * z j ≠ 0 ∧ HasDerivAt
      (fun t : ℂ => squareSum (fun i => z i + if i = j then t else 0) - (r : ℂ) ^ 2)
      (2 * z j) 0 := by
  obtain ⟨j, hj⟩ := quadric_exists_nonzero_coordinate z r hr hz
  refine ⟨j, mul_ne_zero (by norm_num) hj, ?_⟩
  simp only [squareSum_coordinate_shift]
  convert (((hasDerivAt_const (0 : ℂ) (squareSum z)).add
    ((hasDerivAt_id (0 : ℂ)).const_mul (2 * z j))).add
    ((hasDerivAt_id (0 : ℂ)).pow 2)).sub_const ((r : ℂ) ^ 2) using 1
  simp

end RieszEuclidean.CompleteMinimal
