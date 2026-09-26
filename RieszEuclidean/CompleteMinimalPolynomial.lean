import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.LinearAlgebra.LinearIndependent.Defs

noncomputable section

namespace RieszEuclidean.CompleteMinimal

open MvPolynomial

/-- Real Euclidean points used for multivariate interpolation. -/
abbrev RealPoint (d : ℕ) := EuclideanSpace ℝ (Fin d)
/-- Complex polynomials in the coordinate variables of Euclidean space. -/
abbrev ComplexPolynomial (d : ℕ) := MvPolynomial (Fin d) ℂ

/-- Evaluation at a real Euclidean point, embedded coordinatewise in `ℂ`. -/
def polynomialEvaluation {d : ℕ} (x : RealPoint d) : ComplexPolynomial d →ₗ[ℂ] ℂ :=
  (MvPolynomial.aeval fun k => (x k : ℂ)).toLinearMap

@[simp]
theorem polynomialEvaluation_apply {d : ℕ} (x : RealPoint d) (p : ComplexPolynomial d) :
    polynomialEvaluation x p = MvPolynomial.eval (fun k => (x k : ℂ)) p := rfl

private theorem exists_coordinate_ne {d : ℕ} {x y : RealPoint d} (h : x ≠ y) :
    ∃ k, x k ≠ y k := by
  by_contra hn
  push_neg at hn
  apply h
  ext k
  exact hn k

/-- A normalized affine factor equal to one at `x` and zero at distinct `y`. -/
def separatingFactor {d : ℕ} (x y : RealPoint d) : ComplexPolynomial d :=
  if h : x ≠ y then
    let k := Classical.choose (exists_coordinate_ne h)
    (X k - C (y k : ℂ)) * C (((x k : ℂ) - (y k : ℂ))⁻¹)
  else 1

theorem separatingFactor_totalDegree_le {d : ℕ} (x y : RealPoint d) :
    (separatingFactor x y).totalDegree ≤ 1 := by
  classical
  unfold separatingFactor
  split_ifs
  · exact (totalDegree_mul _ _).trans (by
      simpa using totalDegree_sub_C_le (X _) (y _ : ℂ))
  · simp

@[simp]
theorem separatingFactor_eval_self {d : ℕ} (x y : RealPoint d) :
    eval (fun k => (x k : ℂ)) (separatingFactor x y) = 1 := by
  classical
  unfold separatingFactor
  split_ifs with h
  · have hk := Classical.choose_spec (exists_coordinate_ne h)
    have hc : (x (Classical.choose (exists_coordinate_ne h)) : ℂ) -
        (y (Classical.choose (exists_coordinate_ne h)) : ℂ) ≠ 0 :=
      sub_ne_zero.mpr (Complex.ofReal_injective.ne hk)
    simp [hc]
  · simp

@[simp]
theorem separatingFactor_eval_other {d : ℕ} (x y : RealPoint d) (h : x ≠ y) :
    eval (fun k => (y k : ℂ)) (separatingFactor x y) = 0 := by
  classical
  simp [separatingFactor, h]

/-- Multivariate Lagrange polynomial for a finite family of distinct real points. -/
def interpolationPolynomial {d : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (points : ι → RealPoint d) (i : ι) : ComplexPolynomial d :=
  ∏ j ∈ Finset.univ.erase i, separatingFactor (points i) (points j)

theorem interpolationPolynomial_totalDegree_le {d : ℕ} {ι : Type*}
    [Fintype ι] [DecidableEq ι] (points : ι → RealPoint d) (i : ι) :
    (interpolationPolynomial points i).totalDegree ≤ Fintype.card ι - 1 := by
  classical
  calc
    _ ≤ ∑ j ∈ Finset.univ.erase i, (separatingFactor (points i) (points j)).totalDegree :=
      totalDegree_finset_prod _ _
    _ ≤ ∑ _j ∈ Finset.univ.erase i, 1 :=
      Finset.sum_le_sum fun j _ => separatingFactor_totalDegree_le _ _
    _ = Fintype.card ι - 1 := by simp

theorem interpolationPolynomial_eval {d : ℕ} {ι : Type*} [Fintype ι]
    [DecidableEq ι] (points : ι → RealPoint d) (hinj : Function.Injective points)
    (i j : ι) :
    polynomialEvaluation (points j) (interpolationPolynomial points i) =
      if j = i then 1 else 0 := by
  classical
  by_cases h : j = i
  · subst j
    simp only [polynomialEvaluation_apply, interpolationPolynomial, map_prod]
    apply Finset.prod_eq_one
    intro j _
    exact separatingFactor_eval_self _ _
  · rw [if_neg h, polynomialEvaluation_apply]
    simp only [interpolationPolynomial, map_prod]
    apply Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨h, Finset.mem_univ j⟩)
    exact separatingFactor_eval_other _ _ (fun he => h (hinj he).symm)

/-- Every prescribed complex value on finitely many distinct points is interpolated
by a polynomial of total degree at most the number of points minus one. -/
theorem exists_interpolating_polynomial {d : ℕ} {ι : Type*} [Fintype ι]
    (points : ι → RealPoint d) (hinj : Function.Injective points) (values : ι → ℂ) :
    ∃ p : ComplexPolynomial d, p.totalDegree ≤ Fintype.card ι - 1 ∧
      ∀ i, polynomialEvaluation (points i) p = values i := by
  classical
  refine ⟨∑ i, C (values i) * interpolationPolynomial points i, ?_, ?_⟩
  · apply totalDegree_finsetSum_le
    intro i _
    exact (totalDegree_mul _ _).trans (by
      simpa using interpolationPolynomial_totalDegree_le points i)
  · intro i
    simp only [polynomialEvaluation_apply, map_sum, map_mul, eval_C]
    simp_rw [← polynomialEvaluation_apply, interpolationPolynomial_eval points hinj]
    simp

/-- Evaluation restricted to the standard submodule of bounded total degree. -/
def boundedPolynomialEvaluation {d : ℕ} (m : ℕ) (x : RealPoint d) :
    MvPolynomial.restrictTotalDegree (Fin d) ℂ m →ₗ[ℂ] ℂ :=
  (polynomialEvaluation x).comp (MvPolynomial.restrictTotalDegree (Fin d) ℂ m).subtype

@[simp]
theorem boundedPolynomialEvaluation_apply {d : ℕ} (m : ℕ) (x : RealPoint d)
    (p : MvPolynomial.restrictTotalDegree (Fin d) ℂ m) :
    boundedPolynomialEvaluation m x p = polynomialEvaluation x p := rfl

/-- Simultaneous evaluation on a finite family of real points. -/
def boundedSampling {d : ℕ} {ι : Type*} (m : ℕ) (points : ι → RealPoint d) :
    MvPolynomial.restrictTotalDegree (Fin d) ℂ m →ₗ[ℂ] (ι → ℂ) :=
  LinearMap.pi fun i => boundedPolynomialEvaluation m (points i)

theorem boundedSampling_surjective {d m : ℕ} {ι : Type*} [Fintype ι]
    (points : ι → RealPoint d) (hinj : Function.Injective points)
    (hm : Fintype.card ι - 1 ≤ m) : Function.Surjective (boundedSampling m points) := by
  intro values
  obtain ⟨p, hp, hv⟩ := exists_interpolating_polynomial points hinj values
  refine ⟨⟨p, (MvPolynomial.mem_restrictTotalDegree _ _ _).mpr (hp.trans hm)⟩, ?_⟩
  ext i
  exact hv i

/-- Distinct point evaluations are linearly independent on bounded-degree polynomials
once the bound is at least the number of points minus one. -/
theorem boundedPolynomialEvaluation_linearIndependent {d m : ℕ} {ι : Type*} [Fintype ι]
    (points : ι → RealPoint d) (hinj : Function.Injective points)
    (hm : Fintype.card ι - 1 ≤ m) :
    LinearIndependent ℂ (fun i => boundedPolynomialEvaluation m (points i)) := by
  classical
  apply Fintype.linearIndependent_iff.mpr
  intro c hc i
  obtain ⟨p, hp⟩ := boundedSampling_surjective points hinj hm
    (Pi.single i (1 : ℂ) : ι → ℂ)
  have hv : ∀ j, boundedPolynomialEvaluation m (points j) p =
      (Pi.single i (1 : ℂ) : ι → ℂ) j :=
    fun j => congrFun hp j
  have he := LinearMap.congr_fun hc p
  simpa [LinearMap.sum_apply, hv, Pi.single_apply] using he

/-- Finite-set form of polynomial interpolation, with the degree bound `card - 1`. -/
theorem exists_interpolating_polynomial_finset {d : ℕ} (s : Finset (RealPoint d))
    (values : ↥s → ℂ) :
    ∃ p : ComplexPolynomial d, p.totalDegree ≤ s.card - 1 ∧
      ∀ x : ↥s, polynomialEvaluation x p = values x := by
  simpa using exists_interpolating_polynomial (fun x : ↥s => x.val)
    Subtype.val_injective values

/-- A Kronecker interpolation polynomial associated to any member of a finite set. -/
theorem exists_kronecker_polynomial_finset {d : ℕ} (s : Finset (RealPoint d))
    (x : ↥s) :
    ∃ p : ComplexPolynomial d, p.totalDegree ≤ s.card - 1 ∧
      ∀ y : ↥s, polynomialEvaluation y.val p = if y = x then 1 else 0 := by
  classical
  exact exists_interpolating_polynomial_finset s (fun y => if y = x then 1 else 0)

theorem boundedSampling_finset_surjective {d m : ℕ} (s : Finset (RealPoint d))
    (hm : s.card - 1 ≤ m) :
    Function.Surjective (boundedSampling m (fun x : ↥s => x.val)) := by
  apply boundedSampling_surjective _ Subtype.val_injective
  simpa using hm

theorem boundedPolynomialEvaluation_finset_linearIndependent {d m : ℕ}
    (s : Finset (RealPoint d)) (hm : s.card - 1 ≤ m) :
    LinearIndependent ℂ (fun x : ↥s => boundedPolynomialEvaluation m x.val) := by
  apply boundedPolynomialEvaluation_linearIndependent _ Subtype.val_injective
  simpa using hm

end RieszEuclidean.CompleteMinimal
