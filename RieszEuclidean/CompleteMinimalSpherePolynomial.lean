import RieszEuclidean.CompleteMinimalPolynomial
import Mathlib.Algebra.MvPolynomial.Polynomial
import Mathlib.Algebra.Polynomial.Degree.SmallDegree
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.RingTheory.MvPolynomial.MonomialOrder.DegLex

noncomputable section

namespace RieszEuclidean.CompleteMinimal

open MvPolynomial

/-- A complex polynomial which vanishes on a nonempty real coordinate box is zero. -/
theorem polynomial_eq_zero_of_real_box {n : ℕ} (P : ComplexPolynomial n)
    (a b : Fin n → ℝ) (hab : ∀ i, a i < b i)
    (hP : ∀ x : Fin n → ℝ, (∀ i, x i ∈ Set.Ioo (a i) (b i)) →
      MvPolynomial.eval (fun i => (x i : ℂ)) P = 0) : P = 0 := by
  induction n with
  | zero =>
    apply (MvPolynomial.isEmptyRingEquiv ℂ (Fin 0)).injective
    change (MvPolynomial.eval (fun i => isEmptyElim i)) P = 0
    convert hP Fin.elim0 (by intro i; exact Fin.elim0 i) using 2
    apply congrArg MvPolynomial.eval
    funext i
    exact Fin.elim0 i
  | succ n ih =>
    let p := MvPolynomial.finSuccEquiv ℂ n P
    have hp : ∀ x : Fin n → ℝ, (∀ i, x i ∈ Set.Ioo (a i.succ) (b i.succ)) →
        p.map (MvPolynomial.eval (fun i => (x i : ℂ))) = 0 := by
      intro x hx
      apply Polynomial.eq_zero_of_infinite_isRoot
      apply ((Set.Ioo_infinite (hab 0)).image Complex.ofReal_injective.injOn).mono
      rintro _ ⟨y, hy, rfl⟩
      change Polynomial.eval (y : ℂ) (p.map _) = 0
      rw [← MvPolynomial.eval_eq_eval_mv_eval']
      have h := hP (Fin.cons y x) (fun i => Fin.cases hy (fun j => hx j) i)
      convert h using 2
      apply congrArg MvPolynomial.eval
      funext i
      refine Fin.cases ?_ (fun j => ?_) i <;> rfl
    apply (MvPolynomial.finSuccEquiv ℂ n).injective
    apply Polynomial.ext
    intro k
    simp only [map_zero, Polynomial.coeff_zero]
    apply ih (p.coeff k) (fun i => a i.succ) (fun i => b i.succ)
      (fun i => hab i.succ)
    intro x hx
    have hk := congrArg (fun q => Polynomial.coeff q k) (hp x hx)
    simpa using hk

/-- The polynomial defining a real sphere, with complex coefficients. -/
def spherePolynomial (n : ℕ) (r : ℝ) : ComplexPolynomial n :=
  (∑ i, X i ^ 2) - C (r ^ 2 : ℂ)

@[simp]
theorem polynomialEvaluation_spherePolynomial {n : ℕ} (x : RealPoint n) (r : ℝ) :
    eval (fun k => (x k : ℂ)) (spherePolynomial n r) = ((‖x‖ ^ 2 - r ^ 2 : ℝ) : ℂ) := by
  have hnorm : ‖x‖ ^ 2 = ∑ i, x i ^ 2 := by
    simpa [Real.norm_eq_abs, sq_abs] using PiLp.norm_sq_eq_of_L2 (fun _ : Fin n => ℝ) x
  simp only [spherePolynomial, map_sub, map_sum, map_pow, eval_X, eval_C]
  exact_mod_cast congrArg (fun a : ℝ => a - r ^ (2 : ℕ)) hnorm.symm

theorem polynomialEvaluation_spherePolynomial_eq_zero_iff {n : ℕ}
    (x : RealPoint n) (r : ℝ) (hr : 0 ≤ r) :
    polynomialEvaluation x (spherePolynomial n r) = 0 ↔ ‖x‖ = r := by
  rw [polynomialEvaluation_apply, polynomialEvaluation_spherePolynomial,
    Complex.ofReal_eq_zero, sub_eq_zero]
  exact sq_eq_sq₀ (norm_nonneg x) hr

/-- Real-ball uniqueness, expressed by the sum of squared coordinates. -/
theorem polynomial_eq_zero_of_real_ball {n : ℕ} (P : ComplexPolynomial n)
    (r : ℝ) (hr : 0 < r)
    (hP : ∀ x : Fin n → ℝ, (∑ i, x i ^ 2) < r ^ 2 →
      MvPolynomial.eval (fun i => (x i : ℂ)) P = 0) : P = 0 := by
  let δ : ℝ := r / (n + 1)
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hδ : 0 < δ := div_pos hr (by positivity)
  have hrδ : r = (n + 1) * δ := by
    dsimp [δ]
    field_simp
  apply polynomial_eq_zero_of_real_box P (fun _ => -δ) (fun _ => δ)
    (fun _ => by change -δ < δ; linarith)
  intro x hx
  apply hP x
  have hs : (∑ i, x i ^ 2) ≤ (n : ℝ) * δ ^ 2 := by
    calc
      _ ≤ ∑ _i : Fin n, δ ^ 2 := Finset.sum_le_sum fun i _ => by
        have hi := hx i
        change -δ < x i ∧ x i < δ at hi
        nlinarith
      _ = _ := by simp
  have h₁ := mul_nonneg hn (sq_nonneg δ)
  have h₂ := mul_nonneg (sq_nonneg (n : ℝ)) (sq_nonneg δ)
  have h₃ := sq_pos_of_pos hδ
  rw [hrδ]
  nlinarith

@[simp]
theorem finSuccEquiv_spherePolynomial (n : ℕ) (r : ℝ) :
    MvPolynomial.finSuccEquiv ℂ n (spherePolynomial (n + 1) r) =
      Polynomial.X ^ 2 + Polynomial.C (spherePolynomial n r) := by
  classical
  simp only [spherePolynomial, Fin.sum_univ_succ]
  simp only [map_sub, map_add, map_sum, map_pow,
    MvPolynomial.finSuccEquiv_X_zero, MvPolynomial.finSuccEquiv_X_succ]
  simp only [MvPolynomial.finSuccEquiv_apply, MvPolynomial.eval₂Hom_C,
    RingHom.comp_apply]
  ring

/-- A sphere-vanishing polynomial is a multiple of its quadratic defining equation.
The hypothesis is in coordinates, so it applies without choosing a Euclidean-space model. -/
theorem spherePolynomial_dvd_of_eval_eq_zero {n : ℕ} (r : ℝ) (hr : 0 < r)
    (P : ComplexPolynomial (n + 1))
    (hP : ∀ x : Fin (n + 1) → ℝ, (∑ i, x i ^ 2) = r ^ 2 →
      MvPolynomial.eval (fun i => (x i : ℂ)) P = 0) :
    spherePolynomial (n + 1) r ∣ P := by
  classical
  let p := MvPolynomial.finSuccEquiv ℂ n P
  let q : Polynomial (ComplexPolynomial n) :=
    Polynomial.X ^ 2 + Polynomial.C (spherePolynomial n r)
  have hq : q.Monic := Polynomial.monic_X_pow_add_C _ (by decide)
  let s := p %ₘ q
  have hsdeg : s.degree ≤ 1 := by
    have h := Polynomial.degree_modByMonic_lt p hq
    rw [Polynomial.degree_X_pow_add_C (by decide)] at h
    change s.degree < (2 : WithBot ℕ) at h
    cases hd : s.degree with
    | bot => simp [hd]
    | coe d =>
      rw [hd] at h
      have hd₂ : d < 2 := WithBot.coe_lt_coe.mp h
      have hd₁ : d ≤ 1 := by omega
      exact WithBot.coe_le_coe.mpr hd₁
  have hsform : s = Polynomial.C (s.coeff 1) * Polynomial.X +
      Polynomial.C (s.coeff 0) := Polynomial.eq_X_add_C_of_degree_le_one hsdeg
  have hcoeff : ∀ k ∈ ({0, 1} : Finset ℕ), s.coeff k = 0 := by
    intro k hk
    apply polynomial_eq_zero_of_real_ball _ r hr
    intro x hx
    let t := Real.sqrt (r ^ 2 - ∑ i, x i ^ 2)
    have ht : 0 < t := Real.sqrt_pos.2 (by linarith)
    have htsq : t ^ 2 = r ^ 2 - ∑ i, x i ^ 2 := Real.sq_sqrt (by linarith)
    have heval : ∀ y : ℝ, y ^ 2 = r ^ 2 - ∑ i, x i ^ 2 →
        Polynomial.eval₂ (MvPolynomial.eval (fun i => (x i : ℂ))) (y : ℂ) s = 0 := by
      intro y hy
      have hp : Polynomial.eval₂ (MvPolynomial.eval (fun i => (x i : ℂ))) (y : ℂ) p = 0 := by
        rw [← Polynomial.eval_map, ← MvPolynomial.eval_eq_eval_mv_eval']
        have h := hP (Fin.cons y x) (by
          simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
          linarith)
        convert h using 2
        apply congrArg MvPolynomial.eval
        funext i
        refine Fin.cases ?_ (fun j => ?_) i <;> rfl
      have hqeval : Polynomial.eval₂ (MvPolynomial.eval (fun i => (x i : ℂ))) (y : ℂ) q = 0 := by
        simp only [q, Polynomial.eval₂_add, Polynomial.eval₂_pow, Polynomial.eval₂_X,
          Polynomial.eval₂_C]
        simp only [spherePolynomial, map_sub, map_sum, map_pow, eval_X, eval_C]
        have hc := congrArg Complex.ofReal hy
        push_cast at hc
        linear_combination hc
      have hdiv := congrArg
        (Polynomial.eval₂ (MvPolynomial.eval (fun i => (x i : ℂ))) (y : ℂ))
        (Polynomial.modByMonic_add_div p hq)
      simp only [Polynomial.eval₂_add, Polynomial.eval₂_mul, hqeval, zero_mul, add_zero,
        hp] at hdiv
      exact hdiv
    have hplus := heval t htsq
    have hminus := heval (-t) (by simpa using htsq)
    rw [hsform] at hplus hminus
    simp only [Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_C,
      Polynomial.eval₂_X, Complex.ofReal_neg] at hplus hminus
    have htcomplex : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
    have hfirst : MvPolynomial.eval (fun i => (x i : ℂ)) (s.coeff 1) = 0 := by
      have hm : MvPolynomial.eval (fun i => (x i : ℂ)) (s.coeff 1) * (t : ℂ) = 0 := by
        linear_combination (hplus - hminus) / 2
      exact (mul_eq_zero.mp hm).resolve_right htcomplex
    have hzero : MvPolynomial.eval (fun i => (x i : ℂ)) (s.coeff 0) = 0 := by
      simpa [hfirst] using hplus
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with rfl | rfl
    · exact hzero
    · exact hfirst
  have hs : s = 0 := by
    rw [hsform, hcoeff 1 (by simp), hcoeff 0 (by simp)]
    simp
  have hdvd : q ∣ p := (Polynomial.modByMonic_eq_zero_iff_dvd hq).mp hs
  rcases hdvd with ⟨u, hu⟩
  refine ⟨(MvPolynomial.finSuccEquiv ℂ n).symm u, ?_⟩
  apply (MvPolynomial.finSuccEquiv ℂ n).injective
  simpa [p, q] using hu

/-- Total degree is additive on nonzero complex polynomials. -/
theorem complexPolynomial_totalDegree_mul {n : ℕ} (P Q : ComplexPolynomial n)
    (hP : P ≠ 0) (hQ : Q ≠ 0) :
    (P * Q).totalDegree = P.totalDegree + Q.totalDegree := by
  rw [← MvPolynomial.degree_degLexDegree, MonomialOrder.degree_mul hP hQ,
    Finsupp.degree_add, MvPolynomial.degree_degLexDegree, MvPolynomial.degree_degLexDegree]

theorem spherePolynomial_totalDegree (n : ℕ) (r : ℝ) :
    (spherePolynomial (n + 1) r).totalDegree = 2 := by
  classical
  have hc : MvPolynomial.coeff (Finsupp.single (0 : Fin (n + 1)) 2)
      (spherePolynomial (n + 1) r) = 1 := by
    simp only [spherePolynomial, coeff_sub, coeff_sum, coeff_X_pow, coeff_C]
    simp [Finsupp.single_left_inj,
      Finsupp.single_eq_zero]
    intro h
    have he := congrArg (fun f : Fin (n + 1) →₀ ℕ => f 0) h
    norm_num at he
  apply le_antisymm
  · apply (totalDegree_sub _ _).trans
    simp only [totalDegree_C, Nat.max_zero]
    apply totalDegree_finsetSum_le
    intro i _
    exact (totalDegree_pow _ _).trans (by simp)
  · have hmem : Finsupp.single (0 : Fin (n + 1)) 2 ∈
        (spherePolynomial (n + 1) r).support := mem_support_iff.mpr (by rw [hc]; exact one_ne_zero)
    simpa using MvPolynomial.le_totalDegree hmem

/-- The sphere divisor lowers total degree by two, including the zero-polynomial case. -/
theorem exists_spherePolynomial_quotient {n : ℕ} (r : ℝ) (hr : 0 < r)
    (P : ComplexPolynomial (n + 1))
    (hP : ∀ x : Fin (n + 1) → ℝ, (∑ i, x i ^ 2) = r ^ 2 →
      MvPolynomial.eval (fun i => (x i : ℂ)) P = 0) :
    ∃ Q : ComplexPolynomial (n + 1), P = spherePolynomial (n + 1) r * Q ∧
      Q.totalDegree ≤ P.totalDegree - 2 := by
  obtain ⟨Q, hQ⟩ := spherePolynomial_dvd_of_eval_eq_zero r hr P hP
  refine ⟨Q, hQ, ?_⟩
  by_cases hzero : Q = 0
  · simp [hzero]
  · have hs : spherePolynomial (n + 1) r ≠ 0 := by
      intro h
      have := spherePolynomial_totalDegree n r
      simp [h] at this
    have hdeg := complexPolynomial_totalDegree_mul _ Q hs hzero
    rw [← hQ, spherePolynomial_totalDegree] at hdeg
    omega

/-- Euclidean-space formulation of sphere divisibility and its degree bound. -/
theorem exists_spherePolynomial_quotient_of_norm {n : ℕ} (hn : 1 ≤ n)
    (r : ℝ) (hr : 0 < r) (P : ComplexPolynomial n)
    (hP : ∀ x : RealPoint n, ‖x‖ = r → polynomialEvaluation x P = 0) :
    ∃ Q : ComplexPolynomial n, P = spherePolynomial n r * Q ∧
      Q.totalDegree ≤ P.totalDegree - 2 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  apply exists_spherePolynomial_quotient r hr P
  intro x hx
  let y : RealPoint (m + 1) := (WithLp.equiv 2 _).symm x
  have hy : ‖y‖ ^ 2 = r ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2]
    simpa [y, Real.norm_eq_abs, sq_abs] using hx
  have hynorm : ‖y‖ = r := (sq_eq_sq₀ (norm_nonneg _) hr.le).mp hy
  simpa [y] using hP y hynorm

theorem spherePolynomial_dvd_of_norm_eq_zero {n : ℕ} (hn : 1 ≤ n)
    (r : ℝ) (hr : 0 < r) (P : ComplexPolynomial n)
    (hP : ∀ x : RealPoint n, ‖x‖ = r → polynomialEvaluation x P = 0) :
    spherePolynomial n r ∣ P := by
  obtain ⟨Q, hQ, _⟩ := exists_spherePolynomial_quotient_of_norm hn r hr P hP
  exact ⟨Q, hQ⟩

end RieszEuclidean.CompleteMinimal
