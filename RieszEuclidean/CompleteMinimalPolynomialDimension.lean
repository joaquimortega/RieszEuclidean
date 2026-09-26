import RieszEuclidean.CompleteMinimalPolynomial
import Mathlib.Data.Finsupp.Multiset
import Mathlib.Data.Sym.Card
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition

/-! # Dimension of polynomials of bounded total degree

Adding one slack exponent identifies bounded exponent vectors in `d` variables
with homogeneous exponent vectors of degree `m` in `d + 1` variables.
The monomial basis and stars-and-bars count then give the exact dimension.
-/

noncomputable section
open scoped BigOperators

namespace RieszEuclidean.CompleteMinimal

/-- Add the unused degree as a slack coordinate, turning a degree bound into an exact sum. -/
def boundedExponentSlackEquiv (d m : ℕ) :
    {f : Fin d → ℕ // ∑ i, f i ≤ m} ≃
      {g : Fin (d + 1) → ℕ // ∑ i, g i = m} where
  toFun f := ⟨Fin.cons (m - ∑ i, f.val i) f.val, by
    rw [Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ]
    exact Nat.sub_add_cancel f.prop⟩
  invFun g := ⟨fun i => g.val i.succ, by
    change (∑ i : Fin d, g.val i.succ) ≤ m
    have h := g.prop
    rw [Fin.sum_univ_succ] at h
    omega⟩
  left_inv f := by
    apply Subtype.ext
    funext i
    rfl
  right_inv g := by
    apply Subtype.ext
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [Fin.cons_zero]
      have h := g.prop
      rw [Fin.sum_univ_succ] at h
      omega
    · rfl

/-- Bounded monomial exponents correspond to multisets of `m` letters on `d + 1` symbols. -/
def boundedMonomialEquivSym (d m : ℕ) :
    {f : Fin d →₀ ℕ // f.sum (fun _ e => e) ≤ m} ≃ Sym (Fin (d + 1)) m :=
  (Finsupp.equivFunOnFinite.subtypeEquiv (by
    intro f
    simp [Finsupp.sum_fintype])).trans ((boundedExponentSlackEquiv d m).trans
      (Sym.equivNatSumOfFintype (Fin (d + 1)) m).symm)

/-- The exact binomial dimension of complex polynomials of bounded total degree. -/
theorem finrank_restrictTotalDegree (d m : ℕ) :
    Module.finrank ℂ (MvPolynomial.restrictTotalDegree (Fin d) ℂ m) =
      Nat.choose (m + d) d := by
  classical
  let e := boundedMonomialEquivSym d m
  letI : Fintype {f : Fin d →₀ ℕ // f.sum (fun _ e => e) ≤ m} :=
    Fintype.ofEquiv (Sym (Fin (d + 1)) m) e.symm
  calc
    _ = Fintype.card {f : Fin d →₀ ℕ // f.sum (fun _ e => e) ≤ m} :=
      Module.finrank_eq_card_basis (MvPolynomial.basisRestrictSupport ℂ _)
    _ = Fintype.card (Sym (Fin (d + 1)) m) := Fintype.card_congr e
    _ = Nat.choose (m + d) d := by
      rw [Sym.card_sym_eq_choose, Fintype.card_fin]
      have h : d + 1 + m - 1 = m + d := by omega
      rw [h, Nat.choose_symm_add]

end RieszEuclidean.CompleteMinimal
