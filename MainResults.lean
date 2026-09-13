import RieszEuclidean

/-!
# Implemented result statements and concrete definitions

This compact Comparator reference currently covers the foundational and affine
results only. It does not contain or certify the unfinished geometric main
theorems. Its wrapper proofs use the checked modular library, so the reference
needs neither theorem placeholders nor warning suppressions.
-/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace RieszEuclidean.Results

/-- Euclidean space in the dimension appearing in the manuscript. -/
abbrev Space (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- The paper's concrete exponential Riesz basis predicate, written out for review. -/
def HasBasis {d : ℕ} (Ω Λ : Set (Space d)) : Prop := by
  classical
  exact ∃ S : lp (fun _ : Λ => ℂ) 2 ≃L[ℂ] Lp ℂ 2 (volume.restrict Ω),
    ∀ ξ : Λ, (S (lp.single 2 ξ 1) : Space d → ℂ) =ᵐ[volume.restrict Ω]
      fun x => Complex.exp
        (2 * (Real.pi : ℂ) * Complex.I * (inner (𝕜 := ℝ) ξ.val x : ℂ))

/-- An arbitrary invertible affine image of the domain. -/
def affineImage {d : ℕ} (a : Space d) (A : Space d ≃L[ℝ] Space d)
    (Ω : Set (Space d)) : Set (Space d) := (fun x => a + A x) '' Ω

/-- Lemma 2.1 with its actual restriction-to-range definition. -/
theorem projection_gap {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (P Q : OrthProjection H) :
    ‖P.op - Q.op‖ < 1 ↔
      ∃ e : Q.range ≃L[ℂ] P.range, ∀ x : Q.range, (e x : H) = P.op x :=
  OrthProjection.gap_iff_rangeIso P Q

/-- Lemma 2.2: strict inclusion of ranges is incompatible with two gaps below one. -/
theorem strict_inclusion_obstruction {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (P Q M : OrthProjection H)
    (h : P.range < Q.range) : ¬ (‖P.op - M.op‖ < 1 ∧ ‖Q.op - M.op‖ < 1) :=
  OrthProjection.nested_not_both_gap P Q M h

/-- Beurling weak limits retain a uniform separation constant. -/
theorem weak_limit_separation {d : ℕ} {δ : ℝ}
    {Γ : ℕ → Set (Space d)} {Γ₀ : Set (Space d)}
    (h : WeaklyConverges Γ Γ₀) (hsep : ∀ j, Separated δ (Γ j)) :
    Separated δ Γ₀ := h.separated hsep

/-- Arbitrary affine transport of the concrete synthesis predicate. -/
theorem affine_invariance {d : ℕ} (a : Space d) (A : Space d ≃L[ℝ] Space d)
    (Ω : Set (Space d)) :
    (∃ Λ, HasBasis (affineImage a A Ω) Λ) ↔ ∃ Λ, HasBasis Ω Λ :=
  exists_exponentialRieszBasis_affine_iff a A Ω

end RieszEuclidean.Results
