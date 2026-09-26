import RieszEuclidean.CompleteMinimalQuadric

/-!
# Uniqueness of entire extensions from real Euclidean space

An affine complex line through the real and imaginary parts reduces uniqueness
to the one-variable identity theorem.
-/

noncomputable section

namespace RieszEuclidean.CompleteMinimal

/-- Entire functions on complex Euclidean space are determined by their real restriction. -/
theorem entire_eq_of_eq_on_real {d : ℕ} {F G : ComplexEuclidean d → ℂ}
    (hF : Differentiable ℂ F) (hG : Differentiable ℂ G)
    (hreal : ∀ x : Euclidean d, F (realToComplex x) = G (realToComplex x)) : F = G := by
  funext z
  let x : Euclidean d := (WithLp.equiv 2 _).symm (fun i => (z i).re)
  let y : Euclidean d := (WithLp.equiv 2 _).symm (fun i => (z i).im)
  let L : ℂ → ComplexEuclidean d := fun w => realToComplex x + w • realToComplex y
  have hL : Differentiable ℂ L :=
    (differentiable_const _).add (differentiable_id.smul_const _)
  have hdiff : Differentiable ℂ (fun w => F (L w) - G (L w)) :=
    (hF.comp hL).sub (hG.comp hL)
  have hzero : ∀ t : ℝ, F (L t) - G (L t) = 0 := by
    intro t
    have he : L t = realToComplex (x + t • y) := by
      ext i
      simp [L, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    rw [he, hreal, sub_self]
  have hz : L Complex.I = z := by
    ext i
    simp only [L, PiLp.add_apply, PiLp.smul_apply, realToComplex_apply, x, y,
      WithLp.equiv_symm_pi_apply, smul_eq_mul]
    apply Complex.ext <;> simp
  have h := entire_zero_of_real_zero _ hdiff hzero Complex.I
  rw [hz] at h
  exact sub_eq_zero.mp h

/-- The zero-function specialization of uniqueness from the real locus. -/
theorem entire_eq_zero_of_zero_on_real {d : ℕ} {F : ComplexEuclidean d → ℂ}
    (hF : Differentiable ℂ F)
    (hreal : ∀ x : Euclidean d, F (realToComplex x) = 0) : F = 0 :=
  entire_eq_of_eq_on_real hF (differentiable_const _) hreal

end RieszEuclidean.CompleteMinimal
