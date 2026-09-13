import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.SpecialFunctions.Exponential

/-!
# Concrete Euclidean synthesis semantics

The Fourier convention is exp(2 π i ⟪ξ,x⟫), as in `paper/RieszEuclidean.tex`.
Mathlib's inner product is conjugate-linear in its first argument.
No lattice or quotient space is part of these definitions.
-/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace RieszEuclidean

/-- Finite-dimensional Euclidean space with its standard inner product and Lebesgue measure. -/
abbrev Euclidean (d : ℕ) := EuclideanSpace ℝ (Fin d)
/-- The coefficient Hilbert space of square-summable complex families. -/
abbrev SeqL2 (ι : Type) := lp (fun _ : ι => ℂ) 2
/-- Complex L² for Lebesgue measure restricted to the actual domain. -/
abbrev DomainL2 {d : ℕ} (Ω : Set (Euclidean d)) := Lp ℂ 2 (volume.restrict Ω)

/-- The paper's exponential with the positive 2π Fourier convention. -/
def exponential {d : ℕ} (ξ x : Euclidean d) : ℂ :=
  Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (inner (𝕜 := ℝ) ξ x : ℂ))

/-- A boundedly invertible synthesis map with its actual exponential columns. -/
def HasExponentialRieszBasis {d : ℕ} (Ω Λ : Set (Euclidean d)) : Prop := by
  classical
  exact ∃ S : SeqL2 Λ ≃L[ℂ] DomainL2 Ω,
    ∀ ξ : Λ, (S (lp.single 2 ξ 1) : Euclidean d → ℂ) =ᵐ[volume.restrict Ω]
      exponential ξ.val

/-- Configuration action T_y Γ = Γ - y. -/
def translate {d : ℕ} (y : Euclidean d) (Γ : Set (Euclidean d)) : Set (Euclidean d) :=
  {x | x + y ∈ Γ}

@[simp] theorem mem_translate {d : ℕ} (y x : Euclidean d) (Γ : Set (Euclidean d)) :
    x ∈ translate y Γ ↔ x + y ∈ Γ := Iff.rfl

@[simp] theorem translate_zero {d : ℕ} (Γ : Set (Euclidean d)) : translate 0 Γ = Γ := by
  ext x
  simp [translate]

@[simp] theorem translate_add {d : ℕ} (y z : Euclidean d) (Γ : Set (Euclidean d)) :
    translate y (translate z Γ) = translate (y + z) Γ := by
  ext x
  simp [translate, add_assoc]

/-- Uniform separation with a specified lower bound. -/
def Separated {d : ℕ} (δ : ℝ) (Γ : Set (Euclidean d)) : Prop :=
  ∀ ⦃x⦄, x ∈ Γ → ∀ ⦃y⦄, y ∈ Γ → x ≠ y → δ ≤ dist x y

/-- Beurling's local matching definition, with centers remaining in Euclidean space. -/
def WeaklyConverges {d : ℕ} (Γ : ℕ → Set (Euclidean d)) (Γ₀ : Set (Euclidean d)) : Prop :=
  ∀ R : ℝ, 0 < R → ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ j ≥ N,
    (∀ x ∈ Γ j, ‖x‖ < R → ∃ y ∈ Γ₀, dist x y < ε) ∧
    (∀ y ∈ Γ₀, ‖y‖ < R → ∃ x ∈ Γ j, dist x y < ε)

/-- An arbitrary invertible affine image of a Euclidean ball. -/
def affineBall {d : ℕ} (a : Euclidean d) (A : Euclidean d ≃L[ℝ] Euclidean d)
    (R : ℝ) : Set (Euclidean d) :=
  (fun x => a + A x) '' Metric.ball 0 R

end RieszEuclidean
