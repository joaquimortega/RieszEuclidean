import RieszEuclidean.CompleteMinimalBasic
import RieszEuclidean.CompleteMinimalEntireFourier
import RieszEuclidean.CompleteMinimalPolynomial
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

noncomputable section

open MeasureTheory

namespace RieszEuclidean.CompleteMinimal

/-- The forward part of a tail annihilator description. The tail theorem must
produce the bounded-degree polynomial multiplying the specified Fourier factor;
completeness of an augmented family is not part of this interface. -/
def TailPolynomialRepresentation {d : ℕ} (Ω : Set (Euclidean d))
    (hΩ : MeasurableSet Ω) (hfinite : volume Ω ≠ ⊤) (tail : Set (Euclidean d))
    (degree : ℕ) (multiplier : ComplexEuclidean d → ℂ) : Prop :=
  ∀ f : DomainL2 Ω,
    (∀ ξ ∈ tail, inner (𝕜 := ℂ) f (exponentialL2 Ω hfinite ξ) = 0) →
    ∃ p : MvPolynomial.restrictTotalDegree (Fin d) ℂ degree,
      ∀ z, domainEntireFourier Ω hΩ f z =
        multiplier z * MvPolynomial.eval (fun i => z i) p.val

/-- A finite polynomial interpolation set completes the later frequencies when
the tail annihilator has the stated Fourier-polynomial representation. -/
theorem available_exponentials_complete {d m : ℕ} (Ω : Set (Euclidean d))
    (hΩ : MeasurableSet Ω) (hbounded : Bornology.IsBounded Ω)
    (hfinite : volume Ω ≠ ⊤) (A : Finset (Euclidean d)) (tail : Set (Euclidean d))
    (multiplier : ComplexEuclidean d → ℂ)
    (htail : TailPolynomialRepresentation Ω hΩ hfinite tail (2 * m) multiplier)
    (hA : Function.Bijective (boundedSampling (2 * m) (fun x : ↥A => x.val)))
    (hmultiplier : ∀ ξ ∈ A, multiplier (realToComplex ξ) ≠ 0) :
    IsCompleteExponential Ω hfinite ((A : Set (Euclidean d)) ∪ tail) := by
  apply (isCompleteExponential_iff_annihilator Ω hfinite _).mpr
  intro f hf
  obtain ⟨p, hp⟩ := htail f (fun ξ hξ => hf ⟨ξ, Or.inr hξ⟩)
  have hsample : boundedSampling (2 * m) (fun x : ↥A => x.val) p = 0 := by
    ext ξ
    have horth : inner (𝕜 := ℂ) (exponentialL2 Ω hfinite ξ.val) f = 0 :=
      (inner_eq_zero_symm (𝕜 := ℂ)).mp (hf ⟨ξ.val, Or.inl ξ.property⟩)
    have hprod : multiplier (realToComplex ξ.val) *
        polynomialEvaluation ξ.val p.val = 0 := by
      rw [← domainEntireFourier_real_inner hΩ hfinite] at horth
      simpa only [hp, realToComplex_apply, polynomialEvaluation_apply] using horth
    exact (mul_eq_zero.mp hprod).resolve_left (hmultiplier ξ.val ξ.property)
  have hpzero : p = 0 := hA.1 (hsample.trans (map_zero _).symm)
  apply domainEntireFourier_injective hΩ hbounded
  funext z
  rw [hp]
  simp only [hpzero, ZeroMemClass.coe_zero, map_zero, mul_zero]
  exact (congrFun (domainEntireFourierLinear Ω hΩ hbounded).map_zero z).symm

/-- Membership in the span of an indexed set only uses finitely many indices. -/
theorem mem_span_image_finite {H X : Type*} [AddCommGroup H] [Module ℂ H]
    (e : X → H) (available : Set X) {v : H}
    (hv : v ∈ Submodule.span ℂ (e '' available)) :
    ∃ B : Finset X, (B : Set X) ⊆ available ∧
      v ∈ Submodule.span ℂ (e '' (B : Set X)) := by
  classical
  obtain ⟨B, hB, c, hc⟩ := (Submodule.mem_span_image_iff_exists_fun ℂ).mp hv
  refine ⟨B, hB, ?_⟩
  rw [← hc]
  apply Submodule.sum_mem
  intro x _
  apply Submodule.smul_mem
  exact Submodule.subset_span ⟨x.val, x.property, rfl⟩

/-- Completeness gives a finite span approximating one target. -/
theorem finite_span_approximates_target {H X : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (e : X → H) (available : Set X)
    (hcomplete : IsComplete (fun ξ : available => e ξ.val)) (f : H) (ε : ℝ)
    (hε : 0 < ε) :
    ∃ B : Finset X, (B : Set X) ⊆ available ∧
      ∃ v ∈ Submodule.span ℂ (e '' (B : Set X)), dist f v < ε := by
  have hrange : Set.range (fun ξ : available => e ξ.val) = e '' available := by
    ext v
    simp
  have hf : f ∈ (Submodule.span ℂ (e '' available)).topologicalClosure := by
    change (Submodule.span ℂ (Set.range (fun ξ : available => e ξ.val))).topologicalClosure =
      ⊤ at hcomplete
    rw [hrange] at hcomplete
    rw [hcomplete]
    trivial
  change f ∈ closure (Submodule.span ℂ (e '' available) : Set H) at hf
  obtain ⟨v, hv, hdist⟩ := Metric.mem_closure_iff.mp hf ε hε
  obtain ⟨B, hB, hvB⟩ := mem_span_image_finite e available hv
  exact ⟨B, hB, v, hvB, hdist⟩

/-- One finite subset of a complete family approximates every member of a finite
set of targets, with any prescribed positive error. -/
theorem finite_span_approximates_finite_targets {H X : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (e : X → H) (available : Set X)
    (hcomplete : IsComplete (fun ξ : available => e ξ.val)) (targets : Finset H)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ B : Finset X, (B : Set X) ⊆ available ∧
      ∀ f ∈ targets, ∃ v ∈ Submodule.span ℂ (e '' (B : Set X)), dist f v < ε := by
  classical
  induction targets using Finset.induction_on with
  | empty => exact ⟨∅, by simp, by simp⟩
  | @insert f targets _ ih =>
    obtain ⟨B, hB, v, hvB, hdist⟩ :=
      finite_span_approximates_target e available hcomplete f ε hε
    obtain ⟨C, hC, htargets⟩ := ih
    refine ⟨B ∪ C, ?_, ?_⟩
    · simpa only [Finset.coe_union] using Set.union_subset hB hC
    · intro g hg
      rcases Finset.mem_insert.mp hg with rfl | hg
      · exact ⟨v, Submodule.span_mono (Set.image_mono (by
          simpa only [Finset.coe_union] using (Set.subset_union_left :
            (B : Set X) ⊆ (B : Set X) ∪ (C : Set X)))) hvB, hdist⟩
      · obtain ⟨w, hw, hwε⟩ := htargets g hg
        exact ⟨w, Submodule.span_mono (Set.image_mono (by
          simpa only [Finset.coe_union] using (Set.subset_union_right :
            (C : Set X) ⊆ (B : Set X) ∪ (C : Set X)))) hw, hwε⟩

/-- Available actual exponentials approximate any finite collection of domain
L² targets using finitely many available frequencies. -/
theorem available_exponentials_approximate_finite_targets {d m : ℕ}
    (Ω : Set (Euclidean d)) (hΩ : MeasurableSet Ω) (hbounded : Bornology.IsBounded Ω)
    (hfinite : volume Ω ≠ ⊤) (A : Finset (Euclidean d)) (tail : Set (Euclidean d))
    (multiplier : ComplexEuclidean d → ℂ)
    (htail : TailPolynomialRepresentation Ω hΩ hfinite tail (2 * m) multiplier)
    (hA : Function.Bijective (boundedSampling (2 * m) (fun x : ↥A => x.val)))
    (hmultiplier : ∀ ξ ∈ A, multiplier (realToComplex ξ) ≠ 0)
    (targets : Finset (DomainL2 Ω)) (ε : ℝ) (hε : 0 < ε) :
    ∃ B : Finset (Euclidean d), (B : Set (Euclidean d)) ⊆ (A : Set (Euclidean d)) ∪ tail ∧
      ∀ f ∈ targets, ∃ v ∈ Submodule.span ℂ
        (exponentialL2 Ω hfinite '' (B : Set (Euclidean d))), dist f v < ε := by
  apply finite_span_approximates_finite_targets (exponentialL2 Ω hfinite) _
    (available_exponentials_complete Ω hΩ hbounded hfinite A tail multiplier htail hA
      hmultiplier) targets ε hε

end RieszEuclidean.CompleteMinimal
