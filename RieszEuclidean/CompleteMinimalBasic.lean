import RieszEuclidean.Affine
import Mathlib.Analysis.InnerProductSpace.Projection
import Mathlib.Tactic.FunProp

/-!
# Complete and minimal families of actual domain exponentials

Completeness and minimality refer to the topological closure of the complex
linear span. In the biorthogonality convention below the test vector occurs
in the first argument, because Mathlib's inner product is linear in its second
argument. No bound on the norms of the biorthogonal vectors is imposed.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace RieszEuclidean.CompleteMinimal

section Hilbert

variable {ι H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The closed complex linear span of a family. -/
def closedSpan (v : ι → H) : Submodule ℂ H :=
  (Submodule.span ℂ (Set.range v)).topologicalClosure

/-- Completeness means density of the complex linear span. -/
def IsComplete (v : ι → H) : Prop := closedSpan v = ⊤

/-- Ordinary minimality: every vector lies outside the closed span of the others. -/
def IsMinimal (v : ι → H) : Prop :=
  ∀ i, v i ∉ (Submodule.span ℂ (v '' {j | j ≠ i})).topologicalClosure

/-- Biorthogonality, with the linear argument of the inner product on the right. -/
def IsBiorthogonal (v w : ι → H) : Prop := by
  classical
  exact ∀ i j, inner (𝕜 := ℂ) (w i) (v j) = if i = j then 1 else 0

/-- A continuous inner-product functional that vanishes on the generators
vanishes on their closed span. -/
theorem inner_zero_on_closedSpan {v : ι → H} {w : H}
    (h : ∀ i, inner (𝕜 := ℂ) w (v i) = 0) {u : H}
    (hu : u ∈ closedSpan v) : inner (𝕜 := ℂ) w u = 0 := by
  have hs : Submodule.span ℂ (Set.range v) ≤ LinearMap.ker (innerSL ℂ w) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact h i
  exact (Submodule.topologicalClosure_minimal _ hs
    (ContinuousLinearMap.isClosed_ker (innerSL ℂ w))) hu

/-- Existence of individual biorthogonal vectors proves ordinary minimality. -/
theorem IsBiorthogonal.isMinimal {v w : ι → H} (h : IsBiorthogonal v w) :
    IsMinimal v := by
  classical
  intro i hi
  have hs : Submodule.span ℂ (v '' {j | j ≠ i}) ≤ LinearMap.ker (innerSL ℂ (w i)) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨j, hj, rfl⟩
    change inner (𝕜 := ℂ) (w i) (v j) = 0
    simpa [IsBiorthogonal, hj, Ne.symm hj] using h i j
  have hz : inner (𝕜 := ℂ) (w i) (v i) = 0 :=
    (Submodule.topologicalClosure_minimal _ hs
      (ContinuousLinearMap.isClosed_ker (innerSL ℂ (w i)))) hi
  have hone : inner (𝕜 := ℂ) (w i) (v i) = 1 := by simpa using h i i
  exact one_ne_zero (hone.symm.trans hz)

/-- A family is complete exactly when its orthogonal annihilator is zero. -/
theorem isComplete_iff_annihilator [CompleteSpace H] (v : ι → H) :
    IsComplete v ↔ ∀ w : H, (∀ i, inner (𝕜 := ℂ) w (v i) = 0) → w = 0 := by
  constructor
  · intro hv w hw
    apply (inner_self_eq_zero (𝕜 := ℂ)).mp
    apply inner_zero_on_closedSpan hw
    change closedSpan v = ⊤ at hv
    rw [hv]
    trivial
  · intro hv
    apply (Submodule.topologicalClosure_eq_top_iff
      (K := Submodule.span ℂ (Set.range v))).mpr
    apply (Submodule.eq_bot_iff _).mpr
    intro w hw
    apply hv w
    intro i
    exact (Submodule.mem_orthogonal' _ _).mp hw (v i)
      (Submodule.subset_span (Set.mem_range_self i))

/-- On a complete family the individual biorthogonal vectors are unique. -/
theorem IsComplete.biorthogonal_unique [CompleteSpace H] {v w z : ι → H}
    (hv : IsComplete v) (hw : IsBiorthogonal v w) (hz : IsBiorthogonal v z) : w = z := by
  funext i
  apply sub_eq_zero.mp
  apply (isComplete_iff_annihilator v).mp hv
  intro j
  rw [inner_sub_left, hw i j, hz i j, sub_self]

end Hilbert

section Exponentials

variable {d : ℕ}

/-- Every real-frequency exponential is continuous on physical Euclidean space. -/
theorem continuous_exponential (ξ : Euclidean d) : Continuous (exponential ξ) := by
  unfold exponential
  fun_prop

/-- Finite volume suffices for a real-frequency exponential to belong to L². -/
theorem exponential_memLp (Ω : Set (Euclidean d)) (hfinite : volume Ω ≠ ⊤)
    (ξ : Euclidean d) : MemLp (exponential ξ) 2 (volume.restrict Ω) := by
  haveI : IsFiniteMeasure (volume.restrict Ω) := ⟨by simpa using hfinite.lt_top⟩
  apply MemLp.of_bound (continuous_exponential ξ).aestronglyMeasurable 1
  exact Filter.Eventually.of_forall fun x => (exponential_norm ξ x).le

/-- In particular, every bounded measurable domain has actual L² exponential vectors.
Measurability of the domain is unnecessary for this integrability assertion. -/
theorem exponential_memLp_of_bounded (Ω : Set (Euclidean d))
    (hbounded : Bornology.IsBounded Ω) (ξ : Euclidean d) :
    MemLp (exponential ξ) 2 (volume.restrict Ω) :=
  exponential_memLp Ω hbounded.measure_lt_top.ne ξ

/-- The actual L² class of the real exponential on a finite-volume domain. -/
def exponentialL2 (Ω : Set (Euclidean d)) (hfinite : volume Ω ≠ ⊤)
    (ξ : Euclidean d) : DomainL2 Ω :=
  (exponential_memLp Ω hfinite ξ).toLp (exponential ξ)

/-- The L² class agrees almost everywhere with the paper's positive Fourier exponential. -/
theorem exponentialL2_ae (Ω : Set (Euclidean d)) (hfinite : volume Ω ≠ ⊤)
    (ξ : Euclidean d) :
    (exponentialL2 Ω hfinite ξ : Euclidean d → ℂ) =ᵐ[volume.restrict Ω] exponential ξ :=
  (exponential_memLp Ω hfinite ξ).coeFn_toLp

/-- The domain inner product against an exponential is its actual set integral.
The conjugation records Mathlib's convention explicitly. -/
theorem inner_exponentialL2 (Ω : Set (Euclidean d)) (hfinite : volume Ω ≠ ⊤)
    (ξ : Euclidean d) (f : DomainL2 Ω) :
    inner (𝕜 := ℂ) f (exponentialL2 Ω hfinite ξ) =
      ∫ x in Ω, exponential ξ x * star (f x) := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [exponentialL2_ae Ω hfinite ξ] with x hx
  rw [hx]
  simp

/-- With the exponential in the first argument the integral has negative Fourier phase. -/
theorem exponentialL2_inner (Ω : Set (Euclidean d)) (hfinite : volume Ω ≠ ⊤)
    (ξ : Euclidean d) (f : DomainL2 Ω) :
    inner (𝕜 := ℂ) (exponentialL2 Ω hfinite ξ) f =
      ∫ x in Ω, f x * star (exponential ξ x) := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [exponentialL2_ae Ω hfinite ξ] with x hx
  rw [hx]
  simp

/-- The frequency set itself indexes the family, so every frequency occurs once. -/
def exponentialFamily (Ω : Set (Euclidean d)) (hfinite : volume Ω ≠ ⊤)
    (Λ : Set (Euclidean d)) : Λ → DomainL2 Ω :=
  fun ξ => exponentialL2 Ω hfinite ξ.val

/-- Completeness of actual domain exponentials. -/
def IsCompleteExponential (Ω : Set (Euclidean d)) (hfinite : volume Ω ≠ ⊤)
    (Λ : Set (Euclidean d)) : Prop :=
  IsComplete (exponentialFamily Ω hfinite Λ)

/-- Minimality of actual domain exponentials. -/
def IsMinimalExponential (Ω : Set (Euclidean d)) (hfinite : volume Ω ≠ ⊤)
    (Λ : Set (Euclidean d)) : Prop :=
  IsMinimal (exponentialFamily Ω hfinite Λ)

/-- A domain L² vector is supported on a physical subset up to a null set. -/
def SupportedOn (Ω : Set (Euclidean d)) (f : DomainL2 Ω)
    (A : Set (Euclidean d)) : Prop :=
  ∀ᵐ x ∂volume.restrict Ω, x ∉ A → f x = 0

/-- Every domain vector is supported in its measurable physical domain. -/
theorem supportedOn_domain (Ω : Set (Euclidean d)) (hΩ : MeasurableSet Ω)
    (f : DomainL2 Ω) : SupportedOn Ω f Ω := by
  filter_upwards [ae_restrict_mem hΩ] with x hx
  exact fun hn => (hn hx).elim

/-- The a.e. support definition agrees with the indicator formulation. -/
theorem supportedOn_iff_indicator (Ω A : Set (Euclidean d)) (f : DomainL2 Ω) :
    SupportedOn Ω f A ↔ A.indicator (fun x => f x) =ᵐ[volume.restrict Ω] f := by
  classical
  constructor
  · intro h
    filter_upwards [h] with x hx
    by_cases hA : x ∈ A
    · simp [hA]
    · simp [hA, hx hA]
  · intro h
    filter_upwards [h] with x hx
    intro hA
    simpa [hA] using hx.symm

/-- Support on the empty set forces the domain L² vector to be zero. -/
theorem supportedOn_empty_iff (Ω : Set (Euclidean d)) (f : DomainL2 Ω) :
    SupportedOn Ω f ∅ ↔ f = 0 := by
  rw [supportedOn_iff_indicator]
  simp only [Set.indicator_empty, Pi.zero_apply]
  constructor
  · intro h
    apply Lp.ext
    exact h.symm.trans (Lp.coeFn_zero _ _ _).symm
  · rintro rfl
    exact (Lp.coeFn_zero _ _ _).symm

/-- A larger physical support set also supports the vector. -/
theorem SupportedOn.mono {Ω A B : Set (Euclidean d)} {f : DomainL2 Ω}
    (hf : SupportedOn Ω f A) (hAB : A ⊆ B) : SupportedOn Ω f B := by
  filter_upwards [hf] with x hx
  exact fun hB => hx (fun hA => hB (hAB hA))

/-- Completeness is equivalent to absence of a nonzero orthogonal domain L² function. -/
theorem isCompleteExponential_iff_annihilator (Ω : Set (Euclidean d))
    (hfinite : volume Ω ≠ ⊤) (Λ : Set (Euclidean d)) :
    IsCompleteExponential Ω hfinite Λ ↔
      ∀ f : DomainL2 Ω,
        (∀ ξ : Λ, inner (𝕜 := ℂ) f (exponentialL2 Ω hfinite ξ.val) = 0) → f = 0 :=
  isComplete_iff_annihilator (exponentialFamily Ω hfinite Λ)

/-- Individual domain L² biorthogonals prove minimality of the exponential system. -/
theorem biorthogonal_exponentials_minimal (Ω : Set (Euclidean d))
    (hfinite : volume Ω ≠ ⊤) (Λ : Set (Euclidean d)) (g : Λ → DomainL2 Ω)
    (hg : IsBiorthogonal (exponentialFamily Ω hfinite Λ) g) :
    IsMinimalExponential Ω hfinite Λ :=
  hg.isMinimal

end Exponentials

end RieszEuclidean.CompleteMinimal
