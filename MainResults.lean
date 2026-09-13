import RieszEuclidean

/-!
# Implemented result statements and concrete definitions

This compact Comparator reference covers proved foundational, Fourier, affine
and configuration-space results. It does not contain or certify the unfinished geometric main
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

/-- The concrete Euclidean Schwartz Parseval pairing underlying the L² extension. -/
theorem fourier_parseval {d : ℕ} (f g : SchwartzMap (Space d) ℂ) :
    (∫ x, Real.fourierIntegral f x * starRingEnd ℂ (Real.fourierIntegral g x)) =
      ∫ x, f x * starRingEnd ℂ (g x) := schwartz_parseval f g

/-- Existence of the actual Euclidean unitary Fourier map and its measurable-domain cutoffs. -/
theorem euclidean_fourier_cutoff (d : ℕ) :
    ∃ U : Lp ℂ 2 (volume : Measure (Euclidean d)) ≃ₗᵢ[ℂ]
        Lp ℂ 2 (volume : Measure (Euclidean d)),
      (∀ f : SchwartzMap (Euclidean d) ℂ,
        (U (f.toLp 2 volume) : Euclidean d → ℂ) =ᵐ[volume] Real.fourierIntegralInv f) ∧
      ∀ Ω : Set (Euclidean d), MeasurableSet Ω →
        ∃ P : OrthProjection (Lp ℂ 2 (volume : Measure (Euclidean d))),
          ∀ f, (U (P.op f) : Euclidean d → ℂ) =ᵐ[volume]
            Ω.indicator (U f : Euclidean d → ℂ) := by
  refine ⟨paperFourierL2 d, paperFourierL2_schwartz d, ?_⟩
  intro Ω hΩ
  refine ⟨fourierProjection Ω hΩ, ?_⟩
  intro f
  rw [fourierProjection_transform]
  exact domainCutoff_coe Ω hΩ _
/-- Schwartz functions are dense in Euclidean L². -/
theorem schwartz_density (d : ℕ) :
    DenseRange (fun f : SchwartzMap (Euclidean d) ℂ => f.toLp 2 volume) :=
  schwartz_toL2_denseRange d
/-- The complete initial Fourier construction, with integral, kernel and translation semantics. -/
theorem euclidean_fourier_analysis (d : ℕ) :
    ∃ U : Lp ℂ 2 (volume : Measure (Euclidean d)) ≃ₗᵢ[ℂ]
        Lp ℂ 2 (volume : Measure (Euclidean d)),
      (∀ f : Lp ℂ 2 (volume : Measure (Euclidean d)), Integrable (f : Euclidean d → ℂ) →
        (U f : Euclidean d → ℂ) =ᵐ[volume] Real.fourierIntegralInv f) ∧
      ∀ Ω : Set (Euclidean d), MeasurableSet Ω → volume Ω ≠ ⊤ →
        ∃ P : OrthProjection (Lp ℂ 2 (volume : Measure (Euclidean d))),
          (∀ f, (U (P.op f) : Euclidean d → ℂ) =ᵐ[volume]
            Ω.indicator (U f : Euclidean d → ℂ)) ∧
          (∀ f : Lp ℂ 2 (volume : Measure (Euclidean d)), Integrable (f : Euclidean d → ℂ) →
            (P.op f : Euclidean d → ℂ) =ᵐ[volume] fun v =>
              ∫ w, (∫ x in Ω, (Real.fourierChar (-inner (𝕜 := ℝ) x (v - w)) : ℂ)) * f w) ∧
          ∀ (t : Euclidean d) (f g : Lp ℂ 2 (volume : Measure (Euclidean d))),
            (g : Euclidean d → ℂ) =ᵐ[volume] (fun x => f (x + t)) →
            (P.op g : Euclidean d → ℂ) =ᵐ[volume] fun x => P.op f (x + t) := by
  refine ⟨paperFourierL2 d, fun f hf => paperFourierL2_eq_integral f hf, ?_⟩
  intro Ω hΩ hfin
  refine ⟨fourierProjection Ω hΩ, ?_, ?_, ?_⟩
  · intro f
    rw [fourierProjection_transform]
    exact domainCutoff_coe Ω hΩ _
  · intro f hf
    exact fourierProjection_kernel Ω hΩ hfin f hf
  · intro t f g hg
    have heq : g = translationL2 t f := Lp.ext (hg.trans (translationL2_coe t f).symm)
    rw [heq, fourierProjection_translation Ω hΩ hfin]
    exact translationL2_coe t _
/-- Every exponential Riesz basis on a bounded domain supplies the paper's small bump and initial gap. -/
theorem initial_bumps {d : ℕ} {Ω Λ : Set (Euclidean d)}
    (hΩ : MeasurableSet Ω) (hb : Bornology.IsBounded Ω)
    (hB : HasExponentialRieszBasis Ω Λ) :
    ∃ δ r : ℝ, 0 < δ ∧ Separated δ Λ ∧ 0 < r ∧ 2 * r < δ ∧
      ∃ b : SchwartzMap (Euclidean d) ℂ,
        HasCompactSupport b ∧ ‖b.toLp 2 volume‖ = 1 ∧
        (∀ ξ, (b ξ).im = 0 ∧ 0 ≤ (b ξ).re) ∧
        (∀ ξ, r ≤ ‖ξ‖ → b ξ = 0) ∧
        (∃ c : ℝ, 0 < c ∧ ∀ x ∈ Ω, c ≤ ‖Real.fourierIntegralInv b x‖) ∧
        ∃ V : SeqL2 Λ →ₗᵢ[ℂ] FullL2 d,
          (∀ i : Λ, V (lp.single 2 i 1) = translationL2 (-(i : Euclidean d)) (b.toLp 2 volume)) ∧
          ‖(fourierProjection Ω hΩ).op - (isometryRangeProjection V).op‖ < 1 :=
  exists_initial_bump_gap hΩ hb hB
/-- The separated configuration space is compact metrizable, realizes Beurling weak
convergence, and carries a jointly continuous real translation action. -/
theorem compact_configuration_space (d : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    CompactSpace (SeparatedConfiguration d δ) ∧
    TopologicalSpace.MetrizableSpace (SeparatedConfiguration d δ) ∧
    (∀ (Γ : ℕ → SeparatedConfiguration d δ) (Γ₀ : SeparatedConfiguration d δ),
      Filter.Tendsto Γ Filter.atTop (nhds Γ₀) ↔
        WeaklyConverges (fun n => (Γ n).carrier) Γ₀.carrier) ∧
    Continuous (fun p : Euclidean d × SeparatedConfiguration d δ =>
      SeparatedConfiguration.translate p.1 p.2) :=
  ⟨SeparatedConfiguration.compactSpace hδ, inferInstance,
    fun _ _ => SeparatedConfiguration.tendsto_iff_weaklyConverges hδ,
    SeparatedConfiguration.continuous_translate hδ⟩
end RieszEuclidean.Results
