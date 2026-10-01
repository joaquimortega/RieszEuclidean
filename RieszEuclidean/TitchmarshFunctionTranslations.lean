import RieszEuclidean.TitchmarshFourierProduct
import Mathlib.Topology.Order.Compact

/-! Translation and support normalization for compactly supported functions. -/

noncomputable section
open MeasureTheory
open scoped Convolution

namespace RieszEuclidean.CompleteMinimal

/-- Translate a function by `a`, with the convention `fₐ(x) = f(x - a)`. -/
def titchmarshTranslate {d : ℕ} (f : Euclidean d → ℂ) (a : Euclidean d) :
    Euclidean d → ℂ := fun x => f (x - a)

theorem continuous_titchmarshTranslate {d : ℕ} {f : Euclidean d → ℂ}
    (hf : Continuous f) (a : Euclidean d) : Continuous (titchmarshTranslate f a) := by
  exact hf.comp (continuous_id.sub continuous_const)

theorem hasCompactSupport_titchmarshTranslate {d : ℕ} {f : Euclidean d → ℂ}
    (hf : HasCompactSupport f) (a : Euclidean d) : HasCompactSupport (titchmarshTranslate f a) := by
  simpa [titchmarshTranslate, sub_eq_add_neg] using
    hf.comp_homeomorph (Homeomorph.addRight (-a))

/-- Translating the factors of a Lebesgue convolution translates its output by the
sum of the two translation vectors. -/
theorem convolution_titchmarshTranslate {d : ℕ}
    (f g : Euclidean d → ℂ) (a b x : Euclidean d) :
    ((titchmarshTranslate f a) ⋆[ContinuousLinearMap.mul ℂ ℂ, volume]
        (titchmarshTranslate g b)) x =
      (f ⋆[ContinuousLinearMap.mul ℂ ℂ, volume] g) (x - (a + b)) := by
  rw [MeasureTheory.convolution_def, MeasureTheory.convolution_def]
  let K : Euclidean d → ℂ := fun y => f y * g ((x - (a + b)) - y)
  calc
    (∫ y, f (y - a) * g ((x - y) - b)) = ∫ y, K (y - a) := by
      apply integral_congr_ae
      filter_upwards with y
      simp only [K]
      congr 1
      congr 1
      abel
    _ = ∫ y, K y := by
      simpa only [sub_eq_add_neg] using
        (measurePreserving_add_right volume (-a)).integral_comp
          (Homeomorph.addRight (-a)).measurableEmbedding K
    _ = ∫ y, f y * g ((x - (a + b)) - y) := rfl

/-- A nonzero compactly supported function has a point in its support where a real
linear functional attains its minimum. -/
theorem exists_minimum_on_tsupport {d : ℕ} {f : Euclidean d → ℂ}
    (hf : HasCompactSupport f) (hfne : f ≠ 0) (ℓ : Euclidean d →L[ℝ] ℝ) :
    ∃ c ∈ tsupport f, ∀ x ∈ tsupport f, ℓ c ≤ ℓ x := by
  have hcompact : IsCompact (tsupport f) := by
    simpa only [HasCompactSupport] using hf
  have hnonempty : (tsupport f).Nonempty := by
    by_contra h
    apply hfne
    funext x
    by_contra hfx
    exact h ⟨x, subset_tsupport f hfx⟩
  obtain ⟨c, hc, hmin⟩ := hcompact.exists_isMinOn hnonempty ℓ.continuous.continuousOn
  exact ⟨c, hc, hmin⟩

/-- Translating a nonzero compactly supported function by the negative of a support
minimum puts its support in the closed half-space `0 ≤ ℓ x`. -/
theorem exists_titchmarshTranslate_supported_nonnegative {d : ℕ}
    {f : Euclidean d → ℂ} (hf : HasCompactSupport f) (hfne : f ≠ 0)
    (ℓ : Euclidean d →L[ℝ] ℝ) :
    ∃ c, c ∈ tsupport f ∧
      (∀ x ∈ tsupport f, ℓ c ≤ ℓ x) ∧
      (∀ x, titchmarshTranslate f (-c) x ≠ 0 → 0 ≤ ℓ x) := by
  obtain ⟨c, hc, hmin⟩ := exists_minimum_on_tsupport hf hfne ℓ
  refine ⟨c, hc, hmin, ?_⟩
  intro x hx
  have hfx : f (x + c) ≠ 0 := by simpa [titchmarshTranslate] using hx
  have hx' : x + c ∈ tsupport f := subset_tsupport f hfx
  have hle := hmin (x + c) hx'
  have heq : ℓ (x + c) = ℓ x + ℓ c := by simp
  rw [heq] at hle
  linarith

end RieszEuclidean.CompleteMinimal
