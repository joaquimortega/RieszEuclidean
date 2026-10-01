import Mathlib.Data.Finsupp.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Archimedean
import Mathlib.Logic.Function.Iterate
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The algebraic Titchmarsh bootstrap

This extracts the Mikusiński–Yosida–Masuda argument from the analytic half lemma.
`V a t` says that `a` vanishes below the level `t`; the intended multiplication is
convolution, and `M` multiplies a function by a fixed real linear coordinate.
-/

noncomputable section

namespace RieszEuclidean.TitchmarshBootstrap

variable {A : Type*} [NonUnitalCommRing A]

/-- Algebraic and support properties needed to bootstrap the self-convolution
half lemma to the full convolution theorem. -/
structure Data (A : Type*) [NonUnitalCommRing A] where
  /-- Multiplication by the chosen physical coordinate. -/
  M : A → A
  /-- Vanishing below the indicated support level. -/
  V : A → ℝ → Prop
  V_zero : ∀ a, V a 0
  V_mono : ∀ {a s t}, V a t → s ≤ t → V a s
  V_closed : ∀ {a t}, (∀ s < t, V a s) → V a t
  V_add : ∀ {a b t}, V a t → V b t → V (a + b) t
  V_neg : ∀ {a t}, V a t → V (-a) t
  V_mul : ∀ {a b s t}, V a s → V b t → V (a * b) (s + t)
  V_M : ∀ {a t}, V a t → V (M a) t
  M_mul : ∀ a b, M (a * b) = M a * b + a * M b
  half : ∀ {a t}, 0 ≤ t → V (a * a) (2 * t) → V a t

namespace Data

variable (D : Data A)

private def Good (α : ℝ) : Prop :=
  ∀ (f g : A) (T : ℝ), 0 ≤ T → D.V (f * g) T → D.V (f * D.M g) (α * T)

private theorem good_zero : D.Good 0 := by
  intro f g T hT hfg
  simpa using D.V_zero (f * D.M g)

private def GoodSet : Set ℝ := {α | 0 ≤ α ∧ α ≤ 1 ∧ D.Good α}

private theorem goodSet_nonempty : D.GoodSet.Nonempty :=
  ⟨0, ⟨le_refl _, zero_le_one, D.good_zero⟩⟩

private theorem goodSet_bddAbove : BddAbove D.GoodSet :=
  ⟨1, fun _ h => h.2.1⟩

private theorem good_improve {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    (hα : D.Good α) : D.Good ((1 + α ^ 2) / 2) := by
  intro f g T hT hfg
  let h := f * D.M g
  have hh : D.V h (α * T) := hα f g T hT hfg
  have hD : D.V (D.M (f * g)) T := D.V_M hfg
  have hprod : D.V (h * D.M (f * g)) (α * T + T) := D.V_mul hh hD
  have hMfg : D.V (D.M f * g) (α * T) := by
    simpa only [mul_comm] using hα g f T hT (by simpa only [mul_comm] using hfg)
  have hMfMg : D.V (D.M f * D.M g) (α * (α * T)) :=
    hα (D.M f) g (α * T) (mul_nonneg hα0 hT) hMfg
  have hfirst : D.V ((f * g) * (D.M f * D.M g))
      (T + α * (α * T)) := D.V_mul hfg hMfMg
  have hprod' : D.V (h * D.M (f * g)) (T + α * (α * T)) := by
    apply D.V_mono hprod
    nlinarith [mul_nonneg (sub_nonneg.mpr hα1) (mul_nonneg hα0 hT)]
  have hself : D.V (h * h) (T + α * (α * T)) := by
    have heq : h * h = h * D.M (f * g) + -((f * g) * (D.M f * D.M g)) := by
      dsimp [h]
      rw [D.M_mul]
      simp only [mul_add, mul_neg, neg_mul, mul_assoc, mul_comm, mul_left_comm,
        add_assoc, add_comm, add_left_comm]
      abel
    rw [heq]
    exact D.V_add hprod' (D.V_neg hfirst)
  have hhalf : D.V h (((1 + α ^ 2) / 2) * T) := by
    apply D.half (mul_nonneg (by nlinarith [sq_nonneg α]) hT)
    convert hself using 1
    ring
  exact hhalf

/-- Vanishing of a convolution below `T` persists after multiplying its second
factor by the coordinate. This is the algebraic heart of Titchmarsh's theorem. -/
theorem multiplier_stability (f g : A) {T : ℝ} (hT : 0 ≤ T)
    (hfg : D.V (f * g) T) : D.V (f * D.M g) T := by
  let α : ℝ := sSup D.GoodSet
  have hα0 : 0 ≤ α := le_csSup D.goodSet_bddAbove
    ⟨le_refl _, zero_le_one, D.good_zero⟩
  have hα1 : α ≤ 1 := csSup_le D.goodSet_nonempty (fun _ h => h.2.1)
  have hαgood : D.Good α := by
    intro p q S hS hpq
    apply D.V_closed
    intro s hs
    by_cases hS0 : S = 0
    · subst S
      have hs0 : s < 0 := by simpa using hs
      exact D.V_mono (D.V_zero _) (le_of_lt hs0)
    · have hSpos : 0 < S := lt_of_le_of_ne hS (Ne.symm hS0)
      have hratio : s / S < α := (div_lt_iff₀ hSpos).mpr (by simpa [α] using hs)
      obtain ⟨β, hβ, hlt⟩ := exists_lt_of_lt_csSup D.goodSet_nonempty hratio
      have hβS : s ≤ β * S := by
        exact le_of_lt ((div_lt_iff₀ hSpos).mp hlt)
      exact D.V_mono (hβ.2.2 p q S hS hpq) hβS
  have hαimp : D.Good ((1 + α ^ 2) / 2) := D.good_improve hα0 hα1 hαgood
  have hβ0 : 0 ≤ (1 + α ^ 2) / 2 := by positivity
  have hβ1 : (1 + α ^ 2) / 2 ≤ 1 := by nlinarith [sq_nonneg (1 - α)]
  have hβle : (1 + α ^ 2) / 2 ≤ α :=
    le_csSup D.goodSet_bddAbove ⟨hβ0, hβ1, hαimp⟩
  have hαeq : α = 1 := by nlinarith [sq_nonneg (1 - α)]
  simpa [Good, hαeq] using hαgood f g T hT hfg

/-- Vanishing is preserved by every iterate of the coordinate multiplier. -/
theorem iterate_multiplier_stability (f g : A) (n : ℕ) {T : ℝ}
    (hT : 0 ≤ T) (hfg : D.V (f * g) T) :
    D.V (f * D.M^[n] g) T := by
  induction n with
  | zero => simpa using hfg
  | succ n ih =>
      simpa only [Function.iterate_succ_apply'] using
        D.multiplier_stability f (D.M^[n] g) hT ih

private theorem V_int_smul {a : A} {t : ℝ} (ha : D.V a t) (z : ℤ) :
    D.V (z • a) t := by
  induction z using Int.induction_on with
  | hz =>
      have hz : D.V (a + -a) t := D.V_add ha (D.V_neg ha)
      simpa using hz
  | hp z ih =>
      have hz : D.V ((z : ℤ) • a + a) t := D.V_add ih ha
      simpa [add_zsmul] using hz
  | hn z ih =>
      have hz : D.V ((-(z : ℤ)) • a + -a) t := D.V_add ih (D.V_neg ha)
      simpa [sub_zsmul] using hz

/-- A finite integer linear combination of iterated multipliers applied to the
second factor retains the same vanishing level. -/
def polynomialCombination (p : ℕ →₀ ℤ) (f g : A) : A :=
  ∑ n ∈ p.support, p n • (f * D.M^[n] g)

theorem polynomial_combination_stability (p : ℕ →₀ ℤ) (f g : A)
    {T : ℝ} (hT : 0 ≤ T) (hfg : D.V (f * g) T) :
    D.V (Data.polynomialCombination D p f g) T := by
  change D.V (∑ n ∈ p.support, p n • (f * D.M^[n] g)) T
  have hzero : D.V (0 : A) T := by
    have hz := D.V_add hfg (D.V_neg hfg)
    simpa using hz
  induction p.support using Finset.induction_on with
  | empty => simpa using hzero
  | @insert n s hn ih =>
      rw [Finset.sum_insert hn]
      apply D.V_add
      · exact D.V_int_smul
          (D.iterate_multiplier_stability f g n hT hfg) (p n)
      · exact ih

end Data

/-- Apply a finite sequence of coordinate multipliers, from left to right. -/
def multiplierWord {ι : Type*} (D : ι → Data A) (word : List ι) (g : A) : A :=
  word.foldr (fun i a => (D i).M a) g

/-- If all indexed data use the same vanishing predicate, any finite sequence
of their multipliers preserves the vanishing level of a convolution. -/
theorem multivariate_multiplier_stability {ι : Type*} (D : ι → Data A)
    (V : A → ℝ → Prop) (hV : ∀ i, (D i).V = V) (word : List ι)
    (f g : A) {T : ℝ} (hT : 0 ≤ T) (hfg : V (f * g) T) :
    V (f * multiplierWord D word g) T := by
  induction word with
  | nil => simpa [multiplierWord] using hfg
  | cons i rest ih =>
      have htail : (D i).V (f * multiplierWord D rest g) T := by
        rw [hV i]
        exact ih
      have hresult := (D i).multiplier_stability f
        (multiplierWord D rest g) hT htail
      simpa [multiplierWord, hV i] using hresult

/-- A finite scalar combination of coordinate monomials applied to `g`. -/
def scalarPolynomial {ι S : Type*} [Semiring S] [Module S A]
    (D : ι → Data A)
    (p : List ι →₀ S) (g : A) : A :=
  ∑ word ∈ p.support, p word • multiplierWord D word g

/-- Finite scalar combinations of coordinate monomials preserve vanishing.
The scalar action is assumed to preserve `V`, and to commute with convolution
in its second factor. -/
theorem scalar_combination_stability {ι S : Type*} [DecidableEq ι]
    [Semiring S] [Module S A]
    (D : ι → Data A) (V : A → ℝ → Prop) (hV : ∀ i, (D i).V = V)
    (p : List ι →₀ S) (f g : A) {T : ℝ} (hT : 0 ≤ T)
    (hfg : V (f * g) T)
    (hVadd : ∀ {a b t}, V a t → V b t → V (a + b) t)
    (hVneg : ∀ {a t}, V a t → V (-a) t)
    (hscalar : ∀ {a t}, V a t → ∀ c : S, V (c • a) t)
    (hcompat : ∀ c : S, ∀ a b : A, a * (c • b) = c • (a * b)) :
    V (f * scalarPolynomial D p g) T := by
  have hzero : V (0 : A) T := by
    have hz := hVadd hfg (hVneg hfg)
    simpa using hz
  have hsum : ∀ s : Finset (List ι),
      (∀ word ∈ s, V (p word • (f * multiplierWord D word g)) T) →
      V (∑ word ∈ s, p word • (f * multiplierWord D word g)) T := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        intro _
        simpa using hzero
    | @insert word s hword ih =>
        intro hterms
        rw [Finset.sum_insert hword]
        apply hVadd
        · exact hterms word (by simp)
        · apply ih
          intro w hw
          exact hterms w (by simp [hw])
  have hterms : ∀ word ∈ p.support,
      V (p word • (f * multiplierWord D word g)) T := by
    intro word _
    apply hscalar
    exact multivariate_multiplier_stability D V hV word f g hT hfg
  have hsum' := hsum p.support hterms
  have heq : f * scalarPolynomial D p g =
      ∑ word ∈ p.support, p word • (f * multiplierWord D word g) := by
    unfold scalarPolynomial
    induction p.support using Finset.induction_on with
    | empty => simp
    | @insert word s hword ih =>
        rw [Finset.sum_insert hword, Finset.sum_insert hword, mul_add,
          hcompat, ih]
  rw [heq]
  exact hsum'

end RieszEuclidean.TitchmarshBootstrap
