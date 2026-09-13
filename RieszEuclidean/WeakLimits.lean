import RieszEuclidean.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Abel

/-! Elementary facts about Beurling weak limits. Hull compactness and the
invariant probability measure remain separate blueprint obligations. -/
noncomputable section
namespace RieszEuclidean

variable {d : ℕ}

theorem Separated.translate {δ : ℝ} {Γ : Set (Euclidean d)}
    (h : Separated δ Γ) (z : Euclidean d) : Separated δ (translate z Γ) := by
  intro x hx y hy hxy
  have hne : x + z ≠ y + z := fun heq => hxy (add_right_cancel heq)
  simpa only [dist_add_right] using h hx hy hne

/-- Constant sequences converge in the actual local matching definition. -/
theorem weaklyConverges_const (Γ : Set (Euclidean d)) :
    WeaklyConverges (fun _ => Γ) Γ := by
  intro R hR ε hε
  refine ⟨0, fun j hj => ⟨?_, ?_⟩⟩
  · intro x hx _
    exact ⟨x, hx, by simpa using hε⟩
  · intro x hx _
    exact ⟨x, hx, by simpa using hε⟩

/-- Fixed translations preserve Beurling weak convergence. -/
theorem WeaklyConverges.translate {Γ : ℕ → Set (Euclidean d)}
    {Γ₀ : Set (Euclidean d)} (h : WeaklyConverges Γ Γ₀) (z : Euclidean d) :
    WeaklyConverges (fun j => translate z (Γ j)) (translate z Γ₀) := by
  intro R hR ε hε
  obtain ⟨N, hN⟩ := h (R + ‖z‖) (by positivity) ε hε
  refine ⟨N, fun j hj => ⟨?_, ?_⟩⟩
  · intro x hx hxR
    have hxz : ‖x + z‖ < R + ‖z‖ := (norm_add_le x z).trans_lt (by linarith)
    obtain ⟨y, hy, hxy⟩ := (hN j hj).1 (x + z) hx hxz
    refine ⟨y - z, ?_, ?_⟩
    · simpa [translate] using hy
    · simpa only [dist_eq_norm, show x - (y - z) = x + z - y by abel] using hxy
  · intro y hy hyR
    have hyz : ‖y + z‖ < R + ‖z‖ := (norm_add_le y z).trans_lt (by linarith)
    obtain ⟨x, hx, hxy⟩ := (hN j hj).2 (y + z) hy hyz
    refine ⟨x - z, ?_, ?_⟩
    · simpa [translate] using hx
    · simpa only [dist_eq_norm, show x - z - y = x - (y + z) by abel] using hxy

/-- The common separation constant is retained by a weak limit. -/
theorem WeaklyConverges.separated {δ : ℝ} {Γ : ℕ → Set (Euclidean d)}
    {Γ₀ : Set (Euclidean d)} (h : WeaklyConverges Γ Γ₀)
    (hsep : ∀ j, Separated δ (Γ j)) : Separated δ Γ₀ := by
  intro x hx y hy hxy
  by_contra hbad
  have hlt : dist x y < δ := lt_of_not_ge hbad
  have hdist : 0 < dist x y := dist_pos.mpr hxy
  let ε : ℝ := min (dist x y / 4) ((δ - dist x y) / 4)
  have hε : 0 < ε := lt_min (by positivity) (by linarith)
  have hε₁ : ε ≤ dist x y / 4 := min_le_left _ _
  have hε₂ : ε ≤ (δ - dist x y) / 4 := min_le_right _ _
  let R : ℝ := max ‖x‖ ‖y‖ + 1
  have hR : 0 < R := by dsimp [R]; linarith [le_max_left ‖x‖ ‖y‖, norm_nonneg x]
  have hxR : ‖x‖ < R := by dsimp [R]; linarith [le_max_left ‖x‖ ‖y‖]
  have hyR : ‖y‖ < R := by dsimp [R]; linarith [le_max_right ‖x‖ ‖y‖]
  obtain ⟨N, hN⟩ := h R hR ε hε
  obtain ⟨a, ha, hax⟩ := (hN N le_rfl).2 x hx hxR
  obtain ⟨b, hb, hby⟩ := (hN N le_rfl).2 y hy hyR
  have hab : a ≠ b := by
    intro heq
    subst b
    have ht := dist_triangle x a y
    rw [dist_comm x a] at ht
    linarith
  have hs := hsep N ha hb hab
  have ht₁ := dist_triangle a x b
  have ht₂ := dist_triangle x y b
  rw [dist_comm y b] at ht₂
  linarith

end RieszEuclidean
