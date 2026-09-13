import RieszEuclidean.Bumps
import RieszEuclidean.FourierTranslations
import Mathlib.Analysis.InnerProductSpace.Orthonormal
open MeasureTheory
namespace RieszEuclidean
/-- Separated centres force distinct small bump translates to have disjoint supports. -/
theorem bump_translates_disjoint {d : ℕ} {δ r : ℝ} {Λ : Set (Euclidean d)}
    (hΛ : Separated δ Λ) (hr : 2 * r < δ) (b : Euclidean d → ℂ)
    (hs : ∀ ξ, r ≤ ‖ξ‖ → b ξ = 0) {i j : Λ} (hij : i ≠ j) (x : Euclidean d) :
    b (x - i) = 0 ∨ b (x - j) = 0 := by
  by_contra! h
  have hi : ‖x - i‖ < r := lt_of_not_ge (fun hn => h.1 (hs _ hn))
  have hj : ‖x - j‖ < r := lt_of_not_ge (fun hn => h.2 (hs _ hn))
  have hdist := hΛ i.property j.property (fun he => hij (Subtype.ext he))
  have ht := dist_triangle (i : Euclidean d) x (j : Euclidean d)
  rw [dist_comm (i : Euclidean d) x, dist_eq_norm x (i : Euclidean d),
    dist_eq_norm x (j : Euclidean d)] at ht
  linarith
/-- The L² translate has the expected bump representative. -/
theorem translated_bump_coe {d : ℕ} (b : SchwartzMap (Euclidean d) ℂ) (t : Euclidean d) :
    (translationL2 (-t) (b.toLp 2 volume) : Euclidean d → ℂ) =ᵐ[volume]
      fun x => b (x - t) := by
  have hae := (measurePreserving_add_right volume (-t)).quasiMeasurePreserving.ae
    (b.coeFn_toLp 2 volume)
  exact (translationL2_coe (-t) (b.toLp 2 volume)).trans (by simpa only [sub_eq_add_neg] using hae)
/-- Unit bumps around separated centres form an orthonormal family in actual Euclidean L². -/
theorem translated_bumps_orthonormal {d : ℕ} {δ r : ℝ} {Λ : Set (Euclidean d)}
    (hΛ : Separated δ Λ) (hr : 2 * r < δ) (b : SchwartzMap (Euclidean d) ℂ)
    (hs : ∀ ξ, r ≤ ‖ξ‖ → b ξ = 0) (hn : ‖b.toLp 2 volume‖ = 1) :
    Orthonormal ℂ (fun i : Λ => translationL2 (-(i : Euclidean d)) (b.toLp 2 volume)) := by
  refine ⟨fun i => by simpa only [LinearIsometry.norm_map] using hn, ?_⟩
  intro i j hij
  rw [L2.inner_def]
  apply integral_eq_zero_of_ae
  filter_upwards [translated_bump_coe b i, translated_bump_coe b j] with x hi hj
  rw [hi, hj]
  rcases bump_translates_disjoint hΛ hr b hs hij x with h | h <;> simp [h]
end RieszEuclidean
