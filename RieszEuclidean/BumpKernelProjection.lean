import RieszEuclidean.BumpKernel
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

open MeasureTheory

namespace RieszEuclidean

/-- An active bump at the second coordinate also determines the whole kernel. -/
theorem bumpKernel_eq_single_right {d : ℕ} {δ r : ℝ} {Γ : Set (Euclidean d)}
    (hΓ : Separated δ Γ) (hr : 2 * r ≤ δ) (b : Euclidean d → ℂ)
    (hs : ∀ x, r ≤ ‖x‖ → b x = 0) (v : Euclidean d) {w : Euclidean d}
    (i : Γ) (hi : b (w - i) ≠ 0) :
    bumpKernel Γ b v w = b (v - i) * star (b (w - i)) := by
  rw [bumpKernel_hermitian Γ b w v, bumpKernel_eq_single hΓ hr b hs v i hi]
  simp [mul_comm]

/-- Products of two translated bumps are integrable, by separation and the squared-norm bound. -/
theorem integrable_bump_cross {d : ℕ} {δ r : ℝ} {Γ : Set (Euclidean d)}
    (hΓ : Separated δ Γ) (hr : 2 * r ≤ δ) (b : Euclidean d → ℂ)
    (hs : ∀ x, r ≤ ‖x‖ → b x = 0) (hb : Integrable (fun x => ‖b x‖ ^ 2))
    (i j : Γ) : Integrable (fun u => star (b (u - i)) * b (u - j)) := by
  by_cases hij : i = j
  · subst j
    convert (hb.ofReal (𝕜 := ℂ)).comp_sub_right (i : Euclidean d) using 1
    ext u
    rw [mul_comm]
    exact (RCLike.mul_conj (b (u - i))).trans (Complex.ofReal_pow _ _).symm
  · have hz : (fun u => star (b (u - i)) * b (u - j)) = fun _ => (0 : ℂ) := by
      funext u
      by_cases hi : b (u - i) = 0
      · simp [hi]
      · have hj : b (u - j) = 0 := by
          by_contra hj
          exact hij (bump_active_unique hΓ hr b hs hi hj)
        simp [hj]
    rw [hz]
    exact integrable_zero _ _ _

/-- Normalization and separation give the translated bump orthogonality integral. -/
theorem integral_bump_cross {d : ℕ} {δ r : ℝ} {Γ : Set (Euclidean d)}
    (hΓ : Separated δ Γ) (hr : 2 * r ≤ δ) (b : Euclidean d → ℂ)
    (hs : ∀ x, r ≤ ‖x‖ → b x = 0) (hn : (∫ x, ‖b x‖ ^ 2) = 1)
    (i j : Γ) : (∫ u, star (b (u - i)) * b (u - j)) = if i = j then 1 else 0 := by
  classical
  split_ifs with hij
  · subst j
    calc
      (∫ u, star (b (u - i)) * b (u - i)) = ∫ u, ((‖b (u - i)‖ ^ 2 : ℝ) : ℂ) := by
        apply integral_congr_ae
        filter_upwards [] with u
        rw [mul_comm]
        exact (RCLike.mul_conj (b (u - i))).trans (Complex.ofReal_pow _ _).symm
      _ = ∫ x, ((‖b x‖ ^ 2 : ℝ) : ℂ) :=
        integral_sub_right_eq_self (fun x => ((‖b x‖ ^ 2 : ℝ) : ℂ)) (i : Euclidean d)
      _ = ((∫ x, ‖b x‖ ^ 2 : ℝ) : ℂ) := integral_ofReal
      _ = 1 := by rw [hn]; norm_num
  · apply integral_eq_zero_of_ae
    filter_upwards [] with u
    by_cases hi : b (u - i) = 0
    · simp [hi]
    · have hj : b (u - j) = 0 := by
        apply Classical.byContradiction
        intro hjn
        exact hij (bump_active_unique hΓ hr b hs hi hjn)
      simp [hj]

/-- With active endpoints the product kernel factors through two translated bumps. -/
theorem bumpKernel_product_eq_cross {d : ℕ} {δ r : ℝ} {Γ : Set (Euclidean d)}
    (hΓ : Separated δ Γ) (hr : 2 * r ≤ δ) (b : Euclidean d → ℂ)
    (hs : ∀ x, r ≤ ‖x‖ → b x = 0) {v w : Euclidean d}
    (i j : Γ) (hi : b (v - i) ≠ 0) (hj : b (w - j) ≠ 0) (u : Euclidean d) :
    bumpKernel Γ b v u * bumpKernel Γ b u w =
      (b (v - i) * star (b (w - j))) * (star (b (u - i)) * b (u - j)) := by
  rw [bumpKernel_eq_single hΓ hr b hs u i hi,
    bumpKernel_eq_single_right hΓ hr b hs u j hj]
  ring

/-- If no bump is active at an endpoint, the entire row of the kernel vanishes. -/
theorem bumpKernel_eq_zero_of_no_active {d : ℕ} (Γ : Set (Euclidean d))
    (b : Euclidean d → ℂ) {v : Euclidean d} (hv : ∀ i : Γ, b (v - i) = 0)
    (w : Euclidean d) : bumpKernel Γ b v w = 0 := by
  simp only [bumpKernel, hv, zero_mul, tsum_zero]

/-- The product defining the projection identity is absolutely integrable. -/
theorem integrable_bumpKernel_product {d : ℕ} {δ r : ℝ} {Γ : Set (Euclidean d)}
    (hΓ : Separated δ Γ) (hr : 2 * r ≤ δ) (b : Euclidean d → ℂ)
    (hs : ∀ x, r ≤ ‖x‖ → b x = 0) (hb : Integrable (fun x => ‖b x‖ ^ 2))
    (v w : Euclidean d) : Integrable (fun u => bumpKernel Γ b v u * bumpKernel Γ b u w) := by
  classical
  by_cases hi : ∃ i : Γ, b (v - i) ≠ 0
  · obtain ⟨i, hi⟩ := hi
    by_cases hj : ∃ j : Γ, b (w - j) ≠ 0
    · obtain ⟨j, hj⟩ := hj
      simpa only [bumpKernel_product_eq_cross hΓ hr b hs i j hi hj] using
        (integrable_bump_cross hΓ hr b hs hb i j).const_mul (b (v - i) * star (b (w - j)))
    · have hw : ∀ j : Γ, b (w - j) = 0 := by simpa using hj
      simp only [bumpKernel_hermitian Γ b w _, bumpKernel_eq_zero_of_no_active Γ b hw,
        star_zero, mul_zero]
      exact integrable_zero _ _ _
  · have hv : ∀ i : Γ, b (v - i) = 0 := by simpa using hi
    simp only [bumpKernel_eq_zero_of_no_active Γ b hv, zero_mul]
    exact integrable_zero _ _ _

/-- The concrete normalized bump kernel satisfies the projection integral identity. -/
theorem integral_bumpKernel_product {d : ℕ} {δ r : ℝ} {Γ : Set (Euclidean d)}
    (hΓ : Separated δ Γ) (hr : 2 * r ≤ δ) (b : Euclidean d → ℂ)
    (hs : ∀ x, r ≤ ‖x‖ → b x = 0) (hn : (∫ x, ‖b x‖ ^ 2) = 1)
    (v w : Euclidean d) :
    (∫ u, bumpKernel Γ b v u * bumpKernel Γ b u w) = bumpKernel Γ b v w := by
  classical
  by_cases hi : ∃ i : Γ, b (v - i) ≠ 0
  · obtain ⟨i, hi⟩ := hi
    by_cases hj : ∃ j : Γ, b (w - j) ≠ 0
    · obtain ⟨j, hj⟩ := hj
      simp only [bumpKernel_product_eq_cross hΓ hr b hs i j hi hj]
      rw [integral_const_mul, integral_bump_cross hΓ hr b hs hn]
      by_cases hij : i = j
      · subst j
        rw [if_pos rfl, mul_one, bumpKernel_eq_single hΓ hr b hs w i hi]
      · rw [if_neg hij, mul_zero, bumpKernel_eq_single hΓ hr b hs w i hi]
        have hw : b (w - i) = 0 := by
          by_contra hw
          exact hij (bump_active_unique hΓ hr b hs hw hj)
        simp [hw]
    · have hw : ∀ j : Γ, b (w - j) = 0 := by simpa using hj
      simp only [bumpKernel_hermitian Γ b w _, bumpKernel_eq_zero_of_no_active Γ b hw,
        star_zero, mul_zero, integral_zero]
  · have hv : ∀ i : Γ, b (v - i) = 0 := by simpa using hi
    simp only [bumpKernel_eq_zero_of_no_active Γ b hv, zero_mul, integral_zero]

end RieszEuclidean
