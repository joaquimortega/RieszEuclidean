import RieszEuclidean.BumpTranslates

namespace RieszEuclidean

/-- The concrete kernel obtained by summing the rank-one bump kernels over a configuration. -/
noncomputable def bumpKernel {d : ℕ} (Γ : Set (Euclidean d)) (b : Euclidean d → ℂ)
    (v w : Euclidean d) : ℂ :=
  ∑' k : Γ, b (v - k) * star (b (w - k))

/-- At most one translated bump is active, including at the endpoint separation bound. -/
theorem bump_active_unique {d : ℕ} {δ r : ℝ} {Γ : Set (Euclidean d)}
    (hΓ : Separated δ Γ) (hr : 2 * r ≤ δ) (b : Euclidean d → ℂ)
    (hs : ∀ x, r ≤ ‖x‖ → b x = 0) {v : Euclidean d} {i j : Γ}
    (hi : b (v - i) ≠ 0) (hj : b (v - j) ≠ 0) : i = j := by
  by_contra hij
  have hvi : ‖v - i‖ < r := lt_of_not_ge (fun hn => hi (hs _ hn))
  have hvj : ‖v - j‖ < r := lt_of_not_ge (fun hn => hj (hs _ hn))
  have hd := hΓ i.property j.property (fun he => hij (Subtype.ext he))
  have ht := dist_triangle (i : Euclidean d) v (j : Euclidean d)
  rw [dist_comm (i : Euclidean d) v, dist_eq_norm v (i : Euclidean d),
    dist_eq_norm v (j : Euclidean d)] at ht
  linarith

/-- For fixed first coordinate, the kernel summand has finite support of size at most one. -/
theorem bumpKernel_support_subsingleton {d : ℕ} {δ r : ℝ} {Γ : Set (Euclidean d)}
    (hΓ : Separated δ Γ) (hr : 2 * r ≤ δ) (b : Euclidean d → ℂ)
    (hs : ∀ x, r ≤ ‖x‖ → b x = 0) (v w : Euclidean d) :
    (Function.support (fun k : Γ => b (v - k) * star (b (w - k)))).Subsingleton := by
  intro i hi j hj
  exact bump_active_unique hΓ hr b hs (left_ne_zero_of_mul hi) (left_ne_zero_of_mul hj)

/-- The kernel series is an actual summable finite-support series. -/
theorem summable_bumpKernel {d : ℕ} {δ r : ℝ} {Γ : Set (Euclidean d)}
    (hΓ : Separated δ Γ) (hr : 2 * r ≤ δ) (b : Euclidean d → ℂ)
    (hs : ∀ x, r ≤ ‖x‖ → b x = 0) (v w : Euclidean d) :
    Summable (fun k : Γ => b (v - k) * star (b (w - k))) := by
  classical
  let s := (bumpKernel_support_subsingleton hΓ hr b hs v w).finite
  apply summable_of_ne_finset_zero (s := s.toFinset)
  intro k hk
  simpa only [Set.Finite.mem_toFinset, Function.mem_support, not_not] using hk

/-- If a bump is active at the first coordinate, its term is the whole kernel. -/
theorem bumpKernel_eq_single {d : ℕ} {δ r : ℝ} {Γ : Set (Euclidean d)}
    (hΓ : Separated δ Γ) (hr : 2 * r ≤ δ) (b : Euclidean d → ℂ)
    (hs : ∀ x, r ≤ ‖x‖ → b x = 0) {v : Euclidean d} (w : Euclidean d)
    (i : Γ) (hi : b (v - i) ≠ 0) :
    bumpKernel Γ b v w = b (v - i) * star (b (w - i)) := by
  apply tsum_eq_single i
  intro j hji
  have hj : b (v - j) = 0 := by
    by_contra hj
    exact hji (bump_active_unique hΓ hr b hs hj hi)
  rw [hj, zero_mul]

/-- A uniform bump bound gives the squared uniform kernel bound. -/
theorem norm_bumpKernel_le {d : ℕ} {δ r M : ℝ} {Γ : Set (Euclidean d)}
    (hΓ : Separated δ Γ) (hr : 2 * r ≤ δ) (b : Euclidean d → ℂ)
    (hs : ∀ x, r ≤ ‖x‖ → b x = 0) (hM : 0 ≤ M)
    (hb : ∀ x, ‖b x‖ ≤ M) (v w : Euclidean d) : ‖bumpKernel Γ b v w‖ ≤ M ^ 2 := by
  classical
  by_cases he : ∃ i : Γ, b (v - i) ≠ 0
  · obtain ⟨i, hi⟩ := he
    rw [bumpKernel_eq_single hΓ hr b hs w i hi, norm_mul, norm_star, pow_two]
    exact mul_le_mul (hb _) (hb _) (norm_nonneg _) hM
  · have hz : bumpKernel Γ b v w = 0 := by
      suffices hh : ∀ i : Γ, b (v - i) * star (b (w - i)) = 0 by
        simp only [bumpKernel, hh, tsum_zero]
      intro i
      have hi : b (v - i) = 0 := by simpa using (not_exists.mp he i)
      rw [hi, zero_mul]
    rw [hz, norm_zero]
    exact sq_nonneg M

/-- The concrete kernel vanishes outside twice the support radius. -/
theorem bumpKernel_eq_zero_of_two_mul_lt {d : ℕ} {r : ℝ} (Γ : Set (Euclidean d))
    (b : Euclidean d → ℂ) (hs : ∀ x, r ≤ ‖x‖ → b x = 0)
    {v w : Euclidean d} (hvw : 2 * r < ‖v - w‖) : bumpKernel Γ b v w = 0 := by
  suffices hh : ∀ i : Γ, b (v - i) * star (b (w - i)) = 0 by
    simp only [bumpKernel, hh, tsum_zero]
  intro i
  by_cases hi : b (v - i) = 0
  · rw [hi, zero_mul]
  · have hv : ‖v - i‖ < r := lt_of_not_ge (fun hn => hi (hs _ hn))
    have hw : r ≤ ‖w - i‖ := by
      have ht := dist_triangle v (i : Euclidean d) w
      rw [dist_eq_norm v w, dist_eq_norm v (i : Euclidean d),
        dist_comm (i : Euclidean d) w, dist_eq_norm w (i : Euclidean d)] at ht
      linarith
    rw [hs _ hw, star_zero, mul_zero]

/-- The bump kernel is Hermitian. -/
theorem bumpKernel_hermitian {d : ℕ} (Γ : Set (Euclidean d))
    (b : Euclidean d → ℂ) (v w : Euclidean d) :
    bumpKernel Γ b w v = star (bumpKernel Γ b v w) := by
  rw [bumpKernel, bumpKernel, tsum_star]
  apply tsum_congr
  intro i
  simp [mul_comm]

/-- Covariance for the project's convention `translate z Γ = Γ - z`. -/
theorem bumpKernel_translate {d : ℕ} (Γ : Set (Euclidean d))
    (b : Euclidean d → ℂ) (z v w : Euclidean d) :
    bumpKernel (translate z Γ) b v w = bumpKernel Γ b (v + z) (w + z) := by
  let e : translate z Γ ≃ Γ :=
    { toFun := fun k => ⟨k + z, k.property⟩
      invFun := fun k => ⟨k - z, by simp [translate, k.property]⟩
      left_inv := fun k => Subtype.ext (by simp)
      right_inv := fun k => Subtype.ext (by simp) }
  rw [bumpKernel, bumpKernel, ← e.tsum_eq]
  apply tsum_congr
  intro k
  change b (v - k) * star (b (w - k)) =
    b (v + z - (k + z)) * star (b (w + z - (k + z)))
  simp only [add_sub_add_right_eq_sub]

end RieszEuclidean
