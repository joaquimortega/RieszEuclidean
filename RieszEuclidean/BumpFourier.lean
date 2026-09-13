import RieszEuclidean.Bumps
import RieszEuclidean.Separation
import RieszEuclidean.Affine
open MeasureTheory
namespace RieszEuclidean
/-- Integral form of the positive-sign Fourier transform in the paper's notation. -/
theorem inverseFourier_exponential {d : ℕ} (b : Euclidean d → ℂ) (x : Euclidean d) :
    Real.fourierIntegralInv b x = ∫ ξ, exponential ξ x * b ξ := by
  rw [Real.fourierIntegralInv_eq']
  simp only [exponential_eq_phase, smul_eq_mul]
/-- The real part is the norm for a nonnegative real-valued bump. -/
theorem bump_norm_eq_re {d : ℕ} (b : Euclidean d → ℂ)
    (hp : ∀ x, (b x).im = 0 ∧ 0 ≤ (b x).re) (x : Euclidean d) :
    ‖b x‖ = (b x).re := by
  have he : b x = ((b x).re : ℂ) := by
    apply Complex.ext <;> simp [hp x]
  rw [he, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hp x).2]
  rfl
/-- A small phase variation bounds the Fourier perturbation by the bump mass. -/
theorem bump_fourier_near_mass {d : ℕ} (b : SchwartzMap (Euclidean d) ℂ)
    (hp : ∀ ξ, (b ξ).im = 0 ∧ 0 ≤ (b ξ).re) (x : Euclidean d)
    {c : ℝ} (hc : ∀ ξ, b ξ ≠ 0 → ‖exponential ξ x - 1‖ ≤ c) :
    ‖Real.fourierIntegralInv b x - ∫ ξ, b ξ‖ ≤ c * ∫ ξ, (b ξ).re := by
  have hcont : Continuous (fun ξ => exponential ξ x) := by
    unfold exponential
    fun_prop
  have hi : Integrable (fun ξ => exponential ξ x * b ξ) :=
    b.integrable.bdd_mul hcont.aestronglyMeasurable ⟨1, fun ξ => (exponential_norm ξ x).le⟩
  rw [inverseFourier_exponential, ← integral_sub hi b.integrable]
  calc
    _ ≤ ∫ ξ, c * (b ξ).re := norm_integral_le_of_norm_le (b.integrable.re.const_mul c)
      (Filter.Eventually.of_forall (fun ξ => by
        by_cases hz : b ξ = 0
        · simp [hz]
        · rw [show exponential ξ x * b ξ - b ξ = (exponential ξ x - 1) * b ξ by ring,
            norm_mul, bump_norm_eq_re b hp]
          exact mul_le_mul_of_nonneg_right (hc ξ hz) (hp ξ).2))
    _ = _ := integral_const_mul _ _
/-- A half-mass perturbation leaves a quantitative Fourier lower bound. -/
theorem bump_fourier_lower {d : ℕ} (b : SchwartzMap (Euclidean d) ℂ)
    (hp : ∀ ξ, (b ξ).im = 0 ∧ 0 ≤ (b ξ).re) (x : Euclidean d)
    (hc : ∀ ξ, b ξ ≠ 0 → ‖exponential ξ x - 1‖ ≤ 1 / 2) :
    (∫ ξ, (b ξ).re) / 2 ≤ ‖Real.fourierIntegralInv b x‖ := by
  have he := bump_fourier_near_mass b hp x hc
  have hm : (∫ ξ, (b ξ).re) ≤ ‖∫ ξ, b ξ‖ := by
    rw [show (∫ ξ, (b ξ).re) = (∫ ξ, b ξ).re from integral_re b.integrable]
    exact Complex.re_le_norm _
  have ht' : ‖∫ ξ, b ξ‖ ≤ ‖Real.fourierIntegralInv b x - ∫ ξ, b ξ‖ +
      ‖Real.fourierIntegralInv b x‖ := by
    simpa only [sub_add_cancel, norm_sub_rev] using
      norm_add_le ((∫ ξ, b ξ) - Real.fourierIntegralInv b x) (Real.fourierIntegralInv b x)
  linarith
/-- Small spatial support makes the Fourier lower bound uniform on a bounded ball. -/
theorem bump_fourier_lower_on_ball {d : ℕ} (b : SchwartzMap (Euclidean d) ℂ)
    (hp : ∀ ξ, (b ξ).im = 0 ∧ 0 ≤ (b ξ).re)
    {r R : ℝ} (hR : 0 ≤ R) (hs : ∀ ξ, r ≤ ‖ξ‖ → b ξ = 0)
    (hsmall : 4 * Real.pi * R * r ≤ 1 / 2)
    {x : Euclidean d} (hx : ‖x‖ ≤ R) :
    (∫ ξ, (b ξ).re) / 2 ≤ ‖Real.fourierIntegralInv b x‖ := by
  apply bump_fourier_lower b hp x
  intro ξ hξ
  have hr : ‖ξ‖ < r := lt_of_not_ge (fun h => hξ (hs ξ h))
  have hb : 4 * Real.pi * R * ‖ξ‖ ≤ 1 / 2 :=
    (mul_le_mul_of_nonneg_left hr.le (by positivity)).trans hsmall
  have hphase : 2 * Real.pi * ‖ξ - 0‖ * R < 1 := by
    simp only [sub_zero]
    nlinarith
  have he := exponential_sub_le_on_ball ξ 0 x hx hphase
  simp only [exponential, inner_zero_left, Complex.ofReal_zero, mul_zero,
    Complex.exp_zero, sub_zero] at he
  exact he.trans hb
/-- A continuous nonnegative bump positive at zero has positive total mass. -/
theorem bump_integral_re_pos {d : ℕ} (b : SchwartzMap (Euclidean d) ℂ)
    (hp : ∀ x, 0 ≤ (b x).re) (h0 : 0 < (b 0).re) :
    0 < ∫ x, (b x).re := by
  exact integral_pos_of_integrable_nonneg_nonzero
    (Complex.continuous_re.comp b.continuous) b.integrable.re hp h0.ne'
/-- Choose a normalized bump with disjoint-translate radius and nonvanishing Fourier transform. -/
theorem exists_bump_fourier_lower {d : ℕ} {Ω : Set (Euclidean d)}
    (hΩ : Bornology.IsBounded Ω) {δ : ℝ} (hδ : 0 < δ) :
    ∃ r : ℝ, 0 < r ∧ 2 * r < δ ∧
      ∃ b : SchwartzMap (Euclidean d) ℂ,
        HasCompactSupport b ∧ ‖b.toLp 2 volume‖ = 1 ∧
        (∀ ξ, (b ξ).im = 0 ∧ 0 ≤ (b ξ).re) ∧
        (∀ ξ, r ≤ ‖ξ‖ → b ξ = 0) ∧
        ∃ c : ℝ, 0 < c ∧ ∀ x ∈ Ω, c ≤ ‖Real.fourierIntegralInv b x‖ := by
  obtain ⟨R, hR, hbound⟩ := hΩ.exists_pos_norm_le
  let A := 4 * Real.pi * R
  let r := min (δ / 4) (1 / (4 * (A + 1)))
  have hr : 0 < r := lt_min (by positivity) (by positivity)
  have hrδ : 2 * r < δ := by
    have h := min_le_left (δ / 4) (1 / (4 * (A + 1)))
    change r ≤ δ / 4 at h
    linarith
  have hsmall : 4 * Real.pi * R * r ≤ 1 / 2 := by
    have h := min_le_right (δ / 4) (1 / (4 * (A + 1)))
    change r ≤ 1 / (4 * (A + 1)) at h
    have ht := (le_div_iff₀ (show 0 < 4 * (A + 1) by positivity)).mp h
    change A * r ≤ 1 / 2
    nlinarith
  obtain ⟨b, hs, hn, hp, hz, h0⟩ := exists_normalized_schwartz_bump (d := d) hr
  refine ⟨r, hr, hrδ, b, hs, hn, hp, hz, (∫ ξ, (b ξ).re) / 2, ?_, ?_⟩
  · exact half_pos (bump_integral_re_pos b (fun ξ => (hp ξ).2) h0)
  · intro x hx
    exact bump_fourier_lower_on_ball b hp hR.le hz hsmall (hbound x hx)
end RieszEuclidean
