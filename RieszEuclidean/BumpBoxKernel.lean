import RieszEuclidean.BumpProjectionLimits
open MeasureTheory
namespace RieszEuclidean
/-- The translated bump coefficient is its actual scalar integral against a L² input. -/
theorem translated_bump_inner_memLp {d : ℕ} (b : SchwartzMap (Euclidean d) ℂ) (g : Euclidean d → ℂ)
    (hg : MemLp g 2 volume) (i : Euclidean d) :
    inner (𝕜 := ℂ) (translationL2 (-i) (b.toLp 2 volume)) (hg.toLp g) =
      ∫ x, star (b (x - i)) * g x := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [translated_bump_coe b i, hg.coeFn_toLp] with x hx hg
  rw [hx, hg]
  simp [RCLike.inner_apply, mul_comm]

/-- Compact support of the input forces only finitely many bump analysis coefficients to survive. -/
theorem finite_bump_coefficients_memLp {d : ℕ} {δ r : ℝ} {Γ : Set (Euclidean d)}
    (hΓ : Separated δ Γ) (hδ : 0 < δ) (b : SchwartzMap (Euclidean d) ℂ) (g : Euclidean d → ℂ)
    (hs : ∀ x, r ≤ ‖x‖ → b x = 0) (hg : MemLp g 2 volume) (hgc : HasCompactSupport g) :
    ∃ s : Finset Γ, ∀ i : Γ, i ∉ s →
      inner (𝕜 := ℂ) (translationL2 (-(i : Euclidean d)) (b.toLp 2 volume))
        (hg.toLp g) = 0 := by
  classical
  obtain ⟨R, _, hR⟩ := hgc.isBounded.subset_ball_lt 0 (0 : Euclidean d)
  have hf := (hΓ.finite_inter_compact hδ (isCompact_closedBall (0 : Euclidean d)
    (R + r + 1))).preimage (f := fun i : Γ => (i : Euclidean d)) Subtype.val_injective.injOn
  refine ⟨hf.toFinset, ?_⟩
  intro i hi
  have hn : R + r + 1 < ‖(i : Euclidean d)‖ := by
    have hn' : ¬‖(i : Euclidean d)‖ ≤ R + r + 1 := by
      intro hn
      exact hi (hf.mem_toFinset.mpr ⟨i.property, by simpa using hn⟩)
    exact lt_of_not_ge hn'
  rw [translated_bump_inner_memLp b g hg]
  apply integral_eq_zero_of_ae
  filter_upwards [] with x
  by_cases hx : g x = 0
  · simp [hx]
  · have hxR : ‖x‖ < R := by simpa using hR (subset_tsupport g hx)
    have hb : b (x - i) = 0 := by
      apply hs
      have ht := norm_sub_norm_le (i : Euclidean d) x
      rw [norm_sub_rev (i : Euclidean d) x] at ht
      linarith
    simp [hb]

/-- The actual synthesis projection of a compactly supported L² function has a finite expansion. -/
theorem bump_projection_memLp_finite_expansion {d : ℕ} {δ r : ℝ}
    {Γ : Set (Euclidean d)} (hΓ : Separated δ Γ) (hδ : 0 < δ) (hr : 2 * r < δ)
    (b : SchwartzMap (Euclidean d) ℂ) (g : Euclidean d → ℂ) (hs : ∀ x, r ≤ ‖x‖ → b x = 0)
    (hn : ‖b.toLp 2 volume‖ = 1) (hg : MemLp g 2 volume) (hgc : HasCompactSupport g) :
    ∃ s : Finset Γ,
      (isometryRangeProjection (bumpSynthesis hΓ hr b hs hn)).op (hg.toLp g) =
        ∑ i ∈ s, (∫ x, star (b (x - i)) * g x) •
          translationL2 (-(i : Euclidean d)) (b.toLp 2 volume) := by
  obtain ⟨s, hcoeff⟩ := finite_bump_coefficients_memLp hΓ hδ b g hs hg hgc
  refine ⟨s, ?_⟩
  have he := isometryRangeProjection_eq_sum_of_coefficients
    (translated_bumps_orthonormal hΓ hr b hs hn) (hg.toLp g) s hcoeff
  simpa only [bumpSynthesis, translated_bump_inner_memLp b g hg] using he
/-- On compactly supported L² inputs, the actual synthesis projection has kernel qΓ. -/
theorem bump_projection_memLp_kernel {d : ℕ} {δ r : ℝ}
    {Γ : Set (Euclidean d)} (hΓ : Separated δ Γ) (hδ : 0 < δ) (hr : 2 * r < δ)
    (b : SchwartzMap (Euclidean d) ℂ) (g : Euclidean d → ℂ) (hs : ∀ x, r ≤ ‖x‖ → b x = 0)
    (hn : ‖b.toLp 2 volume‖ = 1) (hg : MemLp g 2 volume) (hgc : HasCompactSupport g) :
    ((isometryRangeProjection (bumpSynthesis hΓ hr b hs hn)).op (hg.toLp g) :
      Euclidean d → ℂ) =ᵐ[volume] fun v => ∫ w, bumpKernel Γ b v w * g w := by
  obtain ⟨s, hcoeff⟩ := finite_bump_coefficients_memLp hΓ hδ b g hs hg hgc
  have he := isometryRangeProjection_eq_sum_of_coefficients
    (translated_bumps_orthonormal hΓ hr b hs hn) (hg.toLp g) s hcoeff
  change (isometryRangeProjection (bumpSynthesis hΓ hr b hs hn)).op (hg.toLp g) = _ at he
  rw [he]
  have hae := finite_bump_sum_coe s
    (fun i : Γ => inner (𝕜 := ℂ) (translationL2 (-(i : Euclidean d)) (b.toLp 2 volume))
      (hg.toLp g)) (fun i : Γ => (i : Euclidean d)) b
  filter_upwards [hae] with v hv
  rw [hv]
  simp only [translated_bump_inner_memLp b g hg]
  exact finite_bump_sum_eq_kernel_integral hΓ hr.le b hs g s
    (fun i hi => by simpa only [translated_bump_inner_memLp b g hg] using hcoeff i hi) v
/-- The actual projection pairing is the iterated scalar kernel pairing for compact L² inputs. -/
theorem bump_projection_memLp_pairing {d : ℕ} {δ r : ℝ}
    {Γ : Set (Euclidean d)} (hΓ : Separated δ Γ) (hδ : 0 < δ) (hr : 2 * r < δ)
    (b : SchwartzMap (Euclidean d) ℂ) (f g : Euclidean d → ℂ)
    (hs : ∀ x, r ≤ ‖x‖ → b x = 0) (hn : ‖b.toLp 2 volume‖ = 1)
    (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) (hgc : HasCompactSupport g) :
    inner (𝕜 := ℂ) (hf.toLp f)
      ((isometryRangeProjection (bumpSynthesis hΓ hr b hs hn)).op (hg.toLp g)) =
      ∫ v, star (f v) * ∫ w, bumpKernel Γ b v w * g w := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp, bump_projection_memLp_kernel hΓ hδ hr b g hs hn hg hgc]
    with v hvf hvg
  rw [hvf, hvg]
  simp [RCLike.inner_apply, mul_comm]
end RieszEuclidean
