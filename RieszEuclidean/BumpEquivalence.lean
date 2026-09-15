import RieszEuclidean.InitialGap

noncomputable section
open MeasureTheory
namespace RieszEuclidean

/-- A strict Fourier-to-bump projection gap recovers exponential synthesis.
The columns are recovered from the Fourier transform of the actual translated
bump, so no Riesz-basis assumption enters this direction. -/
theorem exponentialRieszBasis_of_bump_gap {d : ℕ} {Ω Λ : Set (Euclidean d)}
    (hΩ : MeasurableSet Ω) (b : SchwartzMap (Euclidean d) ℂ)
    (V : SeqL2 Λ →ₗᵢ[ℂ] FullL2 d)
    (hV : ∀ i : Λ, V (lp.single 2 i 1) =
      translationL2 (-(i : Euclidean d)) (b.toLp 2 volume))
    {c : ℝ} (hc : 0 < c) (hl : ∀ x ∈ Ω, c ≤ ‖Real.fourierIntegralInv b x‖)
    (hgap : ‖(fourierProjection Ω hΩ).op - (isometryRangeProjection V).op‖ < 1) :
    HasExponentialRieszBasis Ω Λ := by
  classical
  obtain ⟨E, hE⟩ :=
    ((fourierProjection Ω hΩ).gap_iff_rangeIso (isometryRangeProjection V)).mp hgap
  let eV := (isometryRangeEquiv V (isometryRangeProjection V).range
    (isometryRangeProjection_range V).symm).toContinuousLinearEquiv
  let eW := (isometryRangeEquiv (fourierDomainEmbedding Ω hΩ)
    (fourierProjection Ω hΩ).range
    (fourierDomainEmbedding_range Ω hΩ)).toContinuousLinearEquiv
  let T := eV.trans (E.trans eW.symm)
  let B := bumpFourierMultiplier Ω hΩ b hc hl
  let S := T.trans B.symm
  have hT (a : SeqL2 Λ) :
      T a = domainRestriction Ω (paperFourierL2 d (V a)) := by
    apply (fourierDomainEmbedding Ω hΩ).injective
    rw [fourierDomainEmbedding_restriction]
    have he := hE (eV a)
    have hw := congrArg (fun z : (fourierProjection Ω hΩ).range => (z : FullL2 d))
      (eW.apply_symm_apply (E (eV a)))
    exact hw.trans he
  refine ⟨S, fun i => ?_⟩
  have hBS : B (S (lp.single 2 i 1)) =
      domainRestriction Ω (paperFourierL2 d (V (lp.single 2 i 1))) := by
    change B (B.symm (T _)) = _
    rw [B.apply_symm_apply, hT]
  have ht := (paperFourierL2_translated_bump b (i : Euclidean d)).filter_mono
    (ae_mono (Measure.restrict_le_self (s := Ω)))
  have hm := bumpFourierMultiplier_coe Ω hΩ b hc hl (S (lp.single 2 i 1))
  rw [hBS, hV] at hm
  filter_upwards [hm, ht, ae_restrict_mem hΩ,
    domainRestriction_coe Ω
      (paperFourierL2 d (translationL2 (-(i : Euclidean d)) (b.toLp 2 volume)))]
    with x hm ht hx hd
  have hn : Real.fourierIntegralInv b x ≠ 0 := norm_pos_iff.mp (hc.trans_le (hl x hx))
  apply mul_left_cancel₀ hn
  rw [← hm, hd, ht, mul_comm]

/-- Lemma 2.1 of the revised manuscript: the Riesz-basis property is equivalent
to the existence of separated normalized bumps at projection distance less than one. -/
theorem exponentialRieszBasis_iff_initial_bump_gap {d : ℕ} {Ω Λ : Set (Euclidean d)}
    (hΩ : MeasurableSet Ω) (hb : Bornology.IsBounded Ω) :
    HasExponentialRieszBasis Ω Λ ↔
    ∃ δ r : ℝ, 0 < δ ∧ Separated δ Λ ∧ 0 < r ∧ 2 * r < δ ∧
      ∃ b : SchwartzMap (Euclidean d) ℂ,
        HasCompactSupport b ∧ ‖b.toLp 2 volume‖ = 1 ∧
        (∀ ξ, (b ξ).im = 0 ∧ 0 ≤ (b ξ).re) ∧
        (∀ ξ, r ≤ ‖ξ‖ → b ξ = 0) ∧
        (∃ c : ℝ, 0 < c ∧ ∀ x ∈ closure Ω, c ≤ ‖Real.fourierIntegralInv b x‖) ∧
        ∃ V : SeqL2 Λ →ₗᵢ[ℂ] FullL2 d,
          (∀ i : Λ, V (lp.single 2 i 1) =
            translationL2 (-(i : Euclidean d)) (b.toLp 2 volume)) ∧
          ‖(fourierProjection Ω hΩ).op - (isometryRangeProjection V).op‖ < 1 := by
  constructor
  · intro hB
    obtain ⟨δ, r, hδ, hΛ, hr, hrδ, b, hs, hn, hp, hz, ⟨c, hc, hl⟩, V, hV, hgap⟩ :=
      exists_initial_bump_gap hΩ hb hB
    refine ⟨δ, r, hδ, hΛ, hr, hrδ, b, hs, hn, hp, hz, ⟨c, hc, ?_⟩, V, hV, hgap⟩
    have hcont : Continuous (Real.fourierIntegralInv b) :=
      VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
        (continuous_fst.inner continuous_snd).neg b.integrable
    exact closure_minimal hl (isClosed_le continuous_const hcont.norm)
  · rintro ⟨δ, r, _, _, _, _, b, _, _, _, _, ⟨c, hc, hl⟩, V, hV, hgap⟩
    exact exponentialRieszBasis_of_bump_gap hΩ b V hV hc
      (fun x hx => hl x (subset_closure hx)) hgap

end RieszEuclidean
