import RieszEuclidean.BumpProjectionLimits
import RieszEuclidean.TranslationHull
import RieszEuclidean.InitialGap
open MeasureTheory Filter Topology
namespace RieszEuclidean
/-- Composition of actual L² translations agrees with addition of their real parameters. -/
theorem translationL2_add {d : ℕ} (y z : Euclidean d) (f : FullL2 d) :
    translationL2 y (translationL2 z f) = translationL2 (y + z) f := by
  have ht := (measurePreserving_add_right volume y).quasiMeasurePreserving.ae (translationL2_coe z f)
  apply Lp.ext
  filter_upwards [translationL2_coe y (translationL2 z f), ht,
    translationL2_coe (y + z) f] with x h1 h2 h3
  rw [h1, h2, h3, add_assoc]
/-- Translation by zero is the identity on actual L² classes. -/
theorem translationL2_zero {d : ℕ} (f : FullL2 d) : translationL2 0 f = f := by
  apply Lp.ext
  simpa only [add_zero] using translationL2_coe 0 f
/-- Translating a compactly supported Schwartz function preserves that class. -/
noncomputable def compactSchwartzTranslate {d : ℕ} (g : SchwartzMap (Euclidean d) ℂ)
    (hg : HasCompactSupport g) (y : Euclidean d) : SchwartzMap (Euclidean d) ℂ :=
  compactSchwartz (fun x => g (x + y))
    (g.smooth'.comp (contDiff_id.add contDiff_const))
    (hg.comp_homeomorph (Homeomorph.addRight y))
/-- The translated Schwartz representative is the actual L² translation. -/
theorem compactSchwartzTranslate_toLp {d : ℕ} (g : SchwartzMap (Euclidean d) ℂ)
    (hg : HasCompactSupport g) (y : Euclidean d) :
    (compactSchwartzTranslate g hg y).toLp 2 volume = translationL2 y (g.toLp 2 volume) := by
  apply Lp.ext
  have ht := (measurePreserving_add_right volume y).quasiMeasurePreserving.ae (g.coeFn_toLp 2 volume)
  filter_upwards [(compactSchwartzTranslate g hg y).coeFn_toLp 2 volume,
    translationL2_coe y (g.toLp 2 volume), ht] with x h1 h2 h3
  rw [h1, h2, h3]
  rfl
/-- Actual bump projections intertwine translations on compact Schwartz inputs. -/
theorem bump_projection_translation_compact {d : ℕ} {δ r : ℝ}
    (Γ : SeparatedConfiguration d δ) (hδ : 0 < δ) (hr : 2 * r < δ)
    (b g : SchwartzMap (Euclidean d) ℂ) (hs : ∀ x, r ≤ ‖x‖ → b x = 0)
    (hn : ‖b.toLp 2 volume‖ = 1) (hg : HasCompactSupport g) (y : Euclidean d) :
    (isometryRangeProjection (bumpSynthesis (SeparatedConfiguration.translate y Γ).separated
      hr b hs hn)).op (translationL2 y (g.toLp 2 volume)) =
    translationL2 y ((isometryRangeProjection (bumpSynthesis Γ.separated hr b hs hn)).op
      (g.toLp 2 volume)) := by
  let gy := compactSchwartzTranslate g hg y
  have hgy : HasCompactSupport gy := hg.comp_homeomorph (Homeomorph.addRight y)
  have hleft := bump_projection_schwartz_kernel (SeparatedConfiguration.translate y Γ).separated
    hδ hr b gy hs hn hgy
  have hright := (measurePreserving_add_right volume y).quasiMeasurePreserving.ae
    (bump_projection_schwartz_kernel Γ.separated hδ hr b g hs hn hg)
  rw [← compactSchwartzTranslate_toLp g hg y]
  apply Lp.ext
  filter_upwards [hleft, translationL2_coe y
    ((isometryRangeProjection (bumpSynthesis Γ.separated hr b hs hn)).op (g.toLp 2 volume)),
    hright] with v h1 h2 h3
  rw [h1, h2, h3]
  change (∫ w, bumpKernel (translate y Γ.carrier) b v w * g (w + y)) =
    ∫ w, bumpKernel Γ.carrier b (v + y) w * g w
  simp only [bumpKernel_translate]
  exact integral_add_right_eq_self (fun w => bumpKernel Γ.carrier b (v + y) w * g w) y
/-- Compactly supported Schwartz vectors are a dense family in actual L². -/
theorem compactSchwartz_toL2_denseRange (d : ℕ) :
    DenseRange (fun g : {g : SchwartzMap (Euclidean d) ℂ // HasCompactSupport g} =>
      g.val.toLp 2 volume) := by
  rw [Metric.denseRange_iff]
  intro f ε hε
  obtain ⟨g, hg, hd⟩ := exists_compactSchwartz_L2_dist_lt f hε
  exact ⟨⟨g, hg⟩, hd⟩
/-- The actual bump projection has translation covariance on every L² vector. -/
theorem bump_projection_translation {d : ℕ} {δ r : ℝ}
    (Γ : SeparatedConfiguration d δ) (hδ : 0 < δ) (hr : 2 * r < δ)
    (b : SchwartzMap (Euclidean d) ℂ) (hs : ∀ x, r ≤ ‖x‖ → b x = 0)
    (hn : ‖b.toLp 2 volume‖ = 1) (y : Euclidean d) (f : FullL2 d) :
    (isometryRangeProjection (bumpSynthesis (SeparatedConfiguration.translate y Γ).separated
      hr b hs hn)).op (translationL2 y f) =
    translationL2 y ((isometryRangeProjection (bumpSynthesis Γ.separated hr b hs hn)).op f) := by
  refine (compactSchwartz_toL2_denseRange d).induction_on f ?_ ?_
  · exact isClosed_eq
      ((isometryRangeProjection (bumpSynthesis (SeparatedConfiguration.translate y Γ).separated
        hr b hs hn)).op.continuous.comp (translationL2 y).continuous)
      ((translationL2 y).continuous.comp
        (isometryRangeProjection (bumpSynthesis Γ.separated hr b hs hn)).op.continuous)
  · intro g
    exact bump_projection_translation_compact Γ hδ hr b g.val hs hn g.property y
/-- Intertwining by a surjective linear isometry preserves operator norm. -/
theorem norm_eq_of_surjective_isometry_intertwines {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (T : H →ₗᵢ[ℂ] H) (hT : Function.Surjective T)
    (A B : H →L[ℂ] H) (h : ∀ f, A (T f) = T (B f)) : ‖A‖ = ‖B‖ := by
  apply le_antisymm
  · apply A.opNorm_le_bound (norm_nonneg B)
    intro f
    obtain ⟨g, rfl⟩ := hT f
    rw [h, T.norm_map, T.norm_map]
    exact B.le_opNorm g
  · apply B.opNorm_le_bound (norm_nonneg A)
    intro f
    have ht := A.le_opNorm (T f)
    rwa [h, T.norm_map, T.norm_map] at ht
/-- Every real L² translation is surjective. -/
theorem translationL2_surjective {d : ℕ} (y : Euclidean d) :
    Function.Surjective (translationL2 y) := by
  intro f
  refine ⟨translationL2 (-y) f, ?_⟩
  rw [translationL2_add, add_neg_cancel, translationL2_zero]
/-- The actual Fourier-to-bump projection gap is constant on real translation orbits. -/
theorem bump_projection_gap_translation {d : ℕ} {δ r : ℝ}
    (Ω : Set (Euclidean d)) (hΩ : MeasurableSet Ω) (hfin : volume Ω ≠ ⊤)
    (Γ : SeparatedConfiguration d δ) (hδ : 0 < δ) (hr : 2 * r < δ)
    (b : SchwartzMap (Euclidean d) ℂ) (hs : ∀ x, r ≤ ‖x‖ → b x = 0)
    (hn : ‖b.toLp 2 volume‖ = 1) (y : Euclidean d) :
    ‖(fourierProjection Ω hΩ).op - (isometryRangeProjection
      (bumpSynthesis (SeparatedConfiguration.translate y Γ).separated hr b hs hn)).op‖ =
    ‖(fourierProjection Ω hΩ).op - (isometryRangeProjection
      (bumpSynthesis Γ.separated hr b hs hn)).op‖ := by
  apply norm_eq_of_surjective_isometry_intertwines (translationL2 y) (translationL2_surjective y)
  intro f
  simp only [ContinuousLinearMap.sub_apply, map_sub,
    fourierProjection_translation Ω hΩ hfin y f, bump_projection_translation Γ hδ hr b hs hn y f]
set_option maxHeartbeats 800000 in
/-- Strong limits propagate the original actual gap bound to every configuration in the hull. -/
theorem bump_projection_gap_hull_le {d : ℕ} {δ r : ℝ}
    (Ω : Set (Euclidean d)) (hΩ : MeasurableSet Ω) (hfin : volume Ω ≠ ⊤)
    (Γ : SeparatedConfiguration d δ) (hδ : 0 < δ) (hr : 2 * r < δ)
    (b : SchwartzMap (Euclidean d) ℂ) (hs : ∀ x, r ≤ ‖x‖ → b x = 0)
    (hn : ‖b.toLp 2 volume‖ = 1) {Δ : SeparatedConfiguration d δ}
    (hΔ : Δ ∈ SeparatedConfiguration.hull Γ) :
    ‖(fourierProjection Ω hΩ).op - (isometryRangeProjection
      (bumpSynthesis Δ.separated hr b hs hn)).op‖ ≤
    ‖(fourierProjection Ω hΩ).op - (isometryRangeProjection
      (bumpSynthesis Γ.separated hr b hs hn)).op‖ := by
  have hΔ' : Δ ∈ closure (SeparatedConfiguration.orbit Γ) := hΔ
  obtain ⟨A, hA, ht⟩ := mem_closure_iff_seq_limit.mp hΔ'
  have hg : ∀ n,
      ‖(isometryRangeProjection (bumpSynthesis (A n).separated hr b hs hn)).op -
        (fourierProjection Ω hΩ).op‖ ≤
      ‖(fourierProjection Ω hΩ).op -
        (isometryRangeProjection (bumpSynthesis Γ.separated hr b hs hn)).op‖ := by
    intro n
    obtain ⟨y, hy⟩ := hA n
    rw [← hy, norm_sub_rev, bump_projection_gap_translation Ω hΩ hfin Γ hδ hr b hs hn y]
  have hlim := bump_projection_stronglyConverges hδ hr b hs hn ht
  have he := OrthProjection.gap_le_of_strong_limit _ _ (fourierProjection Ω hΩ).op _ hlim hg
  rw [norm_sub_rev]
  exact he
/-- One strict initial gap gives a single strict constant valid uniformly on the entire hull. -/
theorem exists_uniform_bump_projection_hull_gap {d : ℕ} {δ r : ℝ}
    (Ω : Set (Euclidean d)) (hΩ : MeasurableSet Ω) (hfin : volume Ω ≠ ⊤)
    (Γ : SeparatedConfiguration d δ) (hδ : 0 < δ) (hr : 2 * r < δ)
    (b : SchwartzMap (Euclidean d) ℂ) (hs : ∀ x, r ≤ ‖x‖ → b x = 0)
    (hn : ‖b.toLp 2 volume‖ = 1)
    (hgap : ‖(fourierProjection Ω hΩ).op -
      (isometryRangeProjection (bumpSynthesis Γ.separated hr b hs hn)).op‖ < 1) :
    ∃ γ : ℝ, 0 ≤ γ ∧ γ < 1 ∧ ∀ Δ : SeparatedConfiguration d δ,
      Δ ∈ SeparatedConfiguration.hull Γ →
      ‖(fourierProjection Ω hΩ).op -
        (isometryRangeProjection (bumpSynthesis Δ.separated hr b hs hn)).op‖ ≤ γ :=
  ⟨_, norm_nonneg _, hgap, fun _ hΔ => bump_projection_gap_hull_le Ω hΩ hfin Γ hδ hr b hs hn hΔ⟩
/-- A bounded-domain exponential Riesz basis supplies an actual uniform strict bump gap on its hull. -/
theorem exists_riesz_basis_uniform_hull_gap {d : ℕ} {Ω Λ : Set (Euclidean d)}
    (hΩ : MeasurableSet Ω) (hb : Bornology.IsBounded Ω)
    (hB : HasExponentialRieszBasis Ω Λ) :
    ∃ (δ r : ℝ), 0 < δ ∧ 0 < r ∧ ∃ (hr : 2 * r < δ)
      (Γ : SeparatedConfiguration d δ) (b : SchwartzMap (Euclidean d) ℂ)
      (hs : ∀ x, r ≤ ‖x‖ → b x = 0) (hn : ‖b.toLp 2 volume‖ = 1),
      Γ.carrier = Λ ∧ HasCompactSupport b ∧
      (∀ x, (b x).im = 0 ∧ 0 ≤ (b x).re) ∧
      ∃ γ : ℝ, 0 ≤ γ ∧ γ < 1 ∧ ∀ Δ : SeparatedConfiguration d δ,
        Δ ∈ SeparatedConfiguration.hull Γ →
        ‖(fourierProjection Ω hΩ).op -
          (isometryRangeProjection (bumpSynthesis Δ.separated hr b hs hn)).op‖ ≤ γ := by
  classical
  obtain ⟨δ, hδ, hΛ⟩ := riesz_frequencies_separated hΩ hb hB
  obtain ⟨r, hr, hrδ, b, hbs, hn, hp, hz, c, hc, hl⟩ := exists_bump_fourier_lower hb hδ
  let Γ : SeparatedConfiguration d δ := ⟨Λ, hΛ.isClosed hδ, hΛ⟩
  let V := bumpSynthesis Γ.separated hrδ b hz hn
  have hV : ∀ i : Λ, V (lp.single 2 i 1) =
      translationL2 (-(i : Euclidean d)) (b.toLp 2 volume) := by
    intro i
    exact orthonormalSynthesis_single (translated_bumps_orthonormal Γ.separated hrδ b hz hn) i
  obtain ⟨S, hS⟩ := hB
  have hgap := initial_bump_gap hΩ b V hV S hS hc hl
  refine ⟨δ, r, hδ, hr, hrδ, Γ, b, hz, hn, rfl, hbs, hp, ?_⟩
  exact exists_uniform_bump_projection_hull_gap Ω hΩ hb.measure_lt_top.ne Γ hδ hrδ b hz hn hgap
end RieszEuclidean
