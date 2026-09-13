import RieszEuclidean.DomainRestriction
noncomputable section
open MeasureTheory Set
namespace RieszEuclidean
/-- Extend a domain L² class by zero to ambient Euclidean space. -/
def domainExtension {d : ℕ} (Ω : Set (Euclidean d)) (hΩ : MeasurableSet Ω)
    (f : DomainL2 Ω) : FullL2 d :=
  ((memLp_indicator_iff_restrict hΩ).mpr (Lp.memLp f)).toLp (Ω.indicator f)
/-- The extension has the zero-extended representative. -/
theorem domainExtension_coe {d : ℕ} (Ω : Set (Euclidean d)) (hΩ : MeasurableSet Ω)
    (f : DomainL2 Ω) : (domainExtension Ω hΩ f : Euclidean d → ℂ) =ᵐ[volume] Ω.indicator f :=
  MemLp.coeFn_toLp _
/-- Zero extension preserves the L² norm. -/
theorem domainExtension_norm {d : ℕ} (Ω : Set (Euclidean d)) (hΩ : MeasurableSet Ω)
    (f : DomainL2 Ω) : ‖domainExtension Ω hΩ f‖ = ‖f‖ := by
  rw [Lp.norm_def, Lp.norm_def, eLpNorm_congr_ae (domainExtension_coe Ω hΩ f),
    eLpNorm_indicator_eq_eLpNorm_restrict hΩ]
/-- Restricting an extension gives the original domain class. -/
theorem domainRestriction_extension {d : ℕ} (Ω : Set (Euclidean d)) (hΩ : MeasurableSet Ω)
    (f : DomainL2 Ω) : domainRestriction Ω (domainExtension Ω hΩ f) = f := by
  apply Lp.ext
  have he := (domainExtension_coe Ω hΩ f).filter_mono
    (ae_mono (Measure.restrict_le_self (s := Ω)))
  filter_upwards [domainRestriction_coe Ω (domainExtension Ω hΩ f), he, ae_restrict_mem hΩ]
    with x h1 h2 hx
  rw [h1, h2, indicator_of_mem hx]
/-- Extending a restriction gives precisely the domain cutoff. -/
theorem domainExtension_restriction {d : ℕ} (Ω : Set (Euclidean d)) (hΩ : MeasurableSet Ω)
    (f : FullL2 d) : domainExtension Ω hΩ (domainRestriction Ω f) = domainCutoff Ω hΩ f := by
  apply Lp.ext
  have hr := (ae_restrict_iff' hΩ).mp (domainRestriction_coe Ω f)
  filter_upwards [domainExtension_coe Ω hΩ (domainRestriction Ω f),
    domainCutoff_coe Ω hΩ f, hr] with x h1 h2 h3
  rw [h1, h2]
  by_cases hx : x ∈ Ω
  · simpa only [indicator_of_mem hx] using h3 hx
  · simp only [indicator_of_not_mem hx]
/-- Zero extension is a complex linear isometry. -/
def domainExtensionLI {d : ℕ} (Ω : Set (Euclidean d)) (hΩ : MeasurableSet Ω) :
    DomainL2 Ω →ₗᵢ[ℂ] FullL2 d where
  toFun := domainExtension Ω hΩ
  map_add' f g := by
    apply Lp.ext
    have ha := (ae_restrict_iff' hΩ).mp (Lp.coeFn_add f g)
    filter_upwards [domainExtension_coe Ω hΩ (f + g), domainExtension_coe Ω hΩ f,
      domainExtension_coe Ω hΩ g, Lp.coeFn_add (domainExtension Ω hΩ f) (domainExtension Ω hΩ g), ha]
      with x h1 h2 h3 h4 h5
    rw [h1, h4]
    simp only [Pi.add_apply, h2, h3]
    by_cases hx : x ∈ Ω
    · simpa only [indicator_of_mem hx, Pi.add_apply] using h5 hx
    · simp only [indicator_of_not_mem hx, add_zero]
  map_smul' c f := by
    apply Lp.ext
    have ha := (ae_restrict_iff' hΩ).mp (Lp.coeFn_smul c f)
    filter_upwards [domainExtension_coe Ω hΩ (c • f), domainExtension_coe Ω hΩ f,
      Lp.coeFn_smul c (domainExtension Ω hΩ f), ha] with x h1 h2 h3 h4
    simp only [RingHom.id_apply, h1, h3, Pi.smul_apply, h2]
    by_cases hx : x ∈ Ω
    · simpa only [indicator_of_mem hx, Pi.smul_apply] using h4 hx
    · simp only [indicator_of_not_mem hx, smul_zero]
  norm_map' := domainExtension_norm Ω hΩ
/-- Zero extension has exactly the range of the domain projection. -/
theorem domainExtension_range {d : ℕ} (Ω : Set (Euclidean d)) (hΩ : MeasurableSet Ω) :
    LinearMap.range (domainExtensionLI Ω hΩ).toLinearMap = (domainProjection Ω hΩ).range := by
  ext f
  constructor
  · rintro ⟨g, rfl⟩
    apply ((domainProjection Ω hΩ).mem_range_iff _).mpr
    change domainCutoff Ω hΩ (domainExtension Ω hΩ g) = domainExtension Ω hΩ g
    rw [← domainExtension_restriction, domainRestriction_extension]
  · intro hf
    refine ⟨domainRestriction Ω f, ?_⟩
    change domainExtension Ω hΩ (domainRestriction Ω f) = f
    rw [domainExtension_restriction]
    exact ((domainProjection Ω hΩ).mem_range_iff f).mp hf
end RieszEuclidean
