import RieszEuclidean.CutoffProjection
noncomputable section
open MeasureTheory
namespace RieszEuclidean
/-- Restrict an ambient L² class to the domain measure. -/
def domainRestriction {d : ℕ} (Ω : Set (Euclidean d)) (f : FullL2 d) : DomainL2 Ω :=
  ((Lp.memLp f).mono_measure Measure.restrict_le_self).toLp f
/-- Restriction keeps the same representative on the restricted measure. -/
theorem domainRestriction_coe {d : ℕ} (Ω : Set (Euclidean d)) (f : FullL2 d) :
    (domainRestriction Ω f : Euclidean d → ℂ) =ᵐ[volume.restrict Ω] f :=
  MemLp.coeFn_toLp _
/-- Restriction is norm decreasing. -/
theorem domainRestriction_norm_le {d : ℕ} (Ω : Set (Euclidean d)) (f : FullL2 d) :
    ‖domainRestriction Ω f‖ ≤ ‖f‖ := by
  rw [Lp.norm_def, Lp.norm_def]
  rw [eLpNorm_congr_ae (domainRestriction_coe Ω f)]
  exact ENNReal.toReal_mono (Lp.memLp f).eLpNorm_ne_top
    (eLpNorm_mono_measure f Measure.restrict_le_self)
/-- Restriction is a complex linear map. -/
def domainRestrictionLM {d : ℕ} (Ω : Set (Euclidean d)) : FullL2 d →ₗ[ℂ] DomainL2 Ω where
  toFun := domainRestriction Ω
  map_add' f g := by
    apply Lp.ext
    have ha := (Lp.coeFn_add f g).filter_mono (ae_mono (Measure.restrict_le_self (s := Ω)))
    filter_upwards [domainRestriction_coe Ω (f + g), domainRestriction_coe Ω f,
      domainRestriction_coe Ω g, Lp.coeFn_add (domainRestriction Ω f) (domainRestriction Ω g), ha]
      with x h1 h2 h3 h4 h5
    simp only [h1, h4, Pi.add_apply, h2, h3, h5]
  map_smul' c f := by
    apply Lp.ext
    have ha := (Lp.coeFn_smul c f).filter_mono (ae_mono (Measure.restrict_le_self (s := Ω)))
    filter_upwards [domainRestriction_coe Ω (c • f), domainRestriction_coe Ω f,
      Lp.coeFn_smul c (domainRestriction Ω f), ha] with x h1 h2 h3 h4
    simp only [h1, h3, Pi.smul_apply, h2, h4, RingHom.id_apply]
/-- Restriction as a bounded linear map of norm at most one. -/
def domainRestrictionCLM {d : ℕ} (Ω : Set (Euclidean d)) : FullL2 d →L[ℂ] DomainL2 Ω :=
  (domainRestrictionLM Ω).mkContinuous 1 (fun f => by simpa using domainRestriction_norm_le Ω f)
end RieszEuclidean
