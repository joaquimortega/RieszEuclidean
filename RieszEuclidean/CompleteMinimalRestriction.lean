import RieszEuclidean.CompleteMinimalEntireFourier
import RieszEuclidean.CompleteMinimalEllipsoid
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.OpenPos

noncomputable section

open MeasureTheory
open Classical

namespace RieszEuclidean.CompleteMinimal

/-- Zero extend a domain class, then restrict it to a second domain. -/
def domainToDomain {d : ℕ} (source target : Set (Euclidean d))
    (hsource : MeasurableSet source) : DomainL2 source →ₗ[ℂ] DomainL2 target :=
  (domainRestrictionLM target).comp (domainExtensionLI source hsource).toLinearMap

/-- The transported class is represented by the source indicator times the original class. -/
theorem domainToDomain_coe {d : ℕ} (source target : Set (Euclidean d))
    (hsource : MeasurableSet source) (f : DomainL2 source) :
    (domainToDomain source target hsource f : Euclidean d → ℂ) =ᵐ[volume.restrict target]
      source.indicator f :=
  (domainRestriction_coe target _).trans ((domainExtension_coe source hsource f).filter_mono
    (ae_mono Measure.restrict_le_self))

/-- Restricting to an almost-everywhere smaller domain keeps the original representative. -/
theorem domainToDomain_coe_of_subset_ae {d : ℕ} (source target : Set (Euclidean d))
    (hsource : MeasurableSet source) (htarget : MeasurableSet target)
    (hsubset : target ≤ᵐ[volume] source) (f : DomainL2 source) :
    (domainToDomain source target hsource f : Euclidean d → ℂ) =ᵐ[volume.restrict target] f := by
  have hsub := hsubset.filter_mono (ae_mono (Measure.restrict_le_self (s := target)))
  filter_upwards [domainToDomain_coe source target hsource f, hsub, ae_restrict_mem htarget]
    with x hx hst ht
  exact hx.trans (Set.indicator_of_mem (hst ht) _)

/-- Lifting a class to an almost-everywhere larger domain preserves its ambient zero extension. -/
theorem domainExtension_domainToDomain_of_subset_ae {d : ℕ}
    (source target : Set (Euclidean d)) (hsource : MeasurableSet source)
    (htarget : MeasurableSet target) (hsubset : source ≤ᵐ[volume] target)
    (f : DomainL2 source) :
    domainExtension target htarget (domainToDomain source target hsource f) =
      domainExtension source hsource f := by
  change domainExtension target htarget (domainRestriction target _) = _
  rw [domainExtension_restriction]
  apply (domainCutoff_eq_self_iff target htarget _).mpr
  filter_upwards [domainExtension_coe source hsource f, hsubset] with x hx hst
  intro hnot
  change (domainExtension source hsource f : Euclidean d → ℂ) x = 0
  rw [hx]
  exact Set.indicator_of_not_mem (fun hs => hnot (hst hs)) _

/-- The lift to a larger domain is injective on actual L² classes. -/
theorem domainToDomain_injective_of_subset_ae {d : ℕ}
    (source target : Set (Euclidean d)) (hsource : MeasurableSet source)
    (htarget : MeasurableSet target) (hsubset : source ≤ᵐ[volume] target) :
    Function.Injective (domainToDomain source target hsource) := by
  intro f g hfg
  apply (domainExtensionLI source hsource).injective
  change domainExtension source hsource f = domainExtension source hsource g
  rw [← domainExtension_domainToDomain_of_subset_ae source target hsource htarget hsubset f,
    ← domainExtension_domainToDomain_of_subset_ae source target hsource htarget hsubset g, hfg]

/-- Almost-everywhere inclusion is sufficient to enlarge a physical support set. -/
theorem SupportedOn.mono_ae {d : ℕ} {Ω E F : Set (Euclidean d)} {f : DomainL2 Ω}
    (hf : SupportedOn Ω f E) (hEF : E ≤ᵐ[volume] F) : SupportedOn Ω f F := by
  have hsub := hEF.filter_mono (ae_mono (Measure.restrict_le_self (s := Ω)))
  filter_upwards [hf, hsub] with x hx hEFx
  intro hxF
  exact hx (fun hxE => hxF (hEFx hxE))

/-- A core-supported vector retains its ambient zero extension after restriction
to any domain containing that core up to null sets. -/
theorem domainExtension_domainToDomain_of_supported {d : ℕ}
    (source target E : Set (Euclidean d)) (hsource : MeasurableSet source)
    (htarget : MeasurableSet target) (hE : E ≤ᵐ[volume] target)
    (f : DomainL2 source) (hf : SupportedOn source f E) :
    domainExtension target htarget (domainToDomain source target hsource f) =
      domainExtension source hsource f := by
  change domainExtension target htarget (domainRestriction target _) = _
  rw [domainExtension_restriction]
  apply (domainCutoff_eq_self_iff target htarget _).mpr
  have hs := (ae_restrict_iff' hsource).mp (hf.mono_ae hE)
  filter_upwards [domainExtension_coe source hsource f, hs] with x hx hsx
  intro hnot
  change (domainExtension source hsource f : Euclidean d → ℂ) x = 0
  rw [hx]
  by_cases hsourcex : x ∈ source
  · rw [Set.indicator_of_mem hsourcex]
    exact hsx hsourcex hnot
  · exact Set.indicator_of_not_mem hsourcex _

/-- Restriction to a smaller domain preserves an individual vector's support. -/
theorem SupportedOn.domainToDomain {d : ℕ} {source target E : Set (Euclidean d)}
    (hsource : MeasurableSet source) (htarget : MeasurableSet target)
    (hsubset : target ≤ᵐ[volume] source) {f : DomainL2 source}
    (hf : SupportedOn source f E) :
    SupportedOn target (domainToDomain source target hsource f) E := by
  have hs := hf.filter_mono (ae_mono (Measure.restrict_mono_ae hsubset))
  filter_upwards [domainToDomain_coe_of_subset_ae source target hsource htarget hsubset f, hs]
    with x hx hsx
  intro hnot
  exact hx.trans (hsx hnot)

/-- The same exponential frequencies remain complete after restricting the domain
by an almost-everywhere inclusion. -/
theorem IsCompleteExponential.restrict_domain_ae {d : ℕ}
    (source target : Set (Euclidean d)) (hsource : MeasurableSet source)
    (htarget : MeasurableSet target) (hfinite : volume source ≠ ⊤)
    (hfinite' : volume target ≠ ⊤) (hsubset : target ≤ᵐ[volume] source)
    (Λ : Set (Euclidean d)) (hcomplete : IsCompleteExponential source hfinite Λ) :
    IsCompleteExponential target hfinite' Λ := by
  apply (isCompleteExponential_iff_annihilator target hfinite' Λ).mpr
  intro f hf
  have hzero : domainToDomain target source htarget f = 0 := by
    apply (isCompleteExponential_iff_annihilator source hfinite Λ).mp hcomplete
    intro ξ
    apply (inner_eq_zero_symm (𝕜 := ℂ)).mpr
    rw [← domainEntireFourier_real_inner hsource hfinite]
    have htransform : domainEntireFourier source hsource
        (domainToDomain target source htarget f) = domainEntireFourier target htarget f := by
      unfold domainEntireFourier
      rw [domainExtension_domainToDomain_of_subset_ae target source htarget hsource hsubset f]
    rw [htransform, domainEntireFourier_real_inner htarget hfinite']
    exact (inner_eq_zero_symm (𝕜 := ℂ)).mp (hf ξ)
  apply domainToDomain_injective_of_subset_ae target source htarget hsource hsubset
  exact hzero.trans (map_zero _).symm

/-- Core-supported biorthogonals remain biorthogonal on every intermediate
measurable domain, including almost-everywhere inclusions. -/
theorem biorthogonal_restrict_domain_ae {d : ℕ}
    (source target E : Set (Euclidean d)) (hsource : MeasurableSet source)
    (htarget : MeasurableSet target) (hfinite : volume source ≠ ⊤)
    (hfinite' : volume target ≠ ⊤) (hE : E ≤ᵐ[volume] target)
    (Λ : Set (Euclidean d)) (g : Λ → DomainL2 source)
    (hg : IsBiorthogonal (exponentialFamily source hfinite Λ) g)
    (hs : ∀ ξ, SupportedOn source (g ξ) E) :
    IsBiorthogonal (exponentialFamily target hfinite' Λ)
      (fun ξ => domainToDomain source target hsource (g ξ)) := by
  intro ξ η
  have htransform : domainEntireFourier target htarget
      (domainToDomain source target hsource (g ξ)) = domainEntireFourier source hsource (g ξ) := by
    unfold domainEntireFourier
    rw [domainExtension_domainToDomain_of_supported source target E hsource htarget hE (g ξ) (hs ξ)]
  have hinner : inner (𝕜 := ℂ) (domainToDomain source target hsource (g ξ))
      (exponentialL2 target hfinite' η.val) =
      inner (𝕜 := ℂ) (g ξ) (exponentialL2 source hfinite η.val) := by
    rw [← inner_conj_symm, ← domainEntireFourier_real_inner htarget hfinite', htransform,
      domainEntireFourier_real_inner hsource hfinite, inner_conj_symm]
  exact hinner.trans (hg ξ η)

/-- The scope remark for intermediate domains, with both inclusions interpreted
up to volume-null sets and actual restricted supported dual vectors. -/
theorem complete_minimal_on_intermediate_domain_ae {d : ℕ}
    (Ω Ω' E : Set (Euclidean d)) (hΩ : MeasurableSet Ω) (hΩ' : MeasurableSet Ω')
    (hfinite : volume Ω ≠ ⊤) (hE : E ≤ᵐ[volume] Ω') (hsubset : Ω' ≤ᵐ[volume] Ω)
    (Λ : Set (Euclidean d)) (hcomplete : IsCompleteExponential Ω hfinite Λ)
    (g : Λ → DomainL2 Ω) (hg : IsBiorthogonal (exponentialFamily Ω hfinite Λ) g)
    (hs : ∀ ξ, SupportedOn Ω (g ξ) E) :
    ∃ hfinite' : volume Ω' ≠ ⊤,
      IsCompleteExponential Ω' hfinite' Λ ∧ IsMinimalExponential Ω' hfinite' Λ ∧
      IsBiorthogonal (exponentialFamily Ω' hfinite' Λ)
        (fun ξ => domainToDomain Ω Ω' hΩ (g ξ)) ∧
      ∀ ξ, SupportedOn Ω' (domainToDomain Ω Ω' hΩ (g ξ)) E := by
  have hfinite' : volume Ω' ≠ ⊤ :=
    ((measure_mono_ae hsubset).trans_lt hfinite.lt_top).ne
  have hbi := biorthogonal_restrict_domain_ae Ω Ω' E hΩ hΩ' hfinite hfinite' hE Λ g hg hs
  exact ⟨hfinite', hcomplete.restrict_domain_ae Ω Ω' hΩ hΩ' hfinite hfinite' hsubset Λ,
    hbi.isMinimal, hbi, fun ξ => (hs ξ).domainToDomain hΩ hΩ' hsubset⟩

/-- Literal-inclusion form of the intermediate-domain scope remark. -/
theorem complete_minimal_on_intermediate_domain {d : ℕ}
    (Ω Ω' E : Set (Euclidean d)) (hΩ : MeasurableSet Ω) (hΩ' : MeasurableSet Ω')
    (hfinite : volume Ω ≠ ⊤) (hE : E ⊆ Ω') (hsubset : Ω' ⊆ Ω)
    (Λ : Set (Euclidean d)) (hcomplete : IsCompleteExponential Ω hfinite Λ)
    (g : Λ → DomainL2 Ω) (hg : IsBiorthogonal (exponentialFamily Ω hfinite Λ) g)
    (hs : ∀ ξ, SupportedOn Ω (g ξ) E) :
    ∃ hfinite' : volume Ω' ≠ ⊤,
      IsCompleteExponential Ω' hfinite' Λ ∧ IsMinimalExponential Ω' hfinite' Λ ∧
      IsBiorthogonal (exponentialFamily Ω' hfinite' Λ)
        (fun ξ => domainToDomain Ω Ω' hΩ (g ξ)) ∧
      ∀ ξ, SupportedOn Ω' (domainToDomain Ω Ω' hΩ (g ξ)) E :=
  complete_minimal_on_intermediate_domain_ae Ω Ω' E hΩ hΩ' hfinite
    (Filter.Eventually.of_forall hE) (Filter.Eventually.of_forall hsubset) Λ hcomplete g hg hs

/-- The actual domain L² indicator of the part outside a measurable core. -/
def outsideCoreVector {d : ℕ} (Ω E : Set (Euclidean d)) (hfinite : volume Ω ≠ ⊤)
    (hE : MeasurableSet E) : DomainL2 Ω := by
  letI : IsFiniteMeasure (volume.restrict Ω) := ⟨by simpa using hfinite.lt_top⟩
  exact ((memLp_const (1 : ℂ)).indicator hE.compl).toLp (Eᶜ.indicator (fun _ => (1 : ℂ)))

/-- The outside-core vector has its expected indicator representative. -/
theorem outsideCoreVector_coe {d : ℕ} (Ω E : Set (Euclidean d))
    (hfinite : volume Ω ≠ ⊤) (hE : MeasurableSet E) :
    (outsideCoreVector Ω E hfinite hE : Euclidean d → ℂ) =ᵐ[volume.restrict Ω]
      Eᶜ.indicator (fun _ => (1 : ℂ)) := by
  letI : IsFiniteMeasure (volume.restrict Ω) := ⟨by simpa using hfinite.lt_top⟩
  exact MemLp.coeFn_toLp _

/-- Positive volume outside the core makes its indicator a nonzero actual L² vector. -/
theorem outsideCoreVector_ne_zero {d : ℕ} (Ω E : Set (Euclidean d))
    (hΩ : MeasurableSet Ω) (hfinite : volume Ω ≠ ⊤) (hE : MeasurableSet E)
    (hpositive : 0 < volume (Ω \ E)) : outsideCoreVector Ω E hfinite hE ≠ 0 := by
  intro hzero
  have hcoe : Eᶜ.indicator (fun _ : Euclidean d => (1 : ℂ)) =ᵐ[volume.restrict Ω] 0 := by
    have hvec := outsideCoreVector_coe Ω E hfinite hE
    rw [hzero] at hvec
    exact hvec.symm.trans (Lp.coeFn_zero _ _ _)
  have hglobal := (ae_restrict_iff' hΩ).mp hcoe
  have hnot : ∀ᵐ x ∂volume, x ∉ Ω \ E := by
    filter_upwards [hglobal] with x hx
    intro hxset
    have hone : (1 : ℂ) = 0 := by
      simpa only [Set.indicator_of_mem (show x ∈ Eᶜ from hxset.2), Pi.zero_apply]
        using hx hxset.1
    exact one_ne_zero hone
  have hmeasure : volume (Ω \ E) = 0 := by
    simpa only [Classical.not_not, Set.setOf_mem_eq] using ae_iff.mp hnot
  exact hpositive.ne' hmeasure

/-- Every vector supported on the core is orthogonal to the outside-core indicator. -/
theorem inner_outsideCoreVector_eq_zero {d : ℕ} (Ω E : Set (Euclidean d))
    (hfinite : volume Ω ≠ ⊤) (hE : MeasurableSet E) (f : DomainL2 Ω)
    (hf : SupportedOn Ω f E) :
    inner (𝕜 := ℂ) (outsideCoreVector Ω E hfinite hE) f = 0 := by
  rw [L2.inner_def]
  apply integral_eq_zero_of_ae
  filter_upwards [outsideCoreVector_coe Ω E hfinite hE, hf] with x hx hfx
  by_cases hxE : x ∈ E
  · rw [hx, Set.indicator_of_not_mem (by simpa using hxE)]
    exact inner_zero_left _
  · rw [hfx hxE]
    exact inner_zero_right _

/-- A dual family supported on a core cannot be complete on a domain with a
positive-volume part outside that core. -/
theorem supported_family_not_complete {d : ℕ} {ι : Type*}
    (Ω E : Set (Euclidean d)) (hΩ : MeasurableSet Ω) (hfinite : volume Ω ≠ ⊤)
    (hE : MeasurableSet E) (hpositive : 0 < volume (Ω \ E))
    (g : ι → DomainL2 Ω) (hs : ∀ i, SupportedOn Ω (g i) E) : ¬ IsComplete g := by
  intro hcomplete
  have hzero := (isComplete_iff_annihilator g).mp hcomplete
    (outsideCoreVector Ω E hfinite hE)
    (fun i => inner_outsideCoreVector_eq_zero Ω E hfinite hE (g i) (hs i))
  exact outsideCoreVector_ne_zero Ω E hΩ hfinite hE hpositive hzero

/-- An open domain properly containing the interior of a closed core has positive
volume outside the core. Convexity is unnecessary for this implication. -/
theorem volume_outside_closed_core_pos {d : ℕ} (Ω E : Set (Euclidean d))
    (hΩ : IsOpen Ω) (hE : IsClosed E) (hproper : interior E ⊂ Ω) :
    0 < volume (Ω \ E) := by
  have hnot : ¬ Ω ⊆ E := by
    intro hsubset
    have hinterior : Ω ⊆ interior E := hΩ.subset_interior_iff.mpr hsubset
    exact hproper.ne (Set.Subset.antisymm hproper.le hinterior)
  obtain ⟨x, hxΩ, hxE⟩ := Set.not_subset.mp hnot
  exact (hΩ.sdiff hE).measure_pos volume ⟨x, hxΩ, hxE⟩

/-- Closed-core form of the noncompleteness part of the scope remark. -/
theorem supported_family_not_complete_of_proper_closed_core {d : ℕ} {ι : Type*}
    (Ω E : Set (Euclidean d)) (hΩ : IsOpen Ω) (hfinite : volume Ω ≠ ⊤)
    (hE : IsClosed E) (hproper : interior E ⊂ Ω)
    (g : ι → DomainL2 Ω) (hs : ∀ i, SupportedOn Ω (g i) E) : ¬ IsComplete g :=
  supported_family_not_complete Ω E hΩ.measurableSet hfinite hE.measurableSet
    (volume_outside_closed_core_pos Ω E hΩ hE hproper) g hs

/-- In particular, duals supported on a proper inscribed closed ellipsoid are
incomplete in the larger open domain. -/
theorem ellipsoid_supported_duals_not_complete {d : ℕ} {ι : Type*}
    (Ω E : Set (Euclidean d)) (hΩ : IsOpen Ω) (hfinite : volume Ω ≠ ⊤)
    (hE : IsEllipsoid E) (hproper : interior E ⊂ Ω)
    (g : ι → DomainL2 Ω) (hs : ∀ i, SupportedOn Ω (g i) E) : ¬ IsComplete g :=
  supported_family_not_complete_of_proper_closed_core Ω E hΩ hfinite
    hE.isCompact.isClosed hproper g hs

end RieszEuclidean.CompleteMinimal
