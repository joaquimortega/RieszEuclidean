import RieszEuclidean.CompleteMinimalMain
import RieszEuclidean.CompleteMinimalRestriction
import Mathlib.Analysis.Convex.Measure

/-! The domain scope of the selected exponential system, including almost-everywhere
intermediate domains and incompleteness of proper ellipsoid-supported dual families. -/

noncomputable section
open MeasureTheory Set

namespace RieszEuclidean.CompleteMinimal

/-- A full-dimensional closed ellipsoid agrees almost everywhere with its interior. -/
theorem IsEllipsoid.ae_eq_interior {d : ℕ} {E : Set (Euclidean d)} (hE : IsEllipsoid E) :
    E =ᵐ[volume] interior E :=
  (interior_ae_eq_of_null_frontier (hE.convex.addHaar_frontier volume)).symm

/-- The closed ellipsoid is almost everywhere contained in its open interior. -/
theorem IsEllipsoid.ae_subset_interior {d : ℕ} {E : Set (Euclidean d)}
    (hE : IsEllipsoid E) : E ≤ᵐ[volume] interior E := by
  filter_upwards [hE.ae_eq_interior] with x hx hEx
  rwa [← hx]

/-- The interior of a John ellipsoid of the closure of an open convex domain
is contained in that domain. -/
theorem IsJohnEllipsoid.interior_subset_domain {d : ℕ} {Ω E : Set (Euclidean d)}
    (hE : IsJohnEllipsoid (closure Ω) E) (hne : Ω.Nonempty)
    (hopen : IsOpen Ω) (hconvex : Convex ℝ Ω) : interior E ⊆ Ω := by
  simpa only [interior_closure_open_convex hne hopen hconvex] using interior_mono hE.subset

/-- The same frequencies are complete and minimal on every measurable intermediate
domain between the open John ellipsoid and the original domain, with inclusions
up to null sets. The duals are the actual restricted original vectors. -/
theorem john_supported_complete_scope_ae {d : ℕ}
    (Ω E : Set (Euclidean d)) (hΩ : MeasurableSet Ω) (hfinite : volume Ω ≠ ⊤)
    (hE : IsEllipsoid E) (Λ : Set (Euclidean d))
    (hcomplete : IsCompleteExponential Ω hfinite Λ)
    (g : Λ → DomainL2 Ω) (hg : IsBiorthogonal (exponentialFamily Ω hfinite Λ) g)
    (hs : ∀ ξ, SupportedOn Ω (g ξ) E) :
    (∀ (D : Set (Euclidean d)), MeasurableSet D →
      interior E ≤ᵐ[volume] D → D ≤ᵐ[volume] Ω →
      ∃ hD : volume D ≠ ⊤,
        IsCompleteExponential D hD Λ ∧ IsMinimalExponential D hD Λ ∧
        IsBiorthogonal (exponentialFamily D hD Λ)
          (fun ξ => domainToDomain Ω D hΩ (g ξ)) ∧
        ∀ ξ, SupportedOn D (domainToDomain Ω D hΩ (g ξ)) E) ∧
    (0 < volume (Ω \ E) → ¬ IsComplete g) := by
  refine ⟨?_, ?_⟩
  · intro D hD hED hDΩ
    exact complete_minimal_on_intermediate_domain_ae Ω D E hΩ hD hfinite
      (hE.ae_subset_interior.trans hED) hDΩ Λ hcomplete g hg hs
  · intro hpositive
    exact supported_family_not_complete Ω E hΩ hfinite hE.isCompact.isClosed.measurableSet
      hpositive g hs

/-- Literal inclusions suffice for the same-frequency scope corollary. Only the
open ellipsoid must lie in the intermediate domain. -/
theorem john_supported_complete_scope {d : ℕ}
    (Ω E D : Set (Euclidean d)) (hΩ : MeasurableSet Ω) (hD : MeasurableSet D)
    (hfinite : volume Ω ≠ ⊤) (hE : IsEllipsoid E)
    (hED : interior E ⊆ D) (hDΩ : D ⊆ Ω) (Λ : Set (Euclidean d))
    (hcomplete : IsCompleteExponential Ω hfinite Λ)
    (g : Λ → DomainL2 Ω) (hg : IsBiorthogonal (exponentialFamily Ω hfinite Λ) g)
    (hs : ∀ ξ, SupportedOn Ω (g ξ) E) :
    ∃ hfiniteD : volume D ≠ ⊤,
      IsCompleteExponential D hfiniteD Λ ∧ IsMinimalExponential D hfiniteD Λ ∧
      IsBiorthogonal (exponentialFamily D hfiniteD Λ)
        (fun ξ => domainToDomain Ω D hΩ (g ξ)) ∧
      ∀ ξ, SupportedOn D (domainToDomain Ω D hΩ (g ξ)) E :=
  (john_supported_complete_scope_ae Ω E hΩ hfinite hE Λ hcomplete g hg hs).1 D hD
    (Filter.Eventually.of_forall hED) (Filter.Eventually.of_forall hDΩ)

/-- Proper inclusion of the open ellipsoid in an open domain forces the original
supported dual family to be incomplete. -/
theorem john_supported_duals_incomplete_of_proper {d : ℕ}
    (Ω E : Set (Euclidean d)) (hΩ : IsOpen Ω) (hfinite : volume Ω ≠ ⊤)
    (hE : IsJohnEllipsoid (closure Ω) E) (hproper : interior E ⊂ Ω)
    {ι : Type*} (g : ι → DomainL2 Ω) (hs : ∀ ξ, SupportedOn Ω (g ξ) E) :
    ¬ IsComplete g :=
  ellipsoid_supported_duals_not_complete Ω E hΩ hfinite hE.isEllipsoid hproper g hs

/-- Existence integration for the manuscript scope remark. Any proved instance of
the main theorem supplies one fixed locally finite frequency set and supported
dual family having all the intermediate-domain properties simultaneously. -/
theorem complete_minimal_scope_of_existence {d : ℕ}
    {Ω : Set (Euclidean d)} (hne : Ω.Nonempty) (hbounded : Bornology.IsBounded Ω)
    (hopen : IsOpen Ω) (hconvex : Convex ℝ Ω)
    (existence : ∃ Λ : Set (Euclidean d), IsLocallyFiniteSet Λ ∧
      IsCompleteExponential Ω hbounded.measure_lt_top.ne Λ ∧
      IsMinimalExponential Ω hbounded.measure_lt_top.ne Λ ∧
      ∃ E : Set (Euclidean d), IsJohnEllipsoid (closure Ω) E ∧
        ∃ g : Λ → DomainL2 Ω,
          IsBiorthogonal (exponentialFamily Ω hbounded.measure_lt_top.ne Λ) g ∧
          ∀ ξ, SupportedOn Ω (g ξ) E) :
    ∃ Λ : Set (Euclidean d), IsLocallyFiniteSet Λ ∧
      IsCompleteExponential Ω hbounded.measure_lt_top.ne Λ ∧
      IsMinimalExponential Ω hbounded.measure_lt_top.ne Λ ∧
      ∃ E : Set (Euclidean d), IsJohnEllipsoid (closure Ω) E ∧ interior E ⊆ Ω ∧
        ∃ g : Λ → DomainL2 Ω,
          IsBiorthogonal (exponentialFamily Ω hbounded.measure_lt_top.ne Λ) g ∧
          (∀ ξ, SupportedOn Ω (g ξ) E) ∧
          (∀ (D : Set (Euclidean d)), MeasurableSet D →
            interior E ≤ᵐ[volume] D → D ≤ᵐ[volume] Ω →
            ∃ hD : volume D ≠ ⊤,
              IsCompleteExponential D hD Λ ∧ IsMinimalExponential D hD Λ ∧
              IsBiorthogonal (exponentialFamily D hD Λ)
                (fun ξ => domainToDomain Ω D hopen.measurableSet (g ξ)) ∧
              ∀ ξ, SupportedOn D (domainToDomain Ω D hopen.measurableSet (g ξ)) E) ∧
          (0 < volume (Ω \ E) → ¬ IsComplete g) ∧
          (interior E ⊂ Ω → ¬ IsComplete g) := by
  obtain ⟨Λ, hlocal, hcomplete, hminimal, E, hJohn, g, hg, hs⟩ := existence
  have hscope := john_supported_complete_scope_ae Ω E hopen.measurableSet
    hbounded.measure_lt_top.ne hJohn.isEllipsoid Λ hcomplete g hg hs
  exact ⟨Λ, hlocal, hcomplete, hminimal, E, hJohn,
    hJohn.interior_subset_domain hne hopen hconvex, g, hg, hs, hscope.1, hscope.2,
    fun hproper => john_supported_duals_incomplete_of_proper Ω E hopen
      hbounded.measure_lt_top.ne hJohn hproper g hs⟩

end RieszEuclidean.CompleteMinimal
