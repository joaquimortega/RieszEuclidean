import RieszEuclidean.CompleteMinimalDomainNormalization
import RieszEuclidean.CompleteMinimalAffine
import RieszEuclidean.CompleteMinimalInterval
import RieszEuclidean.CompleteMinimalAssembly
import Mathlib.Topology.Compactness.SigmaCompact

/-! Geometric assembly of the complete-minimal theorem. The normalized-domain
existence premise is explicit until the analytic construction discharges it. -/

noncomputable section
open MeasureTheory Set Metric

namespace RieszEuclidean.CompleteMinimal

/-- Finite intersections with compact sets give the local-finiteness convention
used by the affine transport theorem. -/
theorem locallyFiniteSet_of_finite_compact_intersections {d : ℕ}
    {Λ : Set (Euclidean d)}
    (hΛ : ∀ K : Set (Euclidean d), IsCompact K → (Λ ∩ K).Finite) :
    IsLocallyFiniteSet Λ := by
  intro x
  refine ⟨ball x 1, ball_mem_nhds x zero_lt_one, ?_⟩
  exact (hΛ (closedBall x 1) (isCompact_closedBall x 1)).subset
    (inter_subset_inter_right Λ ball_subset_closedBall)

/-- A locally finite set is a locally finite family of its singleton points. -/
theorem IsLocallyFiniteSet.singletons {X : Type*} [TopologicalSpace X]
    {Λ : Set X} (hΛ : IsLocallyFiniteSet Λ) : LocallyFinite (fun ξ : Λ => ({ξ.val} : Set X)) := by
  intro x
  obtain ⟨U, hU, hfinite⟩ := hΛ x
  refine ⟨U, hU, ?_⟩
  have hpre : (((↑) : Λ → X) ⁻¹' (Λ ∩ U)).Finite :=
    hfinite.preimage (fun _ _ _ _ heq => Subtype.coe_injective heq)
  exact hpre.subset (by
    intro ξ hξ
    obtain ⟨y, hy, hyU⟩ := hξ
    rw [mem_singleton_iff] at hy
    subst y
    exact ⟨ξ.property, hyU⟩)

/-- Local finiteness implies finite intersections with compact sets. -/
theorem IsLocallyFiniteSet.finite_inter_compact {X : Type*} [TopologicalSpace X]
    {Λ K : Set X} (hΛ : IsLocallyFiniteSet Λ) (hK : IsCompact K) : (Λ ∩ K).Finite := by
  have hfin := hΛ.singletons.finite_nonempty_inter_compact hK
  have heq : ((↑) : Λ → X) '' {ξ : Λ | (({ξ.val} : Set X) ∩ K).Nonempty} = Λ ∩ K := by
    ext x
    simp [and_comm]
  rw [← heq]
  exact hfin.image _

/-- On a sigma-compact space, a locally finite frequency set is countable. -/
theorem IsLocallyFiniteSet.countable {X : Type*} [TopologicalSpace X] [SigmaCompactSpace X]
    {Λ : Set X} (hΛ : IsLocallyFiniteSet Λ) : Λ.Countable := by
  have h := hΛ.singletons.countable_univ (fun ξ => singleton_nonempty ξ.val)
  simpa only [image_univ, Subtype.range_coe] using h.image ((↑) : Λ → X)

/-- The geometric part of the source main theorem. Existence on normalized
John domains in dimensions at least two is the sole premise of this helper;
the one-dimensional case is already proved by the interval Fourier basis. -/
theorem complete_minimal_from_normalized_domains {d : ℕ} (hd : 1 ≤ d)
    (normalized : 2 ≤ d → ∀ (D : Set (Euclidean d))
      (_hne : D.Nonempty) (hbounded : Bornology.IsBounded D)
      (_hopen : IsOpen D) (_hconvex : Convex ℝ D),
      IsJohnEllipsoid (closure D) (closedBall (0 : Euclidean d) 1) →
      ball (0 : Euclidean d) 1 ⊆ D →
      (∀ t : Euclidean d, (fun x => t + x) '' closedBall 0 1 ⊆ closure D → t = 0) →
      ∃ Λ : Set (Euclidean d), IsLocallyFiniteSet Λ ∧
        IsCompleteExponential D hbounded.measure_lt_top.ne Λ ∧
        ∃ g : Λ → DomainL2 D,
          IsBiorthogonal (exponentialFamily D hbounded.measure_lt_top.ne Λ) g ∧
          ∀ ξ, SupportedOn D (g ξ) (closedBall 0 1))
    {Ω : Set (Euclidean d)} (hne : Ω.Nonempty) (hbounded : Bornology.IsBounded Ω)
    (hopen : IsOpen Ω) (hconvex : Convex ℝ Ω) :
    ∃ Λ : Set (Euclidean d), IsLocallyFiniteSet Λ ∧
      IsCompleteExponential Ω hbounded.measure_lt_top.ne Λ ∧
      IsMinimalExponential Ω hbounded.measure_lt_top.ne Λ ∧
      ∃ E : Set (Euclidean d), IsJohnEllipsoid (closure Ω) E ∧
        ∃ g : Λ → DomainL2 Ω,
          IsBiorthogonal (exponentialFamily Ω hbounded.measure_lt_top.ne Λ) g ∧
          ∀ ξ, SupportedOn Ω (g ξ) E := by
  by_cases hone : d = 1
  · subst d
    obtain ⟨Λ, hΛ, hcomplete, hminimal, E, hE, g, hg, hs⟩ :=
      complete_minimal_dim_one hne hbounded hopen hconvex
    exact ⟨Λ, locallyFiniteSet_of_finite_compact_intersections hΛ,
      hcomplete, hminimal, E, hE, g, hg, hs⟩
  · obtain ⟨a, A, hJohn, hneD, hboundedD, hopenD, hconvexD, hJohnD, hballD, htranslateD⟩ :=
      exists_john_normalization hne hbounded hopen hconvex
    obtain ⟨Λ, hlocal, hcomplete, g, hg, hs⟩ := normalized (by omega)
      (normalizedDomain Ω a A) hneD hboundedD hopenD hconvexD hJohnD hballD htranslateD
    have htransport := complete_minimal_supported_affineImage a A
      (normalizedDomain Ω a A) Λ (closedBall 0 1) hboundedD.measure_lt_top.ne
      hcomplete g hg hs hlocal
    dsimp only at htransport
    have hpackage : ∃ hfin : volume ((planeAffine a A) '' normalizedDomain Ω a A) ≠ ⊤,
        IsCompleteExponential ((planeAffine a A) '' normalizedDomain Ω a A) hfin
          ((affineFrequency A.symm) '' Λ) ∧
        IsMinimalExponential ((planeAffine a A) '' normalizedDomain Ω a A) hfin
          ((affineFrequency A.symm) '' Λ) ∧
        IsLocallyFiniteSet ((affineFrequency A.symm) '' Λ) ∧
        ∃ w : (affineFrequency A.symm) '' Λ →
            DomainL2 ((planeAffine a A) '' normalizedDomain Ω a A),
          IsBiorthogonal (exponentialFamily _ hfin ((affineFrequency A.symm) '' Λ)) w ∧
          ∀ η, SupportedOn _ (w η) (closedEllipsoid a A) := ⟨_, htransport⟩
    rw [normalizedDomain_image] at hpackage
    obtain ⟨_hfin, hc, hm, hl, w, hw, hws⟩ := hpackage
    exact ⟨(affineFrequency A.symm) '' Λ, hl, hc, hm,
      closedEllipsoid a A, hJohn, w, hw, hws⟩

/-- Concrete spherical analytic packages on normalized John domains assemble into
the full geometric conclusion. The package premise is retained explicitly until
its analytic construction is discharged. -/
theorem complete_minimal_from_normalized_sphere_inputs {d : ℕ} (hd : 1 ≤ d)
    (radius : ℕ → ℝ) (hzero : radius 0 = 0)
    (hpositive : ∀ j, 0 < j → 0 < radius j) (hstrict : StrictMono radius)
    (hescape : Filter.Tendsto radius Filter.atTop Filter.atTop)
    (inputs : 2 ≤ d → ∀ (D : Set (Euclidean d))
      (_hne : D.Nonempty) (hbounded : Bornology.IsBounded D)
      (hopen : IsOpen D) (_hconvex : Convex ℝ D),
      IsJohnEllipsoid (closure D) (closedBall (0 : Euclidean d) 1) →
      ball (0 : Euclidean d) 1 ⊆ D →
      (∀ t : Euclidean d, (fun x => t + x) '' closedBall 0 1 ⊆ closure D → t = 0) →
      SphereAnalyticInputs D hopen.measurableSet hbounded.measure_lt_top.ne radius
        (closedBall 0 1))
    {Ω : Set (Euclidean d)} (hne : Ω.Nonempty) (hbounded : Bornology.IsBounded Ω)
    (hopen : IsOpen Ω) (hconvex : Convex ℝ Ω) :
    ∃ Λ : Set (Euclidean d), IsLocallyFiniteSet Λ ∧
      IsCompleteExponential Ω hbounded.measure_lt_top.ne Λ ∧
      IsMinimalExponential Ω hbounded.measure_lt_top.ne Λ ∧
      ∃ E : Set (Euclidean d), IsJohnEllipsoid (closure Ω) E ∧
        ∃ g : Λ → DomainL2 Ω,
          IsBiorthogonal (exponentialFamily Ω hbounded.measure_lt_top.ne Λ) g ∧
          ∀ ξ, SupportedOn Ω (g ξ) E := by
  apply complete_minimal_from_normalized_domains hd ?_ hne hbounded hopen hconvex
  intro hd2 D hneD hboundedD hopenD hconvexD hJohnD hballD htranslateD
  obtain ⟨Λ, _hspheres, hcomplete, _hminimal, hlocal, g, hg, hs⟩ :=
    complete_minimal_exponentials_of_sphere_analytic_inputs hd D hopenD.measurableSet
      hboundedD hboundedD.measure_lt_top.ne radius hzero hpositive hstrict hescape
      (closedBall 0 1) (inputs hd2 D hneD hboundedD hopenD hconvexD hJohnD hballD htranslateD)
  exact ⟨Λ, hlocal, hcomplete, g, hg, hs⟩

end RieszEuclidean.CompleteMinimal
