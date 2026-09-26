import RieszEuclidean.CompleteMinimalEllipsoid

/-! John coordinates for actual bounded open convex domains. -/

noncomputable section
open Set Metric

namespace RieszEuclidean.CompleteMinimal

/-- The inverse affine coordinates associated with an ellipsoid. -/
def normalizedDomain {d : ℕ} (Ω : Set (Euclidean d)) (a : Euclidean d)
    (A : Euclidean d ≃L[ℝ] Euclidean d) : Set (Euclidean d) :=
  (planeAffine (-A.symm a) A.symm) '' Ω

theorem normalizedDomain_image {d : ℕ} (Ω : Set (Euclidean d)) (a : Euclidean d)
    (A : Euclidean d ≃L[ℝ] Euclidean d) :
    (planeAffine a A) '' normalizedDomain Ω a A = Ω := by
  rw [normalizedDomain, planeAffine_inverse, image_image]
  simp only [Function.comp_def, MeasurableEquiv.apply_symm_apply, image_id']

theorem normalizedDomain_isOpen {d : ℕ} {Ω : Set (Euclidean d)} (hΩ : IsOpen Ω)
    (a : Euclidean d) (A : Euclidean d ≃L[ℝ] Euclidean d) :
    IsOpen (normalizedDomain Ω a A) :=
  (affineHomeomorph (-A.symm a) A.symm).isOpenMap Ω hΩ

theorem normalizedDomain_convex {d : ℕ} {Ω : Set (Euclidean d)} (hΩ : Convex ℝ Ω)
    (a : Euclidean d) (A : Euclidean d ≃L[ℝ] Euclidean d) :
    Convex ℝ (normalizedDomain Ω a A) := convex_affine_image hΩ _ _

theorem closure_normalizedDomain {d : ℕ} (Ω : Set (Euclidean d)) (a : Euclidean d)
    (A : Euclidean d ≃L[ℝ] Euclidean d) :
    closure (normalizedDomain Ω a A) = normalizedDomain (closure Ω) a A :=
  ((affineHomeomorph (-A.symm a) A.symm).image_closure Ω).symm

theorem normalizedDomain_isBounded {d : ℕ} {Ω : Set (Euclidean d)}
    (hΩ : Bornology.IsBounded Ω) (a : Euclidean d)
    (A : Euclidean d ≃L[ℝ] Euclidean d) : Bornology.IsBounded (normalizedDomain Ω a A) := by
  have hc : IsCompact (closure (normalizedDomain Ω a A)) := by
    rw [closure_normalizedDomain]
    exact hΩ.isCompact_closure.image (affineHomeomorph (-A.symm a) A.symm).continuous
  exact hc.isBounded.subset subset_closure

theorem interior_closure_open_convex {d : ℕ} {Ω : Set (Euclidean d)}
    (hne : Ω.Nonempty) (hopen : IsOpen Ω) (hconvex : Convex ℝ Ω) :
    interior (closure Ω) = Ω := by
  simpa only [hopen.interior_eq] using
    hconvex.interior_closure_eq_interior_of_nonempty_interior
      (by simpa only [hopen.interior_eq] using hne)

/-- The source normalization lemma: the actual normalized domain contains the
open unit ball, whose closure is a John ellipsoid with no nonzero contained translate. -/
theorem exists_john_normalization {d : ℕ} {Ω : Set (Euclidean d)}
    (hne : Ω.Nonempty) (hbounded : Bornology.IsBounded Ω)
    (hopen : IsOpen Ω) (hconvex : Convex ℝ Ω) :
    ∃ a : Euclidean d, ∃ A : Euclidean d ≃L[ℝ] Euclidean d,
      IsJohnEllipsoid (closure Ω) (closedEllipsoid a A) ∧
      (normalizedDomain Ω a A).Nonempty ∧
      Bornology.IsBounded (normalizedDomain Ω a A) ∧
      IsOpen (normalizedDomain Ω a A) ∧
      Convex ℝ (normalizedDomain Ω a A) ∧
      IsJohnEllipsoid (closure (normalizedDomain Ω a A)) (closedBall 0 1) ∧
      ball 0 1 ⊆ normalizedDomain Ω a A ∧
      ∀ t : Euclidean d, (fun x => t + x) '' closedBall 0 1 ⊆
        closure (normalizedDomain Ω a A) → t = 0 := by
  have hreg := interior_closure_open_convex hne hopen hconvex
  have hKi : (interior (closure Ω)).Nonempty := by rwa [hreg]
  obtain ⟨E, hE⟩ := exists_isJohnEllipsoid hbounded.isCompact_closure hKi
  obtain ⟨a, A, rfl⟩ := hE.isEllipsoid
  have hneD : (normalizedDomain Ω a A).Nonempty := hne.image _
  have hopenD := normalizedDomain_isOpen hopen a A
  have hconvD := normalizedDomain_convex hconvex a A
  have hJD : IsJohnEllipsoid (closure (normalizedDomain Ω a A)) (closedBall 0 1) := by
    rw [closure_normalizedDomain]
    exact hE.normalize
  have hball : ball 0 1 ⊆ normalizedDomain Ω a A := by
    rw [← interior_closure_open_convex hneD hopenD hconvD]
    exact ball_subset_interior_closedBall.trans (interior_mono hJD.subset)
  exact ⟨a, A, hE, hneD, normalizedDomain_isBounded hbounded a A, hopenD, hconvD,
    hJD, hball, fun _ ht => hJD.eq_zero_of_translated_unitBall_subset hconvD.closure ht⟩

end RieszEuclidean.CompleteMinimal
