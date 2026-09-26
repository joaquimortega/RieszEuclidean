import RieszEuclidean.CompleteMinimalPolynomial
import RieszEuclidean.CompleteMinimalSpherePolynomial
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

noncomputable section

namespace RieszEuclidean.CompleteMinimal

/-- Extend a finite independent family to a basis, using only the supplied
available indices in addition to the prescribed ones. -/
theorem exists_finite_basis_extension
    {K V X : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (f : X → V) (s : Finset X) (available : Set X)
    (hs : LinearIndependent K (fun x : ↥s => f x.val))
    (hspan : Submodule.span K (f '' ((s : Set X) ∪ available)) = ⊤) :
    ∃ t : Finset X, s ⊆ t ∧ (t : Set X) ⊆ (s : Set X) ∪ available ∧
      ∃ b : Basis ↥t K V, ∀ x, b x = f x.val := by
  classical
  let allowed : Set X := (s : Set X) ∪ available
  have hsi : Set.InjOn f (s : Set X) := by
    intro x hx y hy hxy
    exact congrArg Subtype.val (hs.injective (show f (⟨x, hx⟩ : ↥s) =
      f (⟨y, hy⟩ : ↥s) from hxy))
  have himg : LinearIndepOn K id (f '' (s : Set X)) :=
    (linearIndepOn_iff_image hsi).mp hs
  have hst : f '' (s : Set X) ⊆ f '' allowed :=
    Set.image_mono Set.subset_union_left
  let b := Basis.extendLe himg hst (le_of_eq hspan.symm)
  let candidates : Set X := allowed ∩ f ⁻¹' Set.range b
  have hsc : (s : Set X) ⊆ candidates := by
    intro x hx
    exact ⟨Or.inl hx, Basis.subset_extendLe himg hst _ ⟨x, hx, rfl⟩⟩
  have hcimage : f '' candidates = Set.range b := by
    apply Set.Subset.antisymm
    · rintro _ ⟨x, hx, rfl⟩
      exact hx.2
    · intro v hv
      obtain ⟨x, hx, hfx⟩ := Basis.extendLe_subset himg hst _ hv
      refine ⟨x, ⟨hx, ?_⟩, hfx⟩
      change f x ∈ Set.range b
      rw [hfx]
      exact hv
  obtain ⟨u, hsu, huc, huimage, huinj⟩ :=
    hsi.exists_subset_injOn_subset_range_eq hsc
  have huimage' : f '' u = Set.range b := huimage.trans hcimage
  have hufinite : u.Finite := by
    letI : Finite (himg.extend hst) := b.linearIndependent.finite_of_isNoetherian
    apply Set.Finite.of_finite_image _ huinj
    rw [huimage']
    exact Set.finite_range b
  let t := hufinite.toFinset
  have htimage : f '' (t : Set X) = Set.range b := by
    simpa [t] using huimage'
  have htind : LinearIndependent K (fun x : ↥t => f x.val) := by
    apply (linearIndepOn_iff_image (show Set.InjOn f (t : Set X) from by
      simpa [t] using huinj)).mpr
    rw [htimage]
    exact b.linearIndependent.linearIndepOn_id
  refine ⟨t, ?_, ?_, Basis.mk htind ?_, ?_⟩
  · simpa [t, ← Finset.coe_subset] using hsu
  · simpa [t, allowed] using huc.trans Set.inter_subset_left
  · have hrange : Set.range (fun x : ↥t => f x.val) = f '' (t : Set X) := by
      ext v
      simp
    rw [hrange, htimage, b.span_eq]
  · intro x
    exact Basis.mk_apply _ _ x

/-- Bounded-degree point evaluations span the dual whenever their common
annihilator consists only of the zero polynomial. -/
theorem boundedPolynomialEvaluation_span_eq_top {d m : ℕ} (points : Set (RealPoint d))
    (hzero : ∀ p : MvPolynomial.restrictTotalDegree (Fin d) ℂ m,
      (∀ x ∈ points, boundedPolynomialEvaluation m x p = 0) → p = 0) :
    Submodule.span ℂ (boundedPolynomialEvaluation m '' points) = ⊤ := by
  apply Submodule.span_eq_top_of_ne_zero
  intro p hp
  have hn : ¬ ∀ x ∈ points, boundedPolynomialEvaluation m x p = 0 :=
    fun h => hp (hzero p h)
  push_neg at hn
  obtain ⟨x, hx, hxp⟩ := hn
  exact ⟨boundedPolynomialEvaluation m x, ⟨x, hx, rfl⟩, hxp⟩

/-- An evaluation basis identifies the polynomial space with its sampled values. -/
theorem boundedSampling_bijective_of_basis {d m : ℕ} (t : Finset (RealPoint d))
    (b : Basis ↥t ℂ (Module.Dual ℂ (MvPolynomial.restrictTotalDegree (Fin d) ℂ m)))
    (hb : ∀ x, b x = boundedPolynomialEvaluation m x.val) :
    Function.Bijective (boundedSampling m (fun x : ↥t => x.val)) := by
  let e := (Module.evalEquiv ℂ (MvPolynomial.restrictTotalDegree (Fin d) ℂ m)).trans
    b.dualBasis.equivFun
  have he : ⇑e = boundedSampling m (fun x : ↥t => x.val) := by
    funext p x
    simp [e, Basis.dualBasis_equivFun, hb, Module.evalEquiv_apply,
      Module.Dual.eval_apply, boundedSampling]
  rw [← he]
  exact e.bijective

/-- Conditional interpolation-basis extension. Its spanning hypothesis can be
supplied by a separate polynomial annihilator theorem. -/
theorem exists_bounded_interpolation_extension {d m : ℕ} (s : Finset (RealPoint d))
    (available : Set (RealPoint d))
    (hs : LinearIndependent ℂ (fun x : ↥s => boundedPolynomialEvaluation m x.val))
    (hspan : Submodule.span ℂ
      (boundedPolynomialEvaluation m '' ((s : Set (RealPoint d)) ∪ available)) = ⊤) :
    ∃ t : Finset (RealPoint d), s ⊆ t ∧
      (t : Set (RealPoint d)) ⊆ (s : Set (RealPoint d)) ∪ available ∧
      Function.Bijective (boundedSampling m (fun x : ↥t => x.val)) := by
  obtain ⟨t, hst, ht, b, hb⟩ :=
    exists_finite_basis_extension (boundedPolynomialEvaluation m) s available hs hspan
  exact ⟨t, hst, ht, boundedSampling_bijective_of_basis t b hb⟩

/-- The extension has exactly as many points as the dimension of the polynomial space. -/
theorem exists_bounded_interpolation_extension_with_card {d m : ℕ}
    (s : Finset (RealPoint d)) (available : Set (RealPoint d))
    (hs : LinearIndependent ℂ (fun x : ↥s => boundedPolynomialEvaluation m x.val))
    (hspan : Submodule.span ℂ
      (boundedPolynomialEvaluation m '' ((s : Set (RealPoint d)) ∪ available)) = ⊤) :
    ∃ t : Finset (RealPoint d), s ⊆ t ∧
      (t : Set (RealPoint d)) ⊆ (s : Set (RealPoint d)) ∪ available ∧
      t.card = Module.finrank ℂ (MvPolynomial.restrictTotalDegree (Fin d) ℂ m) ∧
      Function.Bijective (boundedSampling m (fun x : ↥t => x.val)) := by
  obtain ⟨t, hst, ht, b, hb⟩ :=
    exists_finite_basis_extension (boundedPolynomialEvaluation m) s available hs hspan
  refine ⟨t, hst, ht, ?_, boundedSampling_bijective_of_basis t b hb⟩
  have hc := Module.finrank_eq_card_basis b
  rw [Subspace.dual_finrank_eq, Fintype.card_coe] at hc
  exact hc.symm

/-- An annihilator formulation of the extension theorem, useful when the
available set is a sphere or another algebraic hypersurface. -/
theorem exists_bounded_interpolation_extension_of_annihilator {d m : ℕ}
    (s : Finset (RealPoint d)) (available : Set (RealPoint d))
    (hs : LinearIndependent ℂ (fun x : ↥s => boundedPolynomialEvaluation m x.val))
    (hzero : ∀ p : MvPolynomial.restrictTotalDegree (Fin d) ℂ m,
      (∀ x ∈ (s : Set (RealPoint d)) ∪ available,
        boundedPolynomialEvaluation m x p = 0) → p = 0) :
    ∃ t : Finset (RealPoint d), s ⊆ t ∧
      (t : Set (RealPoint d)) ⊆ (s : Set (RealPoint d)) ∪ available ∧
      Function.Bijective (boundedSampling m (fun x : ↥t => x.val)) :=
  exists_bounded_interpolation_extension s available hs
    (boundedPolynomialEvaluation_span_eq_top _ hzero)

/-- Surjective sampling implies independence of its component evaluation forms. -/
theorem boundedPolynomialEvaluation_independent_of_surjective {d m : ℕ}
    {ι : Type*} [Fintype ι] (points : ι → RealPoint d)
    (h : Function.Surjective (boundedSampling m points)) :
    LinearIndependent ℂ (fun i => boundedPolynomialEvaluation m (points i)) := by
  classical
  apply Fintype.linearIndependent_iff.mpr
  intro c hc i
  obtain ⟨p, hp⟩ := h (Pi.single i (1 : ℂ) : ι → ℂ)
  have hv : ∀ j, boundedPolynomialEvaluation m (points j) p =
      (Pi.single i (1 : ℂ) : ι → ℂ) j := fun j => congrFun hp j
  have he := LinearMap.congr_fun hc p
  simpa [LinearMap.sum_apply, hv, Pi.single_apply] using he

/-- Independence persists when the allowed polynomial degree increases. -/
theorem boundedPolynomialEvaluation_independent_mono {d a b : ℕ} {ι : Type*}
    (points : ι → RealPoint d) (hab : a ≤ b)
    (h : LinearIndependent ℂ (fun i => boundedPolynomialEvaluation a (points i))) :
    LinearIndependent ℂ (fun i => boundedPolynomialEvaluation b (points i)) := by
  have hsub : MvPolynomial.restrictTotalDegree (Fin d) ℂ a ≤
      MvPolynomial.restrictTotalDegree (Fin d) ℂ b := by
    intro p hp
    exact (MvPolynomial.mem_restrictTotalDegree _ _ _).mpr
      (((MvPolynomial.mem_restrictTotalDegree _ _ _).mp hp).trans hab)
  let inc := Submodule.inclusion hsub
  apply LinearIndependent.of_comp inc.dualMap
  exact h

/-- A polynomial vanishing at an interpolation set of degree `m - 2` inside the
ball and on the surrounding sphere is zero in degree at most `m`. -/
theorem polynomial_eq_zero_of_interpolation_and_sphere {d m : ℕ} (hd : 1 ≤ d)
    (s : Finset (RealPoint d)) (r : ℝ) (hr : 0 < r)
    (hsball : ∀ x ∈ s, ‖x‖ < r)
    (hsampling : Function.Injective (boundedSampling (m - 2) (fun x : ↥s => x.val)))
    (p : MvPolynomial.restrictTotalDegree (Fin d) ℂ m)
    (hzero : ∀ x ∈ (s : Set (RealPoint d)) ∪ {x | ‖x‖ = r},
      boundedPolynomialEvaluation m x p = 0) : p = 0 := by
  obtain ⟨q, hpq, hqdegree⟩ := exists_spherePolynomial_quotient_of_norm hd r hr p.val
    (fun x hx => hzero x (Or.inr hx))
  have hqbound : q.totalDegree ≤ m - 2 := hqdegree.trans
    (Nat.sub_le_sub_right ((MvPolynomial.mem_restrictTotalDegree _ _ _).mp p.property) 2)
  let q' : MvPolynomial.restrictTotalDegree (Fin d) ℂ (m - 2) :=
    ⟨q, (MvPolynomial.mem_restrictTotalDegree _ _ _).mpr hqbound⟩
  have hqzero : boundedSampling (m - 2) (fun x : ↥s => x.val) q' = 0 := by
    ext x
    have hxzero := hzero x.val (Or.inl x.property)
    have hfactor : polynomialEvaluation x.val (spherePolynomial d r) ≠ 0 := by
      intro he
      exact (hsball x.val x.property).ne
        ((polynomialEvaluation_spherePolynomial_eq_zero_iff x.val r hr.le).mp he)
    have hmul : polynomialEvaluation x.val (spherePolynomial d r) *
        polynomialEvaluation x.val q = 0 := by
      simpa only [boundedPolynomialEvaluation_apply, hpq, polynomialEvaluation_apply,
        map_mul] using hxzero
    exact (mul_eq_zero.mp hmul).resolve_left hfactor
  have hq' : q' = 0 := hsampling (hqzero.trans (map_zero _).symm)
  have hq : q = 0 := congrArg Subtype.val hq'
  apply Subtype.ext
  simpa [hq] using hpq

/-- Sphere interpolation-basis extension: retain an interpolation set for degree
`m - 2` inside the ball and add only points on its surrounding sphere. -/
theorem exists_sphere_interpolation_extension {d m : ℕ} (hd : 1 ≤ d)
    (s : Finset (RealPoint d)) (r : ℝ) (hr : 0 < r)
    (hsball : ∀ x ∈ s, ‖x‖ < r)
    (hsampling : Function.Bijective (boundedSampling (m - 2) (fun x : ↥s => x.val))) :
    ∃ t : Finset (RealPoint d), s ⊆ t ∧
      (t : Set (RealPoint d)) ⊆ (s : Set (RealPoint d)) ∪ {x | ‖x‖ = r} ∧
      t.card = Module.finrank ℂ (MvPolynomial.restrictTotalDegree (Fin d) ℂ m) ∧
      Function.Bijective (boundedSampling m (fun x : ↥t => x.val)) := by
  have hsind := boundedPolynomialEvaluation_independent_of_surjective _ hsampling.2
  have hsind' := boundedPolynomialEvaluation_independent_mono _ (Nat.sub_le m 2) hsind
  apply exists_bounded_interpolation_extension_with_card s {x | ‖x‖ = r} hsind'
  apply boundedPolynomialEvaluation_span_eq_top
  exact polynomial_eq_zero_of_interpolation_and_sphere hd s r hr hsball hsampling.1

end RieszEuclidean.CompleteMinimal
