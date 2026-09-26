import RieszEuclidean.CompleteMinimalBasic
import RieszEuclidean.CompleteMinimalEllipsoid
import Mathlib.Topology.Algebra.Module.LinearMap

/-! Affine transport of actual complete and minimal exponential families. -/

noncomputable section

open MeasureTheory MeasureTheory.Measure Filter Topology
open scoped ENNReal

namespace RieszEuclidean.CompleteMinimal

section Families

variable {ι κ H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K]

theorem mem_closed_span_image_iff (E : H ≃L[ℂ] K) (s : Set H) (x : H) :
    E x ∈ (Submodule.span ℂ (E '' s)).topologicalClosure ↔
      x ∈ (Submodule.span ℂ s).topologicalClosure := by
  have hs : (Submodule.span ℂ (E '' s) : Set K) =
      E '' (Submodule.span ℂ s : Set H) := by
    simpa only [Submodule.map_coe] using
      congrArg (fun P : Submodule ℂ K => (P : Set K))
        (Submodule.map_span E.toLinearMap s).symm
  change E x ∈ closure (Submodule.span ℂ (E '' s) : Set K) ↔
    x ∈ closure (Submodule.span ℂ s : Set H)
  rw [hs]
  change E.toHomeomorph x ∈ closure (E.toHomeomorph '' (Submodule.span ℂ s : Set H)) ↔ _
  rw [← E.toHomeomorph.image_closure]
  constructor
  · rintro ⟨y, hy, he⟩
    have hh : y = x := E.toHomeomorph.injective he
    simpa only [hh] using hy
  · intro hx
    exact ⟨x, hx, rfl⟩

/-- A bounded invertible linear map preserves completeness. -/
theorem IsComplete.linearEquiv {v : ι → H} (hv : IsComplete v) (E : H ≃L[ℂ] K) :
    IsComplete (fun i => E (v i)) := by
  change (Submodule.span ℂ (Set.range (fun i => E (v i)))).topologicalClosure = ⊤
  apply top_unique
  intro y _
  obtain ⟨x, rfl⟩ := E.surjective y
  change E x ∈ (Submodule.span ℂ (Set.range (E ∘ v))).topologicalClosure
  rw [Set.range_comp]
  apply (mem_closed_span_image_iff E (Set.range v) x).mpr
  change x ∈ closedSpan v
  rw [show closedSpan v = ⊤ from hv]
  trivial

/-- A bounded invertible linear map preserves ordinary minimality. -/
theorem IsMinimal.linearEquiv {v : ι → H} (hv : IsMinimal v) (E : H ≃L[ℂ] K) :
    IsMinimal (fun i => E (v i)) := by
  intro i hi
  apply hv i
  have he : (fun j => E (v j)) '' {j | j ≠ i} = E '' (v '' {j | j ≠ i}) :=
    (Set.image_image E v _).symm
  rw [he] at hi
  exact (mem_closed_span_image_iff E _ _).mp hi

/-- Multiplying individual generators by nonzero scalars leaves their span unchanged. -/
theorem span_weighted_image (v : ι → H) (c : ι → ℂ) (hc : ∀ i, c i ≠ 0) (s : Set ι) :
    Submodule.span ℂ ((fun i => c i • v i) '' s) = Submodule.span ℂ (v '' s) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, hi, rfl⟩
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, hi, rfl⟩)
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, hi, rfl⟩
    have h := Submodule.smul_mem (Submodule.span ℂ ((fun j => c j • v j) '' s))
      (c i)⁻¹ (Submodule.subset_span ⟨i, hi, rfl⟩)
    simpa [smul_smul, hc i] using h

theorem IsComplete.weighted {v : ι → H} (hv : IsComplete v)
    (c : ι → ℂ) (hc : ∀ i, c i ≠ 0) : IsComplete (fun i => c i • v i) := by
  unfold IsComplete closedSpan at hv ⊢
  simpa only [← Set.image_univ, span_weighted_image v c hc Set.univ] using hv

theorem IsMinimal.weighted {v : ι → H} (hv : IsMinimal v)
    (c : ι → ℂ) (hc : ∀ i, c i ≠ 0) : IsMinimal (fun i => c i • v i) := by
  intro i hi
  rw [span_weighted_image v c hc] at hi
  have h := Submodule.smul_mem _ (c i)⁻¹ hi
  apply hv i
  simpa [smul_smul, hc i] using h

theorem IsComplete.reindex {v : ι → H} (hv : IsComplete v) (r : κ ≃ ι) :
    IsComplete (fun i => v (r i)) := by
  unfold IsComplete closedSpan at hv ⊢
  have hr : Set.range (fun i => v (r i)) = Set.range v := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩; exact ⟨r i, rfl⟩
    · rintro ⟨i, rfl⟩; exact ⟨r.symm i, by simp⟩
  rwa [hr]

theorem IsMinimal.reindex {v : ι → H} (hv : IsMinimal v) (r : κ ≃ ι) :
    IsMinimal (fun i => v (r i)) := by
  intro i hi
  apply hv (r i)
  have hr : (fun j => v (r j)) '' {j | j ≠ i} = v '' {j | j ≠ r i} := by
    ext x
    constructor
    · rintro ⟨j, hj, rfl⟩
      exact ⟨r j, r.injective.ne hj, rfl⟩
    · rintro ⟨j, hj, rfl⟩
      exact ⟨r.symm j, (by intro hh; apply hj; simpa [hh] using (r.apply_symm_apply j).symm), by simp⟩
  rwa [hr] at hi

end Families

variable {d : ℕ}

/-- The actual pullback L² equivalence; its norm includes the Jacobian factor. -/
def affineL2Pullback (a : Euclidean d) (A : Euclidean d ≃L[ℝ] Euclidean d)
    (D : Set (Euclidean d)) :
    DomainL2 ((planeAffine a A) '' D) ≃L[ℂ] DomainL2 D :=
  scaledL2Equiv (planeAffine a A) (planeAffine_map a A D)
    (affineJacobian_ne_zero A) (affineJacobian_ne_top A)

/-- Pullback multiplies both-vector inner products by the real Jacobian. -/
theorem affineL2Pullback_inner (a : Euclidean d) (A : Euclidean d ≃L[ℝ] Euclidean d)
    (D : Set (Euclidean d)) (g f : DomainL2 ((planeAffine a A) '' D)) :
    inner (𝕜 := ℂ) (affineL2Pullback a A D g) (affineL2Pullback a A D f) =
      (affineJacobian A).toReal • inner (𝕜 := ℂ) g f := by
  rw [L2.inner_def, L2.inner_def]
  have he : (∫ x, inner (𝕜 := ℂ) (g (planeAffine a A x)) (f (planeAffine a A x))
      ∂volume.restrict D) =
      (affineJacobian A).toReal •
        ∫ x, inner (𝕜 := ℂ) (g x) (f x) ∂volume.restrict ((planeAffine a A) '' D) := by
    have h := integral_map_equiv (μ := volume.restrict D) (planeAffine a A)
      (fun x => inner (𝕜 := ℂ) (g x) (f x))
    rw [planeAffine_map, integral_smul_measure] at h
    exact h.symm
  rw [← he]
  apply integral_congr_ae
  filter_upwards [scaledL2Equiv_ae (planeAffine a A) (planeAffine_map a A D)
    (affineJacobian_ne_zero A) (affineJacobian_ne_top A) g,
    scaledL2Equiv_ae (planeAffine a A) (planeAffine_map a A D)
    (affineJacobian_ne_zero A) (affineJacobian_ne_top A) f] with x hg hf
  simpa only [affineL2Pullback, Function.comp_apply] using
    congrArg₂ (fun u v : ℂ => inner (𝕜 := ℂ) u v) hg hf

/-- The phase identity holds for the actual L² equivalence classes. -/
theorem affineL2Pullback_exponential (a ξ : Euclidean d)
    (A : Euclidean d ≃L[ℝ] Euclidean d) (D : Set (Euclidean d))
    (hD : volume D ≠ ⊤) (himage : volume ((planeAffine a A) '' D) ≠ ⊤) :
    affineL2Pullback a A D (exponentialL2 _ himage ξ) =
      exponential ξ a • exponentialL2 D hD (affineFrequency A ξ) := by
  have hq : QuasiMeasurePreserving (planeAffine a A) (volume.restrict D)
      (volume.restrict ((planeAffine a A) '' D)) :=
    ⟨(planeAffine a A).measurable, by rw [planeAffine_map]; exact Measure.smul_absolutelyContinuous⟩
  apply Lp.ext
  filter_upwards [scaledL2Equiv_ae (planeAffine a A) (planeAffine_map a A D)
      (affineJacobian_ne_zero A) (affineJacobian_ne_top A) (exponentialL2 _ himage ξ),
    hq.ae (exponentialL2_ae _ himage ξ),
    Lp.coeFn_smul (exponential ξ a) (exponentialL2 D hD (affineFrequency A ξ)),
    exponentialL2_ae D hD (affineFrequency A ξ)] with x hx hy hz hw
  dsimp only [affineL2Pullback]
  simp only [Function.comp_apply] at hx
  rw [hx, hy, hz]
  change exponential ξ (planeAffine a A x) = exponential ξ a *
    (exponentialL2 D hD (affineFrequency A ξ)) x
  rw [hw]
  exact exponential_planeAffine a ξ x A

/-- The pullback of a supported vector has the corresponding preimage support. -/
theorem SupportedOn.affinePullback {D K : Set (Euclidean d)}
    {g : DomainL2 ((planeAffine a A) '' D)}
    (hg : SupportedOn ((planeAffine a A) '' D) g K) :
    SupportedOn D (affineL2Pullback a A D g) ((planeAffine a A) ⁻¹' K) := by
  have hq : QuasiMeasurePreserving (planeAffine a A) (volume.restrict D)
      (volume.restrict ((planeAffine a A) '' D)) :=
    ⟨(planeAffine a A).measurable, by rw [planeAffine_map]; exact Measure.smul_absolutelyContinuous⟩
  filter_upwards [hq.ae hg, scaledL2Equiv_ae (planeAffine a A) (planeAffine_map a A D)
    (affineJacobian_ne_zero A) (affineJacobian_ne_top A) g] with x hx hy
  exact fun h => hy.trans (hx h)

/-- Scalar multiplication preserves physical support. -/
theorem SupportedOn.smul {D K : Set (Euclidean d)} {g : DomainL2 D}
    (hg : SupportedOn D g K) (c : ℂ) : SupportedOn D (c • g) K := by
  filter_upwards [hg, Lp.coeFn_smul c g] with x hx hy
  intro hK
  rw [hy]
  change c * g x = 0
  rw [hx hK, mul_zero]

/-- The pullback formula solved for the new exponential. -/
theorem exponentialL2_affineFrequency (a ξ : Euclidean d)
    (A : Euclidean d ≃L[ℝ] Euclidean d) (D : Set (Euclidean d))
    (hD : volume D ≠ ⊤) (himage : volume ((planeAffine a A) '' D) ≠ ⊤) :
    exponentialL2 D hD (affineFrequency A ξ) =
      (exponential ξ a)⁻¹ • affineL2Pullback a A D (exponentialL2 _ himage ξ) := by
  rw [affineL2Pullback_exponential, smul_smul, inv_mul_cancel₀, one_smul]
  exact Complex.exp_ne_zero _

private theorem reindexed_affine_exponentials (A : Euclidean d ≃L[ℝ] Euclidean d) (D Λ : Set (Euclidean d))
    (hD : volume D ≠ ⊤) :
    (fun η : (affineFrequency A) '' Λ => exponentialL2 D hD
      (affineFrequency A ((Equiv.Set.image (affineFrequency A) Λ
        (affineFrequency_injective A)).symm η).val)) =
      exponentialFamily D hD ((affineFrequency A) '' Λ) := by
  funext η
  congr 1
  exact congrArg Subtype.val
    ((Equiv.Set.image (affineFrequency A) Λ (affineFrequency_injective A)).apply_symm_apply η)

/-- Affine pullback preserves completeness of actual domain exponentials. -/
theorem IsCompleteExponential.affinePullback (a : Euclidean d)
    (A : Euclidean d ≃L[ℝ] Euclidean d) (D Λ : Set (Euclidean d))
    (hD : volume D ≠ ⊤) (himage : volume ((planeAffine a A) '' D) ≠ ⊤)
    (h : IsCompleteExponential ((planeAffine a A) '' D) himage Λ) :
    IsCompleteExponential D hD ((affineFrequency A) '' Λ) := by
  have hc : ∀ ξ : Λ, (exponential ξ.val a)⁻¹ ≠ 0 :=
    fun ξ => inv_ne_zero (Complex.exp_ne_zero _)
  have ht := (h.linearEquiv (affineL2Pullback a A D)).weighted
    (fun ξ : Λ => (exponential ξ.val a)⁻¹) hc
  have he : (fun ξ : Λ => (exponential ξ.val a)⁻¹ •
      affineL2Pullback a A D (exponentialFamily _ himage Λ ξ)) =
      (fun ξ : Λ => exponentialL2 D hD (affineFrequency A ξ.val)) := by
    funext ξ
    exact (exponentialL2_affineFrequency a ξ.val A D hD himage).symm
  rw [he] at ht
  have hr := ht.reindex
    (Equiv.Set.image (affineFrequency A) Λ (affineFrequency_injective A)).symm
  rwa [reindexed_affine_exponentials A D Λ hD] at hr

/-- Affine pullback preserves ordinary minimality of actual domain exponentials. -/
theorem IsMinimalExponential.affinePullback (a : Euclidean d)
    (A : Euclidean d ≃L[ℝ] Euclidean d) (D Λ : Set (Euclidean d))
    (hD : volume D ≠ ⊤) (himage : volume ((planeAffine a A) '' D) ≠ ⊤)
    (h : IsMinimalExponential ((planeAffine a A) '' D) himage Λ) :
    IsMinimalExponential D hD ((affineFrequency A) '' Λ) := by
  have hc : ∀ ξ : Λ, (exponential ξ.val a)⁻¹ ≠ 0 :=
    fun ξ => inv_ne_zero (Complex.exp_ne_zero _)
  have ht := (h.linearEquiv (affineL2Pullback a A D)).weighted
    (fun ξ : Λ => (exponential ξ.val a)⁻¹) hc
  have he : (fun ξ : Λ => (exponential ξ.val a)⁻¹ •
      affineL2Pullback a A D (exponentialFamily _ himage Λ ξ)) =
      (fun ξ : Λ => exponentialL2 D hD (affineFrequency A ξ.val)) := by
    funext ξ
    exact (exponentialL2_affineFrequency a ξ.val A D hD himage).symm
  rw [he] at ht
  have hr := ht.reindex
    (Equiv.Set.image (affineFrequency A) Λ (affineFrequency_injective A)).symm
  rwa [reindexed_affine_exponentials A D Λ hD] at hr

/-- The exact dual weight for the unnormalized L² pullback. The inverse real
Jacobian compensates for the scaling of the inner product. -/
def affineDualWeight (a ξ : Euclidean d) (A : Euclidean d ≃L[ℝ] Euclidean d) : ℂ :=
  ((affineJacobian A).toReal : ℂ)⁻¹ * star (exponential ξ a)

/-- Transported dual vectors, reindexed by the transpose image of the frequencies. -/
def affineDualPullback (a : Euclidean d) (A : Euclidean d ≃L[ℝ] Euclidean d)
    (D Λ : Set (Euclidean d)) (g : Λ → DomainL2 ((planeAffine a A) '' D)) :
    (affineFrequency A) '' Λ → DomainL2 D := fun η =>
  let ξ := (Equiv.Set.image (affineFrequency A) Λ (affineFrequency_injective A)).symm η
  affineDualWeight a ξ.val A • affineL2Pullback a A D (g ξ)

/-- The Jacobian and phase corrected pullbacks are biorthogonal to the transported
actual exponential family. -/
theorem affineDualPullback_biorthogonal (a : Euclidean d)
    (A : Euclidean d ≃L[ℝ] Euclidean d) (D Λ : Set (Euclidean d))
    (hD : volume D ≠ ⊤) (himage : volume ((planeAffine a A) '' D) ≠ ⊤)
    (g : Λ → DomainL2 ((planeAffine a A) '' D))
    (hg : IsBiorthogonal (exponentialFamily _ himage Λ) g) :
    IsBiorthogonal (exponentialFamily D hD ((affineFrequency A) '' Λ))
      (affineDualPullback a A D Λ g) := by
  classical
  have hc : ((affineJacobian A).toReal : ℂ) ≠ 0 := by
    exact_mod_cast ENNReal.toReal_ne_zero.mpr
      ⟨affineJacobian_ne_zero A, affineJacobian_ne_top A⟩
  have hi : ∀ ξ ζ : Λ,
      inner (𝕜 := ℂ) (affineDualWeight a ξ.val A • affineL2Pullback a A D (g ξ))
        (exponentialL2 D hD (affineFrequency A ζ.val)) = if ξ = ζ then 1 else 0 := by
    intro ξ ζ
    rw [exponentialL2_affineFrequency a ζ.val A D hD himage,
      inner_smul_left, inner_smul_right, affineL2Pullback_inner]
    change star (affineDualWeight a ξ.val A) * ((exponential ζ.val a)⁻¹ *
      (((affineJacobian A).toReal : ℂ) *
        inner (𝕜 := ℂ) (g ξ) (exponentialFamily _ himage Λ ζ))) = _
    rw [hg ξ ζ]
    by_cases hξζ : ξ = ζ
    · subst ζ
      simp only [if_pos rfl, affineDualWeight, star_mul, star_inv₀, star_star,
        Complex.star_def, Complex.conj_ofReal, mul_one]
      have hp : exponential ξ.val a ≠ 0 := Complex.exp_ne_zero _
      field_simp
    · simp [hξζ]
  intro η θ
  let r := (Equiv.Set.image (affineFrequency A) Λ (affineFrequency_injective A)).symm
  have ht := hi (r η) (r θ)
  have hf : affineFrequency A (r θ).val = θ.val :=
    congrArg Subtype.val ((Equiv.Set.image (affineFrequency A) Λ
      (affineFrequency_injective A)).apply_symm_apply θ)
  by_cases hh : η = θ
  · have heq : r η = r θ := congrArg r hh
    simpa only [affineDualPullback, hf, if_pos hh, if_pos heq, exponentialFamily] using ht
  · have hne : r η ≠ r θ := r.injective.ne hh
    simpa only [affineDualPullback, hf, if_neg hh, if_neg hne, exponentialFamily] using ht

/-- The explicitly corrected dual family keeps its transported physical support. -/
theorem affineDualPullback_supported (a : Euclidean d)
    (A : Euclidean d ≃L[ℝ] Euclidean d) (D Λ K : Set (Euclidean d))
    (g : Λ → DomainL2 ((planeAffine a A) '' D))
    (hg : ∀ ξ, SupportedOn ((planeAffine a A) '' D) (g ξ) K) :
    ∀ η, SupportedOn D (affineDualPullback a A D Λ g η) ((planeAffine a A) ⁻¹' K) := by
  intro η
  exact ((hg _).affinePullback).smul _

/-- The transpose map is an actual topological linear equivalence, whose inverse
is the transpose of the inverse coordinate map. -/
def affineFrequencyEquiv (A : Euclidean d ≃L[ℝ] Euclidean d) :
    Euclidean d ≃L[ℝ] Euclidean d where
  toLinearEquiv :=
    { toLinearMap := (affineFrequency A).toLinearMap
      invFun := affineFrequency A.symm
      left_inv := fun ξ => by
        apply ext_inner_right ℝ
        intro x
        change inner (𝕜 := ℝ) (affineFrequency A.symm (affineFrequency A ξ)) x = _
        rw [affineFrequency_inner, affineFrequency_inner]
        simp
      right_inv := fun ξ => by
        apply ext_inner_right ℝ
        intro x
        change inner (𝕜 := ℝ) (affineFrequency A (affineFrequency A.symm ξ)) x = _
        rw [affineFrequency_inner, affineFrequency_inner]
        simp }
  continuous_toFun := (affineFrequency A).continuous
  continuous_invFun := (affineFrequency A.symm).continuous

/-- Local finiteness of a set, expressed by finite intersections with neighborhoods. -/
def IsLocallyFiniteSet {X : Type*} [TopologicalSpace X] (Λ : Set X) : Prop :=
  ∀ x, ∃ U ∈ nhds x, (Λ ∩ U).Finite

/-- Homeomorphisms preserve local finiteness of selected frequencies. -/
theorem IsLocallyFiniteSet.image_homeomorph {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] {Λ : Set X}
    (hΛ : IsLocallyFiniteSet Λ) (h : X ≃ₜ Y) : IsLocallyFiniteSet (h '' Λ) := by
  intro y
  obtain ⟨U, hU, hfin⟩ := hΛ (h.symm y)
  obtain ⟨W, hWU, hWopen, hyW⟩ := mem_nhds_iff.mp hU
  refine ⟨h '' W, (h.isOpenMap W hWopen).mem_nhds ?_, ?_⟩
  · exact ⟨h.symm y, hyW, h.apply_symm_apply y⟩
  · apply (hfin.image h).subset
    rintro z ⟨⟨x, hx, rfl⟩, hzW⟩
    obtain ⟨w, hwW, heq⟩ := hzW
    have hEq : w = x := h.injective heq
    subst w
    exact ⟨x, ⟨hx, hWU hwW⟩, rfl⟩

/-- Both transpose and inverse-transpose frequency transport preserve local finiteness. -/
theorem IsLocallyFiniteSet.affineFrequency {Λ : Set (Euclidean d)}
    (hΛ : IsLocallyFiniteSet Λ) (A : Euclidean d ≃L[ℝ] Euclidean d) :
    IsLocallyFiniteSet ((affineFrequency A) '' Λ) :=
  hΛ.image_homeomorph (affineFrequencyEquiv A).toHomeomorph

private theorem affine_inverse_image_domain (a : Euclidean d)
    (A : Euclidean d ≃L[ℝ] Euclidean d) (D : Set (Euclidean d)) :
    (planeAffine (-A.symm a) A.symm) '' ((planeAffine a A) '' D) = D := by
  rw [planeAffine_inverse, Set.image_image]
  simp only [Function.comp_def, MeasurableEquiv.symm_apply_apply, Set.image_id']

/-- Forward domain transport uses precisely the inverse-transpose frequency map. -/
theorem IsCompleteExponential.affineImage (a : Euclidean d)
    (A : Euclidean d ≃L[ℝ] Euclidean d) (D Λ : Set (Euclidean d))
    (hD : volume D ≠ ⊤) (himage : volume ((planeAffine a A) '' D) ≠ ⊤)
    (h : IsCompleteExponential D hD Λ) :
    IsCompleteExponential ((planeAffine a A) '' D) himage ((affineFrequency A.symm) '' Λ) := by
  have heq := affine_inverse_image_domain a A D
  have hfin : volume ((planeAffine (-A.symm a) A.symm) '' ((planeAffine a A) '' D)) ≠ ⊤ :=
    heq.symm ▸ hD
  have hh : IsCompleteExponential
      ((planeAffine (-A.symm a) A.symm) '' ((planeAffine a A) '' D)) hfin Λ := by simpa only [heq] using h
  exact hh.affinePullback (-A.symm a) A.symm _ Λ himage hfin

/-- Ordinary minimality passes to every invertible affine image of the domain. -/
theorem IsMinimalExponential.affineImage (a : Euclidean d)
    (A : Euclidean d ≃L[ℝ] Euclidean d) (D Λ : Set (Euclidean d))
    (hD : volume D ≠ ⊤) (himage : volume ((planeAffine a A) '' D) ≠ ⊤)
    (h : IsMinimalExponential D hD Λ) :
    IsMinimalExponential ((planeAffine a A) '' D) himage ((affineFrequency A.symm) '' Λ) := by
  have heq := affine_inverse_image_domain a A D
  have hfin : volume ((planeAffine (-A.symm a) A.symm) '' ((planeAffine a A) '' D)) ≠ ⊤ :=
    heq.symm ▸ hD
  have hh : IsMinimalExponential
      ((planeAffine (-A.symm a) A.symm) '' ((planeAffine a A) '' D)) hfin Λ := by simpa only [heq] using h
  exact hh.affinePullback (-A.symm a) A.symm _ Λ himage hfin

/-- Finite volume is preserved by every invertible affine domain map. -/
theorem finite_volume_affineImage (a : Euclidean d)
    (A : Euclidean d ≃L[ℝ] Euclidean d) (D : Set (Euclidean d))
    (hD : volume D ≠ ⊤) : volume ((planeAffine a A) '' D) ≠ ⊤ := by
  rw [volume_affine_image]
  exact ENNReal.mul_ne_top (volumeFactor_ne_top A) hD

/-- Forward affine domain transport of an actual supported biorthogonal family. -/
theorem exists_supported_biorthogonal_affineImage (a : Euclidean d)
    (A : Euclidean d ≃L[ℝ] Euclidean d) (D Λ K : Set (Euclidean d))
    (hD : volume D ≠ ⊤) (himage : volume ((planeAffine a A) '' D) ≠ ⊤)
    (g : Λ → DomainL2 D) (hg : IsBiorthogonal (exponentialFamily D hD Λ) g)
    (hs : ∀ ξ, SupportedOn D (g ξ) K) :
    ∃ w : (affineFrequency A.symm) '' Λ → DomainL2 ((planeAffine a A) '' D),
      IsBiorthogonal (exponentialFamily _ himage ((affineFrequency A.symm) '' Λ)) w ∧
      ∀ η, SupportedOn ((planeAffine a A) '' D) (w η) ((planeAffine a A) '' K) := by
  have heq := affine_inverse_image_domain a A D
  have hbase : ∃ hfin : volume D ≠ ⊤, ∃ g₀ : Λ → DomainL2 D,
      IsBiorthogonal (exponentialFamily D hfin Λ) g₀ ∧
      ∀ ξ, SupportedOn D (g₀ ξ) K := ⟨hD, g, hg, hs⟩
  have hr : ∃ hfin : volume
      ((planeAffine (-A.symm a) A.symm) '' ((planeAffine a A) '' D)) ≠ ⊤,
      ∃ g₀ : Λ → DomainL2
        ((planeAffine (-A.symm a) A.symm) '' ((planeAffine a A) '' D)),
        IsBiorthogonal (exponentialFamily _ hfin Λ) g₀ ∧
        ∀ ξ, SupportedOn _ (g₀ ξ) K := heq.symm ▸ hbase
  obtain ⟨hfin, g₀, hg₀, hs₀⟩ := hr
  refine ⟨affineDualPullback (-A.symm a) A.symm _ Λ g₀,
    affineDualPullback_biorthogonal (-A.symm a) A.symm _ Λ himage hfin g₀ hg₀, ?_⟩
  have hsupport : (planeAffine (-A.symm a) A.symm) ⁻¹' K = (planeAffine a A) '' K := by
    rw [planeAffine_inverse]
    exact (Set.image_equiv_eq_preimage_symm K (planeAffine a A).toEquiv).symm
  simpa only [hsupport] using
    affineDualPullback_supported (-A.symm a) A.symm _ Λ K g₀ hs₀

/-- The complete and minimal system, its supported duals, and local finiteness
transport together under an arbitrary invertible affine domain map. -/
theorem complete_minimal_supported_affineImage (a : Euclidean d)
    (A : Euclidean d ≃L[ℝ] Euclidean d) (D Λ K : Set (Euclidean d))
    (hD : volume D ≠ ⊤) (hcomplete : IsCompleteExponential D hD Λ)
    (g : Λ → DomainL2 D) (hg : IsBiorthogonal (exponentialFamily D hD Λ) g)
    (hs : ∀ ξ, SupportedOn D (g ξ) K) (hlocal : IsLocallyFiniteSet Λ) :
    let himage := finite_volume_affineImage a A D hD
    IsCompleteExponential ((planeAffine a A) '' D) himage ((affineFrequency A.symm) '' Λ) ∧
      IsMinimalExponential ((planeAffine a A) '' D) himage ((affineFrequency A.symm) '' Λ) ∧
      IsLocallyFiniteSet ((affineFrequency A.symm) '' Λ) ∧
      ∃ w : (affineFrequency A.symm) '' Λ → DomainL2 ((planeAffine a A) '' D),
        IsBiorthogonal (exponentialFamily _ himage ((affineFrequency A.symm) '' Λ)) w ∧
        ∀ η, SupportedOn ((planeAffine a A) '' D) (w η) ((planeAffine a A) '' K) := by
  dsimp only
  obtain ⟨w, hw, hws⟩ := exists_supported_biorthogonal_affineImage a A D Λ K hD
    (finite_volume_affineImage a A D hD) g hg hs
  exact ⟨hcomplete.affineImage a A D Λ hD _, hw.isMinimal,
    hlocal.affineFrequency A.symm, w, hw, hws⟩

/-- When the prescribed support is a John ellipsoid, its transported support
remains the John ellipsoid of the affine image domain. -/
theorem john_supported_affineImage (a : Euclidean d)
    (A : Euclidean d ≃L[ℝ] Euclidean d) (D Λ K : Set (Euclidean d))
    (hD : volume D ≠ ⊤) (hJohn : IsJohnEllipsoid D K)
    (g : Λ → DomainL2 D) (hg : IsBiorthogonal (exponentialFamily D hD Λ) g)
    (hs : ∀ ξ, SupportedOn D (g ξ) K) :
    IsJohnEllipsoid ((planeAffine a A) '' D) ((planeAffine a A) '' K) ∧
      ∃ w : (affineFrequency A.symm) '' Λ → DomainL2 ((planeAffine a A) '' D),
        IsBiorthogonal (exponentialFamily _ (finite_volume_affineImage a A D hD)
          ((affineFrequency A.symm) '' Λ)) w ∧
        ∀ η, SupportedOn ((planeAffine a A) '' D) (w η) ((planeAffine a A) '' K) :=
  ⟨hJohn.affine_image a A, exists_supported_biorthogonal_affineImage a A D Λ K hD
    (finite_volume_affineImage a A D hD) g hg hs⟩

end RieszEuclidean.CompleteMinimal
