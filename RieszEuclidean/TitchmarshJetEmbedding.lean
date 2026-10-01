import RieszEuclidean.CompleteMinimalPointSupport
import Mathlib.Analysis.NormedSpace.HahnBanach.Extension

set_option maxHeartbeats 1000000

/-!
# Factoring distributions through finite jets

The central interchange tool is a normed-space statement: a continuous linear
functional controlled by a continuous linear jet map factors through that map.
The Hahn–Banach extension then supplies a functional on the whole jet space.
-/

noncomputable section

namespace RieszEuclidean.CompleteMinimal

open scoped BoundedContinuousFunction SchwartzMap

/-- A functional bounded by the norm of a jet map factors through that map and
extends to a bounded functional on the target space. -/
theorem exists_bounded_functional_factorization
    {E F : Type*} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    (J : E →L[ℂ] F) (u : E →L[ℂ] ℂ) (C : ℝ)
    (hbound : ∀ x : E, ‖u x‖ ≤ C * ‖J x‖) :
    ∃ L : F →L[ℂ] ℂ, L.comp J = u := by
  let kerJ : Submodule ℂ E := LinearMap.ker J.toLinearMap
  have hker : kerJ ≤ LinearMap.ker u.toLinearMap := by
    intro x hx
    have hu : ‖u x‖ ≤ C * ‖J x‖ := hbound x
    have hJ : J x = 0 := by simpa [kerJ] using hx
    rw [hJ, norm_zero, mul_zero] at hu
    exact (norm_eq_zero.mp (le_antisymm hu (norm_nonneg _)))
  let quotientFunctional : (E ⧸ kerJ) →ₗ[ℂ] ℂ := kerJ.liftQ u.toLinearMap hker
  let rangeFunctional : LinearMap.range J.toLinearMap →ₗ[ℂ] ℂ :=
    quotientFunctional.comp (LinearMap.quotKerEquivRange J.toLinearMap).symm.toLinearMap
  have hrangeBound (y : LinearMap.range J.toLinearMap) :
      ‖rangeFunctional y‖ ≤ C * ‖(y : F)‖ := by
    obtain ⟨x, hx⟩ := y.property
    have hy : y = ⟨J x, ⟨x, rfl⟩⟩ := Subtype.ext hx.symm
    rw [hy]
    have hy : rangeFunctional ⟨J x, ⟨x, rfl⟩⟩ = u x := by
      have heq : (LinearMap.quotKerEquivRange J.toLinearMap).symm
          ⟨J x, ⟨x, rfl⟩⟩ = kerJ.mkQ x := by
        simpa [kerJ] using LinearMap.quotKerEquivRange_symm_apply_image
          J.toLinearMap x ⟨x, rfl⟩
      calc
        rangeFunctional ⟨J x, ⟨x, rfl⟩⟩ =
            quotientFunctional ((LinearMap.quotKerEquivRange J.toLinearMap).symm
              ⟨J x, ⟨x, rfl⟩⟩) := rfl
        _ = quotientFunctional (kerJ.mkQ x) := congrArg quotientFunctional heq
        _ = u x := by simp [quotientFunctional]
    rw [hy]
    exact hbound x
  let rangeFunctionalCLM : LinearMap.range J.toLinearMap →L[ℂ] ℂ :=
    rangeFunctional.mkContinuous C hrangeBound
  obtain ⟨L, hL, _⟩ := exists_extension_norm_eq
    (LinearMap.range J.toLinearMap) rangeFunctionalCLM
  refine ⟨L, ?_⟩
  ext x
  have hLx := hL ⟨J x, ⟨x, rfl⟩⟩
  have hfactor : rangeFunctionalCLM ⟨J x, ⟨x, rfl⟩⟩ = u x := by
    change rangeFunctional ⟨J x, ⟨x, rfl⟩⟩ = u x
    have heq : (LinearMap.quotKerEquivRange J.toLinearMap).symm
        ⟨J x, ⟨x, rfl⟩⟩ = kerJ.mkQ x := by
      simpa [kerJ] using LinearMap.quotKerEquivRange_symm_apply_image
        J.toLinearMap x ⟨x, rfl⟩
    calc
      rangeFunctional ⟨J x, ⟨x, rfl⟩⟩ =
          quotientFunctional ((LinearMap.quotKerEquivRange J.toLinearMap).symm
            ⟨J x, ⟨x, rfl⟩⟩) := rfl
      _ = quotientFunctional (kerJ.mkQ x) := congrArg quotientFunctional heq
      _ = u x := by simp [quotientFunctional]
  · exact hLx.trans hfactor

/-- The value space for a derivative of order `j`. -/
abbrev JetValue (d : ℕ) (j : ℕ) :=
  ContinuousMultilinearMap ℝ (fun _ : Fin j => RieszEuclidean.Euclidean d) ℂ

/-- The finite family of weighted derivatives through orders `N` in both indices. -/
abbrev FiniteJetSpace (d N : ℕ) :=
  ∀ i : {i : ℕ × ℕ // i ∈ Finset.Iic (N, N)},
    (RieszEuclidean.Euclidean d →ᵇ JetValue d i.1.2)

/-- Canonical normed additive group structure on the finite jet product. -/
instance (priority := 1001) finiteJetSpaceNormedAddCommGroup {d N : ℕ} :
    NormedAddCommGroup (FiniteJetSpace d N) :=
  inferInstanceAs (NormedAddCommGroup
    (∀ i : {i : ℕ × ℕ // i ∈ Finset.Iic (N, N)},
      RieszEuclidean.Euclidean d →ᵇ
        ContinuousMultilinearMap ℝ (fun _ : Fin i.1.2 => RieszEuclidean.Euclidean d) ℂ))

/-- Canonical complex normed-space structure on the finite jet product. -/
instance (priority := 1001) finiteJetSpaceNormedSpaceComplex {d N : ℕ} :
    NormedSpace ℂ (FiniteJetSpace d N) :=
  inferInstanceAs (NormedSpace ℂ
    (∀ i : {i : ℕ × ℕ // i ∈ Finset.Iic (N, N)},
      RieszEuclidean.Euclidean d →ᵇ
        ContinuousMultilinearMap ℝ (fun _ : Fin i.1.2 => RieszEuclidean.Euclidean d) ℂ))

/-- Canonical real normed-space structure on the finite jet product. -/
instance (priority := 1001) finiteJetSpaceNormedSpaceReal {d N : ℕ} :
    NormedSpace ℝ (FiniteJetSpace d N) :=
  inferInstanceAs (NormedSpace ℝ
    (∀ i : {i : ℕ × ℕ // i ∈ Finset.Iic (N, N)},
      RieszEuclidean.Euclidean d →ᵇ
        ContinuousMultilinearMap ℝ (fun _ : Fin i.1.2 => RieszEuclidean.Euclidean d) ℂ))

/-- Canonical completeness structure on the finite jet product. -/
instance (priority := 1001) finiteJetSpaceCompleteSpace {d N : ℕ} :
    CompleteSpace (FiniteJetSpace d N) :=
  inferInstanceAs (CompleteSpace
    (∀ i : {i : ℕ × ℕ // i ∈ Finset.Iic (N, N)},
      RieszEuclidean.Euclidean d →ᵇ
        ContinuousMultilinearMap ℝ (fun _ : Fin i.1.2 => RieszEuclidean.Euclidean d) ℂ))

/-- A weighted derivative, viewed as a bounded continuous function. -/
def weightedJetCoordinate {d : ℕ} (i : ℕ × ℕ)
    (φ : 𝓢(RieszEuclidean.Euclidean d, ℂ)) :
    (RieszEuclidean.Euclidean d →ᵇ JetValue d i.2) := by
  let f : C(RieszEuclidean.Euclidean d, JetValue d i.2) :=
    ⟨fun x => ‖x‖ ^ i.1 • iteratedFDeriv ℝ i.2 (φ : RieszEuclidean.Euclidean d → ℂ) x,
      (continuous_norm.pow i.1).smul
        (ContDiff.continuous_iteratedFDeriv (by exact_mod_cast le_top) φ.smooth')⟩
  refine BoundedContinuousFunction.mkOfBound f
    (2 * SchwartzMap.seminorm ℂ i.1 i.2 φ) ?_
  intro x y
  have hx : ‖‖x‖ ^ i.1 • iteratedFDeriv ℝ i.2 (φ : RieszEuclidean.Euclidean d → ℂ) x‖ ≤
      SchwartzMap.seminorm ℂ i.1 i.2 φ := by
    rw [norm_smul, Real.norm_of_nonneg (pow_nonneg (norm_nonneg _) _)]
    exact φ.le_seminorm ℂ i.1 i.2 x
  have hy : ‖‖y‖ ^ i.1 • iteratedFDeriv ℝ i.2 (φ : RieszEuclidean.Euclidean d → ℂ) y‖ ≤
      SchwartzMap.seminorm ℂ i.1 i.2 φ := by
    rw [norm_smul, Real.norm_of_nonneg (pow_nonneg (norm_nonneg _) _)]
    exact φ.le_seminorm ℂ i.1 i.2 y
  calc
    dist (f x) (f y) = ‖f x - f y‖ := dist_eq_norm _ _
    _ ≤ ‖f x‖ + ‖f y‖ := norm_sub_le _ _
    _ ≤ SchwartzMap.seminorm ℂ i.1 i.2 φ + SchwartzMap.seminorm ℂ i.1 i.2 φ :=
      add_le_add hx hy
    _ = 2 * SchwartzMap.seminorm ℂ i.1 i.2 φ := by ring

/-- The finite product of weighted derivative coordinates through order `N`. -/
def finiteJetFun {d : ℕ} (N : ℕ) (φ : 𝓢(RieszEuclidean.Euclidean d, ℂ)) :
    FiniteJetSpace d N := fun i => weightedJetCoordinate i.1 φ

private theorem weightedJetCoordinate_add {d : ℕ} (i : ℕ × ℕ)
    (φ ψ : 𝓢(RieszEuclidean.Euclidean d, ℂ)) :
    weightedJetCoordinate i (φ + ψ) =
      weightedJetCoordinate i φ + weightedJetCoordinate i ψ := by
  apply BoundedContinuousFunction.ext
  intro x
  change ‖x‖ ^ i.1 • iteratedFDeriv ℝ i.2
      (fun z => (φ : RieszEuclidean.Euclidean d → ℂ) z + ψ z) x =
    ‖x‖ ^ i.1 • iteratedFDeriv ℝ i.2 (φ : RieszEuclidean.Euclidean d → ℂ) x +
      ‖x‖ ^ i.1 • iteratedFDeriv ℝ i.2 (ψ : RieszEuclidean.Euclidean d → ℂ) x
  rw [iteratedFDeriv_add_apply' (f := (φ : RieszEuclidean.Euclidean d → ℂ))
    (g := (ψ : RieszEuclidean.Euclidean d → ℂ)) (i := i.2) (x := x)
    (hf := φ.smooth'.contDiffAt.of_le (by exact_mod_cast le_top))
    (hg := ψ.smooth'.contDiffAt.of_le (by exact_mod_cast le_top)), smul_add]

private theorem weightedJetCoordinate_smul {d : ℕ} (i : ℕ × ℕ) (c : ℂ)
    (φ : 𝓢(RieszEuclidean.Euclidean d, ℂ)) :
    weightedJetCoordinate i (c • φ) = c • weightedJetCoordinate i φ := by
  apply BoundedContinuousFunction.ext
  intro x
  change ‖x‖ ^ i.1 • iteratedFDeriv ℝ i.2
      (fun z => c • (φ : RieszEuclidean.Euclidean d → ℂ) z) x =
    c • (‖x‖ ^ i.1 • iteratedFDeriv ℝ i.2 (φ : RieszEuclidean.Euclidean d → ℂ) x)
  rw [iteratedFDeriv_const_smul_apply' (f := (φ : RieszEuclidean.Euclidean d → ℂ))
    (i := i.2) (x := x) (a := c)
    (hf := φ.smooth'.contDiffAt.of_le (by exact_mod_cast le_top))]
  rw [smul_comm]

/-- The finite weighted-derivative jet as a continuous linear map out of Schwartz space. -/
def finiteJetMap {d : ℕ} (N : ℕ) :
    𝓢(RieszEuclidean.Euclidean d, ℂ) →L[ℂ] FiniteJetSpace d N := by
  apply SchwartzMap.mkCLMtoNormedSpace (σ := RingHom.id ℂ) (finiteJetFun N)
  · intro φ ψ
    funext i
    exact weightedJetCoordinate_add i.1 φ ψ
  · intro c φ
    funext i
    exact weightedJetCoordinate_smul i.1 c φ
  · letI : Nonempty (RieszEuclidean.Euclidean d) := ⟨0⟩
    refine ⟨Finset.Iic (N, N), 1, zero_le_one, ?_⟩
    intro φ
    let S := (Finset.Iic (N, N)).sup
      (schwartzSeminormFamily ℂ (RieszEuclidean.Euclidean d) ℂ) φ
    have hS0 : 0 ≤ S := by
      dsimp [S]
      exact apply_nonneg _ _
    have hfinite : ‖finiteJetFun N φ‖ ≤ S := by
      change ‖(fun i : {i : ℕ × ℕ // i ∈ Finset.Iic (N, N)} =>
        weightedJetCoordinate i.1 φ)‖ ≤ S
      apply (pi_norm_le_iff_of_nonneg hS0).2
      intro i
      apply (BoundedContinuousFunction.norm_le_of_nonempty).2
      intro x
      change ‖‖x‖ ^ i.1.1 • iteratedFDeriv ℝ i.1.2
        (φ : RieszEuclidean.Euclidean d → ℂ) x‖ ≤ S
      have hpoint := φ.le_seminorm ℂ i.1.1 i.1.2 x
      have hsup : SchwartzMap.seminorm ℂ i.1.1 i.1.2 φ ≤ S := by
        dsimp [S]
        have := Seminorm.le_finset_sup_apply (p := schwartzSeminormFamily ℂ
          (RieszEuclidean.Euclidean d) ℂ) (s := Finset.Iic (N, N))
          (x := φ) (i := i.1) i.2
        simpa only [SchwartzMap.schwartzSeminormFamily_apply] using this
      rw [norm_smul, Real.norm_of_nonneg (pow_nonneg (norm_nonneg x) _)]
      exact hpoint.trans hsup
    calc
      ‖finiteJetFun N φ‖ ≤ S := hfinite
      _ = 1 * ((Finset.Iic (N, N)).sup
          (schwartzSeminormFamily ℂ (RieszEuclidean.Euclidean d) ℂ) φ) := by
        simp [S]

/-- The finite jet norm controls every Schwartz seminorm in its defining square. -/
theorem finiteJetMap_controls_seminorm {d : ℕ} (N : ℕ)
    (φ : 𝓢(RieszEuclidean.Euclidean d, ℂ)) :
    (Finset.Iic (N, N)).sup
      (schwartzSeminormFamily ℂ (RieszEuclidean.Euclidean d) ℂ) φ ≤
      ‖finiteJetMap N φ‖ := by
  apply Seminorm.finset_sup_apply_le (norm_nonneg (finiteJetMap N φ))
  intro ij hij
  have hseminorm : SchwartzMap.seminorm ℂ ij.1 ij.2 φ ≤ ‖finiteJetMap N φ‖ := by
    apply SchwartzMap.seminorm_le_bound ℂ ij.1 ij.2 φ
      (norm_nonneg (finiteJetMap N φ))
    intro x
    let i : {p : ℕ × ℕ // p ∈ Finset.Iic (N, N)} := ⟨ij, hij⟩
    have hcoord := (weightedJetCoordinate ij φ).norm_coe_le_norm x
    have hpi : ‖finiteJetMap N φ i‖ ≤ ‖finiteJetMap N φ‖ :=
      norm_le_pi_norm (finiteJetMap N φ) i
    have hweighted : ‖x‖ ^ ij.1 *
        ‖iteratedFDeriv ℝ ij.2 (φ : RieszEuclidean.Euclidean d → ℂ) x‖ ≤
        ‖finiteJetMap N φ‖ := by
      have hcoord' :
          ‖‖x‖ ^ ij.1 • iteratedFDeriv ℝ ij.2
              (φ : RieszEuclidean.Euclidean d → ℂ) x‖ ≤ ‖finiteJetMap N φ‖ := by
        simpa [finiteJetMap, finiteJetFun, i, weightedJetCoordinate] using hcoord.trans hpi
      simpa only [norm_smul,
        Real.norm_of_nonneg (pow_nonneg (norm_nonneg x) _)] using hcoord'
    exact hweighted
  simpa only [SchwartzMap.schwartzSeminormFamily_apply] using hseminorm

/-- Every tempered distribution factors continuously through a finite weighted
derivative jet. -/
theorem temperedDistribution_factors_through_finiteJet {d : ℕ}
    (u : TemperedDistribution d) :
    ∃ N : ℕ, ∃ L : FiniteJetSpace d N →L[ℂ] ℂ,
      L.comp (finiteJetMap N) = u := by
  obtain ⟨N, C, hC, hbound⟩ := distribution_finite_order_bound u
  have hjetbound : ∀ φ : 𝓢(RieszEuclidean.Euclidean d, ℂ),
      ‖u φ‖ ≤ C * ‖finiteJetMap N φ‖ := by
    intro φ
    apply (hbound φ).trans
    apply mul_le_mul_of_nonneg_left _ hC.le
    exact finiteJetMap_controls_seminorm N φ
  obtain ⟨L, hL⟩ := exists_bounded_functional_factorization
    (E := 𝓢(RieszEuclidean.Euclidean d, ℂ)) (F := FiniteJetSpace d N)
    (finiteJetMap N) u C hjetbound
  exact ⟨N, L, hL⟩

/-- Evaluating a jet at an index and a point gives the corresponding weighted derivative. -/
@[simp] theorem finiteJetMap_apply {d : ℕ} (N : ℕ)
    (φ : 𝓢(RieszEuclidean.Euclidean d, ℂ))
    (i : {i : ℕ × ℕ // i ∈ Finset.Iic (N, N)}) (x : RieszEuclidean.Euclidean d) :
    finiteJetMap N φ i x = ‖x‖ ^ i.1.1 •
      iteratedFDeriv ℝ i.1.2 (φ : RieszEuclidean.Euclidean d → ℂ) x := rfl

end RieszEuclidean.CompleteMinimal

end
