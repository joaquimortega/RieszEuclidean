import RieszEuclidean.SchwartzDensity
import Mathlib.Analysis.NormedSpace.OperatorNorm.Completeness
noncomputable section
open MeasureTheory
namespace RieszEuclidean
/-- Ambient Euclidean L² space. -/
abbrev FullL2 (d : ℕ) := Lp ℂ 2 (volume : Measure (Euclidean d))
/-- The Schwartz subspace with its inherited L² norm. -/
def schwartzL2 (d : ℕ) : Submodule ℂ (FullL2 d) :=
  LinearMap.range (SchwartzMap.toLpCLM ℂ ℂ 2 (volume : Measure (Euclidean d))).toLinearMap
/-- Identify Schwartz functions with their actual L² representatives. -/
def schwartzL2Equiv (d : ℕ) : SchwartzMap (Euclidean d) ℂ ≃ₗ[ℂ] schwartzL2 d :=
  LinearEquiv.ofInjective (SchwartzMap.toLpCLM ℂ ℂ 2 volume).toLinearMap
    (SchwartzMap.injective_toLp 2 volume)
/-- Fourier transform restricted to the dense Schwartz subspace. -/
def schwartzFourierIsometry (d : ℕ) : schwartzL2 d ≃ₗᵢ[ℂ] schwartzL2 d where
  toLinearEquiv := (schwartzL2Equiv d).symm.trans
    ((SchwartzMap.fourierTransformCLE ℂ).toLinearEquiv.trans (schwartzL2Equiv d))
  norm_map' x := by
    obtain ⟨f, rfl⟩ := (schwartzL2Equiv d).surjective x
    simpa [schwartzL2Equiv] using schwartz_fourier_norm f
/-- The inclusion of the Schwartz subspace into L² has dense range. -/
theorem schwartzL2_dense (d : ℕ) : DenseRange (schwartzL2 d).subtypeL := by
  rw [Metric.denseRange_iff]
  intro x ε hε
  obtain ⟨f, hf⟩ := Metric.denseRange_iff.mp (schwartz_toL2_denseRange d) x ε hε
  exact ⟨schwartzL2Equiv d f, hf⟩
/-- Continuous extension of the negative-sign Fourier transform to Euclidean L². -/
def fourierL2CLM (d : ℕ) : FullL2 d →L[ℂ] FullL2 d :=
  ((schwartzL2 d).subtypeL.comp
    (schwartzFourierIsometry d).toContinuousLinearEquiv.toContinuousLinearMap).extend
    (schwartzL2 d).subtypeL (schwartzL2_dense d)
    (schwartzL2 d).subtypeₗᵢ.isometry.isUniformInducing
/-- The extension agrees with Fourier on the Schwartz subspace. -/
theorem fourierL2CLM_subtype (d : ℕ) (x : schwartzL2 d) :
    fourierL2CLM d x = (schwartzFourierIsometry d x : FullL2 d) :=
  ContinuousLinearMap.extend_eq _ _ _ _ x
/-- The extended Fourier transform preserves the L² norm. -/
theorem fourierL2CLM_norm (d : ℕ) (x : FullL2 d) : ‖fourierL2CLM d x‖ = ‖x‖ := by
  refine (schwartzL2_dense d).induction_on (p := fun y => ‖fourierL2CLM d y‖ = ‖y‖) x ?_ ?_
  · exact isClosed_eq ((fourierL2CLM d).continuous.norm) continuous_norm
  · intro y
    change ‖fourierL2CLM d (y : FullL2 d)‖ = ‖(y : FullL2 d)‖
    rw [fourierL2CLM_subtype]
    exact (schwartzFourierIsometry d).norm_map y
/-- The extended transform as a linear isometry. -/
def fourierL2Isometry (d : ℕ) : FullL2 d →ₗᵢ[ℂ] FullL2 d where
  toLinearMap := (fourierL2CLM d).toLinearMap
  norm_map' := fourierL2CLM_norm d
/-- The extended transform has dense range, by Schwartz inversion. -/
theorem fourierL2_dense (d : ℕ) : DenseRange (fourierL2Isometry d) := by
  rw [Metric.denseRange_iff]
  intro x ε hε
  obtain ⟨y, hy⟩ := Metric.denseRange_iff.mp (schwartzL2_dense d) x ε hε
  refine ⟨((schwartzFourierIsometry d).symm y : FullL2 d), ?_⟩
  change dist x (fourierL2CLM d _) < ε
  rw [fourierL2CLM_subtype, LinearIsometryEquiv.apply_symm_apply]
  exact hy
/-- Completeness closes the isometric range, so the Fourier extension is onto. -/
theorem fourierL2_surjective (d : ℕ) : Function.Surjective (fourierL2Isometry d) := by
  apply Set.range_eq_univ.mp
  rw [← (fourierL2Isometry d).isometry.isClosedEmbedding.isClosed_range.closure_eq]
  exact (fourierL2_dense d).closure_eq
/-- Unitary negative-sign Euclidean Fourier transform on L². -/
def fourierL2Equiv (d : ℕ) : FullL2 d ≃ₗᵢ[ℂ] FullL2 d :=
  LinearIsometryEquiv.ofSurjective (fourierL2Isometry d) (fourierL2_surjective d)
/-- The unitary extension has the exact Schwartz Fourier values. -/
theorem fourierL2Equiv_schwartz (d : ℕ) (f : SchwartzMap (Euclidean d) ℂ) :
    fourierL2Equiv d (f.toLp 2 volume) =
      (SchwartzMap.fourierTransformCLE ℂ f).toLp 2 volume := by
  change fourierL2CLM d (f.toLp 2 volume) = _
  have h := fourierL2CLM_subtype d (schwartzL2Equiv d f)
  simpa [schwartzFourierIsometry, schwartzL2Equiv] using h
/-- The inverse extension agrees with inverse Fourier on Schwartz functions. -/
theorem fourierL2Equiv_symm_schwartz (d : ℕ) (f : SchwartzMap (Euclidean d) ℂ) :
    (fourierL2Equiv d).symm (f.toLp 2 volume) =
      ((SchwartzMap.fourierTransformCLE ℂ).symm f).toLp 2 volume := by
  apply (fourierL2Equiv d).injective
  rw [LinearIsometryEquiv.apply_symm_apply, fourierL2Equiv_schwartz,
    ContinuousLinearEquiv.apply_symm_apply]
/-- The paper's positive-sign Fourier transform, defined on all of Euclidean L². -/
def paperFourierL2 (d : ℕ) : FullL2 d ≃ₗᵢ[ℂ] FullL2 d := (fourierL2Equiv d).symm
/-- Exact positive-sign integral formula on the dense Schwartz subspace. -/
theorem paperFourierL2_schwartz (d : ℕ) (f : SchwartzMap (Euclidean d) ℂ) :
    (paperFourierL2 d (f.toLp 2 volume) : Euclidean d → ℂ) =ᵐ[volume]
      Real.fourierIntegralInv f := by
  rw [paperFourierL2, fourierL2Equiv_symm_schwartz]
  exact (((SchwartzMap.fourierTransformCLE ℂ).symm f).coeFn_toLp 2 volume).trans
    (Filter.Eventually.of_forall (fun x => congrFun
      (SchwartzMap.fourierTransformCLE_symm_apply ℂ f) x))
end RieszEuclidean
