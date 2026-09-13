import RieszEuclidean.BumpTranslates
import Mathlib.Analysis.InnerProductSpace.l2Space
noncomputable section
open MeasureTheory
namespace RieszEuclidean
/-- An orthonormal family defines isometric synthesis of square-summable coefficients. -/
def orthonormalSynthesis {ι H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] {v : ι → H} (hv : Orthonormal ℂ v) : SeqL2 ι →ₗᵢ[ℂ] H :=
  hv.orthogonalFamily.linearIsometry
/-- Synthesis sends a coordinate vector to its designated family member. -/
theorem orthonormalSynthesis_single {ι H : Type} [DecidableEq ι]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {v : ι → H} (hv : Orthonormal ℂ v) (i : ι) :
    orthonormalSynthesis hv (lp.single 2 i 1) = v i := by
  simp [orthonormalSynthesis]
/-- Concrete isometric synthesis for the separated translates of a normalized bump. -/
def bumpSynthesis {d : ℕ} {δ r : ℝ} {Λ : Set (Euclidean d)}
    (hΛ : Separated δ Λ) (hr : 2 * r < δ) (b : SchwartzMap (Euclidean d) ℂ)
    (hs : ∀ ξ, r ≤ ‖ξ‖ → b ξ = 0) (hn : ‖b.toLp 2 volume‖ = 1) :
    SeqL2 Λ →ₗᵢ[ℂ] FullL2 d :=
  orthonormalSynthesis (translated_bumps_orthonormal hΛ hr b hs hn)
/-- Orthogonal projection onto the closed range of a linear isometry. -/
def isometryRangeProjection {H K : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (e : H →ₗᵢ[ℂ] K) : OrthProjection K where
  op := e.toContinuousLinearMap.comp e.toContinuousLinearMap.adjoint
  idempotent := by
    have he := e.toContinuousLinearMap.norm_map_iff_adjoint_comp_self.mp e.norm_map
    calc
      _ = e.toContinuousLinearMap.comp
          ((e.toContinuousLinearMap.adjoint.comp e.toContinuousLinearMap).comp
            e.toContinuousLinearMap.adjoint) := by rw [ContinuousLinearMap.comp_assoc, ContinuousLinearMap.comp_assoc]
      _ = _ := by rw [he]; rfl
  symmetric x y := by
    change inner (𝕜 := ℂ) (e.toContinuousLinearMap (e.toContinuousLinearMap.adjoint x)) y =
      inner (𝕜 := ℂ) x (e.toContinuousLinearMap (e.toContinuousLinearMap.adjoint y))
    rw [← ContinuousLinearMap.adjoint_inner_right, ContinuousLinearMap.adjoint_inner_left]
/-- The constructed projection has exactly the synthesis range. -/
theorem isometryRangeProjection_range {H K : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] [NormedAddCommGroup K]
    [InnerProductSpace ℂ K] [CompleteSpace K] (e : H →ₗᵢ[ℂ] K) :
    (isometryRangeProjection e).range = LinearMap.range e.toLinearMap := by
  have he := e.toContinuousLinearMap.norm_map_iff_adjoint_comp_self.mp e.norm_map
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨e.toContinuousLinearMap.adjoint y, rfl⟩
  · rintro ⟨y, rfl⟩
    refine ⟨e y, ?_⟩
    change e (e.toContinuousLinearMap.adjoint (e y)) = e y
    have hy := DFunLike.congr_fun he y
    exact congrArg e hy
end RieszEuclidean
