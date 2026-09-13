import Mathlib.Analysis.InnerProductSpace.Adjoint
open scoped ComplexInnerProductSpace
namespace RieszEuclidean
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
/-- Pointwise norm domination by a projection forces right absorption. -/
theorem projection_right_absorption_of_norm_le (P Q : H →L[ℂ] H)
    (hQ : Q.comp Q = Q) (horder : ∀ f, ‖P f‖ ≤ ‖Q f‖) : P.comp Q = P := by
  ext f
  have hq : Q (f - Q f) = 0 := by
    rw [map_sub, show Q (Q f) = Q f from DFunLike.congr_fun hQ f, _root_.sub_self]
  have hp : P (f - Q f) = 0 := by
    apply norm_eq_zero.mp
    exact le_antisymm (by simpa [hq] using horder (f - Q f)) (norm_nonneg _)
  rw [map_sub] at hp
  exact (sub_eq_zero.mp hp).symm
variable [CompleteSpace H]
/-- Self-adjointness turns right absorption into left absorption. -/
theorem projection_left_absorption_of_norm_le (P Q : H →L[ℂ] H)
    (hPself : IsSelfAdjoint P) (hQself : IsSelfAdjoint Q)
    (hQ : Q.comp Q = Q) (horder : ∀ f, ‖P f‖ ≤ ‖Q f‖) : Q.comp P = P := by
  have h := congrArg ContinuousLinearMap.adjoint
    (projection_right_absorption_of_norm_le P Q hQ horder)
  simpa only [ContinuousLinearMap.adjoint_comp, hPself.adjoint_eq, hQself.adjoint_eq] using h
/-- Pointwise norm order of orthogonal projections implies inclusion of their actual ranges. -/
theorem projection_range_le_of_norm_le (P Q : H →L[ℂ] H)
    (hPself : IsSelfAdjoint P) (hQself : IsSelfAdjoint Q)
    (hQ : Q.comp Q = Q) (horder : ∀ f, ‖P f‖ ≤ ‖Q f‖) :
    LinearMap.range P.toLinearMap ≤ LinearMap.range Q.toLinearMap := by
  rintro _ ⟨f, rfl⟩
  exact ⟨P f, DFunLike.congr_fun (projection_left_absorption_of_norm_le P Q hPself hQself hQ horder) f⟩
/-- An orthogonal projection preserves a vector's norm only when it fixes that vector. -/
theorem projection_eq_self_of_norm_eq (P : H →L[ℂ] H) (hself : IsSelfAdjoint P)
    (hidem : P.comp P = P) (f : H) (hnorm : ‖P f‖ = ‖f‖) : P f = f := by
  have hi : inner (𝕜 := ℂ) (P f) (P f) = inner (𝕜 := ℂ) (P f) f := by
    have h := (hself.isSymmetric (P f) f).symm
    change inner (𝕜 := ℂ) (P f) (P f) = inner (𝕜 := ℂ) (P (P f)) f at h
    rwa [show P (P f) = P f from DFunLike.congr_fun hidem f] at h
  have hz : ‖f - P f‖ ^ 2 = 0 := by
    rw [norm_sub_sq (𝕜 := ℂ)]
    have hr := congrArg Complex.re hi
    simp only [inner_self_eq_norm_sq_to_K] at hr
    change ((‖P f‖ : ℂ) ^ 2).re = (inner (𝕜 := ℂ) (P f) f).re at hr
    have he : (inner (𝕜 := ℂ) f (P f)).re = ‖P f‖ ^ 2 := by
      rw [← inner_conj_symm (𝕜 := ℂ) f (P f), Complex.conj_re]
      simpa only [← Complex.ofReal_pow, Complex.ofReal_re] using hr.symm
    change ‖f‖ ^ 2 - 2 * (inner (𝕜 := ℂ) f (P f)).re + ‖P f‖ ^ 2 = 0
    rw [he, hnorm]
    ring
  exact (sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hz))).symm
/-- A unit vector killed by the smaller projection and fully retained by the larger
projection certifies strict inclusion of their actual ranges. -/
theorem projection_range_lt_of_unit_witness (P Q : H →L[ℂ] H)
    (hPself : IsSelfAdjoint P) (hQself : IsSelfAdjoint Q)
    (hP : P.comp P = P) (hQ : Q.comp Q = Q)
    (horder : ∀ f, ‖P f‖ ≤ ‖Q f‖) (u : H) (hu : ‖u‖ = 1)
    (hPu : P u = 0) (hQu : ‖Q u‖ = 1) :
    Q u = u ∧ LinearMap.range P.toLinearMap < LinearMap.range Q.toLinearMap := by
  have hfix := projection_eq_self_of_norm_eq Q hQself hQ u (hQu.trans hu.symm)
  refine ⟨hfix, lt_of_le_not_le (projection_range_le_of_norm_le P Q hPself hQself hQ horder) ?_⟩
  intro hrev
  have humem : u ∈ LinearMap.range Q.toLinearMap := ⟨u, hfix⟩
  obtain ⟨f, hf⟩ := hrev humem
  have hPfix : P u = u := by
    change P f = u at hf
    rw [← hf]
    exact DFunLike.congr_fun hP f
  have hz : u = 0 := hPfix.symm.trans hPu
  rw [hz, norm_zero] at hu
  norm_num at hu
end RieszEuclidean
