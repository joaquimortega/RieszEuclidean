import RieszEuclidean.BumpSynthesis
noncomputable section
namespace RieszEuclidean
/-- An isometry identifies its source with any equal range submodule. -/
def isometryRangeEquiv {A H : Type} [NormedAddCommGroup A] [InnerProductSpace ℂ A]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] (V : A →ₗᵢ[ℂ] H)
    (Q : Submodule ℂ H) (hQ : LinearMap.range V.toLinearMap = Q) : A ≃ₗᵢ[ℂ] Q :=
  V.equivRange.trans (LinearIsometryEquiv.ofEq _ _ hQ)
/-- The range equivalence has the original isometry as its ambient representative. -/
theorem isometryRangeEquiv_coe {A H : Type} [NormedAddCommGroup A] [InnerProductSpace ℂ A]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] (V : A →ₗᵢ[ℂ] H)
    (Q : Submodule ℂ H) (hQ : LinearMap.range V.toLinearMap = Q) (x : A) :
    (isometryRangeEquiv V Q hQ x : H) = V x := rfl
/-- An invertible synthesis identity induces the required projection range isomorphism. -/
theorem rangeIso_of_synthesis {A B H : Type} [NormedAddCommGroup A] [InnerProductSpace ℂ A]
    [NormedAddCommGroup B] [InnerProductSpace ℂ B]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (P Q : OrthProjection H) (V : A →ₗᵢ[ℂ] H) (W : B →ₗᵢ[ℂ] H)
    (hV : LinearMap.range V.toLinearMap = Q.range)
    (hW : LinearMap.range W.toLinearMap = P.range) (E : A ≃L[ℂ] B)
    (h : ∀ a, P.op (V a) = W (E a)) : P.RangeIso Q := by
  let eV := (isometryRangeEquiv V Q.range hV).toContinuousLinearEquiv
  let eW := (isometryRangeEquiv W P.range hW).toContinuousLinearEquiv
  refine ⟨eV.symm.trans (E.trans eW), ?_⟩
  intro x
  obtain ⟨a, rfl⟩ := eV.surjective x
  change (eW (E (eV.symm (eV a))) : H) = P.op (eV a)
  rw [ContinuousLinearEquiv.symm_apply_apply]
  exact (h a).symm
end RieszEuclidean
