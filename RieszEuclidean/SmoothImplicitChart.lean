import RieszEuclidean.RegularLevelNullity
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff

noncomputable section
open Filter Topology
namespace RieszEuclidean

/-- The implicit-function parametrization inherits C² regularity. -/
theorem implicit_data_contDiffAt
    {E F G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
    (D : ImplicitFunctionData ℝ E F G)
    (hl : ContDiffAt ℝ 2 D.leftFun D.pt) (hr : ContDiffAt ℝ 2 D.rightFun D.pt) :
    ContDiffAt ℝ 2 (D.implicitFunction (D.leftFun D.pt)) (D.rightFun D.pt) := by
  have hc : ContDiffAt ℝ 2 D.prodFun D.pt := hl.prodMk hr
  have hpt : D.toPartialHomeomorph.symm (D.prodFun D.pt) = D.pt :=
    D.toPartialHomeomorph.left_inv D.pt_mem_toPartialHomeomorph_source
  have hinv : ContDiffAt ℝ 2 D.toPartialHomeomorph.symm (D.prodFun D.pt) := by
    apply D.toPartialHomeomorph.contDiffAt_symm
      (f₀' := D.leftDeriv.equivProdOfSurjectiveOfIsCompl D.rightDeriv
        D.left_range D.right_range D.isCompl_ker)
      D.map_pt_mem_toPartialHomeomorph_target
    · change HasFDerivAt D.prodFun _ (D.toPartialHomeomorph.symm (D.prodFun D.pt))
      rw [hpt]
      exact D.hasStrictFDerivAt.hasFDerivAt
    · change ContDiffAt ℝ 2 D.prodFun (D.toPartialHomeomorph.symm (D.prodFun D.pt))
      rw [hpt]
      exact hc
  exact hinv.comp (D.rightFun D.pt) (contDiffAt_const.prodMk contDiffAt_id)

/-- A regular C² scalar level is C²-parametrized by its tangent kernel. -/
theorem regular_implicit_contDiffAt {n : ℕ} {f : Euclidean n → ℝ}
    {L : Euclidean n →L[ℝ] ℝ} {a : Euclidean n}
    (hf : HasStrictFDerivAt f L a) (hL : LinearMap.range L = ⊤)
    (hC : ContDiffAt ℝ 2 f a) :
    ContDiffAt ℝ 2 (hf.implicitFunction f L hL (f a)) 0 := by
  let hker := L.ker_closedComplemented_of_finiteDimensional_range
  let D := hf.implicitFunctionDataOfComplemented f L hL hker
  have hr : ContDiffAt ℝ 2 D.rightFun a := by
    exact (Classical.choose hker).contDiff.contDiffAt.comp a
      (contDiffAt_id.sub contDiffAt_const)
  have he := implicit_data_contDiffAt D hC hr
  simpa only [D, HasStrictFDerivAt.implicitFunctionDataOfComplemented,
    _root_.sub_self, map_zero] using he

end RieszEuclidean
