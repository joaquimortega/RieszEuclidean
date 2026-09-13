import RieszEuclidean.TriangleAnalyticAssembly
import RieszEuclidean.Affine
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

noncomputable section
open MeasureTheory Filter Topology
namespace RieszEuclidean

/-- The open triangle with vertices `a`, `b`, `c`, expressed by positive barycentric
coordinates. Nondegeneracy is imposed separately by independence of its two edges. -/
def vertexTriangle (a b c : Euclidean 2) : Set (Euclidean 2) :=
  {y | ∃ u v : ℝ, 0 < u ∧ 0 < v ∧ u + v < 1 ∧
    y = a + u • (b - a) + v • (c - a)}

/-- Nondegenerate edge vectors define an invertible map from the standard coordinates. -/
def triangleLinearEquiv (a b c : Euclidean 2)
    (h : LinearIndependent ℝ ![b - a, c - a]) : Euclidean 2 ≃L[ℝ] Euclidean 2 :=
  (EuclideanSpace.equiv (Fin 2) ℝ).trans
    (basisOfLinearIndependentOfCardEqFinrank h (by simp [Euclidean])).equivFun.symm.toContinuousLinearEquiv

/-- The normal-form map sends standard coordinates to the two actual edge vectors. -/
theorem triangleLinearEquiv_apply (a b c : Euclidean 2)
    (h : LinearIndependent ℝ ![b - a, c - a]) (x : Euclidean 2) :
    triangleLinearEquiv a b c h x = x 0 • (b - a) + x 1 • (c - a) := by
  simp [triangleLinearEquiv, Basis.equivFun_symm_apply, Fin.sum_univ_two]

/-- Every ordinary nondegenerate vertex triangle is an affine image of the standard triangle. -/
theorem vertexTriangle_eq_affine_image (a b c : Euclidean 2)
    (h : LinearIndependent ℝ ![b - a, c - a]) :
    vertexTriangle a b c = (planeAffine a (triangleLinearEquiv a b c h)) '' standardTriangle 1 := by
  ext y
  constructor
  · rintro ⟨u, v, hu, hv, huv, rfl⟩
    let x : Euclidean 2 := (WithLp.equiv 2 (Fin 2 → ℝ)).symm ![u, v]
    refine ⟨x, ⟨hu, hv, huv⟩, ?_⟩
    change a + triangleLinearEquiv a b c h x = _
    rw [triangleLinearEquiv_apply]
    change a + (u • (b - a) + v • (c - a)) = _
    abel
  · rintro ⟨x, ⟨h0, h1, hsum⟩, rfl⟩
    refine ⟨x 0, x 1, h0, h1, hsum, ?_⟩
    change a + triangleLinearEquiv a b c h x = _
    rw [triangleLinearEquiv_apply]
    abel

/-- The affine reduction covers arbitrary noncollinear triples of vertices. -/
theorem vertexTriangle_basis_iff (a b c : Euclidean 2)
    (h : LinearIndependent ℝ ![b - a, c - a]) :
    (∃ Λ, HasExponentialRieszBasis (vertexTriangle a b c) Λ) ↔
      ∃ Λ, HasExponentialRieszBasis (standardTriangle 1) Λ := by
  rw [vertexTriangle_eq_affine_image a b c h]
  exact exists_exponentialRieszBasis_affine_iff _ _ _

open SeparatedConfiguration in
/-- Every actual nondegenerate vertex triangle has no exponential Riesz basis,
given representing measures for the stationary hull correlations. -/
theorem vertexTriangle_no_exponentialRieszBasis_of_hull_representations
    (a b c : Euclidean 2) (h : LinearIndependent ℝ ![b - a, c - a])
    (hrep : ∀ {δ : ℝ} (hδ : 0 < δ) (Γ : SeparatedConfiguration 2 δ)
      [MeasurableSpace (hull Γ)] [BorelSpace (hull Γ)]
      (μ : Measure (hull Γ)) [IsProbabilityMeasure μ]
      (hμ : ∀ z : Euclidean 2, MeasurePreserving (hullTranslate hδ Γ z) μ μ),
      ∃ σ : Lp ℂ 2 μ → Measure (Euclidean 2),
        ∀ f, RepresentsCorrelation
          (unitaryCorrelation (hullKoopmanUnitary hδ Γ μ hμ) f) (σ f))
    (Λ : Set (Euclidean 2)) : ¬ HasExponentialRieszBasis (vertexTriangle a b c) Λ := by
  intro hB
  rw [vertexTriangle_eq_affine_image a b c h] at hB
  exact standardTriangle_no_exponentialRieszBasis_of_hull_representations 1 zero_lt_one hrep
    ((affineFrequency (triangleLinearEquiv a b c h)) '' Λ)
    (hasExponentialRieszBasis_affine_pullback a (triangleLinearEquiv a b c h)
      (standardTriangle 1) Λ hB)

/-- Affine independence of three vertices gives precisely the edge independence
used in the explicit normal form. -/
theorem vertex_edges_linearIndependent_of_affineIndependent (a b c : Euclidean 2)
    (h : AffineIndependent ℝ ![a, b, c]) : LinearIndependent ℝ ![b - a, c - a] := by
  have he := (affineIndependent_iff_linearIndependent_vsub ℝ ![a, b, c] 0).mp h
  let e : Fin 2 → {j : Fin 3 // j ≠ 0} := fun i => ⟨i.succ, Fin.succ_ne_zero i⟩
  have hi : Function.Injective e := by
    intro i j hij
    exact Fin.succ_injective _ (congrArg Subtype.val hij)
  convert he.comp e hi using 1
  ext i
  fin_cases i <;> rfl

open SeparatedConfiguration in
/-- The conditional triangle theorem for arbitrary noncollinear vertex triples,
with no affine-image assumption in its statement. -/
theorem noncollinear_triangle_no_exponentialRieszBasis_of_hull_representations
    (a b c : Euclidean 2) (h : ¬ Collinear ℝ (Set.range ![a, b, c]))
    (hrep : ∀ {δ : ℝ} (hδ : 0 < δ) (Γ : SeparatedConfiguration 2 δ)
      [MeasurableSpace (hull Γ)] [BorelSpace (hull Γ)]
      (μ : Measure (hull Γ)) [IsProbabilityMeasure μ]
      (hμ : ∀ z : Euclidean 2, MeasurePreserving (hullTranslate hδ Γ z) μ μ),
      ∃ σ : Lp ℂ 2 μ → Measure (Euclidean 2),
        ∀ f, RepresentsCorrelation
          (unitaryCorrelation (hullKoopmanUnitary hδ Γ μ hμ) f) (σ f))
    (Λ : Set (Euclidean 2)) : ¬ HasExponentialRieszBasis (vertexTriangle a b c) Λ :=
  vertexTriangle_no_exponentialRieszBasis_of_hull_representations a b c
    (vertex_edges_linearIndependent_of_affineIndependent a b c
      (affineIndependent_iff_not_collinear.mpr h)) hrep Λ

end RieszEuclidean
