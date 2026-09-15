import RieszEuclidean.Basic
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Analysis.InnerProductSpace.Dual

noncomputable section
namespace RieszEuclidean

/-- Two nonproportional nonzero real functionals give a surjective map to ℝ². -/
theorem prod_functionals_surjective {n : ℕ}
    (L M : Euclidean n →L[ℝ] ℝ) (hL : L ≠ 0)
    (hM : ∀ c : ℝ, M ≠ c • L) : Function.Surjective (L.prod M) := by
  classical
  obtain ⟨u, hu⟩ : ∃ u, L u ≠ 0 := by
    contrapose! hL
    ext u
    exact hL u
  have hv : ∃ v, L v = 0 ∧ M v ≠ 0 := by
    by_contra! hv
    apply hM (M u / L u)
    ext x
    have hz : L (x - (L x / L u) • u) = 0 := by
      simp [hu]
    have hm := hv _ hz
    simp only [map_sub, map_smul, smul_eq_mul] at hm
    change M x = (M u / L u) * L x
    have he : M x = (L x / L u) * M u := sub_eq_zero.mp hm
    rw [he]
    ring
  obtain ⟨v, hvL, hvM⟩ := hv
  intro y
  refine ⟨(y.1 / L u) • u + ((y.2 - (y.1 / L u) * M u) / M v) • v, ?_⟩
  apply Prod.ext
  · simp [hvL, hu]
  · simp [hvM]

/-- Surjectivity to ℝ² gives codimension two by rank-nullity. -/
theorem prod_functionals_kernel_dim {n : ℕ}
    (L M : Euclidean n →L[ℝ] ℝ) (h : Function.Surjective (L.prod M)) :
    Module.finrank ℝ (LinearMap.ker (L.prod M)) + 2 = n := by
  have he := LinearMap.finrank_range_add_finrank_ker (L.prod M).toLinearMap
  have hr : LinearMap.range (L.prod M).toLinearMap = ⊤ := LinearMap.range_eq_top.mpr h
  rw [hr, finrank_top] at he
  simpa [Module.finrank_prod, Euclidean, Nat.add_comm] using he

end RieszEuclidean
