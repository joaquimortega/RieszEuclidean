import RieszEuclidean.CompleteMinimalSpherePolynomial
import RieszEuclidean.CompleteMinimalEntireFourier

/-! The finite polynomial denominators of the spherical interpolation spaces.

The radii in this file are frequency-space radii `a_j / (2π)`. Consequently
the paper's denominator is `(4π²)^N` times `sphereDenominator`.
-/

noncomputable section
open MvPolynomial
open scoped BigOperators

namespace RieszEuclidean.CompleteMinimal

/-- The denominator containing the first `N` positive-index sphere factors. -/
def sphereDenominator (d : ℕ) (radius : ℕ → ℝ) (N : ℕ) : ComplexPolynomial d :=
  ∏ j ∈ Finset.range N, spherePolynomial d (radius (j + 1))

@[simp] theorem sphereDenominator_zero (d : ℕ) (radius : ℕ → ℝ) :
    sphereDenominator d radius 0 = 1 := by simp [sphereDenominator]

theorem sphereDenominator_succ (d N : ℕ) (radius : ℕ → ℝ) :
    sphereDenominator d radius (N + 1) =
      sphereDenominator d radius N * spherePolynomial d (radius (N + 1)) := by
  simp only [sphereDenominator, Finset.prod_range_succ]

theorem spherePolynomial_ne_zero {d : ℕ} (hd : 1 ≤ d) (r : ℝ) :
    spherePolynomial d r ≠ 0 := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : d ≠ 0)
  intro h
  have hh := spherePolynomial_totalDegree n r
  simp [h] at hh

theorem sphereDenominator_ne_zero {d : ℕ} (hd : 1 ≤ d) (radius : ℕ → ℝ) (N : ℕ) :
    sphereDenominator d radius N ≠ 0 := by
  exact Finset.prod_ne_zero_iff.mpr (fun j _ => spherePolynomial_ne_zero hd (radius (j + 1)))

theorem sphereDenominator_totalDegree {d : ℕ} (hd : 1 ≤ d) (radius : ℕ → ℝ) (N : ℕ) :
    (sphereDenominator d radius N).totalDegree = 2 * N := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [sphereDenominator_succ, complexPolynomial_totalDegree_mul _ _
      (sphereDenominator_ne_zero hd radius N) (spherePolynomial_ne_zero hd _), ih]
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : d ≠ 0)
    rw [spherePolynomial_totalDegree]
    omega

theorem sphereDenominator_eval_real {d N : ℕ} (radius : ℕ → ℝ) (x : Euclidean d) :
    eval (fun j => (x j : ℂ)) (sphereDenominator d radius N) =
      ∏ j ∈ Finset.range N, ((‖x‖ ^ 2 - radius (j + 1) ^ 2 : ℝ) : ℂ) := by
  simp only [sphereDenominator, map_prod, polynomialEvaluation_spherePolynomial]

theorem sphereDenominator_eval_eq_zero_on_sphere {d N j : ℕ} (radius : ℕ → ℝ)
    (hj : 0 < j) (hjN : j ≤ N) (x : Euclidean d) (hx : ‖x‖ = radius j) :
    eval (fun k => (x k : ℂ)) (sphereDenominator d radius N) = 0 := by
  rw [sphereDenominator_eval_real]
  apply Finset.prod_eq_zero_iff.mpr
  refine ⟨j - 1, Finset.mem_range.mpr (by omega), ?_⟩
  have hj' : j - 1 + 1 = j := by omega
  simp [hj', hx]

theorem sphereDenominator_eval_ne_zero {d N : ℕ} (radius : ℕ → ℝ)
    (hr : ∀ j, 0 < j → 0 < radius j) (x : Euclidean d)
    (hx : ∀ j, 0 < j → j ≤ N → ‖x‖ ≠ radius j) :
    eval (fun k => (x k : ℂ)) (sphereDenominator d radius N) ≠ 0 := by
  rw [sphereDenominator, map_prod]
  apply Finset.prod_ne_zero_iff.mpr
  intro j hj
  have he := polynomialEvaluation_spherePolynomial_eq_zero_iff x (radius (j + 1))
    (hr _ (by omega)).le
  exact fun hz => hx (j + 1) (by omega) (by simpa using Finset.mem_range.mp hj) (he.mp hz)

theorem sphereDenominator_eval_zero_ne_zero {d N : ℕ} (radius : ℕ → ℝ)
    (hr : ∀ j, 0 < j → 0 < radius j) :
    eval (fun _ : Fin d => (0 : ℂ)) (sphereDenominator d radius N) ≠ 0 := by
  simpa using sphereDenominator_eval_ne_zero (N := N) radius hr (0 : Euclidean d)
    (fun j hj _ => by simpa using (hr j hj).ne)

/-- The denominator in the paper's `q=4π²∑zᵢ²` convention. -/
def sourceSphereDenominator (d : ℕ) (radius : ℕ → ℝ) (N : ℕ) : ComplexPolynomial d :=
  ∏ j ∈ Finset.range N,
    C ((4 * Real.pi ^ 2 : ℝ) : ℂ) * spherePolynomial d (radius (j + 1))

theorem sourceSphereDenominator_eq (d N : ℕ) (radius : ℕ → ℝ) :
    sourceSphereDenominator d radius N =
      C (((4 * Real.pi ^ 2) ^ N : ℝ) : ℂ) * sphereDenominator d radius N := by
  simp [sourceSphereDenominator, sphereDenominator, Finset.prod_mul_distrib, map_pow]

theorem sourceSphereFactor_eval {d : ℕ} (r : ℝ) (z : ComplexEuclidean d) :
    eval (fun j => z j) (C ((4 * Real.pi ^ 2 : ℝ) : ℂ) * spherePolynomial d r) =
      4 * (Real.pi : ℂ) ^ 2 * (∑ j, z j ^ 2) - ((2 * Real.pi * r : ℝ) : ℂ) ^ 2 := by
  simp only [spherePolynomial, map_mul, eval_C, map_sub, map_sum, map_pow, eval_X]
  push_cast
  ring

end RieszEuclidean.CompleteMinimal
