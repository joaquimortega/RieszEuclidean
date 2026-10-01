import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.NormedSpace.HahnBanach.Separation
import Mathlib.Analysis.Complex.Basic
import RieszEuclidean.TitchmarshCompactHull

/-!
# Convex geometry for the Titchmarsh–Lions support theorem

This file packages the finite-dimensional geometric step which passes from
approximate support identities to the exact convex-hull inclusion.
-/

open Set
open scoped Pointwise

namespace RieszEuclidean.CompleteMinimal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [LocallyConvexSpace ℝ E]

/-- A point outside a convex hull can be strictly separated from it by a continuous
real linear functional. We retain a weak inequality on the original set for use
with support approximations. -/
theorem exists_strict_separating_functional_of_not_mem_convexHull
    {C : Set E} {x : E}
    (hclosed : IsClosed (convexHull ℝ C))
    (hx : x ∉ convexHull ℝ C) :
    ∃ (ℓ : E →L[ℝ] ℝ) (T : ℝ),
      ℓ x < T ∧ ∀ c ∈ C, T ≤ ℓ c := by
  obtain ⟨ℓ, T, hxT, hTC⟩ :=
    geometric_hahn_banach_point_closed
      (convex_convexHull ℝ C) hclosed hx
  refine ⟨ℓ, T, hxT, ?_⟩
  intro c hc
  exact le_of_lt (hTC c (subset_convexHull ℝ C hc))

/-- If every pair of points in `A × B` can be approximated by support sets whose
Minkowski-sum convex hull is exact, and the resulting support lies within ε of `C`,
then the exact sum of the convex hulls of `A` and `B` lies in the convex hull of `C`.

The proof separates a hypothetical point outside `convexHull C`; the functional's
operator norm controls the error introduced by the ε-neighborhood. -/
theorem convexHull_add_subset_convexHull_of_approx
    {A B C : Set E}
    (hclosed : IsClosed (convexHull ℝ C))
    (happrox : ∀ ⦃a b : E⦄, a ∈ A → b ∈ B → ∀ ε : ℝ, 0 < ε →
      ∃ Aε Bε Cε : Set E,
        a ∈ Aε ∧ b ∈ Bε ∧
        convexHull ℝ Cε = convexHull ℝ Aε + convexHull ℝ Bε ∧
        Cε ⊆ C + Metric.closedBall (0 : E) ε) :
    convexHull ℝ A + convexHull ℝ B ⊆ convexHull ℝ C := by
  have hsum : A + B ⊆ convexHull ℝ C := by
    rintro x ⟨a, ha, b, hb, rfl⟩
    by_contra hx
    obtain ⟨ℓ, T, hlt, hsep⟩ :=
      exists_strict_separating_functional_of_not_mem_convexHull hclosed hx
    let ε : ℝ := (T - ℓ (a + b)) / (2 * (‖ℓ‖ + 1))
    have hgap : 0 < T - ℓ (a + b) := sub_pos.mpr hlt
    have hε : 0 < ε := by
      dsimp [ε]
      positivity
    obtain ⟨Aε, Bε, Cε, haε, hbε, hconv, hCε⟩ := happrox ha hb ε hε
    have hbase : ∀ z ∈ Cε, T - ‖ℓ‖ * ε ≤ ℓ z := by
      intro z hz
      obtain ⟨c, hc, y, hy, rfl⟩ := Set.mem_add.mp (hCε hz)
      have hy' : ‖y‖ ≤ ε := by
        simpa only [Metric.mem_closedBall, dist_zero_right] using hy
      have hnorm := ℓ.le_opNorm y
      rw [map_add]
      have hAbs : |ℓ y| ≤ ‖ℓ‖ * ε := by
        simpa only [Real.norm_eq_abs] using
          hnorm.trans (mul_le_mul_of_nonneg_left hy' (norm_nonneg _))
      have hly : -(‖ℓ‖ * ε) ≤ ℓ y := (abs_le.mp hAbs).1
      linarith [hsep c hc]
    have hℓ : IsLinearMap ℝ ℓ := ⟨map_add ℓ, map_smul ℓ⟩
    have hhalf : Convex ℝ {z : E | T - ‖ℓ‖ * ε ≤ ℓ z} :=
      convex_halfSpace_ge hℓ _
    have hconvbase : convexHull ℝ Cε ⊆ {z : E | T - ‖ℓ‖ * ε ≤ ℓ z} :=
      convexHull_min hbase hhalf
    have hpoint : a + b ∈ convexHull ℝ Cε := by
      rw [hconv]
      exact Set.mem_add.mpr
        ⟨a, subset_convexHull ℝ Aε haε, b, subset_convexHull ℝ Bε hbε, rfl⟩
    have hlow := hconvbase hpoint
    have hεeq : ε * (2 * (‖ℓ‖ + 1)) = T - ℓ (a + b) := by
      dsimp [ε]
      field_simp
    change T - ‖ℓ‖ * ε ≤ ℓ (a + b) at hlow
    nlinarith [hεeq, norm_nonneg ℓ, hε]
  calc
    convexHull ℝ A + convexHull ℝ B = convexHull ℝ (A + B) := (convexHull_add A B).symm
    _ ⊆ convexHull ℝ (convexHull ℝ C) := convexHull_mono hsum
    _ = convexHull ℝ C := (convex_convexHull ℝ C).convexHull_eq

/-- Compact-target version of `convexHull_add_subset_convexHull_of_approx` in a
finite-dimensional space. Compactness makes the algebraic convex hull closed. -/
theorem convexHull_add_subset_convexHull_of_approx_of_compact
    [FiniteDimensional ℝ E] {A B C : Set E} (hC : IsCompact C)
    (happrox : ∀ ⦃a b : E⦄, a ∈ A → b ∈ B → ∀ ε : ℝ, 0 < ε →
      ∃ Aε Bε Cε : Set E,
        a ∈ Aε ∧ b ∈ Bε ∧
        convexHull ℝ Cε = convexHull ℝ Aε + convexHull ℝ Bε ∧
        Cε ⊆ C + Metric.closedBall (0 : E) ε) :
    convexHull ℝ A + convexHull ℝ B ⊆ convexHull ℝ C :=
  convexHull_add_subset_convexHull_of_approx
    (RieszEuclidean.Titchmarsh.isCompact_convexHull_of_compact hC).isClosed happrox

/-! ### Recovery of a convex support hull from directional endpoint bounds -/

/-- If a continuous compactly supported function `h` vanishes to one side of every
separating hyperplane, and the endpoint of its support is at least the sum of the
two factor endpoints in every direction, then its support hull contains the sum
of the factor support hulls. The other inclusion is supplied by `hforward`.

The closedness assumption is automatic once one has the finite-dimensional
compact-convex-hull lemma for `tsupport h`. -/
theorem convexHull_tsupport_eq_add_of_all_direction_endpoint
    {f g h : E → ℂ}
    (hclosed : IsClosed (convexHull ℝ (tsupport h)))
    (hforward : convexHull ℝ (tsupport h) ⊆
      convexHull ℝ (tsupport f) + convexHull ℝ (tsupport g))
    (hendpoint : ∀ (ℓ : E →L[ℝ] ℝ) (T : ℝ),
      (∀ z, ℓ z < T → h z = 0) →
      ∀ x y, f x ≠ 0 → g y ≠ 0 → T ≤ ℓ (x + y)) :
    convexHull ℝ (tsupport h) =
      convexHull ℝ (tsupport f) + convexHull ℝ (tsupport g) := by
  have hsum : tsupport f + tsupport g ⊆ convexHull ℝ (tsupport h) := by
    rintro z ⟨x, hx, y, hy, rfl⟩
    by_contra hnot
    obtain ⟨ℓ, T, hlt, hsep⟩ :=
      exists_strict_separating_functional_of_not_mem_convexHull hclosed hnot
    have hvanish : ∀ z, ℓ z < T → h z = 0 := by
      intro z hz
      by_contra hhz
      have hts : z ∈ tsupport h := subset_tsupport _ hhz
      exact (not_lt_of_ge (hsep z hts)) hz
    have hpair : ∀ x ∈ tsupport f, ∀ y ∈ tsupport g, T ≤ ℓ (x + y) := by
      intro x hx y hy
      have hfor_y : ∀ y' ∈ Function.support g, T ≤ ℓ (x + y') := by
        intro y' hy'
        have hfhalf : Function.support f ⊆ {x' | T ≤ ℓ (x' + y')} := by
          intro x' hx'
          change f x' ≠ 0 at hx'
          change g y' ≠ 0 at hy'
          exact hendpoint ℓ T hvanish x' y' hx' hy'
        have hfclosed : IsClosed {x' : E | T ≤ ℓ (x' + y')} := by
          exact isClosed_le continuous_const
            (ℓ.continuous.comp (continuous_id.add continuous_const))
        have hx' : T ≤ ℓ (x + y') := by
          have hcl : closure (Function.support f) ⊆ {x' | T ≤ ℓ (x' + y')} :=
            closure_minimal hfhalf hfclosed
          exact hcl hx
        exact hx'
      have hgclosed : IsClosed {y' : E | T ≤ ℓ (x + y')} := by
        exact isClosed_le continuous_const
          (ℓ.continuous.comp (continuous_const.add continuous_id))
      have hcl : closure (Function.support g) ⊆ {y' | T ≤ ℓ (x + y')} :=
        closure_minimal hfor_y hgclosed
      exact hcl hy
    exact (not_lt_of_ge (hpair x hx y hy)) hlt
  have hback : convexHull ℝ (tsupport f) + convexHull ℝ (tsupport g) ⊆
      convexHull ℝ (tsupport h) := by
    calc
      convexHull ℝ (tsupport f) + convexHull ℝ (tsupport g) =
          convexHull ℝ (tsupport f + tsupport g) :=
        (convexHull_add (tsupport f) (tsupport g)).symm
      _ ⊆ convexHull ℝ (convexHull ℝ (tsupport h)) := convexHull_mono hsum
      _ = convexHull ℝ (tsupport h) := (convex_convexHull ℝ (tsupport h)).convexHull_eq
  exact Set.Subset.antisymm hforward hback

/-- Compact-support version of the all-directions endpoint criterion. -/
theorem convexHull_tsupport_eq_add_of_all_direction_endpoint_of_compact
    [FiniteDimensional ℝ E] {f g h : E → ℂ}
    (hh : IsCompact (tsupport h))
    (hforward : convexHull ℝ (tsupport h) ⊆
      convexHull ℝ (tsupport f) + convexHull ℝ (tsupport g))
    (hendpoint : ∀ (ℓ : E →L[ℝ] ℝ) (T : ℝ),
      (∀ z, ℓ z < T → h z = 0) →
      ∀ x y, f x ≠ 0 → g y ≠ 0 → T ≤ ℓ (x + y)) :
    convexHull ℝ (tsupport h) =
      convexHull ℝ (tsupport f) + convexHull ℝ (tsupport g) :=
  convexHull_tsupport_eq_add_of_all_direction_endpoint
    (RieszEuclidean.Titchmarsh.isCompact_convexHull_of_compact hh).isClosed
    hforward hendpoint

end RieszEuclidean.CompleteMinimal
