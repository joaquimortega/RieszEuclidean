import RieszEuclidean.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic.Linarith
import Mathlib.Topology.Algebra.Indicator
open Set MeasureTheory Filter
namespace RieszEuclidean
/-- A probability kernel smoothed against the actual translated indicator. -/
noncomputable def smoothedIndicator {d : ℕ} (k : Euclidean d → ℝ)
    (Ω : Set (Euclidean d)) (x : Euclidean d) : ℝ :=
  ∫ y, k y * Ω.indicator (fun _ => (1 : ℝ)) (x - y)
/-- Integrability of the concrete smoothed-indicator integrand. -/
theorem integrable_smoothedIndicator {d : ℕ} {k : Euclidean d → ℝ}
    (hk : Integrable k) {Ω : Set (Euclidean d)} (hΩ : MeasurableSet Ω)
    (x : Euclidean d) :
    Integrable (fun y => k y * Ω.indicator (fun _ => (1 : ℝ)) (x - y)) := by
  have hi := hk.indicator (hΩ.preimage ((measurable_const (a := x)).sub measurable_id))
  convert hi using 1
  ext y
  by_cases hy : x - y ∈ Ω <;> simp [hy]
/-- A nonnegative normalized kernel gives a cutoff between zero and one. -/
theorem smoothedIndicator_mem_Icc {d : ℕ} {k : Euclidean d → ℝ}
    (hk : Integrable k) (hpos : ∀ y, 0 ≤ k y) (hmass : ∫ y, k y = 1)
    {Ω : Set (Euclidean d)} (hΩ : MeasurableSet Ω) (x : Euclidean d) :
    smoothedIndicator k Ω x ∈ Icc (0 : ℝ) 1 := by
  constructor
  · apply integral_nonneg
    intro y
    by_cases hy : x - y ∈ Ω <;> simp [hy, hpos]
  · unfold smoothedIndicator
    calc
      _ ≤ ∫ y, k y := ?_
      _ = 1 := hmass
    apply integral_mono (integrable_smoothedIndicator hk hΩ x) hk
    intro y
    by_cases hy : x - y ∈ Ω <;> simp [hy, hpos]
/-- Away from the frontier, the indicator is constant on a small translated closed ball. -/
theorem exists_indicator_constant_ball {d : ℕ} {Ω : Set (Euclidean d)}
    {x : Euclidean d} (hx : x ∉ frontier Ω) :
    ∃ ε > 0, ∀ y : Euclidean d, ‖y‖ ≤ ε →
      Ω.indicator (fun _ => (1 : ℝ)) (x - y) = Ω.indicator (fun _ => (1 : ℝ)) x := by
  rw [← mem_compl_iff, compl_frontier_eq_union_interior] at hx
  rcases hx with hx | hx
  · obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hx)
    refine ⟨r / 2, by positivity, fun y hy => ?_⟩
    have hxy : x - y ∈ Ω := hball (by
      rw [Metric.mem_ball, dist_eq_norm, sub_sub_cancel_left, norm_neg]
      linarith)
    simp [hxy, interior_subset hx]
  · obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hx)
    refine ⟨r / 2, by positivity, fun y hy => ?_⟩
    have hxy : x - y ∈ Ωᶜ := hball (by
      rw [Metric.mem_ball, dist_eq_norm, sub_sub_cancel_left, norm_neg]
      linarith)
    have hn : x ∉ Ω := interior_subset hx
    have hny : x - y ∉ Ω := hxy
    simp [hny, hn]
/-- Cutoff error is bounded by the kernel mass outside any ball of local constancy. -/
theorem abs_smoothedIndicator_sub_le_tail {d : ℕ} {k : Euclidean d → ℝ}
    (hk : Integrable k) (hpos : ∀ y, 0 ≤ k y) (hmass : ∫ y, k y = 1)
    {Ω : Set (Euclidean d)} (hΩ : MeasurableSet Ω) (x : Euclidean d) (ε : ℝ)
    (hlocal : ∀ y : Euclidean d, ‖y‖ ≤ ε →
      Ω.indicator (fun _ => (1 : ℝ)) (x - y) = Ω.indicator (fun _ => (1 : ℝ)) x) :
    |smoothedIndicator k Ω x - Ω.indicator (fun _ => (1 : ℝ)) x| ≤
      ∫ y in {y : Euclidean d | ε < ‖y‖}, k y := by
  let c := Ω.indicator (fun _ => (1 : ℝ)) x
  let f := fun y => k y * Ω.indicator (fun _ => (1 : ℝ)) (x - y) - k y * c
  have hi : Integrable f := (integrable_smoothedIndicator hk hΩ x).sub (hk.mul_const c)
  have he : smoothedIndicator k Ω x - c = ∫ y, f y := by
    rw [integral_sub (integrable_smoothedIndicator hk hΩ x) (hk.mul_const c),
      integral_mul_const, hmass, one_mul]
    rfl
  have htail : MeasurableSet {y : Euclidean d | ε < ‖y‖} :=
    measurableSet_lt measurable_const continuous_norm.measurable
  rw [show Ω.indicator (fun _ => (1 : ℝ)) x = c from rfl, he, ← Real.norm_eq_abs]
  calc
    ‖∫ y, f y‖ ≤ ∫ y, ‖f y‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ y, {y : Euclidean d | ε < ‖y‖}.indicator k y := by
      apply integral_mono hi.norm (hk.indicator htail)
      intro y
      by_cases hy : ε < ‖y‖
      · simp only [Set.indicator_of_mem hy]
        dsimp [f, c]
        by_cases hx : x ∈ Ω <;> by_cases hxy : x - y ∈ Ω <;>
          simp [hx, hxy, hy, Real.norm_eq_abs, abs_of_nonneg (hpos y), hpos y]
      · have hl := hlocal y (le_of_not_gt hy)
        simp [f, hl, c, hy]
    _ = ∫ y in {y : Euclidean d | ε < ‖y‖}, k y := integral_indicator htail
/-- Concentrating nonnegative probability kernels converge to the indicator off its frontier. -/
theorem tendsto_smoothedIndicator {d : ℕ} {k : ℝ → Euclidean d → ℝ}
    (hk : ∀ R > 0, Integrable (k R))
    (hpos : ∀ R > 0, ∀ y, 0 ≤ k R y)
    (hmass : ∀ R > 0, ∫ y, k R y = 1)
    (htail : ∀ ε > 0, Tendsto (fun R : ℝ => ∫ y in {y : Euclidean d | ε < ‖y‖}, k R y)
      atTop (nhds 0))
    {Ω : Set (Euclidean d)} (hΩ : MeasurableSet Ω) {x : Euclidean d}
    (hx : x ∉ frontier Ω) :
    Tendsto (fun R : ℝ => smoothedIndicator (k R) Ω x) atTop
      (nhds (Ω.indicator (fun _ => (1 : ℝ)) x)) := by
  obtain ⟨ε, hε, hlocal⟩ := exists_indicator_constant_ball hx
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (g := fun R => Ω.indicator (fun _ => (1 : ℝ)) x - ∫ y in {y : Euclidean d | ε < ‖y‖}, k R y)
    (h := fun R => Ω.indicator (fun _ => (1 : ℝ)) x + ∫ y in {y : Euclidean d | ε < ‖y‖}, k R y)
    ?_ ?_ ?_ ?_
  · simpa using (tendsto_const_nhds (x := Ω.indicator (fun _ => (1 : ℝ)) x)).sub
      (htail ε hε)
  · simpa using (tendsto_const_nhds (x := Ω.indicator (fun _ => (1 : ℝ)) x)).add
      (htail ε hε)
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
    have h := abs_smoothedIndicator_sub_le_tail (hk R hR) (hpos R hR) (hmass R hR) hΩ x ε hlocal
    linarith [(abs_le.mp h).1]
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
    have h := abs_smoothedIndicator_sub_le_tail (hk R hR) (hpos R hR) (hmass R hR) hΩ x ε hlocal
    linarith [(abs_le.mp h).2]
end RieszEuclidean
