import RieszEuclidean.LocalExtraction
open Filter TopologicalSpace Metric EMetric
namespace RieszEuclidean
/-- Hausdorff convergence gives uniform two-sided matching of points. -/
theorem hausdorff_eventually_matching {α : Type*} [MetricSpace α]
    {C : ℕ → Closeds α} {D : Closeds α} (h : Tendsto C atTop (nhds D))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop,
      (∀ x ∈ C n, ∃ y ∈ D, dist x y < ε) ∧
      (∀ y ∈ D, ∃ x ∈ C n, dist y x < ε) := by
  have he := (EMetric.tendsto_atTop.mp h) (ENNReal.ofReal ε) (by positivity)
  obtain ⟨N, hN⟩ := he
  filter_upwards [eventually_ge_atTop N] with n hn
  have hd := hN n hn
  constructor
  · intro x hx
    obtain ⟨y, hy, hxy⟩ := exists_edist_lt_of_hausdorffEdist_lt hx hd
    exact ⟨y, hy, edist_lt_ofReal.mp hxy⟩
  · intro y hy
    have hd' : edist D (C n) < ENNReal.ofReal ε := by rwa [edist_comm]
    obtain ⟨x, hx, hyx⟩ := exists_edist_lt_of_hausdorffEdist_lt hy hd'
    exact ⟨x, hx, edist_lt_ofReal.mp hyx⟩
/-- A convergent sequence of points in Hausdorff-convergent closed sets lies in the limit. -/
theorem hausdorff_mem_of_tendsto {α : Type*} [MetricSpace α]
    {C : ℕ → Closeds α} {D : Closeds α} (h : Tendsto C atTop (nhds D))
    {x : ℕ → α} {y : α} (hx : ∀ n, x n ∈ C n)
    (hy : Tendsto x atTop (nhds y)) : y ∈ D := by
  apply (mem_iff_infEdist_zero_of_closed D.isClosed).mpr
  have ht := (continuous_infEdist_hausdorffEdist.tendsto (y, D)).comp (hy.prodMk_nhds h)
  have hz : (fun n => infEdist (x n) (C n)) = fun _ => 0 :=
    funext fun n => infEdist_zero_of_mem (hx n)
  change Tendsto (fun n => infEdist (x n) (C n)) atTop (nhds (infEdist y D)) at ht
  rw [hz] at ht
  exact tendsto_nhds_unique ht tendsto_const_nhds
/-- Hausdorff limits preserve a common separation constant. -/
theorem hausdorff_separated {α : Type*} [MetricSpace α] {δ : ℝ}
    {C : ℕ → Closeds α} {D : Closeds α}
    (h : Tendsto C atTop (nhds D))
    (hs : ∀ n, ∀ ⦃x⦄, x ∈ C n → ∀ ⦃y⦄, y ∈ C n → x ≠ y → δ ≤ dist x y) :
    ∀ ⦃x⦄, x ∈ D → ∀ ⦃y⦄, y ∈ D → x ≠ y → δ ≤ dist x y := by
  intro x hx y hy hxy
  by_contra hn
  have hgap : 0 < δ - dist x y := sub_pos.mpr (lt_of_not_ge hn)
  have hdist : 0 < dist x y := dist_pos.mpr hxy
  let ε := min (dist x y / 3) ((δ - dist x y) / 3)
  have hε : 0 < ε := lt_min (by positivity) (by positivity)
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hausdorff_eventually_matching h hε)
  obtain ⟨a, ha, hxa⟩ := (hN N le_rfl).2 x hx
  obtain ⟨b, hb, hyb⟩ := (hN N le_rfl).2 y hy
  have he1 : ε ≤ dist x y / 3 := min_le_left _ _
  have he2 : ε ≤ (δ - dist x y) / 3 := min_le_right _ _
  have hab : a ≠ b := by
    intro heq
    have ht := dist_triangle x a y
    rw [← heq] at hyb
    rw [dist_comm a y] at ht
    linarith
  have hsep := hs N ha hb hab
  have ht := dist_triangle a x b
  have ht' := dist_triangle x y b
  rw [dist_comm a x] at ht
  linarith
end RieszEuclidean
