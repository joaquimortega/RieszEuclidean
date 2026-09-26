import RieszEuclidean.CompleteMinimalLocalDivision
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.MetricSpace.HausdorffDistance

/-!
# Removal of the quadric zeros of an entire denominator

Local simple-zero factorizations of the denominator and quadric vanishing of the
numerator give actual analytic local quotients. Their uniqueness then glues them
to a single entire quotient.
-/

noncomputable section
open scoped Topology
open Set Filter

namespace RieszEuclidean.CompleteMinimal

section Gluing

variable {E : Type*} [NormedAddCommGroup E]

/-- A nonzero entire function cannot vanish on any neighborhood. -/
theorem entire_not_eventually_zero [NormedSpace ℂ E] [ConnectedSpace E]
    (κ : E → ℂ) (hκ : AnalyticOnNhd ℂ κ univ)
    (hbase : ∃ z, κ z ≠ 0) (z₀ : E) : ¬∀ᶠ z in 𝓝 z₀, κ z = 0 := by
  intro hz
  obtain ⟨z, hzκ⟩ := hbase
  have hκzero : EqOn κ 0 univ :=
    hκ.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ (mem_univ z₀) hz
  exact hzκ (hκzero (mem_univ z))

/-- Continuous local quotients have a unique value wherever the denominator is not
locally identically zero, including at its zeros. -/
theorem local_quotient_value_unique (A κ H K : E → ℂ) (z₀ : E)
    (hκ : ¬∀ᶠ z in 𝓝 z₀, κ z = 0) (hH : ContinuousAt H z₀) (hK : ContinuousAt K z₀)
    (hAH : ∀ᶠ z in 𝓝 z₀, A z = κ z * H z)
    (hAK : ∀ᶠ z in 𝓝 z₀, A z = κ z * K z) : H z₀ = K z₀ := by
  by_contra hne
  have hdiff : H z₀ - K z₀ ≠ 0 := sub_ne_zero.mpr hne
  apply hκ
  filter_upwards [hAH, hAK, (hH.sub hK).eventually_ne hdiff] with z hAH hAK hne
  by_contra hz
  apply hne
  apply sub_eq_zero.mpr
  exact mul_left_cancel₀ hz (hAH.symm.trans hAK)

/-- Genuine gluing of analytic local quotients. The output is an entire function
with the product identity everywhere and the ordinary quotient off the zero set. -/
theorem global_analytic_division_of_local [NormedSpace ℂ E] [ConnectedSpace E] (A κ : E → ℂ)
    (hκ : AnalyticOnNhd ℂ κ univ) (hbase : ∃ z, κ z ≠ 0)
    (hlocal : ∀ z₀, ∃ H : E → ℂ, AnalyticAt ℂ H z₀ ∧
      ∀ᶠ z in 𝓝 z₀, A z = κ z * H z) :
    ∃ G : E → ℂ, AnalyticOnNhd ℂ G univ ∧ (∀ z, A z = κ z * G z) ∧
      ∀ z, κ z ≠ 0 → G z = A z / κ z := by
  choose H hH hAH using hlocal
  let G : E → ℂ := fun z => H z z
  have hG : AnalyticOnNhd ℂ G univ := by
    intro z₀ _
    apply (hH z₀).congr
    filter_upwards [(hH z₀).eventually_analyticAt, (hAH z₀).eventually_nhds] with z hz hAz
    exact local_quotient_value_unique A κ (H z₀) (H z) z
      (entire_not_eventually_zero κ hκ hbase z) hz.continuousAt (hH z).continuousAt
      hAz (hAH z)
  have hprod : ∀ z, A z = κ z * G z := fun z => (hAH z).self_of_nhds
  refine ⟨G, hG, hprod, ?_⟩
  intro z hz
  apply (eq_div_iff hz).mpr
  simpa only [mul_comm] using (hprod z).symm

end Gluing

/-- The precise local geometry needed from the Bessel product: every zero belongs
to a positive-radius quadric, and the denominator is its equation times an analytic unit. -/
def HasSimpleQuadricZeros {n : ℕ} {ι : Type*} (κ : ComplexEuclidean n → ℂ) (radius : ι → ℝ) : Prop :=
  ∀ z₀, κ z₀ = 0 → ∃ i, squareSum (fun j => z₀ j) = (radius i : ℂ) ^ 2 ∧
    ∃ u : ComplexEuclidean n → ℂ, AnalyticAt ℂ u z₀ ∧ u z₀ ≠ 0 ∧
      ∀ᶠ z in 𝓝 z₀, κ z = (squareSum (fun j => z j) - (radius i : ℂ) ^ 2) * u z

/-- The local analytic quotient at every point, derived from actual simple quadric
factorizations rather than postulated as an analytic input. -/
theorem local_analytic_division_of_simple_quadric_zeros {n : ℕ} {ι : Type*}
    (A κ : ComplexEuclidean n → ℂ) (radius : ι → ℝ)
    (hA : AnalyticOnNhd ℂ A univ) (hκ : AnalyticOnNhd ℂ κ univ)
    (hradius : ∀ i, 0 < radius i) (hgeometry : HasSimpleQuadricZeros κ radius)
    (hzero : ∀ i z, squareSum (fun j => z j) = (radius i : ℂ) ^ 2 → A z = 0)
    (z₀ : ComplexEuclidean n) :
    ∃ H : ComplexEuclidean n → ℂ, AnalyticAt ℂ H z₀ ∧
      ∀ᶠ z in 𝓝 z₀, A z = κ z * H z := by
  by_cases hz₀ : κ z₀ = 0
  · obtain ⟨i, hquadric, u, hu, hunit, hfactor⟩ := hgeometry z₀ hz₀
    obtain ⟨U, K, hU, hzU, hK, hAK⟩ := quadric_local_analytic_division A (radius i)
      (hradius i) z₀ hquadric (hA z₀ (mem_univ z₀)) (hzero i)
    let H : ComplexEuclidean n → ℂ := fun z => K z / u z
    refine ⟨H, (hK z₀ hzU).fun_div hu hunit, ?_⟩
    filter_upwards [hU.mem_nhds hzU, hfactor, hu.continuousAt.eventually_ne hunit]
      with z hz hfactor hunit
    rw [hAK z hz, hfactor]
    change (squareSum (fun j => z j) - (radius i : ℂ) ^ 2) * K z =
      ((squareSum (fun j => z j) - (radius i : ℂ) ^ 2) * u z) * (K z / u z)
    field_simp
    ring
  · let H : ComplexEuclidean n → ℂ := fun z => A z / κ z
    refine ⟨H, (hA z₀ (mem_univ z₀)).fun_div (hκ z₀ (mem_univ z₀)) hz₀, ?_⟩
    filter_upwards [(hκ z₀ (mem_univ z₀)).continuousAt.eventually_ne hz₀] with z hz
    change A z = κ z * (A z / κ z)
    field_simp

/-- Global analytic removal of all the simple quadric zeros of an entire denominator.
Disjointness and local finiteness of the Bessel quadrics are used to establish
`HasSimpleQuadricZeros`; no global quotient is assumed here. -/
theorem global_analytic_division_of_simple_quadric_zeros {n : ℕ} {ι : Type*}
    (A κ : ComplexEuclidean n → ℂ) (radius : ι → ℝ)
    (hA : AnalyticOnNhd ℂ A univ) (hκ : AnalyticOnNhd ℂ κ univ) (hκ₀ : κ 0 ≠ 0)
    (hradius : ∀ i, 0 < radius i) (hgeometry : HasSimpleQuadricZeros κ radius)
    (hzero : ∀ i z, squareSum (fun j => z j) = (radius i : ℂ) ^ 2 → A z = 0) :
    ∃ G : ComplexEuclidean n → ℂ, AnalyticOnNhd ℂ G univ ∧
      (∀ z, A z = κ z * G z) ∧ ∀ z, κ z ≠ 0 → G z = A z / κ z := by
  exact global_analytic_division_of_local A κ hκ ⟨0, hκ₀⟩
    (local_analytic_division_of_simple_quadric_zeros A κ radius hA hκ hradius hgeometry hzero)

/-- Bounded derivatives and vanishing at the radial zeros supply exactly the distance
factor needed to cancel the denominator's small values near those zeros. -/
theorem radial_numerator_cancellation (H H' : ℝ → ℂ) (Z : Set ℝ)
    (hZ : IsClosed Z) (hZne : Z.Nonempty) (C : ℝ) (hC : 0 ≤ C) (m : ℕ)
    (hH : ∀ s, ‖H s‖ ≤ C * (1 + ‖s‖) ^ m)
    (hderiv : ∀ s, HasDerivAt H (H' s) s)
    (hH' : ∀ s, ‖H' s‖ ≤ C * (1 + ‖s‖) ^ m) (hzero : ∀ a ∈ Z, H a = 0) (s : ℝ) :
    ‖H s‖ ≤ C * 2 ^ m * (1 + ‖s‖) ^ m * min 1 (Metric.infDist s Z) := by
  by_cases hd : 1 ≤ Metric.infDist s Z
  · rw [min_eq_left hd, mul_one]
    calc
      ‖H s‖ ≤ C * (1 + ‖s‖) ^ m := hH s
      _ ≤ C * 2 ^ m * (1 + ‖s‖) ^ m := by
        have hp : (1 : ℝ) ≤ 2 ^ m := one_le_pow₀ (by norm_num)
        nlinarith [mul_nonneg hC (pow_nonneg (by positivity : 0 ≤ 1 + ‖s‖) m)]
  · have hd : Metric.infDist s Z < 1 := lt_of_not_ge hd
    obtain ⟨a, ha, hdist⟩ := hZ.exists_infDist_eq_dist hZne s
    have haB : a ∈ Metric.closedBall s 1 := by
      rw [Metric.mem_closedBall, dist_comm, ← hdist]
      exact hd.le
    have hsB : s ∈ Metric.closedBall s 1 := Metric.mem_closedBall_self (by norm_num)
    have hbound : ∀ t ∈ Metric.closedBall s 1, ‖H' t‖ ≤ C * 2 ^ m * (1 + ‖s‖) ^ m := by
      intro t ht
      have hts : ‖t - s‖ ≤ 1 := by simpa only [dist_eq_norm] using Metric.mem_closedBall.mp ht
      have htbound : 1 + ‖t‖ ≤ 2 * (1 + ‖s‖) := by
        have htri : ‖t‖ ≤ ‖t - s‖ + ‖s‖ := by
          simpa only [sub_add_cancel] using norm_add_le (t - s) s
        have hsnonneg := norm_nonneg s
        linarith
      calc
        ‖H' t‖ ≤ C * (1 + ‖t‖) ^ m := hH' t
        _ ≤ C * (2 * (1 + ‖s‖)) ^ m := by gcongr
        _ = C * 2 ^ m * (1 + ‖s‖) ^ m := by rw [mul_pow, mul_assoc]
    have hmean := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun t (_ : t ∈ Metric.closedBall s 1) => (hderiv t).hasDerivWithinAt)
      hbound (convex_closedBall s 1) haB hsB
    rw [hzero a ha, sub_zero, ← dist_eq_norm, ← hdist] at hmean
    rwa [min_eq_right hd.le]

/-- A quantitative radial denominator lower bound and actual numerator derivatives give
a polynomial bound for its quotient away from the radial zeros. -/
theorem radial_quotient_bound_off_zeros (H H' k G : ℝ → ℂ) (Z : Set ℝ)
    (hZ : IsClosed Z) (hZne : Z.Nonempty) (C c : ℝ) (hC : 0 ≤ C) (hc : 0 < c) (m b : ℕ)
    (hH : ∀ s, ‖H s‖ ≤ C * (1 + ‖s‖) ^ m)
    (hderiv : ∀ s, HasDerivAt H (H' s) s)
    (hH' : ∀ s, ‖H' s‖ ≤ C * (1 + ‖s‖) ^ m) (hzero : ∀ a ∈ Z, H a = 0)
    (hprod : ∀ s, H s = k s * G s) (s : ℝ) (hs : s ∉ Z)
    (hlower : c / (1 + ‖s‖) ^ b * min 1 (Metric.infDist s Z) ≤ ‖k s‖) :
    ‖G s‖ ≤ (C * 2 ^ m / c) * (1 + ‖s‖) ^ (m + b) := by
  have hd : 0 < Metric.infDist s Z := (hZ.not_mem_iff_infDist_pos hZne).mp hs
  have hδ : 0 < min 1 (Metric.infDist s Z) := lt_min (by norm_num) hd
  have hw : 0 < (1 + ‖s‖) ^ b := pow_pos (by positivity) _
  have hcancel := radial_numerator_cancellation H H' Z hZ hZne C hC m hH hderiv hH' hzero s
  have hle : (c / (1 + ‖s‖) ^ b * ‖G s‖) * min 1 (Metric.infDist s Z) ≤
      (C * 2 ^ m * (1 + ‖s‖) ^ m) * min 1 (Metric.infDist s Z) := by
    calc
      _ = (c / (1 + ‖s‖) ^ b * min 1 (Metric.infDist s Z)) * ‖G s‖ := by ring
      _ ≤ ‖k s‖ * ‖G s‖ := mul_le_mul_of_nonneg_right hlower (norm_nonneg _)
      _ = ‖H s‖ := by rw [hprod s, norm_mul]
      _ ≤ _ := hcancel
  have hle' := (mul_le_mul_right hδ).mp hle
  have hmul : c * ‖G s‖ ≤ (C * 2 ^ m) * (1 + ‖s‖) ^ (m + b) := by
    have h := mul_le_mul_of_nonneg_right hle' hw.le
    calc
      c * ‖G s‖ = (c / (1 + ‖s‖) ^ b * ‖G s‖) * (1 + ‖s‖) ^ b := by field_simp
      _ ≤ (C * 2 ^ m * (1 + ‖s‖) ^ m) * (1 + ‖s‖) ^ b := h
      _ = _ := by rw [pow_add]; ring
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hc).mpr
  simpa only [mul_comm] using hmul

/-- Continuity removes the excluded radial zeros from the polynomial quotient estimate.
The denominator lower bound is needed only beyond the indicated radial threshold. -/
theorem radial_quotient_polynomial_bound (H H' k G : ℝ → ℂ) (Z : Set ℝ)
    (hZ : IsClosed Z) (hZne : Z.Nonempty) (hdense : Dense Zᶜ)
    (C c R : ℝ) (hC : 0 ≤ C) (hc : 0 < c) (m b : ℕ)
    (hH : ∀ s, ‖H s‖ ≤ C * (1 + ‖s‖) ^ m)
    (hderiv : ∀ s, HasDerivAt H (H' s) s)
    (hH' : ∀ s, ‖H' s‖ ≤ C * (1 + ‖s‖) ^ m) (hzero : ∀ a ∈ Z, H a = 0)
    (hprod : ∀ s, H s = k s * G s) (hG : Continuous G)
    (hlower : ∀ s, R < s → c / (1 + ‖s‖) ^ b * min 1 (Metric.infDist s Z) ≤ ‖k s‖) :
    ∀ s, R < s → ‖G s‖ ≤ (C * 2 ^ m / c) * (1 + ‖s‖) ^ (m + b) := by
  intro s hs
  by_contra hbound
  have hstrict : (C * 2 ^ m / c) * (1 + ‖s‖) ^ (m + b) < ‖G s‖ := lt_of_not_ge hbound
  have hweight : Continuous (fun t : ℝ => (C * 2 ^ m / c) * (1 + ‖t‖) ^ (m + b)) := by
    fun_prop
  have hevent := hweight.continuousAt.eventually_lt hG.norm.continuousAt hstrict
  have htail : ∀ᶠ t in 𝓝 s, R < t := isOpen_Ioi.mem_nhds hs
  have hfreq : ∃ᶠ t in 𝓝 s, t ∈ Zᶜ := mem_closure_iff_frequently.mp (hdense s)
  obtain ⟨t, ⟨htZ, htR⟩, hlt⟩ := ((hfreq.and_eventually htail).and_eventually hevent).exists
  exact (not_lt_of_ge (radial_quotient_bound_off_zeros H H' k G Z hZ hZne C c hC hc m b
    hH hderiv hH' hzero hprod t htZ (hlower t htR))) hlt

end RieszEuclidean.CompleteMinimal
