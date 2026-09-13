import RieszEuclidean.WindowWeakLimit
import Mathlib.Topology.Metrizable.Basic
open Filter TopologicalSpace Metric EMetric Set
namespace RieszEuclidean
/-- Beurling weak convergence implies convergence of extended distances to configurations. -/
theorem WeaklyConverges.tendsto_infEdist {d : ℕ}
    {Γ : ℕ → Set (Euclidean d)} {Γ₀ : Set (Euclidean d)}
    (h : WeaklyConverges Γ Γ₀) (x : Euclidean d) :
    Tendsto (fun n => infEdist x (Γ n)) atTop (nhds (infEdist x Γ₀)) := by
  apply tendsto_order.mpr
  constructor
  · intro b hb
    obtain ⟨r, hr, hbr, hri⟩ := ENNReal.lt_iff_exists_real_btwn.mp hb
    obtain ⟨s, hs, hrs, hsi⟩ := ENNReal.lt_iff_exists_real_btwn.mp hri
    have hrs' : r < s := (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hr).mp hrs
    obtain ⟨N, hN⟩ := h (‖x‖ + r + 1) (by positivity) (s - r) (by linarith)
    filter_upwards [eventually_ge_atTop N] with n hn
    apply hbr.trans_le
    by_contra hbad
    obtain ⟨y, hy, hxy⟩ := infEdist_lt_iff.mp (lt_of_not_ge hbad)
    have hxy' : dist x y < r := edist_lt_ofReal.mp hxy
    have hyR : ‖y‖ < ‖x‖ + r + 1 := by
      have ht := norm_sub_norm_le y x
      rw [← dist_eq_norm, dist_comm y x] at ht
      linarith
    obtain ⟨z, hz, hyz⟩ := (hN n hn).1 y hy hyR
    have hxz : dist x z < s := by linarith [dist_triangle x y z]
    have hi := infEdist_le_edist_of_mem (x := x) hz
    have he : edist x z < ENNReal.ofReal s := edist_lt_ofReal.mpr hxz
    exact (not_lt_of_ge (hsi.le.trans hi)) he
  · intro b hb
    obtain ⟨y, hy, hxy⟩ := infEdist_lt_iff.mp hb
    obtain ⟨r, hr, hdr, hrb⟩ := ENNReal.lt_iff_exists_real_btwn.mp hxy
    have hdr' : dist x y < r := edist_lt_ofReal.mp hdr
    obtain ⟨N, hN⟩ := h (‖y‖ + 1) (by positivity) (r - dist x y) (by linarith)
    filter_upwards [eventually_ge_atTop N] with n hn
    obtain ⟨a, ha, hay⟩ := (hN n hn).2 y hy (by linarith)
    have hxa : dist x a < r := by
      have ht := dist_triangle x y a
      rw [dist_comm y a] at ht
      linarith
    exact (infEdist_le_edist_of_mem ha).trans_lt ((edist_lt_ofReal.mpr hxa).trans hrb)
end RieszEuclidean
