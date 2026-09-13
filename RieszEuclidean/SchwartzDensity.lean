import RieszEuclidean.FourierL2
import Mathlib.Topology.EMetricSpace.Paracompact
import Mathlib.Analysis.Calculus.BumpFunction.SmoothApprox
import Mathlib.MeasureTheory.Function.ContinuousMapDense

noncomputable section
open scoped ContDiff
open Metric Set Function MeasureTheory
open scoped ENNReal
namespace RieszEuclidean

/-- Smooth compactly supported functions are Schwartz functions. -/
def compactSchwartz {d : ℕ} (f : Euclidean d → ℂ)
    (hf : ContDiff ℝ ∞ f) (hs : HasCompactSupport f) :
    SchwartzMap (Euclidean d) ℂ where
  toFun := f
  smooth' := hf
  decay' k n := by
    have hc : Continuous (fun x => ‖x‖ ^ k * ‖iteratedFDeriv ℝ n f x‖) :=
      (continuous_norm.pow k).mul (hf.continuous_iteratedFDeriv (by exact_mod_cast le_top)).norm
    have hcs : HasCompactSupport (fun x => ‖x‖ ^ k * ‖iteratedFDeriv ℝ n f x‖) :=
      (hs.iteratedFDeriv n).norm.mul_left
    obtain ⟨C, hC⟩ := hcs.exists_bound_of_continuous hc
    exact ⟨C, fun x => (le_abs_self _).trans (hC x)⟩


/-- Local mollifier estimates preserve compact support within a fixed thickening. -/
theorem local_approx_support {d : ℕ} {f g : Euclidean d → ℂ} {r : ℝ}
    (hr1 : r ≤ 1)
    (hg : ∀ a δ, (∀ x ∈ ball a r, dist (f x) (f a) ≤ δ) → dist (g a) (f a) ≤ δ) :
    support g ⊆ cthickening 1 (tsupport f) := by
  intro a ha
  by_contra hnot
  have hfzero (x : Euclidean d) (hx : dist a x ≤ 1) : f x = 0 := by
    by_contra hxne
    exact hnot (mem_cthickening_of_dist_le a x 1 (tsupport f)
      (subset_tsupport f hxne) hx)
  have hfa : f a = 0 := hfzero a (by simp)
  have hga := hg a 0 (fun x hx => by
    have hfx := hfzero x ((by simpa [dist_comm] using hx : dist a x < r).le.trans hr1)
    simp [hfx, hfa])
  have : g a = 0 := by simpa [hfa] using hga
  exact ha this

/-- Uniform smooth approximation with all supports in one compact neighbourhood. -/
theorem smooth_compact_uniform_approx {d : ℕ} {f : Euclidean d → ℂ}
    (hf : Continuous f) (hs : HasCompactSupport f) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : Euclidean d → ℂ, ContDiff ℝ ∞ g ∧ HasCompactSupport g ∧
      support g ⊆ cthickening 1 (tsupport f) ∧ ∀ x, dist (g x) (f x) < ε := by
  obtain ⟨δ, hδ, hu⟩ := Metric.uniformContinuous_iff.mp
    (hs.uniformContinuous_of_continuous hf) (ε / 2) (half_pos hε)
  obtain ⟨g, hg, hbound⟩ :=
    hf.exists_contDiff_dist_le_of_forall_mem_ball_dist_le (lt_min one_pos hδ)
  have hsupp := local_approx_support (min_le_left 1 δ) hbound
  refine ⟨g, hg, HasCompactSupport.of_support_subset_isCompact
    hs.cthickening hsupp, hsupp, fun x => ?_⟩
  apply (hbound x (ε / 2) ?_).trans_lt (half_lt_self hε)
  intro y hy
  apply (hu ?_).le
  exact (mem_ball.mp hy).trans_le (min_le_right 1 δ)


/-- A uniform bound on a finite support gives the usual L² estimate. -/
theorem eLpNorm_two_le_of_support {d : ℕ} {f : Euclidean d → ℂ}
    {K : Set (Euclidean d)} (hK : MeasurableSet K) (hs : support f ⊆ K)
    {C : ℝ} (hC : ∀ x, ‖f x‖ ≤ C) :
    eLpNorm f 2 volume ≤ volume K ^ (1 / (2 : ℝ)) * ENNReal.ofReal C := by
  have heq : K.indicator f = f := indicator_eq_self.mpr hs
  rw [← heq, eLpNorm_indicator_eq_eLpNorm_restrict hK]
  simpa using (eLpNorm_le_of_ae_bound (p := 2) (μ := volume.restrict K)
    (Filter.Eventually.of_forall hC))
/-- Continuous compactly supported functions admit Schwartz approximation in L². -/
theorem compact_exists_schwartz_eLpNorm_lt {d : ℕ} {f : Euclidean d → ℂ}
    (hf : Continuous f) (hs : HasCompactSupport f) {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ g : SchwartzMap (Euclidean d) ℂ, eLpNorm (f - (g : Euclidean d → ℂ)) 2 volume < ε := by
  let K := Metric.cthickening 1 (tsupport f)
  have hK : IsCompact K := hs.cthickening
  have hfinite : volume K ^ (1 / (2 : ℝ)) ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg (by positivity) hK.measure_lt_top.ne
  obtain ⟨η, hη, hηε⟩ := ENNReal.exists_nnreal_pos_mul_lt hfinite hε
  obtain ⟨g, hg, hgs, hsupport, happrox⟩ :=
    smooth_compact_uniform_approx hf hs (show 0 < (η : ℝ) from hη)
  refine ⟨compactSchwartz g hg hgs, ?_⟩
  have hfs : support f ⊆ K :=
    (subset_tsupport f).trans (Metric.self_subset_cthickening (tsupport f))
  have hdiff : support (f - g) ⊆ K :=
    (support_sub f g).trans (union_subset hfs hsupport)
  have hb := eLpNorm_two_le_of_support hK.measurableSet hdiff
    (C := (η : ℝ)) (fun x => by
      simpa only [Pi.sub_apply, ← dist_eq_norm, dist_comm] using (happrox x).le)
  exact hb.trans_lt (by simpa only [ENNReal.ofReal_coe_nnreal, mul_comm] using hηε)

/-- Schwartz functions approximate every Euclidean L² function in the L² seminorm. -/
theorem memLp_exists_schwartz_eLpNorm_lt {d : ℕ} {f : Euclidean d → ℂ}
    (hf : MemLp f 2 volume) {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ g : SchwartzMap (Euclidean d) ℂ,
      eLpNorm (f - (g : Euclidean d → ℂ)) 2 volume < ε := by
  obtain ⟨η, hη, hηε⟩ := ENNReal.exists_nnreal_pos_mul_lt (a := 2) (by norm_num) hε
  have hη0 : (η : ℝ≥0∞) ≠ 0 := by exact_mod_cast hη.ne'
  obtain ⟨c, hcs, hfc, hc, hcm⟩ :=
    hf.exists_hasCompactSupport_eLpNorm_sub_le (by norm_num) hη0
  obtain ⟨g, hcg⟩ := compact_exists_schwartz_eLpNorm_lt hc hcs hη0
  refine ⟨g, ?_⟩
  have hsum := eLpNorm_add_le (hf.aestronglyMeasurable.sub hcm.aestronglyMeasurable)
    (hcm.aestronglyMeasurable.sub g.continuous.aestronglyMeasurable) (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have heq : (f - c) + (c - (g : Euclidean d → ℂ)) = f - (g : Euclidean d → ℂ) := by abel
  rw [heq] at hsum
  calc
    eLpNorm (f - (g : Euclidean d → ℂ)) 2 volume
        ≤ eLpNorm (f - c) 2 volume + eLpNorm (c - (g : Euclidean d → ℂ)) 2 volume := hsum
    _ ≤ (η : ℝ≥0∞) + η := add_le_add hfc hcg.le
    _ < ε := by simpa only [mul_two] using hηε

/-- The Schwartz embedding has dense range in the actual Euclidean L² space. -/
theorem schwartz_toL2_denseRange (d : ℕ) :
    DenseRange (fun g : SchwartzMap (Euclidean d) ℂ => g.toLp 2 volume) := by
  rw [Metric.denseRange_iff]
  intro f ε hε
  obtain ⟨g, hg⟩ := memLp_exists_schwartz_eLpNorm_lt (Lp.memLp f)
    (show ENNReal.ofReal ε ≠ 0 by positivity)
  refine ⟨g, ?_⟩
  rw [Lp.dist_def]
  have heq : eLpNorm ((f : Euclidean d → ℂ) - (g.toLp 2 volume : Euclidean d → ℂ)) 2 volume =
      eLpNorm ((f : Euclidean d → ℂ) - (g : Euclidean d → ℂ)) 2 volume := by
    apply eLpNorm_congr_ae
    filter_upwards [g.coeFn_toLp 2 volume] with x hx
    simp only [Pi.sub_apply, hx]
  rw [heq]
  exact ENNReal.toReal_lt_of_lt_ofReal hg

end RieszEuclidean
