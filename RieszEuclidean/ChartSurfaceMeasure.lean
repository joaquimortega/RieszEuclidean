import RieszEuclidean.ConvexCurvedPatch
import Mathlib.MeasureTheory.Measure.Hausdorff

noncomputable section
open MeasureTheory Filter Topology
open scoped NNReal ENNReal
namespace RieszEuclidean

/-- A regular chart with a Lipschitz inverse contains a patch of positive finite
Hausdorff measure in its parameter dimension. -/
theorem chart_positive_finite_measure
    {n : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {φ : E → Euclidean n} {A : E →L[ℝ] Euclidean n}
    (hd : HasStrictFDerivAt φ A 0)
    (P : Euclidean n →L[ℝ] E) (p : Euclidean n) (U : Set (Euclidean n))
    (hmem : ∀ᶠ u in nhds 0, φ u ∈ U)
    (hinv : ∀ᶠ u in nhds 0, P (φ u-p) = u) :
    ∃ K ⊆ U, (Measure.hausdorffMeasure (Module.finrank ℝ E : ℝ)) K ≠ 0 ∧
      (Measure.hausdorffMeasure (Module.finrank ℝ E : ℝ)) K ≠ ⊤ := by
  obtain ⟨D, hD, happ⟩ := hd.approximates_deriv_on_nhds
    (Or.inr (show (0 : ℝ≥0) < 1 by norm_num))
  have hlip : LipschitzOnWith (‖A‖₊ + 1) φ D := by
    intro x hx y hy
    exact happ.lipschitz ⟨x, hx⟩ ⟨y, hy⟩
  obtain ⟨r, hr, hsmall⟩ := Metric.mem_nhds_iff.mp (Filter.inter_mem hD (hmem.and hinv))
  let B := Metric.closedBall (0 : E) (r/2)
  have hB : B ⊆ Metric.ball 0 r := Metric.closedBall_subset_ball (by linarith)
  have hBD : B ⊆ D := fun x hx => (hsmall (hB hx)).1
  have hpos : 0 < (Measure.hausdorffMeasure (Module.finrank ℝ E : ℝ)) B :=
    Metric.measure_closedBall_pos _ _ (half_pos hr)
  have hfin : (Measure.hausdorffMeasure (Module.finrank ℝ E : ℝ)) B < ⊤ :=
    (isCompact_closedBall (0 : E) (r/2)).measure_lt_top
  refine ⟨φ '' B, ?_, ?_, ?_⟩
  · rintro x ⟨u, hu, rfl⟩
    exact (hsmall (hB hu)).2.1
  · intro hz
    have hQ : LipschitzWith ‖P‖₊ (fun x => P (x-p)) :=
      by
        intro x y
        have he : (x-p)-(y-p) = x-y := by abel
        simpa only [edist_eq_enorm_sub, he] using P.lipschitz (x-p) (y-p)
    have he : (fun x => P (x-p)) '' (φ '' B) = B := by
      ext u
      constructor
      · rintro ⟨x, ⟨v, hv, rfl⟩, rfl⟩
        change P (φ v-p) ∈ B
        rwa [(hsmall (hB hv)).2.2]
      · intro hu
        exact ⟨φ u, ⟨u, hu, rfl⟩, (hsmall (hB hu)).2.2⟩
    have hh := hQ.hausdorffMeasure_image_le (by positivity : (0 : ℝ) ≤ Module.finrank ℝ E) (φ '' B)
    rw [he, hz, mul_zero] at hh
    exact (not_le_of_gt hpos) hh
  · apply ne_top_of_le_ne_top _ ((hlip.mono hBD).hausdorffMeasure_image_le
      (by positivity : (0 : ℝ) ≤ Module.finrank ℝ E))
    rw [ENNReal.rpow_natCast]
    exact (ENNReal.mul_lt_top (ENNReal.pow_lt_top ENNReal.coe_lt_top) hfin).ne

/-- The curved patch contains a positive finite `(n-1)`-dimensional surface
measure patch. -/
theorem CurvedBoundaryPatch.exists_positive_finite_subpatch {n : ℕ}
    {Ω : Set (Euclidean n)} (C : CurvedBoundaryPatch Ω) :
    ∃ K ⊆ C.neighborhood ∩ frontier Ω,
      (Measure.hausdorffMeasure ((n-1 : ℕ) : ℝ)) K ≠ 0 ∧
      (Measure.hausdorffMeasure ((n-1 : ℕ) : ℝ)) K ≠ ⊤ := by
  borelize ↥(LinearMap.ker C.functional)
  have hL : C.functional.toLinearMap ≠ 0 := by
    intro hz
    apply C.functional_ne_zero
    ext x
    exact DFunLike.congr_fun hz x
  have hdim := Module.Dual.finrank_ker_add_one_of_ne_zero hL
  have hd : Module.finrank ℝ (LinearMap.ker C.functional) = n-1 := by
    simpa only [Euclidean, finrank_euclideanSpace, Fintype.card_fin] using (Nat.eq_sub_of_add_eq hdim)
  have hh := chart_positive_finite_measure C.chart_deriv C.projection C.point
    (C.neighborhood ∩ frontier Ω) C.chart_mem C.projection_chart
  rwa [hd] at hh

end RieszEuclidean
