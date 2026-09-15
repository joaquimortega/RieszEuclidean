import RieszEuclidean.Basic
import Mathlib.Topology.MetricSpace.HausdorffDimension

noncomputable section
open MeasureTheory
open scoped ENNReal NNReal
namespace RieszEuclidean

/-- A continuously differentiable parametrization of dimension `m` has zero
`k`-dimensional Hausdorff measure whenever `m < k`. -/
theorem smooth_chart_hausdorff_null {m n k : ℕ} (hmk : m < k)
    {f : Euclidean m → Euclidean n} {D : Set (Euclidean m)}
    (hf : ContDiffOn ℝ 1 f D) (hD : Convex ℝ D) :
    (Measure.hausdorffMeasure (k : ℝ)) (f '' D) = 0 := by
  have hdim : dimH (f '' D) ≤ (m : ℝ≥0∞) := by
    calc
      dimH (f '' D) ≤ dimH D := hf.dimH_image_le hD Set.Subset.rfl
      _ ≤ dimH (Set.univ : Set (Euclidean m)) := dimH_mono (Set.subset_univ D)
      _ = m := by rw [Real.dimH_univ_eq_finrank]; simp [Euclidean]
  exact hausdorffMeasure_of_dimH_lt (d := (k : ℝ≥0))
    (hdim.trans_lt (by exact_mod_cast hmk))

/-- A countable collection of lower-dimensional smooth charts is surface-null.
This is the measure-theoretic step after obtaining local transverse charts. -/
theorem countable_smooth_charts_hausdorff_null {m n k : ℕ} (hmk : m < k)
    {T : Set (Euclidean n)} (f : ℕ → Euclidean m → Euclidean n)
    (D : ℕ → Set (Euclidean m))
    (hf : ∀ j, ContDiffOn ℝ 1 (f j) (D j)) (hD : ∀ j, Convex ℝ (D j))
    (hcover : T ⊆ ⋃ j, f j '' D j) :
    (Measure.hausdorffMeasure (k : ℝ)) T = 0 := by
  apply measure_mono_null hcover
  exact measure_iUnion_null (fun j => smooth_chart_hausdorff_null hmk (hf j) (hD j))

end RieszEuclidean
