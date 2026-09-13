import RieszEuclidean.Basic
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
open MeasureTheory Set
open scoped ENNReal
namespace RieszEuclidean
/-- The real coordinate cube with half-side length `R`, inside Euclidean space. -/
def euclideanBox (d : ℕ) (R : ℝ) : Set (Euclidean d) :=
  (EuclideanSpace.measurableEquiv (Fin d)) ⁻¹' Metric.closedBall 0 R
/-- Coordinate boxes are measurable. -/
theorem measurableSet_euclideanBox (d : ℕ) (R : ℝ) : MeasurableSet (euclideanBox d R) :=
  Metric.isClosed_closedBall.measurableSet.preimage (EuclideanSpace.measurableEquiv (Fin d)).measurable
/-- The Lebesgue volume of the coordinate cube is its side length to the dimension. -/
theorem volume_euclideanBox (d : ℕ) {R : ℝ} (hR : 0 ≤ R) :
    volume (euclideanBox d R) = ENNReal.ofReal ((2 * R) ^ d) := by
  rw [euclideanBox, (EuclideanSpace.volume_preserving_measurableEquiv (Fin d)).measure_preimage
    Metric.isClosed_closedBall.measurableSet.nullMeasurableSet]
  simpa using Real.volume_pi_closedBall (0 : Fin d → ℝ) hR
/-- Positive-side coordinate cubes have finite positive volume. -/
theorem volume_euclideanBox_pos_lt_top (d : ℕ) {R : ℝ} (hR : 0 < R) :
    0 < volume (euclideanBox d R) ∧ volume (euclideanBox d R) < ⊤ := by
  rw [volume_euclideanBox d hR.le]
  constructor
  · exact ENNReal.ofReal_pos.mpr (pow_pos (by positivity) _)
  · exact ENNReal.ofReal_lt_top
/-- Normalized Lebesgue measure on a real coordinate box. -/
noncomputable def boxProbabilityMeasure (d : ℕ) (R : ℝ) : Measure (Euclidean d) :=
  (volume (euclideanBox d R))⁻¹ • volume.restrict (euclideanBox d R)
/-- Every positive-side box gives a probability measure. -/
theorem boxProbabilityMeasure_isProbability (d : ℕ) {R : ℝ} (hR : 0 < R) :
    IsProbabilityMeasure (boxProbabilityMeasure d R) := by
  obtain ⟨hp, hf⟩ := volume_euclideanBox_pos_lt_top d hR
  constructor
  simp only [boxProbabilityMeasure, Measure.smul_apply, Measure.restrict_apply_univ,
    smul_eq_mul]
  exact ENNReal.inv_mul_cancel hp.ne' hf.ne
end RieszEuclidean
