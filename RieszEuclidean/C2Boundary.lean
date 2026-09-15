import RieszEuclidean.Basic
import Mathlib.Analysis.Calculus.ContDiff.Defs

noncomputable section
open MeasureTheory Topology
namespace RieszEuclidean

/-- A `C²` boundary, expressed by local regular defining functions. The domain
is the negative side and its frontier is the zero level. The derivative is
nonzero on the chart neighborhood, which can always be shrunk at a regular
boundary point. This definition contains no curvature, measure, or spectral
conclusion. -/
def HasC2Boundary {d : ℕ} (Ω : Set (Euclidean d)) : Prop :=
  ∀ p ∈ frontier Ω, ∃ (W : Set (Euclidean d)) (f : Euclidean d → ℝ),
    IsOpen W ∧ p ∈ W ∧ ContDiffOn ℝ 2 f W ∧
    (∀ x ∈ W, fderiv ℝ f x ≠ 0) ∧
    (∀ x ∈ W, x ∈ Ω ↔ f x < 0) ∧
    (∀ x ∈ W, x ∈ frontier Ω ↔ f x = 0)

end RieszEuclidean
