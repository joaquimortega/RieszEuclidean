import RieszEuclidean.BoxOverlap
import RieszEuclidean.FejerKernel
import RieszEuclidean.IntegratedAlgebra
open Set MeasureTheory
namespace RieszEuclidean
/-- The complex indicator of a finite-radius box is integrable. -/
theorem integrable_box_indicator {d : ℕ} {R : ℝ} (hR : 0 < R) :
    Integrable ((euclideanBox d R).indicator (fun _ => (1 : ℂ))) := by
  exact (integrable_indicator_iff (measurableSet_euclideanBox d R)).mpr
    (integrableOn_const.mpr (Or.inr (volume_euclideanBox_pos_lt_top d hR).2))
/-- The box autocorrelation equals the volume of its translated intersection. -/
theorem box_indicator_autocorrelation {d : ℕ} (R : ℝ) (y : Euclidean d) :
    integratedKernelConvolution ((euclideanBox d R).indicator (fun _ => (1 : ℂ)))
      (adjointKernel ((euclideanBox d R).indicator (fun _ => (1 : ℂ)))) y =
        (volume.real (euclideanBox d R ∩ translate (-y) (euclideanBox d R)) : ℂ) := by
  have hm : MeasurableSet (euclideanBox d R ∩ translate (-y) (euclideanBox d R)) :=
    (measurableSet_euclideanBox d R).inter
      ((measurableSet_euclideanBox d R).preimage (measurable_id.add measurable_const))
  change (∫ v, (euclideanBox d R).indicator (fun _ => (1 : ℂ)) v *
    star ((euclideanBox d R).indicator (fun _ => (1 : ℂ)) (-(y - v)))) = _
  have he : (fun v => (euclideanBox d R).indicator (fun _ => (1 : ℂ)) v *
    star ((euclideanBox d R).indicator (fun _ => (1 : ℂ)) (-(y - v)))) =
      (euclideanBox d R ∩ translate (-y) (euclideanBox d R)).indicator
        (fun _ => (1 : ℂ)) := by
    funext v
    have hv : -(y - v) = v + -y := by abel
    rw [hv]
    by_cases h₁ : v ∈ euclideanBox d R <;>
      by_cases h₂ : v + -y ∈ euclideanBox d R <;> simp [h₁, h₂, translate]
  rw [he, integral_indicator_const 1 hm]
  simp
/-- The continuous product Fejér weight is the normalized box autocorrelation. -/
theorem fejerWeight_eq_box_autocorrelation {d : ℕ} {R : ℝ} (hR : 0 < R) :
    (fun y : Euclidean d => (fejerWeight R y : ℂ)) =
      fun y => (volume.real (euclideanBox d R) : ℂ)⁻¹ *
        integratedKernelConvolution ((euclideanBox d R).indicator (fun _ => (1 : ℂ)))
          (adjointKernel ((euclideanBox d R).indicator (fun _ => (1 : ℂ)))) y := by
  funext y
  rw [box_indicator_autocorrelation]
  have h := fejerWeight_eq_normalized_overlap hR (-y)
  rw [fejerWeight_neg] at h
  rw [h]
  push_cast
  ring
/-- The actual positive-sign Fourier symbol of the continuous Fejér weight is the box kernel. -/
theorem integratedKernelSymbol_fejerWeight {d : ℕ} {R : ℝ} (hR : 0 < R)
    (x : Euclidean d) :
    integratedKernelSymbol (fun y => (fejerWeight R y : ℂ)) x = (fejerKernel d R x : ℂ) := by
  rw [fejerWeight_eq_box_autocorrelation hR]
  have hscale (c : ℂ) (a : Euclidean d → ℂ) :
      integratedKernelSymbol (fun y => c * a y) x = c * integratedKernelSymbol a x := by
    unfold integratedKernelSymbol
    simp only [mul_assoc, integral_const_mul]
  rw [hscale, integratedKernelSymbol_convolution (integrable_box_indicator hR)
    (integrable_adjointKernel (integrable_box_indicator hR)), integratedKernelSymbol_adjoint]
  simp only [← starRingEnd_apply, RCLike.mul_conj, integratedKernelSymbol_eq_fourierInv]
  simp [fejerKernel]
end RieszEuclidean
