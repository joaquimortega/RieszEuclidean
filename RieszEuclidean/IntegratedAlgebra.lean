import RieszEuclidean.SpectralNorm
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Convolution
import Mathlib.MeasureTheory.Measure.Haar.Unique
open MeasureTheory
namespace RieszEuclidean
variable {d : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
/-- The involution on L¹ kernels appearing in the operator adjoint formula. -/
def adjointKernel (a : Euclidean d → ℂ) (y : Euclidean d) : ℂ := star (a (-y))
/-- Reflection and conjugation preserve integrability. -/
theorem integrable_adjointKernel {a : Euclidean d → ℂ} (ha : Integrable a) :
    Integrable (adjointKernel a) := by
  have hi : Integrable (fun y => a (-y)) := ha.comp_neg
  exact Complex.conjCLE.toContinuousLinearMap.integrable_comp hi
/-- Unitarity moves a translation across the inner product with opposite sign. -/
theorem unitary_inner_neg (U : Euclidean d → H ≃ₗᵢ[ℂ] H)
    (hadd : ∀ z y f, U z (U y f) = U (z + y) f)
    (h0 : ∀ f, U 0 f = f) (y : Euclidean d) (f g : H) :
    inner (𝕜 := ℂ) (U (-y) g) f = inner (𝕜 := ℂ) g (U y f) := by
  rw [← (U y).inner_map_map, hadd, add_neg_cancel, h0]
/-- The involuted kernel gives the adjoint pairing of integrated unitary operators. -/
theorem integratedUnitary_adjoint_pairing [CompleteSpace H]
    (U : Euclidean d → H ≃ₗᵢ[ℂ] H)
    (hU : ∀ f, Continuous (fun y => U y f))
    (hadd : ∀ z y f, U z (U y f) = U (z + y) f)
    (h0 : ∀ f, U 0 f = f) {a : Euclidean d → ℂ} (ha : Integrable a) (f g : H) :
    inner (𝕜 := ℂ) (integratedUnitary U (adjointKernel a) g) f =
      inner (𝕜 := ℂ) g (integratedUnitary U a f) := by
  have hi := integrable_unitary_smul U hU (integrable_adjointKernel ha) g
  calc
    inner (𝕜 := ℂ) (integratedUnitary U (adjointKernel a) g) f =
        ∫ y, inner (𝕜 := ℂ) (adjointKernel a y • U y g) f := by
      rw [← inner_conj_symm, integratedUnitary, ← integral_inner hi, ← integral_conj]
      apply integral_congr_ae
      filter_upwards [] with y
      exact inner_conj_symm _ _
    _ = ∫ y, a (-y) * inner (𝕜 := ℂ) (U y g) f := by
      apply integral_congr_ae
      filter_upwards [] with y
      simp [inner_smul_left, adjointKernel]
    _ = ∫ y, a y * inner (𝕜 := ℂ) (U (-y) g) f := by
      simpa using (integral_neg_eq_self
        (fun y => a (-y) * inner (𝕜 := ℂ) (U y g) f) volume).symm
    _ = ∫ y, a y * inner (𝕜 := ℂ) g (U y f) := by
      apply integral_congr_ae
      filter_upwards [] with y
      rw [unitary_inner_neg U hadd h0]
    _ = inner (𝕜 := ℂ) g (integratedUnitary U a f) := by
      simp_rw [← inner_smul_right]
      exact integral_inner (integrable_unitary_smul U hU ha f) g
/-- The adjoint formula holds for the actual bounded operators. -/
theorem integratedUnitaryCLM_adjoint [CompleteSpace H]
    (U : Euclidean d → H ≃ₗᵢ[ℂ] H)
    (hU : ∀ f, Continuous (fun y => U y f))
    (hadd : ∀ z y f, U z (U y f) = U (z + y) f)
    (h0 : ∀ f, U 0 f = f) {a : Euclidean d → ℂ} (ha : Integrable a) :
    (integratedUnitaryCLM U hU ha).adjoint =
      integratedUnitaryCLM U hU (integrable_adjointKernel ha) := by
  symm
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro g f
  exact integratedUnitary_adjoint_pairing U hU hadd h0 ha f g
/-- The kernel operation is an involution. -/
theorem adjointKernel_involutive (a : Euclidean d → ℂ) :
    adjointKernel (adjointKernel a) = a := by
  funext y
  simp [adjointKernel]
/-- The adjoint kernel conjugates the actual Fourier symbol. -/
theorem integratedKernelSymbol_adjoint (a : Euclidean d → ℂ) (θ : Euclidean d) :
    integratedKernelSymbol (adjointKernel a) θ = star (integratedKernelSymbol a θ) := by
  change (∫ y, star (a (-y)) * (Real.fourierChar (inner (𝕜 := ℝ) y θ) : ℂ)) = _
  calc
    (∫ y, star (a (-y)) * (Real.fourierChar (inner (𝕜 := ℝ) y θ) : ℂ)) =
        ∫ y, star (a y) * (Real.fourierChar (inner (𝕜 := ℝ) (-y) θ) : ℂ) := by
      simpa using (integral_neg_eq_self
        (fun y => star (a (-y)) * (Real.fourierChar (inner (𝕜 := ℝ) y θ) : ℂ)) volume).symm
    _ = star (integratedKernelSymbol a θ) := by
      change _ = starRingEnd ℂ (∫ y, a y * (Real.fourierChar (inner (𝕜 := ℝ) y θ) : ℂ))
      rw [← integral_conj]
      apply integral_congr_ae
      filter_upwards [] with y
      simp [inner_neg_left, Real.fourierChar.map_neg_eq_inv, Circle.coe_inv_eq_conj]
/-- Scalar convolution of integrable kernels. -/
noncomputable def integratedKernelConvolution (a b : Euclidean d → ℂ) : Euclidean d → ℂ :=
  convolution a b (ContinuousLinearMap.mul ℂ ℂ) volume
/-- The scalar convolution remains integrable. -/
theorem integrable_integratedKernelConvolution {a b : Euclidean d → ℂ}
    (ha : Integrable a) (hb : Integrable b) : Integrable (integratedKernelConvolution a b) :=
  ha.integrable_convolution (ContinuousLinearMap.mul ℂ ℂ) hb
/-- Absolute integrability permits Fubini in the integrated convolution formula. -/
theorem integrable_unitary_convolution_kernel
    (U : Euclidean d → H ≃ₗᵢ[ℂ] H)
    (hU : ∀ f, Continuous (fun y => U y f))
    {a b : Euclidean d → ℂ} (ha : Integrable a) (hb : Integrable b) (f : H) :
    Integrable (fun p : Euclidean d × Euclidean d =>
      (a p.2 * b (p.1 - p.2)) • U p.1 f) (volume.prod volume) := by
  have hi : Integrable (fun p : Euclidean d × Euclidean d =>
      a p.2 * b (p.1 - p.2)) (volume.prod volume) :=
    ha.convolution_integrand (ContinuousLinearMap.mul ℂ ℂ) hb
  apply (hi.norm.mul_const ‖f‖).mono'
    (hi.aestronglyMeasurable.smul ((hU f).comp continuous_fst).aestronglyMeasurable)
  filter_upwards [] with p
  simp [norm_smul]
/-- Convolution of L¹ kernels composes their integrated unitary actions. -/
theorem integratedUnitary_convolution [CompleteSpace H]
    (U : Euclidean d → H ≃ₗᵢ[ℂ] H)
    (hU : ∀ f, Continuous (fun y => U y f))
    (hadd : ∀ z y f, U z (U y f) = U (z + y) f)
    {a b : Euclidean d → ℂ} (ha : Integrable a) (hb : Integrable b) (f : H) :
    integratedUnitary U (integratedKernelConvolution a b) f =
      integratedUnitary U a (integratedUnitary U b f) := by
  calc
    integratedUnitary U (integratedKernelConvolution a b) f =
        ∫ x, ∫ y, (a y * b (x - y)) • U x f := by
      apply integral_congr_ae
      filter_upwards [] with x
      exact (integral_smul_const (fun y => a y * b (x - y)) (U x f)).symm
    _ = ∫ y, ∫ x, (a y * b (x - y)) • U x f :=
      integral_integral_swap (integrable_unitary_convolution_kernel U hU ha hb f)
    _ = integratedUnitary U a (integratedUnitary U b f) := by
      apply integral_congr_ae
      filter_upwards [] with y
      calc
        (∫ x, (a y * b (x - y)) • U x f) =
            ∫ w, (a y * b w) • U (y + w) f := by
          simpa using (integral_add_left_eq_self
            (fun x => (a y * b (x - y)) • U x f) y).symm
        _ = ∫ w, a y • U y (b w • U w f) := by
          apply integral_congr_ae
          filter_upwards [] with w
          rw [map_smul, hadd, mul_smul]
        _ = a y • U y (integratedUnitary U b f) := by
          rw [integral_smul]
          congr 1
          exact (U y).toContinuousLinearEquiv.toContinuousLinearMap.integral_comp_comm
            (integrable_unitary_smul U hU hb f)
/-- Convolution gives composition at the bounded-operator level. -/
theorem integratedUnitaryCLM_convolution [CompleteSpace H]
    (U : Euclidean d → H ≃ₗᵢ[ℂ] H)
    (hU : ∀ f, Continuous (fun y => U y f))
    (hadd : ∀ z y f, U z (U y f) = U (z + y) f)
    {a b : Euclidean d → ℂ} (ha : Integrable a) (hb : Integrable b) :
    integratedUnitaryCLM U hU (integrable_integratedKernelConvolution ha hb) =
      (integratedUnitaryCLM U hU ha).comp (integratedUnitaryCLM U hU hb) := by
  ext f
  exact integratedUnitary_convolution U hU hadd ha hb f
/-- The Fourier symbol converts scalar convolution into multiplication. -/
theorem integratedKernelSymbol_convolution {a b : Euclidean d → ℂ}
    (ha : Integrable a) (hb : Integrable b) (θ : Euclidean d) :
    integratedKernelSymbol (integratedKernelConvolution a b) θ =
      integratedKernelSymbol a θ * integratedKernelSymbol b θ := by
  let c : Euclidean d → ℂ := fun y => Real.fourierChar (inner (𝕜 := ℝ) y θ)
  have hc (x y : Euclidean d) : c y * c (x - y) = c x := by
    dsimp only [c]
    rw [← Circle.coe_mul, ← Real.fourierChar.map_add_eq_mul, ← inner_add_left]
    congr 3
    abel
  calc
    integratedKernelSymbol (integratedKernelConvolution a b) θ =
        ∫ x, convolution (fun y => a y * c y) (fun y => b y * c y)
          (ContinuousLinearMap.mul ℂ ℂ) volume x := by
      apply integral_congr_ae
      filter_upwards [] with x
      change (∫ y, a y * b (x - y)) * c x =
        ∫ y, (a y * c y) * (b (x - y) * c (x - y))
      rw [← integral_mul_const]
      apply integral_congr_ae
      filter_upwards [] with y
      rw [mul_mul_mul_comm, hc]
    _ = integratedKernelSymbol a θ * integratedKernelSymbol b θ :=
      integral_convolution (ContinuousLinearMap.mul ℂ ℂ)
        (integrable_kernel_character ha θ) (integrable_kernel_character hb θ)
end RieszEuclidean
