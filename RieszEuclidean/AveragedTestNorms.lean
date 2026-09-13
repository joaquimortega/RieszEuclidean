import RieszEuclidean.AveragedTests
import RieszEuclidean.FejerKernel
import Mathlib.MeasureTheory.Integral.Prod

open MeasureTheory Set Filter
namespace RieszEuclidean

/-- Turn an actual function into its canonical `L²` class when it belongs to `L²`,
and use zero otherwise. -/
noncomputable def fullL2OfMemLp {X : Type*} {d : ℕ}
    (j : X → Euclidean d → ℂ) (x : X) : FullL2 d := by
  classical
  exact if h : MemLp (j x) 2 volume then h.toLp (j x) else 0

theorem fullL2OfMemLp_coe_ae {X : Type*} {d : ℕ}
    (j : X → Euclidean d → ℂ) {x : X} (hx : MemLp (j x) 2 volume) :
    (fullL2OfMemLp j x : Euclidean d → ℂ) =ᵐ[volume] j x := by
  classical
  rw [fullL2OfMemLp, dif_pos hx]
  exact hx.coeFn_toLp

theorem fullL2OfMemLp_norm_sq {X : Type*} {d : ℕ}
    (j : X → Euclidean d → ℂ) {x : X} (hx : MemLp (j x) 2 volume) :
    ‖fullL2OfMemLp j x‖ ^ 2 = ∫ v, ‖j x v‖ ^ 2 := by
  rw [← integral_sq_norm_fullL2 (fullL2OfMemLp j x)]
  exact integral_congr_ae ((fullL2OfMemLp_coe_ae j hx).fun_comp fun z => ‖z‖ ^ 2)

/-- A strongly measurable joint squared norm has a measurable fibre integral. -/
theorem aestronglyMeasurable_integral_sq_norm {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {d : ℕ}
    {j : X → Euclidean d → ℂ}
    (hj : StronglyMeasurable (fun p : X × Euclidean d => j p.1 p.2)) :
    AEStronglyMeasurable (fun x => ∫ v, ‖j x v‖ ^ 2) μ := by
  exact (hj.norm.pow 2).integral_prod_right'.aestronglyMeasurable

theorem memLp_fullL2OfMemLp_norm {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {d : ℕ} [SFinite (volume : Measure (Euclidean d))]
    {j : X → Euclidean d → ℂ}
    (hj : StronglyMeasurable (fun p : X × Euclidean d => j p.1 p.2))
    (hi : Integrable (fun p : X × Euclidean d => ‖j p.1 p.2‖ ^ 2) (μ.prod volume))
    (hmem : ∀ᵐ x ∂μ, MemLp (j x) 2 volume) :
    MemLp (fun x => ‖fullL2OfMemLp j x‖) 2 μ := by
  have hE : StronglyMeasurable (fun x => ∫ v, ‖j x v‖ ^ 2) :=
    (hj.norm.pow 2).integral_prod_right'
  have heq : ∀ᵐ x ∂μ, ‖fullL2OfMemLp j x‖ ^ 2 = ∫ v, ‖j x v‖ ^ 2 := by
    filter_upwards [hmem] with x hx
    exact fullL2OfMemLp_norm_sq j hx
  have hsqrt : ∀ᵐ x ∂μ,
      ‖fullL2OfMemLp j x‖ = Real.sqrt (∫ v, ‖j x v‖ ^ 2) := by
    filter_upwards [heq] with x hx
    rw [← hx, Real.sqrt_sq (norm_nonneg _)]
  have hm : AEStronglyMeasurable (fun x => ‖fullL2OfMemLp j x‖) μ :=
    (Real.continuous_sqrt.comp_stronglyMeasurable hE).aestronglyMeasurable.congr (by
      filter_upwards [hsqrt] with x hx
      exact hx.symm)
  apply (memLp_two_iff_integrable_sq_norm hm).mpr
  apply hi.integral_prod_left.congr
  filter_upwards [heq] with x hx
  simpa using hx.symm

/-- The canonical `L²` representatives have the same averaged squared energy as
their actual representatives. -/
theorem integral_fullL2OfMemLp_norm_sq {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {d : ℕ} {j : X → Euclidean d → ℂ}
    (hmem : ∀ᵐ x ∂μ, MemLp (j x) 2 volume) {a : ℝ}
    (henergy : (∫ x, (∫ v, ‖j x v‖ ^ 2) ∂μ) = a) :
    (∫ x, ‖fullL2OfMemLp j x‖ ^ 2 ∂μ) = a := by
  rw [← henergy]
  apply integral_congr_ae
  filter_upwards [hmem] with x hx
  exact fullL2OfMemLp_norm_sq j hx

/-- The paper's actual scalar test, regarded as a canonical vector in full `L²`. -/
noncomputable def averagedTestL2 {X : Type*} {d : ℕ} (R : ℝ) (t : Euclidean d)
    (T : Euclidean d → X → X) (f : X → ℂ) (x : X) : FullL2 d :=
  fullL2OfMemLp (averagedTest R t T f) x

/-- Whenever the actual scalar test is in `L²`, its canonical vector has that
test as an almost-everywhere representative. -/
theorem averagedTestL2_coe_ae {X : Type*} {d : ℕ}
    (R : ℝ) (t : Euclidean d) (T : Euclidean d → X → X) (f : X → ℂ) {x : X}
    (hx : MemLp (averagedTest R t T f x) 2 volume) :
    (averagedTestL2 R t T f x : Euclidean d → ℂ) =ᵐ[volume]
      averagedTest R t T f x :=
  fullL2OfMemLp_coe_ae _ hx

/-- Almost every paper test is also integrable, since its `L²` representative is
supported on the finite-volume coordinate box. -/
theorem ae_integrable_averagedTest {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {d : ℕ} [SFinite μ]
    (T : Euclidean d → X → X) (hT : Measurable (fun p : X × Euclidean d => T p.2 p.1))
    (hμ : ∀ v, MeasurePreserving (T v) μ μ) (f : Lp ℂ 2 μ) {R : ℝ} (hR : 0 < R)
    (t : Euclidean d) :
    ∀ᵐ x ∂μ, Integrable (averagedTest R t T f x) volume := by
  filter_upwards [ae_memLp_averagedTest T hT hμ f hR t] with x hx
  letI : IsFiniteMeasure (volume.restrict (euclideanBox d R)) :=
    IsFiniteMeasure.mk (by
      rw [Measure.restrict_apply_univ]
      exact (volume_euclideanBox_pos_lt_top d hR).2)
  have hi : IntegrableOn (averagedTest R t T f x) (euclideanBox d R) volume :=
    (hx.restrict (euclideanBox d R)).integrable (by norm_num)
  apply (hi.integrable_indicator (measurableSet_euclideanBox d R)).congr
  exact Filter.Eventually.of_forall fun v => by
    by_cases hv : v ∈ euclideanBox d R
    · simp [hv]
    · simp [averagedTest, hv]

/-- Norms of the canonical paper tests form an `L²` scalar field. -/
theorem memLp_norm_averagedTestL2 {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {d : ℕ} [SFinite μ]
    (T : Euclidean d → X → X) (hT : Measurable (fun p : X × Euclidean d => T p.2 p.1))
    (hμ : ∀ v, MeasurePreserving (T v) μ μ) (f : Lp ℂ 2 μ) {R : ℝ} (hR : 0 < R)
    (t : Euclidean d) :
    MemLp (fun x => ‖averagedTestL2 R t T f x‖) 2 μ := by
  apply memLp_fullL2OfMemLp_norm
  · exact (measurable_averagedTest R t T hT (Lp.stronglyMeasurable f).measurable).stronglyMeasurable
  · exact integrable_averagedTest_sq T hT hμ f hR t
  · exact ae_memLp_averagedTest T hT hμ f hR t

/-- The norm field of the canonical paper tests has exactly the original `L²`
energy. -/
theorem integral_norm_averagedTestL2_sq {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {d : ℕ} [SFinite μ]
    (T : Euclidean d → X → X) (hT : Measurable (fun p : X × Euclidean d => T p.2 p.1))
    (hμ : ∀ v, MeasurePreserving (T v) μ μ) (f : Lp ℂ 2 μ) {R : ℝ} (hR : 0 < R)
    (t : Euclidean d) :
    (∫ x, ‖averagedTestL2 R t T f x‖ ^ 2 ∂μ) = ‖f‖ ^ 2 :=
  integral_fullL2OfMemLp_norm_sq (ae_memLp_averagedTest T hT hμ f hR t)
    (integral_averagedTest_energy T hT hμ f hR t)

namespace SeparatedConfiguration

/-- On the actual compact hull, the canonical test vectors represent the paper's
scalar tests, and their norm field has the required normalized energy. -/
theorem hull_averagedTestL2_norm_energy {d : ℕ} {δ : ℝ} (hδ : 0 < δ)
    (Γ : SeparatedConfiguration d δ)
    [MeasurableSpace (hull Γ)] [BorelSpace (hull Γ)]
    (μ : Measure (hull Γ)) [IsProbabilityMeasure μ]
    (hμ : ∀ v, MeasurePreserving (hullTranslate hδ Γ v) μ μ)
    (f : Lp ℂ 2 μ) {R : ℝ} (hR : 0 < R) (t : Euclidean d) :
    (∀ᵐ Δ ∂μ,
      (averagedTestL2 R t (hullTranslate hδ Γ) f Δ : Euclidean d → ℂ) =ᵐ[volume]
        averagedTest R t (hullTranslate hδ Γ) f Δ) ∧
    MemLp (fun Δ => ‖averagedTestL2 R t (hullTranslate hδ Γ) f Δ‖) 2 μ ∧
    (∫ Δ, ‖averagedTestL2 R t (hullTranslate hδ Γ) f Δ‖ ^ 2 ∂μ) = ‖f‖ ^ 2 := by
  have hT : Measurable (fun p : hull Γ × Euclidean d =>
      hullTranslate hδ Γ p.2 p.1) :=
    ((continuous_hullTranslate hδ Γ).comp (continuous_snd.prodMk continuous_fst)).measurable
  refine ⟨?_, memLp_norm_averagedTestL2 _ hT hμ f hR t,
    integral_norm_averagedTestL2_sq _ hT hμ f hR t⟩
  filter_upwards [ae_memLp_averagedTest _ hT hμ f hR t] with Δ hΔ
  exact averagedTestL2_coe_ae _ _ _ _ hΔ

end SeparatedConfiguration

end RieszEuclidean
