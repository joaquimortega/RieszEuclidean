import RieszEuclidean.BochnerWindows
import RieszEuclidean.BochnerCoordinateWindows
noncomputable section
open MeasureTheory
open scoped ENNReal NNReal
namespace RieszEuclidean
variable {d : ℕ} {H ι : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
/-- Sum the actual physical spectral measures of the scalar coordinates of the original window. -/
def bochnerApproxMeasure {R : ℝ} (hR : 0 < R) (U : Euclidean d → H ≃ₗᵢ[ℂ] H)
    (hU : ∀ f, Continuous (fun x => U x f)) (f : H) (e : HilbertBasis ι ℂ H) :
    Measure (Euclidean d) :=
  Measure.sum (fun i => physicalSpectralMeasure (bochnerWindowCoordinate hR U hU f (e i)))
/-- Integrated Parseval sums the actual scalar coordinate energies. -/
theorem bochnerWindowCoordinate_hasSum_energy [Countable ι] {R : ℝ} (hR : 0 < R)
    (U : Euclidean d → H ≃ₗᵢ[ℂ] H) (hU : ∀ f, Continuous (fun x => U x f))
    (f : H) (e : HilbertBasis ι ℂ H) :
    HasSum (fun i => ‖bochnerWindowCoordinate hR U hU f (e i)‖ ^ 2) (‖f‖ ^ 2) := by
  have h := hilbertBasis_hasSum_integral_sq e (bochnerWindow R U f)
    (stronglyMeasurable_bochnerWindow R U hU f).aestronglyMeasurable
    (integrable_norm_bochnerWindow_sq hR U f)
  simpa only [norm_bochnerWindowCoordinate_sq, integral_norm_bochnerWindow_sq hR U f] using h
/-- Each approximation has exactly the prescribed finite total mass. -/
theorem bochnerApproxMeasure_univ [Countable ι] {R : ℝ} (hR : 0 < R)
    (U : Euclidean d → H ≃ₗᵢ[ℂ] H) (hU : ∀ f, Continuous (fun x => U x f))
    (f : H) (e : HilbertBasis ι ℂ H) :
    bochnerApproxMeasure hR U hU f e Set.univ = ENNReal.ofReal (‖f‖ ^ 2) := by
  have he (i : ι) : physicalSpectralMeasure (bochnerWindowCoordinate hR U hU f (e i)) Set.univ =
      ENNReal.ofReal (‖bochnerWindowCoordinate hR U hU f (e i)‖ ^ 2) := by
    letI := physicalSpectralMeasure_finite (bochnerWindowCoordinate hR U hU f (e i))
    rw [← physicalSpectralMeasure_mass, measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)]
  rw [bochnerApproxMeasure, Measure.sum_apply _ MeasurableSet.univ]
  simp_rw [he]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun i => sq_nonneg _)
    (bochnerWindowCoordinate_hasSum_energy hR U hU f e).summable,
    (bochnerWindowCoordinate_hasSum_energy hR U hU f e).tsum_eq]
/-- The approximating positive measures are finite, uniformly in the box radius. -/
theorem bochnerApproxMeasure_finite [Countable ι] {R : ℝ} (hR : 0 < R)
    (U : Euclidean d → H ≃ₗᵢ[ℂ] H) (hU : ∀ f, Continuous (fun x => U x f))
    (f : H) (e : HilbertBasis ι ℂ H) : IsFiniteMeasure (bochnerApproxMeasure hR U hU f e) := by
  constructor
  rw [bochnerApproxMeasure_univ]
  exact ENNReal.ofReal_lt_top
/-- Real total mass of each approximation is the original vector energy. -/
theorem bochnerApproxMeasure_mass [Countable ι] {R : ℝ} (hR : 0 < R)
    (U : Euclidean d → H ≃ₗᵢ[ℂ] H) (hU : ∀ f, Continuous (fun x => U x f))
    (f : H) (e : HilbertBasis ι ℂ H) :
    (bochnerApproxMeasure hR U hU f e).real Set.univ = ‖f‖ ^ 2 := by
  rw [measureReal_def, bochnerApproxMeasure_univ, ENNReal.toReal_ofReal (sq_nonneg _)]
/-- The exact Fourier transform of the finite positive approximation is the Fejér-weighted correlation. -/
theorem bochnerApproxMeasure_fourier [Countable ι] {R : ℝ} (hR : 0 < R)
    (U : Euclidean d → H ≃ₗᵢ[ℂ] H) (hU : ∀ f, Continuous (fun x => U x f))
    (hadd : ∀ z y f, U z (U y f) = U (z + y) f)
    (f : H) (e : HilbertBasis ι ℂ H) (y : Euclidean d) :
    (∫ θ, (Real.fourierChar (inner (𝕜 := ℝ) y θ) : ℂ) ∂bochnerApproxMeasure hR U hU f e) =
      (fejerWeight R y : ℂ) * unitaryCorrelation U f y := by
  letI := bochnerApproxMeasure_finite hR U hU f e
  have hchar := integrable_fourierChar d (bochnerApproxMeasure hR U hU f e) y
  rw [bochnerApproxMeasure] at hchar ⊢
  rw [integral_sum_measure hchar]
  simp_rw [← (represents_physicalTranslationCorrelation _).2 y, bochnerWindowCoordinate_correlation]
  have hv : AEStronglyMeasurable (bochnerWindow R U f) volume :=
    (stronglyMeasurable_bochnerWindow R U hU f).aestronglyMeasurable
  have hw : AEStronglyMeasurable (fun x => bochnerWindow R U f (x - y)) volume :=
    ((stronglyMeasurable_bochnerWindow R U hU f).comp_measurable (measurable_id.sub_const y)).aestronglyMeasurable
  have hi := integrable_norm_bochnerWindow_sq hR U f
  have hj : Integrable (fun x => ‖bochnerWindow R U f (x - y)‖ ^ 2) := by
    have ht := ((measurePreserving_add_right volume (-y)).integrable_comp hi.aestronglyMeasurable).mpr hi
    simpa only [sub_eq_add_neg] using ht
  exact (hilbertBasis_hasSum_integral_inner e _ _ hv hw hi hj).tsum_eq.trans
    (integral_inner_bochnerWindow_shift hR U hadd f y)
end RieszEuclidean
