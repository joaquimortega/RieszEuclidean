import RieszEuclidean.PhysicalTranslationSpectrum
import RieszEuclidean.AveragedTests
import RieszEuclidean.BoxOverlap
noncomputable section
open MeasureTheory Set
namespace RieszEuclidean
variable {d : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
/-- A normalized box window in the original Hilbert space, with the physical Fourier sign. -/
def bochnerWindow (R : ℝ) (U : Euclidean d → H ≃ₗᵢ[ℂ] H) (f : H) (x : Euclidean d) : H :=
  (((Real.sqrt (volume.real (euclideanBox d R)))⁻¹ : ℝ) : ℂ) •
    (euclideanBox d R).indicator (fun x => U (-x) f) x
/-- The vector window has exactly the normalized box density as its squared norm. -/
theorem norm_bochnerWindow_sq (R : ℝ) (U : Euclidean d → H ≃ₗᵢ[ℂ] H) (f : H) (x : Euclidean d) :
    ‖bochnerWindow R U f x‖ ^ 2 = averagedBoxWeight d R x * ‖f‖ ^ 2 := by
  by_cases hx : x ∈ euclideanBox d R
  · simp only [bochnerWindow, averagedBoxWeight, indicator_of_mem hx, norm_smul,
      Complex.norm_real, Real.norm_eq_abs, abs_inv, abs_of_nonneg (Real.sqrt_nonneg _),
      LinearIsometryEquiv.norm_map, mul_pow, inv_pow]
    rw [Real.sq_sqrt (show 0 ≤ volume.real (euclideanBox d R) from ENNReal.toReal_nonneg)]
  · simp [bochnerWindow, averagedBoxWeight, hx]
/-- Strong continuity of the representation makes its finite window strongly measurable. -/
theorem stronglyMeasurable_bochnerWindow (R : ℝ) (U : Euclidean d → H ≃ₗᵢ[ℂ] H)
    (hU : ∀ f, Continuous (fun x => U x f)) (f : H) :
    StronglyMeasurable (bochnerWindow R U f) :=
  (((hU f).comp continuous_neg).stronglyMeasurable.indicator (measurableSet_euclideanBox d R)).const_smul _
/-- The window's squared norm is integrable. -/
theorem integrable_norm_bochnerWindow_sq {R : ℝ} (hR : 0 < R)
    (U : Euclidean d → H ≃ₗᵢ[ℂ] H) (f : H) :
    Integrable (fun x => ‖bochnerWindow R U f x‖ ^ 2) := by
  simpa only [norm_bochnerWindow_sq] using (integrable_averagedBoxWeight d hR).mul_const (‖f‖ ^ 2)
/-- The window preserves the original vector energy exactly. -/
theorem integral_norm_bochnerWindow_sq {R : ℝ} (hR : 0 < R)
    (U : Euclidean d → H ≃ₗᵢ[ℂ] H) (f : H) :
    (∫ x, ‖bochnerWindow R U f x‖ ^ 2) = ‖f‖ ^ 2 := by
  simp_rw [norm_bochnerWindow_sq]
  rw [integral_mul_const, integral_averagedBoxWeight d hR, one_mul]
/-- Every finite window belongs to Hilbert-valued L² on Euclidean space. -/
theorem memLp_bochnerWindow {R : ℝ} (hR : 0 < R) (U : Euclidean d → H ≃ₗᵢ[ℂ] H)
    (hU : ∀ f, Continuous (fun x => U x f)) (f : H) :
    MemLp (bochnerWindow R U f) 2 volume :=
  (memLp_two_iff_integrable_sq_norm (stronglyMeasurable_bochnerWindow R U hU f).aestronglyMeasurable).mpr
    (integrable_norm_bochnerWindow_sq hR U f)
/-- Scalar Hilbert coordinates of the window are actual L² functions. -/
theorem memLp_bochnerWindow_coordinate {R : ℝ} (hR : 0 < R) (U : Euclidean d → H ≃ₗᵢ[ℂ] H)
    (hU : ∀ f, Continuous (fun x => U x f)) (f e : H) :
    MemLp (fun x => inner (𝕜 := ℂ) e (bochnerWindow R U f x)) 2 volume := by
  apply (memLp_bochnerWindow hR U hU f).of_le_mul
    (continuous_const.inner (show Continuous (fun x : H => x) from continuous_id)
      |>.comp_aestronglyMeasurable (stronglyMeasurable_bochnerWindow R U hU f).aestronglyMeasurable)
  exact Filter.Eventually.of_forall fun x => norm_inner_le_norm _ _
/-- The actual scalar coordinate vector whose physical spectrum contributes to the approximation. -/
def bochnerWindowCoordinate {R : ℝ} (hR : 0 < R) (U : Euclidean d → H ≃ₗᵢ[ℂ] H)
    (hU : ∀ f, Continuous (fun x => U x f)) (f e : H) : FullL2 d :=
  (memLp_bochnerWindow_coordinate hR U hU f e).toLp _
/-- The coordinate L² class has its prescribed scalar representative. -/
theorem bochnerWindowCoordinate_coe {R : ℝ} (hR : 0 < R) (U : Euclidean d → H ≃ₗᵢ[ℂ] H)
    (hU : ∀ f, Continuous (fun x => U x f)) (f e : H) :
    (bochnerWindowCoordinate hR U hU f e : Euclidean d → ℂ) =ᵐ[volume]
      fun x => inner (𝕜 := ℂ) e (bochnerWindow R U f x) := MemLp.coeFn_toLp _
/-- Scalar-coordinate energy is the literal integral of its squared scalar coefficient. -/
theorem norm_bochnerWindowCoordinate_sq {R : ℝ} (hR : 0 < R) (U : Euclidean d → H ≃ₗᵢ[ℂ] H)
    (hU : ∀ f, Continuous (fun x => U x f)) (f e : H) :
    ‖bochnerWindowCoordinate hR U hU f e‖ ^ 2 =
      ∫ x, ‖inner (𝕜 := ℂ) e (bochnerWindow R U f x)‖ ^ 2 := by
  rw [← integral_sq_norm_fullL2]
  exact integral_congr_ae ((bochnerWindowCoordinate_coe hR U hU f e).fun_comp fun z => ‖z‖ ^ 2)
/-- A coordinate's ordinary-translation correlation is its actual translated scalar pairing. -/
theorem bochnerWindowCoordinate_correlation {R : ℝ} (hR : 0 < R)
    (U : Euclidean d → H ≃ₗᵢ[ℂ] H) (hU : ∀ f, Continuous (fun x => U x f))
    (f e : H) (y : Euclidean d) :
    unitaryCorrelation physicalTranslationUnitary (bochnerWindowCoordinate hR U hU f e) y =
      ∫ x, inner (𝕜 := ℂ) (inner (𝕜 := ℂ) e (bochnerWindow R U f x))
        (inner (𝕜 := ℂ) e (bochnerWindow R U f (x - y))) := by
  have hj := bochnerWindowCoordinate_coe hR U hU f e
  have ht := (measurePreserving_add_right volume (-y)).quasiMeasurePreserving.ae hj
  rw [unitaryCorrelation, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hj, physicalTranslationUnitary_coe y (bochnerWindowCoordinate hR U hU f e), ht]
    with x hx hxtrans hxshift
  rw [hx, hxtrans]
  simpa only [sub_eq_add_neg] using congrArg (inner (𝕜 := ℂ) (inner (𝕜 := ℂ) e (bochnerWindow R U f x))) hxshift
/-- Inside their common support, two windows have constant correlation. -/
theorem inner_bochnerWindow_shift (R : ℝ) (U : Euclidean d → H ≃ₗᵢ[ℂ] H)
    (hadd : ∀ z y f, U z (U y f) = U (z + y) f) (f : H) (y x : Euclidean d) :
    inner (𝕜 := ℂ) (bochnerWindow R U f x) (bochnerWindow R U f (x - y)) =
      (euclideanBox d R ∩ translate (-y) (euclideanBox d R)).indicator
        (fun _ => (volume.real (euclideanBox d R) : ℂ)⁻¹ * unitaryCorrelation U f y) x := by
  have hmemiff : x ∈ euclideanBox d R ∩ translate (-y) (euclideanBox d R) ↔
      x ∈ euclideanBox d R ∧ x - y ∈ euclideanBox d R := by
    simp only [mem_inter_iff, mem_translate, sub_eq_add_neg]
  have hinner : inner (𝕜 := ℂ) (U (-x) f) (U (-(x - y)) f) = unitaryCorrelation U f y := by
    have h := unitaryCorrelation_sub U hadd f (-x) (-(x - y))
    rw [show -(x - y) - -x = y by abel] at h
    exact h.symm
  have hn : (((Real.sqrt (volume.real (euclideanBox d R)))⁻¹ : ℝ) : ℂ) ^ 2 =
      (volume.real (euclideanBox d R) : ℂ)⁻¹ := by
    rw [← Complex.ofReal_pow, inv_pow,
      Real.sq_sqrt (show 0 ≤ volume.real (euclideanBox d R) from ENNReal.toReal_nonneg), Complex.ofReal_inv]
  by_cases hx : x ∈ euclideanBox d R <;> by_cases hxy : x - y ∈ euclideanBox d R
  · have hmem : x ∈ euclideanBox d R ∩ translate (-y) (euclideanBox d R) :=
      ⟨hx, by simpa only [mem_translate, sub_eq_add_neg] using hxy⟩
    simp only [bochnerWindow, indicator_of_mem hx, indicator_of_mem hxy, indicator_of_mem hmem,
      inner_smul_left, inner_smul_right, Complex.conj_ofReal]
    rw [hinner]
    calc
      _ = ((((Real.sqrt (volume.real (euclideanBox d R)))⁻¹ : ℝ) : ℂ) ^ 2) * unitaryCorrelation U f y := by ring
      _ = _ := by rw [hn]
  all_goals simp [bochnerWindow, hx, hxy, hmemiff]
/-- The window correlation is exactly the continuous Fejér weight times the original correlation. -/
theorem integral_inner_bochnerWindow_shift {R : ℝ} (hR : 0 < R)
    (U : Euclidean d → H ≃ₗᵢ[ℂ] H) (hadd : ∀ z y f, U z (U y f) = U (z + y) f)
    (f : H) (y : Euclidean d) :
    (∫ x, inner (𝕜 := ℂ) (bochnerWindow R U f x) (bochnerWindow R U f (x - y))) =
      (fejerWeight R y : ℂ) * unitaryCorrelation U f y := by
  simp_rw [inner_bochnerWindow_shift R U hadd f y]
  have hm : MeasurableSet (euclideanBox d R ∩ translate (-y) (euclideanBox d R)) :=
    (measurableSet_euclideanBox d R).inter
      ((measurableSet_euclideanBox d R).preimage (measurable_id.add_const (-y)))
  rw [integral_indicator_const _ hm, Complex.real_smul]
  have hw := fejerWeight_eq_normalized_overlap hR (-y)
  rw [fejerWeight_neg] at hw
  rw [hw, Complex.ofReal_div]
  ring
end RieszEuclidean
