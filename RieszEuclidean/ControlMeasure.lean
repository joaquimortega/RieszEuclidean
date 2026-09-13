import RieszEuclidean.SpectralMeasures
import RieszEuclidean.UnitSphereApproximation
open MeasureTheory
open scoped ENNReal NNReal
namespace RieszEuclidean
variable {d : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
/-- The parallelogram identity bounds the measure of a vector by a nearby vector. -/
theorem spectralMeasure_set_le (U : Euclidean d → H ≃ₗᵢ[ℂ] H)
    (σ : H → Measure (Euclidean d))
    (hσ : ∀ f, RepresentsCorrelation (unitaryCorrelation U f) (σ f))
    (f g : H) (E : Set (Euclidean d)) :
    σ f E ≤ 2 * (σ (f - g) E + σ g E) := by
  have hp := spectralMeasure_parallelogram U (f - g) g
    (hσ ((f - g) + g)) (hσ ((f - g) - g)) (hσ (f - g)) (hσ g)
  have he := congrArg (fun μ : Measure (Euclidean d) => μ E) hp
  simp only [sub_add_cancel, Measure.add_apply, Measure.smul_apply, smul_eq_mul] at he
  calc
    σ f E ≤ σ f E + σ ((f - g) - g) E := le_self_add
    _ = 2 * (σ (f - g) E + σ g E) := he
/-- Total spectral mass in the extended nonnegative reals. -/
theorem spectralMeasure_univ (U : Euclidean d → H ≃ₗᵢ[ℂ] H)
    (h0 : ∀ f, U 0 f = f) (σ : H → Measure (Euclidean d))
    (hσ : ∀ f, RepresentsCorrelation (unitaryCorrelation U f) (σ f)) (f : H) :
    σ f Set.univ = ENNReal.ofReal (‖f‖ ^ 2) := by
  letI := (hσ f).1
  have hm := (hσ f).unitary_mass U h0 f
  rw [← hm, measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)]
/-- The total mass bounds the error term in the control-measure argument. -/
theorem spectralMeasure_set_le_norm (U : Euclidean d → H ≃ₗᵢ[ℂ] H)
    (h0 : ∀ f, U 0 f = f) (σ : H → Measure (Euclidean d))
    (hσ : ∀ f, RepresentsCorrelation (unitaryCorrelation U f) (σ f))
    (f g : H) (E : Set (Euclidean d)) :
    σ f E ≤ 2 * (ENNReal.ofReal (‖f - g‖ ^ 2) + σ g E) := by
  apply (spectralMeasure_set_le U σ hσ f g E).trans
  gcongr
  calc
    σ (f - g) E ≤ σ (f - g) Set.univ := measure_mono (Set.subset_univ _)
    _ = _ := spectralMeasure_univ U h0 σ hσ _
/-- A common spectral null set stays null under norm limits of vectors. -/
theorem spectralMeasure_null_of_tendsto (U : Euclidean d → H ≃ₗᵢ[ℂ] H)
    (h0 : ∀ f, U 0 f = f) (σ : H → Measure (Euclidean d))
    (hσ : ∀ f, RepresentsCorrelation (unitaryCorrelation U f) (σ f))
    {g : ℕ → H} {f : H} (hg : Filter.Tendsto g Filter.atTop (nhds f))
    (E : Set (Euclidean d)) (hE : ∀ n, σ (g n) E = 0) : σ f E = 0 := by
  have ht : Filter.Tendsto (fun n => 2 * ‖f - g n‖ ^ 2) Filter.atTop (nhds 0) := by
    simpa using (tendsto_const_nhds (x := (2 : ℝ))).mul
      (((tendsto_const_nhds (x := f)).sub hg).norm.pow 2)
  have ht' : Filter.Tendsto (fun n => ENNReal.ofReal (2 * ‖f - g n‖ ^ 2))
      Filter.atTop (nhds 0) := by
    simpa using (ENNReal.continuous_ofReal.tendsto 0).comp ht
  apply le_antisymm _ bot_le
  apply ge_of_tendsto ht'
  apply Filter.Eventually.of_forall
  intro n
  have he := spectralMeasure_set_le_norm U h0 σ hσ f (g n) E
  simpa [hE n, ENNReal.ofReal_mul] using he
/-- The paper's positive summable weights, with natural indices starting at zero. -/
noncomputable def spectralControlWeight (n : ℕ) : ℝ≥0∞ := (2 : ℝ≥0∞)⁻¹ ^ (n + 1)
/-- The control weights have sum one. -/
theorem tsum_spectralControlWeight : (∑' n, spectralControlWeight n) = 1 := by
  simp only [spectralControlWeight, pow_succ]
  rw [ENNReal.tsum_mul_right, ENNReal.tsum_geometric, ENNReal.one_sub_inv_two, inv_inv]
  exact ENNReal.mul_inv_cancel (by norm_num) (by norm_num)
/-- Every control weight is nonzero. -/
theorem spectralControlWeight_ne_zero (n : ℕ) : spectralControlWeight n ≠ 0 := by
  exact pow_ne_zero _ (ENNReal.inv_ne_zero.mpr ENNReal.ofNat_ne_top)
/-- The common control measure is the actual countable weighted sum of spectral measures. -/
noncomputable def spectralControlMeasure (σ : H → Measure (Euclidean d))
    (h : ℕ → H) : Measure (Euclidean d) :=
  Measure.sum (fun n => spectralControlWeight n • σ (h n))
/-- Unit vectors give a control measure of mass one. -/
theorem spectralControlMeasure_probability (U : Euclidean d → H ≃ₗᵢ[ℂ] H)
    (h0 : ∀ f, U 0 f = f) (σ : H → Measure (Euclidean d))
    (hσ : ∀ f, RepresentsCorrelation (unitaryCorrelation U f) (σ f))
    (h : ℕ → H) (hh : ∀ n, ‖h n‖ = 1) : IsProbabilityMeasure (spectralControlMeasure σ h) := by
  constructor
  rw [spectralControlMeasure, Measure.sum_apply _ MeasurableSet.univ]
  simp_rw [Measure.smul_apply, smul_eq_mul, spectralMeasure_univ U h0 σ hσ, hh,
    one_pow, ENNReal.ofReal_one, mul_one]
  exact tsum_spectralControlWeight
omit [NormedAddCommGroup H] [InnerProductSpace ℂ H] in
/-- A null set for the control measure is null for every measure in the sequence. -/
theorem spectralControlMeasure_null_seq (σ : H → Measure (Euclidean d)) (h : ℕ → H)
    (E : Set (Euclidean d)) (hE : spectralControlMeasure σ h E = 0) (n : ℕ) :
    σ (h n) E = 0 := by
  have he := Measure.sum_apply_eq_zero.mp hE n
  simpa only [Measure.smul_apply, smul_eq_mul, mul_eq_zero,
    spectralControlWeight_ne_zero, false_or] using he
/-- Dense scalar multiples of the chosen unit vectors give one null-set control for all vectors. -/
theorem spectralMeasure_absolutelyContinuous_control
    (U : Euclidean d → H ≃ₗᵢ[ℂ] H) (h0 : ∀ f, U 0 f = f)
    (σ : H → Measure (Euclidean d))
    (hσ : ∀ f, RepresentsCorrelation (unitaryCorrelation U f) (σ f))
    (h : ℕ → H)
    (hdense : ∀ f : H, ∃ g : ℕ → H,
      (∀ n, ∃ c : ℂ, ∃ j : ℕ, g n = c • h j) ∧
      Filter.Tendsto g Filter.atTop (nhds f)) (f : H) :
    σ f ≪ spectralControlMeasure σ h := by
  intro E hE
  obtain ⟨g, hg, hlim⟩ := hdense f
  apply spectralMeasure_null_of_tendsto U h0 σ hσ hlim E
  intro n
  obtain ⟨c, j, he⟩ := hg n
  rw [he, spectralMeasure_smul U c (h j) (hσ _) (hσ _)]
  simp only [Measure.smul_apply, smul_eq_mul,
    spectralControlMeasure_null_seq σ h E hE j, mul_zero]
/-- Separability constructs the paper's probability control measure from unit spectral measures.
The representing family is supplied explicitly while Bochner existence is postponed. -/
theorem exists_spectralControlMeasure [TopologicalSpace.SeparableSpace H]
    (U : Euclidean d → H ≃ₗᵢ[ℂ] H) (h0 : ∀ f, U 0 f = f)
    (σ : H → Measure (Euclidean d))
    (hσ : ∀ f, RepresentsCorrelation (unitaryCorrelation U f) (σ f))
    (u : H) (hu : ‖u‖ = 1) :
    ∃ h : ℕ → H, (∀ n, ‖h n‖ = 1) ∧
      IsProbabilityMeasure (spectralControlMeasure σ h) ∧
      ∀ f, σ f ≪ spectralControlMeasure σ h := by
  obtain ⟨h, hh, hdense⟩ := exists_unit_sequence_scalar_approximants u hu
  exact ⟨h, hh, spectralControlMeasure_probability U h0 σ hσ h hh,
    spectralMeasure_absolutelyContinuous_control U h0 σ hσ h hdense⟩
end RieszEuclidean
