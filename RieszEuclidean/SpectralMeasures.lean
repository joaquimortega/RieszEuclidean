import RieszEuclidean.Correlations
import Mathlib.MeasureTheory.Measure.CharacteristicFunction
open MeasureTheory RealInnerProductSpace
open scoped ENNReal NNReal
namespace RieszEuclidean
/-- A finite positive Borel measure representing a Euclidean scalar correlation
with the paper's positive 2π Fourier convention. -/
def RepresentsCorrelation {d : ℕ} (φ : Euclidean d → ℂ)
    (σ : Measure (Euclidean d)) : Prop :=
  IsFiniteMeasure σ ∧ ∀ y, φ y =
    ∫ θ, (Real.fourierChar (inner (𝕜 := ℝ) y θ) : ℂ) ∂σ
/-- Finite measures are determined by the paper's Euclidean Fourier characters. -/
theorem measure_eq_of_fourierChar_integral_eq {d : ℕ}
    {σ τ : Measure (Euclidean d)} [IsFiniteMeasure σ] [IsFiniteMeasure τ]
    (h : ∀ y : Euclidean d,
      (∫ θ, (Real.fourierChar (inner (𝕜 := ℝ) y θ) : ℂ) ∂σ) =
      ∫ θ, (Real.fourierChar (inner (𝕜 := ℝ) y θ) : ℂ) ∂τ) : σ = τ := by
  refine ext_of_integral_char_eq Real.continuous_fourierChar Real.fourierChar_ne_one
    (V := Euclidean d) (W := Euclidean d) (L := bilinFormOfRealInner) ?_ ?_ ?_
  · intro v hv
    exact DFunLike.ne_iff.mpr ⟨v, inner_self_ne_zero.mpr hv⟩
  · exact continuous_inner
  · intro y
    simpa only [BoundedContinuousFunction.char_apply, bilinFormOfRealInner_apply_apply,
      real_inner_comm] using h y
/-- A finite positive representing spectral measure is unique. -/
theorem RepresentsCorrelation.unique {d : ℕ} {φ : Euclidean d → ℂ}
    {σ τ : Measure (Euclidean d)} (hσ : RepresentsCorrelation φ σ)
    (hτ : RepresentsCorrelation φ τ) : σ = τ := by
  letI := hσ.1
  letI := hτ.1
  exact measure_eq_of_fourierChar_integral_eq (fun y => (hσ.2 y).symm.trans (hτ.2 y))
/-- The zero-frequency value of a correlation is the total representing mass. -/
theorem RepresentsCorrelation.mass {d : ℕ} {φ : Euclidean d → ℂ}
    {σ : Measure (Euclidean d)} (hσ : RepresentsCorrelation φ σ) :
    (σ.real Set.univ : ℂ) = φ 0 := by
  letI := hσ.1
  simpa using (hσ.2 0).symm
/-- A representing measure for a unitary correlation has the required squared-norm mass. -/
theorem RepresentsCorrelation.unitary_mass {d : ℕ} {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (U : Euclidean d → H ≃ₗᵢ[ℂ] H) (h0 : ∀ f, U 0 f = f) (f : H)
    {σ : Measure (Euclidean d)} (hσ : RepresentsCorrelation (unitaryCorrelation U f) σ) :
    σ.real Set.univ = ‖f‖ ^ 2 := by
  have hm := hσ.mass
  rw [unitaryCorrelation_zero U h0 f] at hm
  exact_mod_cast hm
/-- The constant correlation one is represented by the unit point mass at zero. -/
theorem representsCorrelation_one {d : ℕ} :
    RepresentsCorrelation (fun _ : Euclidean d => (1 : ℂ)) (Measure.dirac 0) := by
  refine ⟨inferInstance, ?_⟩
  intro y
  simp
/-- The actual invariant unit constant has precisely the Dirac spectral measure at zero. -/
theorem represents_hullCorrelation_one {d : ℕ} {δ : ℝ} (hδ : 0 < δ)
    (Γ : SeparatedConfiguration d δ) [MeasurableSpace (SeparatedConfiguration.hull Γ)]
    (μ : Measure (SeparatedConfiguration.hull Γ)) [IsProbabilityMeasure μ]
    (hμ : ∀ z : Euclidean d, MeasurePreserving (SeparatedConfiguration.hullTranslate hδ Γ z) μ μ) :
    RepresentsCorrelation (SeparatedConfiguration.hullCorrelation hδ Γ μ hμ (Lp.const 2 μ (1 : ℂ)))
      (Measure.dirac 0) := by
  have he : SeparatedConfiguration.hullCorrelation hδ Γ μ hμ (Lp.const 2 μ (1 : ℂ)) =
      (fun _ => 1) := funext (SeparatedConfiguration.hullCorrelation_one hδ Γ μ hμ)
  rw [he]
  exact representsCorrelation_one
/-- Fourier characters are integrable against any finite Euclidean measure. -/
theorem integrable_fourierChar (d : ℕ) (σ : Measure (Euclidean d)) [IsFiniteMeasure σ]
    (y : Euclidean d) : Integrable (fun θ => (Real.fourierChar (inner (𝕜 := ℝ) y θ) : ℂ)) σ := by
  have hi := (BoundedContinuousFunction.char Real.continuous_fourierChar
    (L := bilinFormOfRealInner) continuous_inner y).integrable σ
  convert hi using 1
  ext θ
  simp only [BoundedContinuousFunction.char_apply, bilinFormOfRealInner_apply_apply,
    real_inner_comm]

/-- Addition of representing measures represents addition of correlations. -/
theorem RepresentsCorrelation.add {d : ℕ} {φ ψ : Euclidean d → ℂ}
    {σ τ : Measure (Euclidean d)} (hσ : RepresentsCorrelation φ σ)
    (hτ : RepresentsCorrelation ψ τ) : RepresentsCorrelation (φ + ψ) (σ + τ) := by
  letI := hσ.1
  letI := hτ.1
  refine ⟨inferInstance, fun y => ?_⟩
  rw [Pi.add_apply, hσ.2 y, hτ.2 y,
    integral_add_measure (integrable_fourierChar d σ y) (integrable_fourierChar d τ y)]
/-- A nonnegative scalar scales a representing measure and its correlation together. -/
theorem RepresentsCorrelation.smul {d : ℕ} {φ : Euclidean d → ℂ}
    {σ : Measure (Euclidean d)} (hσ : RepresentsCorrelation φ σ) (c : ℝ≥0) :
    RepresentsCorrelation (fun y => (c : ℂ) * φ y) ((c : ℝ≥0∞) • σ) := by
  letI := hσ.1
  refine ⟨σ.smul_finite ENNReal.coe_ne_top, fun y => ?_⟩
  change (c : ℂ) * φ y = _
  rw [integral_smul_measure, hσ.2 y]
  simp [Complex.real_smul]
/-- Uniqueness turns the correlation parallelogram identity into the measure identity. -/
theorem spectralMeasure_parallelogram {d : ℕ} {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (U : Euclidean d → H ≃ₗᵢ[ℂ] H) (f g : H)
    {σp σm σf σg : Measure (Euclidean d)}
    (hp : RepresentsCorrelation (unitaryCorrelation U (f + g)) σp)
    (hm : RepresentsCorrelation (unitaryCorrelation U (f - g)) σm)
    (hf : RepresentsCorrelation (unitaryCorrelation U f) σf)
    (hg : RepresentsCorrelation (unitaryCorrelation U g) σg) :
    σp + σm = (2 : ℝ≥0∞) • (σf + σg) := by
  have hl := hp.add hm
  have he : unitaryCorrelation U (f + g) + unitaryCorrelation U (f - g) =
      (fun y => (2 : ℂ) * (unitaryCorrelation U f + unitaryCorrelation U g) y) :=
    funext (unitaryCorrelation_parallelogram U f g)
  rw [he] at hl
  exact hl.unique ((hf.add hg).smul 2)
/-- Uniqueness turns correlation homogeneity into squared-modulus scaling of measures. -/
theorem spectralMeasure_smul {d : ℕ} {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (U : Euclidean d → H ≃ₗᵢ[ℂ] H) (c : ℂ) (f : H)
    {σc σf : Measure (Euclidean d)}
    (hc : RepresentsCorrelation (unitaryCorrelation U (c • f)) σc)
    (hf : RepresentsCorrelation (unitaryCorrelation U f) σf) :
    σc = ((‖c‖₊ ^ 2 : ℝ≥0) : ℝ≥0∞) • σf := by
  have he : unitaryCorrelation U (c • f) =
      (fun y => ((‖c‖₊ ^ 2 : ℝ≥0) : ℂ) * unitaryCorrelation U f y) := by
    ext y
    simpa using unitaryCorrelation_smul U c f y
  rw [he] at hc
  exact hc.unique (hf.smul (‖c‖₊ ^ 2))
end RieszEuclidean
