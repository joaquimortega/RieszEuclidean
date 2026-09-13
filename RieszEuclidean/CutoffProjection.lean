import RieszEuclidean.FourierExtension
import RieszEuclidean.ProjectionGap
noncomputable section
open MeasureTheory Set
namespace RieszEuclidean
/-- Multiplication by the domain indicator on actual L² classes. -/
def domainCutoff {d : ℕ} (Ω : Set (Euclidean d)) (hΩ : MeasurableSet Ω)
    (f : FullL2 d) : FullL2 d := ((Lp.memLp f).indicator hΩ).toLp (Ω.indicator f)
/-- The cutoff has the expected almost-everywhere representative. -/
theorem domainCutoff_coe {d : ℕ} (Ω : Set (Euclidean d)) (hΩ : MeasurableSet Ω)
    (f : FullL2 d) : (domainCutoff Ω hΩ f : Euclidean d → ℂ) =ᵐ[volume] Ω.indicator f :=
  MemLp.coeFn_toLp _
/-- Indicator multiplication contracts the L² norm. -/
theorem domainCutoff_norm_le {d : ℕ} (Ω : Set (Euclidean d)) (hΩ : MeasurableSet Ω)
    (f : FullL2 d) : ‖domainCutoff Ω hΩ f‖ ≤ ‖f‖ := by
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [domainCutoff_coe Ω hΩ f] with x hx
  rw [hx]
  exact norm_indicator_le_norm_self _ _
/-- The domain cutoff as a complex linear map. -/
def domainCutoffLM {d : ℕ} (Ω : Set (Euclidean d)) (hΩ : MeasurableSet Ω) :
    FullL2 d →ₗ[ℂ] FullL2 d where
  toFun := domainCutoff Ω hΩ
  map_add' f g := by
    apply Lp.ext
    filter_upwards [domainCutoff_coe Ω hΩ (f + g), domainCutoff_coe Ω hΩ f,
      domainCutoff_coe Ω hΩ g, Lp.coeFn_add f g,
      Lp.coeFn_add (domainCutoff Ω hΩ f) (domainCutoff Ω hΩ g)] with x h1 h2 h3 h4 h5
    simp only [h1, h5, Pi.add_apply, h2, h3]
    by_cases hx : x ∈ Ω
    · simpa only [indicator_of_mem hx, Pi.add_apply] using h4
    · simp only [indicator_of_not_mem hx, add_zero]
  map_smul' c f := by
    apply Lp.ext
    filter_upwards [domainCutoff_coe Ω hΩ (c • f), domainCutoff_coe Ω hΩ f,
      Lp.coeFn_smul c f, Lp.coeFn_smul c (domainCutoff Ω hΩ f)] with x h1 h2 h3 h4
    simp only [h1, h4, Pi.smul_apply, h2, RingHom.id_apply]
    by_cases hx : x ∈ Ω <;> simp [hx, h3]
/-- The domain cutoff is a bounded complex linear operator. -/
def domainCutoffCLM {d : ℕ} (Ω : Set (Euclidean d)) (hΩ : MeasurableSet Ω) :
    FullL2 d →L[ℂ] FullL2 d :=
  (domainCutoffLM Ω hΩ).mkContinuous 1 (fun f => by simpa using domainCutoff_norm_le Ω hΩ f)
/-- Multiplication by a measurable indicator is an orthogonal projection. -/
def domainProjection {d : ℕ} (Ω : Set (Euclidean d)) (hΩ : MeasurableSet Ω) :
    OrthProjection (FullL2 d) where
  op := domainCutoffCLM Ω hΩ
  idempotent := by
    ext f
    filter_upwards [domainCutoff_coe Ω hΩ (domainCutoff Ω hΩ f),
      domainCutoff_coe Ω hΩ f] with x h1 h2
    change (domainCutoff Ω hΩ (domainCutoff Ω hΩ f) : Euclidean d → ℂ) x =
      (domainCutoff Ω hΩ f : Euclidean d → ℂ) x
    rw [h1, h2]
    by_cases hx : x ∈ Ω <;> simp [hx, h2]
  symmetric f g := by
    rw [L2.inner_def, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [domainCutoff_coe Ω hΩ f, domainCutoff_coe Ω hΩ g] with x hf hg
    change inner (𝕜 := ℂ) ((domainCutoff Ω hΩ f : Euclidean d → ℂ) x) (g x) =
      inner (𝕜 := ℂ) (f x) ((domainCutoff Ω hΩ g : Euclidean d → ℂ) x)
    rw [hf, hg]
    by_cases hx : x ∈ Ω <;> simp [hx]
/-- The paper's Euclidean Fourier cutoff P = F⁻¹ 1_Ω F. -/
def fourierProjection {d : ℕ} (Ω : Set (Euclidean d)) (hΩ : MeasurableSet Ω) :
    OrthProjection (FullL2 d) := (domainProjection Ω hΩ).conjugate (paperFourierL2 d)
/-- Fourier transforms the cutoff projection into multiplication by the domain indicator. -/
theorem fourierProjection_transform {d : ℕ} (Ω : Set (Euclidean d)) (hΩ : MeasurableSet Ω)
    (f : FullL2 d) :
    paperFourierL2 d ((fourierProjection Ω hΩ).op f) =
      domainCutoff Ω hΩ (paperFourierL2 d f) := by
  exact (paperFourierL2 d).apply_symm_apply _
/-- A cutoff fixes precisely the L² functions vanishing outside its domain. -/
theorem domainCutoff_eq_self_iff {d : ℕ} (Ω : Set (Euclidean d)) (hΩ : MeasurableSet Ω)
    (f : FullL2 d) : domainCutoff Ω hΩ f = f ↔ ∀ᵐ x ∂volume, x ∉ Ω → f x = 0 := by
  constructor
  · intro h
    have hc := domainCutoff_coe Ω hΩ f
    rw [h] at hc
    filter_upwards [hc] with x hx hnot
    simpa only [Set.indicator_of_not_mem hnot] using hx
  · intro h
    apply Lp.ext
    filter_upwards [domainCutoff_coe Ω hΩ f, h] with x hx hz
    rw [hx]
    by_cases hmem : x ∈ Ω
    · exact Set.indicator_of_mem hmem _
    · simp only [Set.indicator_of_not_mem hmem, hz hmem]
/-- The Fourier cutoff range is exactly the functions whose Fourier transform vanishes off Ω. -/
theorem fourierProjection_mem_range_iff {d : ℕ} (Ω : Set (Euclidean d))
    (hΩ : MeasurableSet Ω) (f : FullL2 d) :
    f ∈ (fourierProjection Ω hΩ).range ↔
      ∀ᵐ x ∂volume, x ∉ Ω → paperFourierL2 d f x = 0 := by
  rw [OrthProjection.mem_range_iff]
  constructor
  · intro h
    have hF := congrArg (paperFourierL2 d) h
    rw [fourierProjection_transform] at hF
    exact (domainCutoff_eq_self_iff Ω hΩ _).mp hF
  · intro h
    apply (paperFourierL2 d).injective
    rw [fourierProjection_transform]
    exact (domainCutoff_eq_self_iff Ω hΩ _).mpr h
end RieszEuclidean
