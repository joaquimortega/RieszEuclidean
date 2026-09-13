import RieszEuclidean.FiniteFilters
import RieszEuclidean.BoxOverlap
import RieszEuclidean.Koopman
import Mathlib.MeasureTheory.Group.Prod
noncomputable section
open MeasureTheory Set
namespace RieszEuclidean
/-- A continuous difference kernel is absolutely integrable on a pair of finite boxes. -/
theorem integrableOn_box_difference {d : ℕ} (R : ℝ) {H : Euclidean d → ℂ}
    (hH : Continuous H) :
    Integrable (fun p : Euclidean d × Euclidean d => H (p.1 - p.2))
      ((volume.restrict (euclideanBox d R)).prod (volume.restrict (euclideanBox d R))) := by
  rw [Measure.prod_restrict]
  exact (hH.comp (continuous_fst.sub continuous_snd)).continuousOn.integrableOn_compact
    ((isCompact_euclideanBox d R).prod (isCompact_euclideanBox d R))
/-- Shearing the two spatial variables computes the unnormalized box overlap exactly. -/
theorem integral_box_difference_eq_overlap {d : ℕ} (R : ℝ) {H : Euclidean d → ℂ}
    (hH : Continuous H) :
    (∫ v in euclideanBox d R, ∫ w in euclideanBox d R, H (v - w)) =
      ∫ y, (volume.real (euclideanBox d R ∩ translate y (euclideanBox d R)) : ℂ) * H y := by
  let C := euclideanBox d R
  let F : Euclidean d × Euclidean d → ℂ :=
    (C ×ˢ C).indicator (fun p => H (p.1 - p.2))
  have hC : MeasurableSet C := (isCompact_euclideanBox d R).measurableSet
  have hFm : StronglyMeasurable F :=
    (hH.comp (continuous_fst.sub continuous_snd)).stronglyMeasurable.indicator (hC.prod hC)
  have hFi : Integrable F (volume.prod volume) := by
    apply (integrable_indicator_iff (hC.prod hC)).mpr
    unfold IntegrableOn
    rw [← Measure.prod_restrict]
    exact integrableOn_box_difference R hH
  have hS := measurePreserving_add_prod (volume : Measure (Euclidean d))
    (volume : Measure (Euclidean d))
  have hSi := (hS.integrable_comp hFm.aestronglyMeasurable).mpr hFi
  have hchange := integral_map_of_stronglyMeasurable (μ := volume.prod volume) hS.measurable hFm
  rw [hS.map_eq] at hchange
  calc
    _ = ∫ p, F p ∂volume.prod volume := by
      rw [integral_indicator (hC.prod hC), ← Measure.prod_restrict]
      exact integral_integral (integrableOn_box_difference R hH)
    _ = ∫ y, ∫ w, F (y + w, w) := hchange.trans (integral_prod _ hSi)
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with y
      have he : (fun w => F (y + w, w)) =
          (C ∩ translate y C).indicator (fun _ => H y) := by
        funext w
        simp only [F, mem_prod, mem_inter_iff, mem_translate]
        by_cases hw : w ∈ C <;> by_cases hyw : w + y ∈ C <;>
          simp [hw, hyw, add_comm y w]
      have hCt : MeasurableSet (C ∩ translate y C) :=
        hC.inter (hC.preimage (measurable_id.add_const y))
      rw [he, integral_indicator hCt]
      simp only [setIntegral_const, Complex.real_smul, smul_eq_mul]
      rfl
/-- The actual box average of any continuous difference kernel is its Fejér-weighted integral. -/
theorem normalized_integral_box_difference {d : ℕ} {R : ℝ} (hR : 0 < R)
    {H : Euclidean d → ℂ} (hH : Continuous H) :
    (volume.real (euclideanBox d R) : ℂ)⁻¹ *
      (∫ v in euclideanBox d R, ∫ w in euclideanBox d R, H (v - w)) =
        ∫ y, (fejerWeight R y : ℂ) * H y := by
  rw [integral_box_difference_eq_overlap R hH, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with y
  rw [fejerWeight_eq_normalized_overlap hR, Complex.ofReal_div]
  ring
/-- The spatial Fourier pairing has an absolutely integrable two-variable kernel. -/
theorem integrable_fourier_pairing_kernel {d : ℕ} (Ω : Set (Euclidean d))
    (hΩ : MeasurableSet Ω) (hfin : volume Ω ≠ ⊤) (f g : FullL2 d)
    (hf : Integrable (f : Euclidean d → ℂ)) (hg : Integrable (g : Euclidean d → ℂ)) :
    Integrable (fun p : Euclidean d × Euclidean d =>
      domainKernel Ω (p.1 - p.2) * f p.2 * star (g p.1)) (volume.prod volume) := by
  have hm : StronglyMeasurable (fun p : Euclidean d × Euclidean d =>
      domainKernel Ω (p.1 - p.2) * f p.2 * star (g p.1)) :=
    (((continuous_domainKernel Ω hΩ hfin).comp
      (continuous_fst.sub continuous_snd)).stronglyMeasurable.mul
      ((Lp.stronglyMeasurable f).comp_measurable measurable_snd)).mul
        (continuous_star.comp_stronglyMeasurable
          ((Lp.stronglyMeasurable g).comp_measurable measurable_fst))
  apply ((hg.norm.mul_prod hf.norm).const_mul (volume.real Ω)).mono' hm.aestronglyMeasurable
  filter_upwards [] with p
  simp only [norm_mul, norm_star]
  calc
    ‖domainKernel Ω (p.1 - p.2)‖ * ‖f p.2‖ * ‖g p.1‖ ≤
        volume.real Ω * ‖f p.2‖ * ‖g p.1‖ :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (norm_domainKernel_le Ω _) (norm_nonneg _)) (norm_nonneg _)
    _ = _ := by ring
/-- The actual Fourier projection paired with any L¹∩L² test has its kernel pairing. -/
theorem inner_fourierProjection_kernel {d : ℕ} (Ω : Set (Euclidean d))
    (hΩ : MeasurableSet Ω) (hfin : volume Ω ≠ ⊤) (f g : FullL2 d)
    (hf : Integrable (f : Euclidean d → ℂ)) :
    inner (𝕜 := ℂ) g ((fourierProjection Ω hΩ).op f) =
      ∫ v, ∫ w, domainKernel Ω (v - w) * f w * star (g v) := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [fourierProjection_kernel Ω hΩ hfin f hf] with v hv
  change inner (𝕜 := ℂ) (g v) ((fourierProjection Ω hΩ).op f v) = _
  rw [hv, integral_mul_const]
  simp only [RCLike.inner_apply, starRingEnd_apply]
/-- Taking a scalar pairing of the actual filter commutes with its Bochner integral. -/
theorem inner_finiteFilter {d : ℕ} {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (U : Euclidean d → H ≃ₗᵢ[ℂ] H) (hU : ∀ f, Continuous (fun y => U y f))
    (Ω : Set (Euclidean d)) (hΩ : MeasurableSet Ω) (hfin : volume Ω ≠ ⊤)
    (t : Euclidean d) {R : ℝ} (hR : 0 < R) (f g : H) :
    inner (𝕜 := ℂ) g (finiteFilter U hU Ω hΩ hfin t hR f) =
      ∫ y, finiteFilterKernel Ω t R y * inner (𝕜 := ℂ) g (U y f) := by
  change inner (𝕜 := ℂ) g (∫ y, finiteFilterKernel Ω t R y • U y f) = _
  rw [← integral_inner (integrable_unitary_smul U hU (integrable_finiteFilterKernel Ω hΩ hfin t hR) f)]
  simp only [inner_smul_right]
namespace SeparatedConfiguration
/-- Stationarity turns the two translated representatives into the actual Koopman pairing. -/
theorem integral_stationary_pairing_Lp {d : ℕ} {δ : ℝ} (hδ : 0 < δ)
    (Γ : SeparatedConfiguration d δ) [MeasurableSpace (hull Γ)]
    (μ : Measure (hull Γ))
    (hμ : ∀ z : Euclidean d, MeasurePreserving (hullTranslate hδ Γ z) μ μ)
    (f g : Lp ℂ 2 μ) (v w : Euclidean d) :
    (∫ Δ, f (hullTranslate hδ Γ w Δ) * star (g (hullTranslate hδ Γ v Δ)) ∂μ) =
      inner (𝕜 := ℂ) g (hullKoopmanUnitary hδ Γ μ hμ (v - w) f) := by
  let F := fun Δ : hull Γ => f (hullTranslate hδ Γ (-(v - w)) Δ) * star (g Δ)
  have hFm : StronglyMeasurable F :=
    ((Lp.stronglyMeasurable f).comp_measurable (hμ (-(v - w))).measurable).mul
      (continuous_star.comp_stronglyMeasurable (Lp.stronglyMeasurable g))
  have he (Δ : hull Γ) : f (hullTranslate hδ Γ w Δ) *
      star (g (hullTranslate hδ Γ v Δ)) = F (hullTranslate hδ Γ v Δ) := by
    have ht : hullTranslate hδ Γ (-(v - w)) (hullTranslate hδ Γ v Δ) =
        hullTranslate hδ Γ w Δ := by
      apply Subtype.ext
      change translate (-(v - w)) (translate v Δ.val) = translate w Δ.val
      rw [translate_add]
      congr 1
      abel
    simp only [F, ht]
  simp_rw [he]
  have hi := integral_map_of_stronglyMeasurable (μ := μ) (hμ v).measurable hFm
  rw [(hμ v).map_eq] at hi
  rw [← hi, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_compMeasurePreserving f (hμ (-(v - w)))] with Δ hΔ
  change F Δ = inner (𝕜 := ℂ) (g Δ)
    (Lp.compMeasurePreserving (hullTranslate hδ Γ (-(v - w))) (hμ (-(v - w))) f Δ)
  rw [hΔ]
  simp only [F, RCLike.inner_apply, starRingEnd_apply, Function.comp_apply]
/-- The expanded normalized spatial Fourier form equals the actual stationary finite filter. -/
theorem normalized_stationary_fourier_form {d : ℕ} {δ : ℝ} (hδ : 0 < δ)
    (Γ : SeparatedConfiguration d δ) [MeasurableSpace (hull Γ)] [BorelSpace (hull Γ)]
    (μ : Measure (hull Γ)) [IsProbabilityMeasure μ]
    (hμ : ∀ z : Euclidean d, MeasurePreserving (hullTranslate hδ Γ z) μ μ)
    (Ω : Set (Euclidean d)) (hΩ : MeasurableSet Ω) (hfin : volume Ω ≠ ⊤)
    (t : Euclidean d) {R : ℝ} (hR : 0 < R) (f g : Lp ℂ 2 μ) :
    (volume.real (euclideanBox d R) : ℂ)⁻¹ *
      (∫ v in euclideanBox d R, ∫ w in euclideanBox d R,
        domainKernel Ω (v - w) * (Real.fourierChar (inner (𝕜 := ℝ) t (v - w)) : ℂ) *
          ∫ Δ, f (hullTranslate hδ Γ w Δ) * star (g (hullTranslate hδ Γ v Δ)) ∂μ) =
      inner (𝕜 := ℂ) g
        (finiteFilter (hullKoopmanUnitary hδ Γ μ hμ)
          (strongContinuous_hullKoopmanUnitary hδ Γ μ hμ) Ω hΩ hfin t hR f) := by
  simp_rw [integral_stationary_pairing_Lp hδ Γ μ hμ]
  have hc : Continuous (fun y => domainKernel Ω y *
      (Real.fourierChar (inner (𝕜 := ℝ) t y) : ℂ) *
      inner (𝕜 := ℂ) g (hullKoopmanUnitary hδ Γ μ hμ y f)) :=
    (((continuous_domainKernel Ω hΩ hfin).mul
      ((continuous_subtype_val.comp Real.continuous_fourierChar).comp
        (continuous_const.inner continuous_id))).mul
      (continuous_const.inner (strongContinuous_hullKoopmanUnitary hδ Γ μ hμ f)))
  rw [normalized_integral_box_difference hR hc, inner_finiteFilter]
  apply integral_congr_ae
  filter_upwards [] with y
  simp only [finiteFilterKernel]
  ring
end SeparatedConfiguration
end RieszEuclidean
