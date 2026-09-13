import RieszEuclidean.Basic
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-! General L² pullback and unit-phase reindexing. -/
noncomputable section
open MeasureTheory MeasureTheory.Measure Filter Topology
open scoped ENNReal
namespace RieszEuclidean

section Pullback
variable {α β : Type} [MeasurableSpace α] [MeasurableSpace β]
  {μ : Measure α} {ν : Measure β} {c : ℝ≥0∞}
  (f : α → β) (hf : Measurable f) (hmap : Measure.map f μ = c • ν) (hc : c ≠ ∞)

/-- The a.e. pullback of an L² function under a map with finite constant Jacobian. -/
def scaledL2PullbackValue (g : Lp ℂ 2 ν) : Lp ℂ 2 μ :=
  (((Lp.memLp g).smul_measure hc).comp_measurePreserving ⟨hf, hmap⟩).toLp (g ∘ f)

theorem scaledL2PullbackValue_ae (g : Lp ℂ 2 ν) :
    (scaledL2PullbackValue f hf hmap hc g : α → ℂ) =ᵐ[μ] g ∘ f :=
  MemLp.coeFn_toLp _

theorem scaledL2PullbackValue_norm (g : Lp ℂ 2 ν) :
    ‖scaledL2PullbackValue f hf hmap hc g‖ = (c ^ (1 / (2 : ℝ≥0∞)).toReal).toReal * ‖g‖ := by
  rw [scaledL2PullbackValue, Lp.norm_toLp,
    eLpNorm_comp_measurePreserving ((Lp.memLp g).smul_measure hc).1 ⟨hf, hmap⟩,
    eLpNorm_smul_measure_of_ne_top (by norm_num : (2 : ℝ≥0∞) ≠ ∞)]
  rw [smul_eq_mul, ENNReal.toReal_mul, Lp.norm_def]

/-- Pullback assembled as a complex linear map on L² equivalence classes. -/
def scaledL2PullbackLinear : Lp ℂ 2 ν →ₗ[ℂ] Lp ℂ 2 μ where
  toFun := scaledL2PullbackValue f hf hmap hc
  map_add' g k := by
    have hq : QuasiMeasurePreserving f μ ν := ⟨hf, by rw [hmap]; exact smul_absolutelyContinuous⟩
    apply Lp.ext
    filter_upwards [scaledL2PullbackValue_ae f hf hmap hc (g + k), scaledL2PullbackValue_ae f hf hmap hc g,
      scaledL2PullbackValue_ae f hf hmap hc k, hq.ae (Lp.coeFn_add g k),
      Lp.coeFn_add (scaledL2PullbackValue f hf hmap hc g) (scaledL2PullbackValue f hf hmap hc k)] with x h1 h2 h3 h4 h5
    simp only [Pi.add_apply, Function.comp_apply] at h1 h2 h3 h4 h5
    exact h1.trans (h4.trans (by rw [h5, h2, h3]))
  map_smul' z g := by
    have hq : QuasiMeasurePreserving f μ ν := ⟨hf, by rw [hmap]; exact smul_absolutelyContinuous⟩
    apply Lp.ext
    filter_upwards [scaledL2PullbackValue_ae f hf hmap hc (z • g), scaledL2PullbackValue_ae f hf hmap hc g,
      hq.ae (Lp.coeFn_smul z g), Lp.coeFn_smul z (scaledL2PullbackValue f hf hmap hc g)] with x h1 h2 h3 h4
    change _ = (z • scaledL2PullbackValue f hf hmap hc g) x
    simp only [Pi.smul_apply, Function.comp_apply] at h1 h2 h3 h4
    exact h1.trans (h3.trans (by rw [h4, h2]))

/-- Pullback along a measurable map with a finite constant measure Jacobian. -/
def scaledL2Pullback : Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 μ :=
  (scaledL2PullbackLinear f hf hmap hc).mkContinuous (c ^ (1 / (2 : ℝ≥0∞)).toReal).toReal
    (fun g => (scaledL2PullbackValue_norm f hf hmap hc g).le)

theorem scaledL2Pullback_ae (g : Lp ℂ 2 ν) :
    (scaledL2Pullback f hf hmap hc g : α → ℂ) =ᵐ[μ] g ∘ f :=
  scaledL2PullbackValue_ae f hf hmap hc g

end Pullback

section Equiv
variable {α β : Type} [MeasurableSpace α] [MeasurableSpace β]
  {μ : Measure α} {ν : Measure β} {c : ℝ≥0∞}
  (e : α ≃ᵐ β) (hmap : Measure.map e μ = c • ν) (hc0 : c ≠ 0) (hc : c ≠ ∞)

include hmap hc0 hc in
theorem scaledL2Equiv_inverse_map : Measure.map e.symm ν = c⁻¹ • μ := by
  have h := e.map_symm_map (μ := μ)
  rw [hmap, Measure.map_smul] at h
  rw [← h, smul_smul, ENNReal.inv_mul_cancel hc0 hc, one_smul]

/-- A measurable equivalence with nonzero finite constant Jacobian induces an L² equivalence. -/
def scaledL2Equiv : Lp ℂ 2 ν ≃L[ℂ] Lp ℂ 2 μ := by
  let p := scaledL2Pullback e e.measurable hmap hc
  let q := scaledL2Pullback e.symm e.symm.measurable (scaledL2Equiv_inverse_map e hmap hc0 hc)
    (ENNReal.inv_ne_top.mpr hc0)
  have hp (g : Lp ℂ 2 ν) : (p g : α → ℂ) =ᵐ[μ] g ∘ e :=
    scaledL2Pullback_ae _ _ _ _ g
  have hq (g : Lp ℂ 2 μ) : (q g : β → ℂ) =ᵐ[ν] g ∘ e.symm :=
    scaledL2Pullback_ae _ _ _ _ g
  have hep : QuasiMeasurePreserving e μ ν :=
    ⟨e.measurable, by rw [hmap]; exact smul_absolutelyContinuous⟩
  have heq : QuasiMeasurePreserving e.symm ν μ :=
    ⟨e.symm.measurable, by rw [scaledL2Equiv_inverse_map e hmap hc0 hc]; exact smul_absolutelyContinuous⟩
  exact
    { toLinearEquiv :=
        { p.toLinearMap with
          invFun := q
          left_inv := fun g => Lp.ext (by
            filter_upwards [hq (p g), heq.ae (hp g)] with x hx hy
            simpa only [Function.comp_apply, e.apply_symm_apply] using hx.trans hy)
          right_inv := fun g => Lp.ext (by
            filter_upwards [hp (q g), hep.ae (hq g)] with x hx hy
            simpa only [Function.comp_apply, e.symm_apply_apply] using hx.trans hy) }
      continuous_toFun := p.continuous
      continuous_invFun := q.continuous }

theorem scaledL2Equiv_ae (g : Lp ℂ 2 ν) :
    (scaledL2Equiv e hmap hc0 hc g : α → ℂ) =ᵐ[μ] g ∘ e :=
  scaledL2Pullback_ae _ _ _ _ g

end Equiv

section Sequences
variable {ι κ : Type} (e : ι ≃ κ) (w : ι → ℂ) (hw : ∀ i, ‖w i‖ = 1)

/-- Reindex a square-summable family and multiply its coordinates by unit phases. -/
def weightedReindexValue (g : SeqL2 κ) : SeqL2 ι :=
  ⟨fun i => w i * g (e i), memℓp_gen (by
    simpa only [norm_mul, hw, one_mul] using
      e.summable_iff.mpr ((lp.memℓp g).summable (by norm_num)))⟩

/-- Reindexing and unit-modulus phases preserve the coefficient Hilbert norm. -/
def weightedReindex : SeqL2 κ ≃ₗᵢ[ℂ] SeqL2 ι where
  toFun := weightedReindexValue e w hw
  invFun := weightedReindexValue e.symm (fun k => (w (e.symm k))⁻¹) (by simp [hw])
  map_add' g k := by ext i; exact mul_add _ _ _
  map_smul' z g := by ext i; exact mul_left_comm _ _ _
  left_inv g := by
    ext k
    change (w (e.symm k))⁻¹ * (w (e.symm k) * g (e (e.symm k))) = g k
    rw [e.apply_symm_apply, ← mul_assoc, inv_mul_cancel₀, one_mul]
    exact norm_ne_zero_iff.mp (by rw [hw]; norm_num)
  right_inv g := by
    ext i
    change w i * ((w (e.symm (e i)))⁻¹ * g (e.symm (e i))) = g i
    rw [e.symm_apply_apply, ← mul_assoc, mul_inv_cancel₀, one_mul]
    exact norm_ne_zero_iff.mp (by rw [hw]; norm_num)
  norm_map' g := by
    rw [lp.norm_eq_tsum_rpow (by norm_num), lp.norm_eq_tsum_rpow (by norm_num)]
    congr 1
    change (∑' i, ‖w i * g (e i)‖ ^ (2 : ℝ≥0∞).toReal) = _
    simp only [norm_mul, hw, one_mul]
    exact e.tsum_eq (fun k => ‖g k‖ ^ (2 : ℝ≥0∞).toReal)

theorem weightedReindex_apply (g : SeqL2 κ) (i : ι) :
    weightedReindex e w hw g i = w i * g (e i) := rfl

theorem weightedReindex_single [DecidableEq ι] [DecidableEq κ] (i : ι) :
    weightedReindex e w hw (lp.single 2 (e i) 1) = w i • lp.single 2 i 1 := by
  classical
  ext j
  simp only [weightedReindex_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
  by_cases h : j = i
  · subst j; simp
  · simp [lp.single_apply, h, e.injective.ne h]

end Sequences


end RieszEuclidean
