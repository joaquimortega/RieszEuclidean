import RieszEuclidean.BumpKernel
import RieszEuclidean.Koopman
import RieszEuclidean.L2Multiplier
noncomputable section
open MeasureTheory
namespace RieszEuclidean
/-- The stationary coefficient of the concrete covariant bump kernel. -/
def stationaryKernel {d : ℕ} {δ : ℝ} (b : Euclidean d → ℂ)
    (y : Euclidean d) (Δ : SeparatedConfiguration d δ) : ℂ :=
  bumpKernel Δ.carrier b 0 (-y)

/-- Stationary coefficients inherit the uniform squared bump bound. -/
theorem norm_stationaryKernel_le {d : ℕ} {δ r M : ℝ} (hr : 2 * r ≤ δ)
    (b : Euclidean d → ℂ) (hs : ∀ x, r ≤ ‖x‖ → b x = 0)
    (hM : 0 ≤ M) (hb : ∀ x, ‖b x‖ ≤ M)
    (y : Euclidean d) (Δ : SeparatedConfiguration d δ) :
    ‖stationaryKernel b y Δ‖ ≤ M ^ 2 :=
  norm_bumpKernel_le Δ.separated hr b hs hM hb 0 (-y)

/-- Stationary coefficients vanish outside twice the bump radius. -/
theorem stationaryKernel_eq_zero {d : ℕ} {δ r : ℝ}
    (b : Euclidean d → ℂ) (hs : ∀ x, r ≤ ‖x‖ → b x = 0)
    {y : Euclidean d} (hy : 2 * r < ‖y‖) (Δ : SeparatedConfiguration d δ) :
    stationaryKernel b y Δ = 0 := by
  apply bumpKernel_eq_zero_of_two_mul_lt Δ.carrier b hs
  simpa using hy

/-- The coefficients transform with the same sign as the paper's Koopman action. -/
theorem stationaryKernel_translate {d : ℕ} {δ : ℝ}
    (b : Euclidean d → ℂ) (y z : Euclidean d) (Δ : SeparatedConfiguration d δ) :
    stationaryKernel b y (SeparatedConfiguration.translate (-z) Δ) =
      bumpKernel Δ.carrier b (-z) (-y - z) := by
  change bumpKernel (translate (-z) Δ.carrier) b 0 (-y) = _
  rw [bumpKernel_translate]
  simp [sub_eq_add_neg]

/-- Hermitian symmetry identifies the coefficient needed for the adjoint. -/
theorem stationaryKernel_adjoint_coefficient {d : ℕ} {δ : ℝ}
    (b : Euclidean d → ℂ) (y : Euclidean d) (Δ : SeparatedConfiguration d δ) :
    stationaryKernel b (-y) (SeparatedConfiguration.translate (-y) Δ) =
      star (stationaryKernel b y Δ) := by
  rw [stationaryKernel_translate]
  simpa [stationaryKernel] using bumpKernel_hermitian Δ.carrier b 0 (-y)

namespace SeparatedConfiguration
/-- Multiplication by the actual stationary coefficient on the hull L² space. -/
def stationaryMultiplier {d : ℕ} {δ r M : ℝ}
    (Γ : SeparatedConfiguration d δ) [MeasurableSpace (hull Γ)]
    (μ : Measure (hull Γ)) (hr : 2 * r ≤ δ)
    (b : Euclidean d → ℂ) (hs : ∀ x, r ≤ ‖x‖ → b x = 0)
    (hM : 0 ≤ M) (hb : ∀ x, ‖b x‖ ≤ M)
    (y : Euclidean d)
    (hm : AEStronglyMeasurable (fun Δ : hull Γ => stationaryKernel b y Δ.val) μ) :
    Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ :=
  l2MultiplierCLM (fun Δ : hull Γ => stationaryKernel b y Δ.val) hm
    (Filter.Eventually.of_forall fun Δ => norm_stationaryKernel_le hr b hs hM hb y Δ.val)

/-- The multiplier acts by its concrete kernel coefficient almost everywhere. -/
theorem stationaryMultiplier_coe {d : ℕ} {δ r M : ℝ}
    (Γ : SeparatedConfiguration d δ) [MeasurableSpace (hull Γ)]
    (μ : Measure (hull Γ)) (hr : 2 * r ≤ δ)
    (b : Euclidean d → ℂ) (hs : ∀ x, r ≤ ‖x‖ → b x = 0)
    (hM : 0 ≤ M) (hb : ∀ x, ‖b x‖ ≤ M)
    (y : Euclidean d)
    (hm : AEStronglyMeasurable (fun Δ : hull Γ => stationaryKernel b y Δ.val) μ)
    (f : Lp ℂ 2 μ) :
    (stationaryMultiplier Γ μ hr b hs hM hb y hm f : hull Γ → ℂ) =ᵐ[μ]
      fun Δ => stationaryKernel b y Δ.val * f Δ :=
  l2Multiplier_coe _ hm (Filter.Eventually.of_forall fun Δ =>
    norm_stationaryKernel_le hr b hs hM hb y Δ.val) f

/-- The multiplier operator norm is at most the square of the uniform bump bound. -/
theorem norm_stationaryMultiplier_le {d : ℕ} {δ r M : ℝ}
    (Γ : SeparatedConfiguration d δ) [MeasurableSpace (hull Γ)]
    (μ : Measure (hull Γ)) (hr : 2 * r ≤ δ)
    (b : Euclidean d → ℂ) (hs : ∀ x, r ≤ ‖x‖ → b x = 0)
    (hM : 0 ≤ M) (hb : ∀ x, ‖b x‖ ≤ M)
    (y : Euclidean d)
    (hm : AEStronglyMeasurable (fun Δ : hull Γ => stationaryKernel b y Δ.val) μ) :
    ‖stationaryMultiplier Γ μ hr b hs hM hb y hm‖ ≤ M ^ 2 := by
  refine (stationaryMultiplier Γ μ hr b hs hM hb y hm).opNorm_le_bound (sq_nonneg M) ?_
  intro f
  exact l2Multiplier_norm_le _ hm (Filter.Eventually.of_forall fun Δ =>
    norm_stationaryKernel_le hr b hs hM hb y Δ.val) f

/-- The multiplier itself vanishes outside twice the bump radius. -/
theorem stationaryMultiplier_eq_zero {d : ℕ} {δ r M : ℝ}
    (Γ : SeparatedConfiguration d δ) [MeasurableSpace (hull Γ)]
    (μ : Measure (hull Γ)) (hr : 2 * r ≤ δ)
    (b : Euclidean d → ℂ) (hs : ∀ x, r ≤ ‖x‖ → b x = 0)
    (hM : 0 ≤ M) (hb : ∀ x, ‖b x‖ ≤ M)
    (y : Euclidean d)
    (hm : AEStronglyMeasurable (fun Δ : hull Γ => stationaryKernel b y Δ.val) μ)
    (hy : 2 * r < ‖y‖) : stationaryMultiplier Γ μ hr b hs hM hb y hm = 0 := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [stationaryMultiplier_coe Γ μ hr b hs hM hb y hm f,
    Lp.coeFn_zero (E := ℂ) (p := 2) (μ := μ)] with Δ hΔ hz
  simp only [hΔ, stationaryKernel_eq_zero b hs hy, zero_mul, ContinuousLinearMap.zero_apply, hz, Pi.zero_apply]
/-- The concrete operator integrand `B_y U_y` in the stationary comparison operator. -/
def stationaryKernelOperator {d : ℕ} {δ r M : ℝ} (hδ : 0 < δ)
    (Γ : SeparatedConfiguration d δ) [MeasurableSpace (hull Γ)]
    (μ : Measure (hull Γ))
    (hμ : ∀ z : Euclidean d, MeasurePreserving (hullTranslate hδ Γ z) μ μ)
    (hr : 2 * r ≤ δ) (b : Euclidean d → ℂ)
    (hs : ∀ x, r ≤ ‖x‖ → b x = 0) (hM : 0 ≤ M) (hb : ∀ x, ‖b x‖ ≤ M)
    (y : Euclidean d)
    (hm : AEStronglyMeasurable (fun Δ : hull Γ => stationaryKernel b y Δ.val) μ) :
    Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ :=
  (stationaryMultiplier Γ μ hr b hs hM hb y hm).comp
    (hullKoopmanUnitary hδ Γ μ hμ y).toContinuousLinearEquiv.toContinuousLinearMap

/-- The operator integrand has the manuscript's actual shifted representative. -/
theorem stationaryKernelOperator_coe {d : ℕ} {δ r M : ℝ} (hδ : 0 < δ)
    (Γ : SeparatedConfiguration d δ) [MeasurableSpace (hull Γ)]
    (μ : Measure (hull Γ))
    (hμ : ∀ z : Euclidean d, MeasurePreserving (hullTranslate hδ Γ z) μ μ)
    (hr : 2 * r ≤ δ) (b : Euclidean d → ℂ)
    (hs : ∀ x, r ≤ ‖x‖ → b x = 0) (hM : 0 ≤ M) (hb : ∀ x, ‖b x‖ ≤ M)
    (y : Euclidean d)
    (hm : AEStronglyMeasurable (fun Δ : hull Γ => stationaryKernel b y Δ.val) μ)
    (f : Lp ℂ 2 μ) :
    (stationaryKernelOperator hδ Γ μ hμ hr b hs hM hb y hm f : hull Γ → ℂ) =ᵐ[μ]
      fun Δ => stationaryKernel b y Δ.val * f (hullTranslate hδ Γ (-y) Δ) := by
  have he := stationaryMultiplier_coe Γ μ hr b hs hM hb y hm
    (hullKoopmanUnitary hδ Γ μ hμ y f)
  have ht := Lp.coeFn_compMeasurePreserving f (hμ (-y))
  filter_upwards [he, ht] with Δ hΔ htΔ
  exact hΔ.trans (congrArg (fun z => stationaryKernel b y Δ.val * z) htΔ)

/-- The concrete shifted operator retains the uniform squared bump bound. -/
theorem norm_stationaryKernelOperator_le {d : ℕ} {δ r M : ℝ} (hδ : 0 < δ)
    (Γ : SeparatedConfiguration d δ) [MeasurableSpace (hull Γ)]
    (μ : Measure (hull Γ))
    (hμ : ∀ z : Euclidean d, MeasurePreserving (hullTranslate hδ Γ z) μ μ)
    (hr : 2 * r ≤ δ) (b : Euclidean d → ℂ)
    (hs : ∀ x, r ≤ ‖x‖ → b x = 0) (hM : 0 ≤ M) (hb : ∀ x, ‖b x‖ ≤ M)
    (y : Euclidean d)
    (hm : AEStronglyMeasurable (fun Δ : hull Γ => stationaryKernel b y Δ.val) μ) :
    ‖stationaryKernelOperator hδ Γ μ hμ hr b hs hM hb y hm‖ ≤ M ^ 2 := by
  refine (stationaryKernelOperator hδ Γ μ hμ hr b hs hM hb y hm).opNorm_le_bound
    (sq_nonneg M) ?_
  intro f
  have hh := (stationaryMultiplier Γ μ hr b hs hM hb y hm).le_opNorm
    (hullKoopmanUnitary hδ Γ μ hμ y f)
  apply hh.trans
  rw [(hullKoopmanUnitary hδ Γ μ hμ y).norm_map]
  exact mul_le_mul_of_nonneg_right (norm_stationaryMultiplier_le Γ μ hr b hs hM hb y hm)
    (norm_nonneg f)

/-- The shifted operator integrand is supported in the radius `2r` ball. -/
theorem stationaryKernelOperator_eq_zero {d : ℕ} {δ r M : ℝ} (hδ : 0 < δ)
    (Γ : SeparatedConfiguration d δ) [MeasurableSpace (hull Γ)]
    (μ : Measure (hull Γ))
    (hμ : ∀ z : Euclidean d, MeasurePreserving (hullTranslate hδ Γ z) μ μ)
    (hr : 2 * r ≤ δ) (b : Euclidean d → ℂ)
    (hs : ∀ x, r ≤ ‖x‖ → b x = 0) (hM : 0 ≤ M) (hb : ∀ x, ‖b x‖ ≤ M)
    (y : Euclidean d)
    (hm : AEStronglyMeasurable (fun Δ : hull Γ => stationaryKernel b y Δ.val) μ)
    (hy : 2 * r < ‖y‖) :
    stationaryKernelOperator hδ Γ μ hμ hr b hs hM hb y hm = 0 := by
  rw [stationaryKernelOperator, stationaryMultiplier_eq_zero Γ μ hr b hs hM hb y hm hy,
    ContinuousLinearMap.zero_comp]
/-- The concrete stationary operator satisfies the adjoint pairing identity. -/
theorem stationaryKernelOperator_inner {d : ℕ} {δ r M : ℝ} (hδ : 0 < δ)
    (Γ : SeparatedConfiguration d δ) [MeasurableSpace (hull Γ)]
    (μ : Measure (hull Γ))
    (hμ : ∀ z : Euclidean d, MeasurePreserving (hullTranslate hδ Γ z) μ μ)
    (hr : 2 * r ≤ δ) (b : Euclidean d → ℂ)
    (hs : ∀ x, r ≤ ‖x‖ → b x = 0) (hM : 0 ≤ M) (hb : ∀ x, ‖b x‖ ≤ M)
    (y : Euclidean d)
    (hm : AEStronglyMeasurable (fun Δ : hull Γ => stationaryKernel b y Δ.val) μ)
    (hmn : AEStronglyMeasurable (fun Δ : hull Γ => stationaryKernel b (-y) Δ.val) μ)
    (f g : Lp ℂ 2 μ) :
    inner (𝕜 := ℂ) (stationaryKernelOperator hδ Γ μ hμ hr b hs hM hb y hm f) g =
      inner (𝕜 := ℂ) f (stationaryKernelOperator hδ Γ μ hμ hr b hs hM hb (-y) hmn g) := by
  let U := hullKoopmanUnitary hδ Γ μ hμ y
  conv_rhs => rw [← U.inner_map_map]
  have hfg := stationaryKernelOperator_coe hδ Γ μ hμ hr b hs hM hb y hm f
  have hg := stationaryKernelOperator_coe hδ Γ μ hμ hr b hs hM hb (-y) hmn g
  have hUg := Lp.coeFn_compMeasurePreserving
    (stationaryKernelOperator hδ Γ μ hμ hr b hs hM hb (-y) hmn g) (hμ (-y))
  have hUf := Lp.coeFn_compMeasurePreserving f (hμ (-y))
  rw [L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hfg, hUg, hUf, (hμ (-y)).quasiMeasurePreserving.ae hg] with Δ hΔ hUΔ hfΔ hgΔ
  have hc := stationaryKernel_adjoint_coefficient b y Δ.val
  have he : hullTranslate hδ Γ (-(-y)) (hullTranslate hδ Γ (-y) Δ) = Δ := by
    apply Subtype.ext
    change translate (-(-y)) (translate (-y) Δ.val) = Δ.val
    rw [translate_add]
    simp
  change inner (𝕜 := ℂ) _ _ = inner (𝕜 := ℂ) _ _
  change inner (𝕜 := ℂ)
    (stationaryKernelOperator hδ Γ μ hμ hr b hs hM hb y hm f Δ) (g Δ) =
    inner (𝕜 := ℂ) (Lp.compMeasurePreserving (hullTranslate hδ Γ (-y)) (hμ (-y)) f Δ)
      (Lp.compMeasurePreserving (hullTranslate hδ Γ (-y)) (hμ (-y))
        (stationaryKernelOperator hδ Γ μ hμ hr b hs hM hb (-y) hmn g) Δ)
  rw [hΔ, hUΔ, hfΔ]
  simp only [Function.comp_apply]
  rw [hgΔ, he]
  change inner (𝕜 := ℂ) (stationaryKernel b y Δ.val * f (hullTranslate hδ Γ (-y) Δ)) (g Δ) =
    inner (𝕜 := ℂ) (f (hullTranslate hδ Γ (-y) Δ))
      (stationaryKernel b (-y) (translate (-y) Δ.val) * g Δ)
  rw [hc]
  simp only [RCLike.inner_apply, map_mul, mul_assoc, starRingEnd_apply]
  ring
/-- Invariance and covariance give the actual shifted-operator adjoint identity. -/
theorem stationaryKernelOperator_adjoint {d : ℕ} {δ r M : ℝ} (hδ : 0 < δ)
    (Γ : SeparatedConfiguration d δ) [MeasurableSpace (hull Γ)]
    (μ : Measure (hull Γ))
    (hμ : ∀ z : Euclidean d, MeasurePreserving (hullTranslate hδ Γ z) μ μ)
    (hr : 2 * r ≤ δ) (b : Euclidean d → ℂ)
    (hs : ∀ x, r ≤ ‖x‖ → b x = 0) (hM : 0 ≤ M) (hb : ∀ x, ‖b x‖ ≤ M)
    (y : Euclidean d)
    (hm : AEStronglyMeasurable (fun Δ : hull Γ => stationaryKernel b y Δ.val) μ)
    (hmn : AEStronglyMeasurable (fun Δ : hull Γ => stationaryKernel b (-y) Δ.val) μ) :
    (stationaryKernelOperator hδ Γ μ hμ hr b hs hM hb y hm).adjoint =
      stationaryKernelOperator hδ Γ μ hμ hr b hs hM hb (-y) hmn := by
  apply ContinuousLinearMap.ext
  intro g
  apply ext_inner_left ℂ
  intro f
  rw [ContinuousLinearMap.adjoint_inner_right]
  exact stationaryKernelOperator_inner hδ Γ μ hμ hr b hs hM hb y hm hmn f g
end SeparatedConfiguration
end RieszEuclidean
