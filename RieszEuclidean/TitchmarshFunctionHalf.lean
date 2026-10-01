import RieszEuclidean.TitchmarshLaplace
import RieszEuclidean.TitchmarshLaplaceIntegral
import RieszEuclidean.TitchmarshFourierDetection
import RieszEuclidean.TitchmarshFourierProduct

/-! The analytic half lemma: a square bound forbids a low support component. -/

noncomputable section
open MeasureTheory Filter Topology
open scoped Convolution

namespace RieszEuclidean.CompleteMinimal

/-- A uniform bound on each Fourier-twisted Laplace square forces the function
to vanish below the corresponding supporting hyperplane. -/
theorem vanishes_below_of_laplace_square_bound {d : ℕ}
    {f : Euclidean d → ℂ} (hf : Continuous f) (hc : HasCompactSupport f)
    (ℓ : Euclidean d →L[ℝ] ℝ) (T : ℝ)
    (hsquare : ∀ ξ : Euclidean d, ∃ C : ℝ, 0 ≤ C ∧
      ∀ z : ℂ, 0 ≤ z.re →
        ‖titchmarshLaplaceIntegral
          (fun x => f x * complexFourierKernel x (realToComplex ξ)) ℓ T z‖ ^ 2 ≤ C ^ 2) :
    ∀ x, ℓ x < T → f x = 0 := by
  let U : Set (Euclidean d) := {x | ℓ x < T}
  have hU : MeasurableSet U := (isOpen_lt ℓ.continuous continuous_const).measurableSet
  obtain ⟨R, hR, hbound⟩ := hc.isBounded.exists_pos_norm_le
  have hfs : ∀ᵐ x, f x ≠ 0 → ‖x‖ ≤ R := Eventually.of_forall
    (fun x hx => hbound x (subset_tsupport f hx))
  have hfi : Integrable f := hf.integrable_of_hasCompactSupport hc
  have hlow₂ : MemLp (U.indicator f) 2 volume :=
    (hf.memLp_of_hasCompactSupport (p := 2) hc).indicator hU
  have hlowi : Integrable (U.indicator f) := hfi.indicator hU
  have hFourier : ∀ ξ, Real.fourierIntegral (U.indicator f) ξ = 0 := by
    intro ξ
    let p : Euclidean d → ℂ := fun x =>
      f x * complexFourierKernel x (realToComplex ξ)
    let g : Euclidean d → ℂ := U.indicator p
    let h : Euclidean d → ℂ := Uᶜ.indicator p
    have hpi : Integrable p := entireFourier_integrable hfi hfs (realToComplex ξ)
    have hgi : Integrable g := hpi.indicator hU
    have hhi : Integrable h := hpi.indicator hU.compl
    have hgs : ∀ᵐ x, g x ≠ 0 → ‖x‖ ≤ R := by
      filter_upwards [hfs] with x hx hgx
      apply hx
      intro hfx
      exact hgx (by simp [g, p, hfx])
    have hhs : ∀ᵐ x, h x ≠ 0 → ‖x‖ ≤ R := by
      filter_upwards [hfs] with x hx hhx
      apply hx
      intro hfx
      exact hhx (by simp [h, p, hfx])
    have hstrict : ∀ᵐ x, g x ≠ 0 → ℓ x < T := Eventually.of_forall (by
      intro x hx
      by_contra hn
      exact hx (Set.indicator_of_not_mem (show x ∉ U from hn) p))
    have hhigh : ∀ᵐ x, h x ≠ 0 → T ≤ ℓ x := Eventually.of_forall (by
      intro x hx
      by_cases hxU : x ∈ U
      · exact False.elim (hx (Set.indicator_of_not_mem
          (Set.not_mem_compl_iff.mpr hxU) p))
      · exact le_of_not_gt hxU)
    let F := titchmarshLaplaceIntegral p ℓ T
    let G := titchmarshLaplaceIntegral g ℓ T
    let H := titchmarshLaplaceIntegral h ℓ T
    have hdecomp : ∀ z, F z = G z + H z := by
      intro z
      change (∫ x, p x * Complex.exp (z * ↑(T - ℓ x))) =
        (∫ x, g x * Complex.exp (z * ↑(T - ℓ x))) +
          ∫ x, h x * Complex.exp (z * ↑(T - ℓ x))
      rw [← integral_add
        (titchmarshLaplaceIntegral_integrable hgi ℓ T hgs z)
        (titchmarshLaplaceIntegral_integrable hhi ℓ T hhs z)]
      apply integral_congr_ae
      filter_upwards with x
      by_cases hx : x ∈ U <;> simp [g, h, hx]
    obtain ⟨C, hC, hsq⟩ := hsquare ξ
    have hGzero : G = 0 := laplace_low_part_eq_zero F G H
      (titchmarshLaplaceIntegral_differentiable hgi ℓ T hR.le hgs)
      hdecomp hC hsq
      (fun z hz => titchmarshLaplaceIntegral_norm_le hhi ℓ T z (Or.inl ⟨hz, hhigh⟩))
      (fun z hz => titchmarshLaplaceIntegral_norm_le hgi ℓ T z
        (Or.inr ⟨hz, hstrict.mono fun _ hx hn => (hx hn).le⟩))
      (titchmarshLaplaceIntegral_tendsto_neg_real hgi ℓ T hstrict)
    have hG0 := congrFun hGzero 0
    change titchmarshLaplaceIntegral g ℓ T 0 = 0 at hG0
    simp only [titchmarshLaplaceIntegral, zero_mul, Complex.exp_zero, mul_one] at hG0
    rw [← entireFourier_realToComplex, entireFourier]
    convert hG0 using 1
    apply integral_congr_ae
    filter_upwards with x
    by_cases hx : x ∈ U <;> simp [g, p, hx]
  exact eq_zero_on_halfspace_of_indicator_ae_eq_zero hf ℓ T
    (ae_eq_zero_of_fourierIntegral_eq_zero hlowi hlow₂ hFourier)

/-- The actual Laplace square is the Laplace transform of self-convolution. -/
theorem titchmarshLaplaceIntegral_twisted_self_convolution {d : ℕ}
    {f : Euclidean d → ℂ} (hf : Integrable f)
    {R : ℝ} (hs : ∀ᵐ x, f x ≠ 0 → ‖x‖ ≤ R)
    (v ξ : Euclidean d) (T : ℝ) (z : ℂ) :
    titchmarshLaplaceIntegral
      (fun x => f x * complexFourierKernel x (realToComplex ξ))
      (innerSL ℝ v) T z ^ 2 =
    titchmarshLaplaceIntegral
      (fun x => (f ⋆[ContinuousLinearMap.mul ℂ ℂ, volume] f) x *
        complexFourierKernel x (realToComplex ξ)) (innerSL ℝ v) (2 * T) z := by
  have hshift (g : Euclidean d → ℂ) (S : ℝ) :
      titchmarshLaplaceIntegral
        (fun x => g x * complexFourierKernel x (realToComplex ξ))
        (innerSL ℝ v) S z =
      Complex.exp (z * (S : ℂ)) * entireFourier g
        (realToComplex ξ + (-(z * Complex.I) / (2 * Real.pi)) • realToComplex v) := by
    unfold titchmarshLaplaceIntegral
    convert integral_directionalLaplace_eq_entireFourier_shift g v ξ S z using 1
    apply integral_congr_ae
    filter_upwards with x
    change g x * complexFourierKernel x (realToComplex ξ) *
      Complex.exp (z * ↑(S - inner (𝕜 := ℝ) v x)) = _
    ring
  rw [hshift, hshift, entireFourier_convolution hf hf hs hs]
  have hexp : Complex.exp (z * ((2 * T : ℝ) : ℂ)) =
      Complex.exp (z * (T : ℂ)) ^ 2 := by
    rw [pow_two, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [hexp]
  ring

/-- If self-convolution vanishes below level `2*T`, the original continuous
compactly supported function vanishes below level `T`. -/
theorem self_convolution_halfspace {d : ℕ}
    {f : Euclidean d → ℂ} (hf : Continuous f) (hc : HasCompactSupport f)
    (v : Euclidean d) (T : ℝ)
    (hw : ∀ x, inner (𝕜 := ℝ) v x < 2 * T →
      (f ⋆[ContinuousLinearMap.mul ℂ ℂ, volume] f) x = 0) :
    ∀ x, inner (𝕜 := ℝ) v x < T → f x = 0 := by
  have hfi : Integrable f := hf.integrable_of_hasCompactSupport hc
  obtain ⟨R, _, hbound⟩ := hc.isBounded.exists_pos_norm_le
  have hfs : ∀ᵐ x, f x ≠ 0 → ‖x‖ ≤ R := Eventually.of_forall
    (fun x hx => hbound x (subset_tsupport f hx))
  let w := f ⋆[ContinuousLinearMap.mul ℂ ℂ, volume] f
  have hwi : Integrable w := hfi.integrable_convolution (L := ContinuousLinearMap.mul ℂ ℂ) hfi
  apply vanishes_below_of_laplace_square_bound hf hc (innerSL ℝ v) T
  intro ξ
  let p : Euclidean d → ℂ := fun x => w x * complexFourierKernel x (realToComplex ξ)
  have hp : Integrable p := by
    apply hwi.norm.mono'
    · exact hwi.aestronglyMeasurable.mul
        (complexFourierKernel_continuous_left (realToComplex ξ)).aestronglyMeasurable
    · filter_upwards with x
      simp [p, norm_mul, complexFourierKernel_real_norm]
  have hps : ∀ᵐ x, p x ≠ 0 → 2 * T ≤ (innerSL ℝ v) x := by
    filter_upwards with x hx
    by_contra hn
    have hlow : inner (𝕜 := ℝ) v x < 2 * T := lt_of_not_ge hn
    exact hx (by simp [p, w, hw x hlow])
  let A : ℝ := ∫ x, ‖p x‖
  have hA : 0 ≤ A := integral_nonneg fun _ => norm_nonneg _
  refine ⟨A + 1, by positivity, ?_⟩
  intro z hz
  rw [← norm_pow, titchmarshLaplaceIntegral_twisted_self_convolution hfi hfs]
  have hb := titchmarshLaplaceIntegral_norm_le hp (innerSL ℝ v) (2 * T) z
    (Or.inl ⟨hz, hps⟩)
  change ‖titchmarshLaplaceIntegral p (innerSL ℝ v) (2 * T) z‖ ≤ (A + 1) ^ 2
  exact hb.trans (by nlinarith [sq_nonneg A])

/-- The half lemma for an arbitrary continuous real linear coordinate. -/
theorem self_convolution_halfspace_linear {d : ℕ}
    {f : Euclidean d → ℂ} (hf : Continuous f) (hc : HasCompactSupport f)
    (ℓ : Euclidean d →L[ℝ] ℝ) (T : ℝ)
    (hw : ∀ x, ℓ x < 2 * T →
      (f ⋆[ContinuousLinearMap.mul ℂ ℂ, volume] f) x = 0) :
    ∀ x, ℓ x < T → f x = 0 := by
  let v : Euclidean d := (InnerProductSpace.toDual ℝ (Euclidean d)).symm ℓ
  have hrepr : ℓ = innerSL ℝ v := by
    ext x
    simp only [innerSL_apply]
    exact (InnerProductSpace.toDual_symm_apply (x := x) (y := ℓ)).symm
  rw [hrepr] at hw ⊢
  exact self_convolution_halfspace hf hc v T hw

end RieszEuclidean.CompleteMinimal
