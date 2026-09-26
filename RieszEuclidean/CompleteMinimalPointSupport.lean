import RieszEuclidean.CompleteMinimalDistributions
import RieszEuclidean.CompleteMinimalSchwartzDensity
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Multilinear.Basis

/-!
# Finite order and localization for point-supported distributions

The results here use actual continuous functionals on Schwartz space. They
derive finite seminorm bounds from continuity and localize compact tests using
smooth cutoffs. The point-support classification is not assumed.
-/

noncomputable section

open SchwartzMap Filter Topology
open scoped SchwartzMap ContDiff

namespace RieszEuclidean.CompleteMinimal

variable {d : ℕ}

/-- Every tempered distribution is controlled by finitely many Schwartz seminorms. -/
theorem distribution_finite_seminorm_bound (u : TemperedDistribution d) :
    ∃ s : Finset (ℕ × ℕ), ∃ C : ℝ, 0 < C ∧
      ∀ φ : 𝓢(Euclidean d, ℂ),
        ‖u φ‖ ≤ C * s.sup (schwartzSeminormFamily ℂ (Euclidean d) ℂ) φ := by
  let q : Seminorm ℂ 𝓢(Euclidean d, ℂ) := (normSeminorm ℂ ℂ).comp u.toLinearMap
  have hq : Continuous q := continuous_norm.comp u.continuous
  obtain ⟨s, C, hC, hbound⟩ := Seminorm.bound_of_continuous
    (schwartz_withSeminorms ℂ (Euclidean d) ℂ) q hq
  refine ⟨s, C, NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hC), ?_⟩
  intro φ
  exact hbound φ

/-- The finite family in the continuity bound can be replaced by a square of
derivative and polynomial-weight indices. -/
theorem distribution_finite_order_bound (u : TemperedDistribution d) :
    ∃ N : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ φ : 𝓢(Euclidean d, ℂ),
        ‖u φ‖ ≤ C * (Finset.Iic (N, N)).sup
          (schwartzSeminormFamily ℂ (Euclidean d) ℂ) φ := by
  obtain ⟨s, C, hC, hbound⟩ := distribution_finite_seminorm_bound u
  let N := s.sup (fun i => max i.1 i.2)
  have hsub : s ⊆ Finset.Iic (N, N) := by
    intro i hi
    have hh : max i.1 i.2 ≤ N := by
      change max i.1 i.2 ≤ s.sup (fun i => max i.1 i.2)
      exact Finset.le_sup (f := fun i : ℕ × ℕ => max i.1 i.2) hi
    exact Finset.mem_Iic.mpr ⟨(le_max_left _ _).trans hh, (le_max_right _ _).trans hh⟩
  refine ⟨N, C, hC, fun φ => (hbound φ).trans ?_⟩
  apply mul_le_mul_of_nonneg_left _ hC.le
  have hp : s.sup (schwartzSeminormFamily ℂ (Euclidean d) ℂ) ≤
      (Finset.Iic (N, N)).sup (schwartzSeminormFamily ℂ (Euclidean d) ℂ) :=
    Finset.sup_mono hsub
  exact hp φ

/-- On tests supported in the unit ball, polynomial weights do not increase
the derivative seminorms. -/
theorem seminorm_le_unweighted_of_unit_support (φ : 𝓢(Euclidean d, ℂ))
    (hs : tsupport (φ : Euclidean d → ℂ) ⊆ Metric.closedBall 0 1) (k n : ℕ) :
    SchwartzMap.seminorm ℂ k n φ ≤ SchwartzMap.seminorm ℂ 0 n φ := by
  apply SchwartzMap.seminorm_le_bound ℂ k n φ (apply_nonneg _ _)
  intro x
  by_cases hx : x ∈ Metric.closedBall (0 : Euclidean d) 1
  · have hnorm : ‖x‖ ≤ 1 := by simpa only [Metric.mem_closedBall, dist_zero_right] using hx
    have hpow : ‖x‖ ^ k ≤ 1 := pow_le_one₀ (norm_nonneg x) hnorm
    calc
      ‖x‖ ^ k * ‖iteratedFDeriv ℝ n φ x‖ ≤ 1 * ‖iteratedFDeriv ℝ n φ x‖ :=
        mul_le_mul_of_nonneg_right hpow (norm_nonneg _)
      _ ≤ SchwartzMap.seminorm ℂ 0 n φ := by
        simpa only [one_mul] using SchwartzMap.norm_iteratedFDeriv_le_seminorm ℂ φ n x
  · have hz : iteratedFDeriv ℝ n φ x = 0 :=
      image_eq_zero_of_nmem_tsupport
        (fun h => hx (hs (tsupport_iteratedFDeriv_subset n h)))
    simp only [hz, norm_zero, mul_zero]
    exact apply_nonneg _ _

/-- A genuine finite-order estimate on a fixed compact neighborhood, with
only derivative seminorms up to `N` and no polynomial weights. -/
theorem distribution_local_finite_order_bound (u : TemperedDistribution d) :
    ∃ N : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ φ : 𝓢(Euclidean d, ℂ),
        tsupport (φ : Euclidean d → ℂ) ⊆ Metric.closedBall 0 1 →
        ‖u φ‖ ≤ C * (Finset.range (N + 1)).sup
          (fun n => SchwartzMap.seminorm ℂ 0 n) φ := by
  obtain ⟨N, C, hC, hbound⟩ := distribution_finite_order_bound u
  refine ⟨N, C, hC, ?_⟩
  intro φ hs
  apply (hbound φ).trans
  apply mul_le_mul_of_nonneg_left _ hC.le
  apply Seminorm.finset_sup_apply_le (apply_nonneg _ _)
  intro i hi
  have hn : i.2 ≤ N := (Finset.mem_Iic.mp hi).2
  exact (seminorm_le_unweighted_of_unit_support φ hs i.1 i.2).trans
    (Seminorm.le_finset_sup_apply (Finset.mem_range.mpr (by omega)))

/-- Multivariable Taylor flatness, derived by repeatedly applying the convex
mean-value estimate: if the jet through `n + m` vanishes, the `n`th derivative
is little-o of the `m`th power of the distance to the origin. -/
theorem flat_jet_iteratedFDeriv_isLittleO (φ : 𝓢(Euclidean d, ℂ)) (n m : ℕ)
    (hzero : ∀ j ≤ n + m, iteratedFDeriv ℝ j φ 0 = 0) :
    (iteratedFDeriv ℝ n φ) =o[𝓝 (0 : Euclidean d)] (fun x => ‖x‖ ^ m) := by
  induction m generalizing n with
  | zero =>
      have hc : Continuous (iteratedFDeriv ℝ n (φ : Euclidean d → ℂ)) :=
        φ.smooth'.continuous_iteratedFDeriv
          (by exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤))
      have ht := hc.tendsto 0
      have hz := hzero n (by omega)
      rw [hz] at ht
      simpa only [pow_zero] using ((Asymptotics.isLittleO_one_iff ℝ).mpr ht)
  | succ m ih =>
      have hnext : (iteratedFDeriv ℝ (n + 1) φ) =o[𝓝 (0 : Euclidean d)]
          (fun x => ‖x‖ ^ m) := ih (n + 1) (fun j hj => hzero j (by omega))
      have hderiv : (fderiv ℝ (iteratedFDeriv ℝ n φ)) =o[𝓝 (0 : Euclidean d)]
          (fun x => ‖x‖ ^ m) := by
        rw [Asymptotics.isLittleO_iff] at hnext ⊢
        simpa only [norm_fderiv_iteratedFDeriv] using hnext
      have hsmooth : ContDiff ℝ 1 (iteratedFDeriv ℝ n φ) :=
        φ.smooth'.iteratedFDeriv_right
          (by exact_mod_cast (le_top : ((1 + n : ℕ) : ℕ∞) ≤ ⊤))
      have hh := (convex_univ : Convex ℝ (Set.univ : Set (Euclidean d))).isLittleO_pow_succ
        (x₀ := (0 : Euclidean d)) (Set.mem_univ _) (n := m)
        (fun x _ => (hsmooth.differentiable le_rfl).differentiableAt.hasFDerivAt.hasFDerivWithinAt)
        (by simpa only [nhdsWithin_univ, sub_zero] using hderiv)
      simpa only [nhdsWithin_univ, hzero n (by omega), sub_zero] using hh

/-- Compactly supported tests that agree near the support point give the same
distribution value. -/
theorem DistributionSupportedIn.compact_locality {u : TemperedDistribution d}
    (hu : DistributionSupportedIn u {(0 : Euclidean d)})
    (φ ψ : 𝓢(Euclidean d, ℂ))
    (hφ : HasCompactSupport (φ : Euclidean d → ℂ))
    (hψ : HasCompactSupport (ψ : Euclidean d → ℂ))
    (heq : (φ : Euclidean d → ℂ) =ᶠ[𝓝 0] ψ) : u φ = u ψ := by
  have hzero : (φ - ψ : 𝓢(Euclidean d, ℂ)) =ᶠ[𝓝 0] (0 : Euclidean d → ℂ) := by
    filter_upwards [heq] with x hx
    change φ x - ψ x = 0
    exact sub_eq_zero.mpr hx
  have hnot : (0 : Euclidean d) ∉ tsupport (φ - ψ : Euclidean d → ℂ) :=
    not_mem_tsupport_iff_eventuallyEq.mpr hzero
  have hdisj : Disjoint (tsupport (φ - ψ : Euclidean d → ℂ)) {(0 : Euclidean d)} :=
    Set.disjoint_singleton_right.mpr hnot
  have hc : HasCompactSupport (φ - ψ : Euclidean d → ℂ) := by
    change HasCompactSupport (fun x => φ x - ψ x)
    simpa only [sub_eq_add_neg] using
      hφ.add (hψ.comp_left (neg_zero : -(0 : ℂ) = 0))
  have hz := hu (φ - ψ) hc hdisj
  exact sub_eq_zero.mp ((map_sub u φ ψ).symm.trans hz)

/-- An actual compactly supported smooth localization of a Schwartz test. -/
def pointCutoffTest (b : ContDiffBump (0 : Euclidean d))
    (φ : 𝓢(Euclidean d, ℂ)) : 𝓢(Euclidean d, ℂ) :=
  compactSchwartz (fun x => (b x : ℂ) * φ x)
    ((Complex.ofRealCLM.contDiff.comp b.contDiff).mul φ.smooth')
    ((b.hasCompactSupport.comp_left Complex.ofReal_zero).mul_right)

@[simp] theorem pointCutoffTest_apply (b : ContDiffBump (0 : Euclidean d))
    (φ : 𝓢(Euclidean d, ℂ)) (x : Euclidean d) :
    pointCutoffTest b φ x = (b x : ℂ) * φ x := rfl

theorem pointCutoffTest_hasCompactSupport (b : ContDiffBump (0 : Euclidean d))
    (φ : 𝓢(Euclidean d, ℂ)) : HasCompactSupport (pointCutoffTest b φ : Euclidean d → ℂ) :=
  (b.hasCompactSupport.comp_left Complex.ofReal_zero).mul_right

/-- Cutoff multiplication does not change the germ at the support point. -/
theorem pointCutoffTest_eventuallyEq (b : ContDiffBump (0 : Euclidean d))
    (φ : 𝓢(Euclidean d, ℂ)) :
    (pointCutoffTest b φ : Euclidean d → ℂ) =ᶠ[𝓝 0] φ := by
  filter_upwards [b.eventuallyEq_one] with x hx
  simp only [pointCutoffTest_apply, hx, Pi.one_apply, Complex.ofReal_one, one_mul]

/-- Every derivative jet at the origin is preserved by localization. -/
theorem pointCutoffTest_iteratedFDeriv_zero (b : ContDiffBump (0 : Euclidean d))
    (φ : 𝓢(Euclidean d, ℂ)) (n : ℕ) :
    iteratedFDeriv ℝ n (pointCutoffTest b φ) 0 = iteratedFDeriv ℝ n φ 0 := by
  have heq := pointCutoffTest_eventuallyEq b φ
  have hw : (pointCutoffTest b φ : Euclidean d → ℂ) =ᶠ[𝓝[Set.univ] 0] φ := by
    simpa only [nhdsWithin_univ] using heq
  simpa only [iteratedFDerivWithin_univ] using
    hw.iteratedFDerivWithin_eq (𝕜 := ℝ) heq.eq_of_nhds n

theorem pointCutoffTest_tsupport_subset (b : ContDiffBump (0 : Euclidean d))
    (φ : 𝓢(Euclidean d, ℂ)) :
    tsupport (pointCutoffTest b φ : Euclidean d → ℂ) ⊆ Metric.closedBall 0 b.rOut := by
  have hs : tsupport (pointCutoffTest b φ : Euclidean d → ℂ) ⊆ tsupport (b : Euclidean d → ℝ) := by
    apply closure_mono
    intro x hx
    change (b x : ℂ) * φ x ≠ 0 at hx
    exact fun h => hx (by simp [h])
  exact hs.trans (le_of_eq b.tsupport_eq)

/-- Point support allows every compact test to be replaced by any smaller cutoff. -/
theorem DistributionSupportedIn.compact_cutoff {u : TemperedDistribution d}
    (hu : DistributionSupportedIn u {(0 : Euclidean d)})
    (b : ContDiffBump (0 : Euclidean d)) (φ : 𝓢(Euclidean d, ℂ))
    (hφ : HasCompactSupport (φ : Euclidean d → ℂ)) : u (pointCutoffTest b φ) = u φ :=
  hu.compact_locality _ _ (pointCutoffTest_hasCompactSupport b φ) hφ
    (pointCutoffTest_eventuallyEq b φ)

/-- Point support permits compact tests to be localized in arbitrarily small
balls, preserving their value and every derivative jet at the origin. -/
theorem DistributionSupportedIn.compact_localize_radius {u : TemperedDistribution d}
    (hu : DistributionSupportedIn u {(0 : Euclidean d)})
    (φ : 𝓢(Euclidean d, ℂ)) (hφ : HasCompactSupport (φ : Euclidean d → ℂ))
    (r : ℝ) (hr : 0 < r) :
    ∃ ψ : 𝓢(Euclidean d, ℂ), HasCompactSupport (ψ : Euclidean d → ℂ) ∧
      tsupport (ψ : Euclidean d → ℂ) ⊆ Metric.closedBall 0 r ∧ u ψ = u φ ∧
      ∀ n : ℕ, iteratedFDeriv ℝ n ψ 0 = iteratedFDeriv ℝ n φ 0 := by
  let b : ContDiffBump (0 : Euclidean d) :=
    { rIn := r / 2
      rOut := r
      rIn_pos := by positivity
      rIn_lt_rOut := by linarith }
  exact ⟨pointCutoffTest b φ, pointCutoffTest_hasCompactSupport b φ,
    pointCutoffTest_tsupport_subset b φ, hu.compact_cutoff b φ hφ,
    pointCutoffTest_iteratedFDeriv_zero b φ⟩

/-- Combining point-support localization with continuity gives a finite-order
estimate on every shrinking cutoff of a compact test. -/
theorem DistributionSupportedIn.compact_cutoff_finite_order_bound
    {u : TemperedDistribution d} (hu : DistributionSupportedIn u {(0 : Euclidean d)}) :
    ∃ N : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ (φ : 𝓢(Euclidean d, ℂ)) (b : ContDiffBump (0 : Euclidean d)),
        HasCompactSupport (φ : Euclidean d → ℂ) → b.rOut ≤ 1 →
        ‖u φ‖ ≤ C * (Finset.range (N + 1)).sup
          (fun n => SchwartzMap.seminorm ℂ 0 n) (pointCutoffTest b φ) := by
  obtain ⟨N, C, hC, hbound⟩ := distribution_local_finite_order_bound u
  refine ⟨N, C, hC, ?_⟩
  intro φ b hφ hb
  rw [← hu.compact_cutoff b φ hφ]
  apply hbound
  exact (pointCutoffTest_tsupport_subset b φ).trans (Metric.closedBall_subset_closedBall hb)

/-- The precise derivative scaling estimate for a fixed Schwartz cutoff. -/
theorem scaled_schwartz_iteratedFDeriv_bound (χ : 𝓢(Euclidean d, ℂ))
    (r : ℝ) (hr : 0 < r) (n : ℕ) (x : Euclidean d) :
    ‖iteratedFDeriv ℝ n (fun y => χ (r⁻¹ • y)) x‖ ≤
      SchwartzMap.seminorm ℂ 0 n χ * (r⁻¹) ^ n := by
  let g : Euclidean d →L[ℝ] Euclidean d := r⁻¹ • ContinuousLinearMap.id ℝ (Euclidean d)
  have hg : ‖g‖ ≤ r⁻¹ := by
    calc
      ‖g‖ ≤ |r⁻¹| * ‖ContinuousLinearMap.id ℝ (Euclidean d)‖ := by
        simpa only [g, Real.norm_eq_abs] using
          ContinuousLinearMap.opNorm_smul_le r⁻¹ (ContinuousLinearMap.id ℝ (Euclidean d))
      _ ≤ |r⁻¹| * 1 := mul_le_mul_of_nonneg_left ContinuousLinearMap.norm_id_le (abs_nonneg _)
      _ = r⁻¹ := by rw [abs_of_pos (inv_pos.mpr hr), mul_one]
  change ‖iteratedFDeriv ℝ n (χ.toFun ∘ g) x‖ ≤ _
  rw [g.iteratedFDeriv_comp_right χ.smooth' x (by exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤))]
  apply (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  exact mul_le_mul (SchwartzMap.norm_iteratedFDeriv_le_seminorm ℂ χ n (g x))
    (pow_le_pow_left₀ (norm_nonneg g) hg n) (by positivity) (apply_nonneg _ _)

/-- A fixed bump, shrunk by the real parameter `r`, localizes any Schwartz test. -/
def scaledPointCutoffTest (b : ContDiffBump (0 : Euclidean d))
    (r : ℝ) (hr : r ≠ 0) (φ : 𝓢(Euclidean d, ℂ)) : 𝓢(Euclidean d, ℂ) :=
  compactSchwartz (fun x => (b (r⁻¹ • x) : ℂ) * φ x)
    ((Complex.ofRealCLM.contDiff.comp
      (b.contDiff.comp (contDiff_const.smul contDiff_id))).mul φ.smooth')
    ((((b.hasCompactSupport.comp_left Complex.ofReal_zero).comp_homeomorph
      (Homeomorph.smulOfNeZero r⁻¹ (inv_ne_zero hr)))).mul_right)

@[simp] theorem scaledPointCutoffTest_apply (b : ContDiffBump (0 : Euclidean d))
    (r : ℝ) (hr : r ≠ 0) (φ : 𝓢(Euclidean d, ℂ)) (x : Euclidean d) :
    scaledPointCutoffTest b r hr φ x = (b (r⁻¹ • x) : ℂ) * φ x := rfl

theorem scaledPointCutoffTest_hasCompactSupport (b : ContDiffBump (0 : Euclidean d))
    (r : ℝ) (hr : r ≠ 0) (φ : 𝓢(Euclidean d, ℂ)) :
    HasCompactSupport (scaledPointCutoffTest b r hr φ : Euclidean d → ℂ) :=
  ((b.hasCompactSupport.comp_left Complex.ofReal_zero).comp_homeomorph
    (Homeomorph.smulOfNeZero r⁻¹ (inv_ne_zero hr))).mul_right

theorem scaledPointCutoffTest_eventuallyEq (b : ContDiffBump (0 : Euclidean d))
    (r : ℝ) (hr : r ≠ 0) (φ : 𝓢(Euclidean d, ℂ)) :
    (scaledPointCutoffTest b r hr φ : Euclidean d → ℂ) =ᶠ[𝓝 0] φ := by
  have ht : Tendsto (fun x : Euclidean d => r⁻¹ • x) (𝓝 0) (𝓝 0) := by
    simpa using ((continuous_const : Continuous (fun _ : Euclidean d => r⁻¹)).smul
      continuous_id).tendsto (0 : Euclidean d)
  filter_upwards [ht.eventually b.eventuallyEq_one] with x hx
  simp only [scaledPointCutoffTest_apply, hx, Pi.one_apply, Complex.ofReal_one, one_mul]

/-- The scaled construction preserves the value of a compact test. -/
theorem DistributionSupportedIn.compact_scaled_cutoff {u : TemperedDistribution d}
    (hu : DistributionSupportedIn u {(0 : Euclidean d)})
    (b : ContDiffBump (0 : Euclidean d)) (r : ℝ) (hr : r ≠ 0)
    (φ : 𝓢(Euclidean d, ℂ)) (hφ : HasCompactSupport (φ : Euclidean d → ℂ)) :
    u (scaledPointCutoffTest b r hr φ) = u φ :=
  hu.compact_locality _ _ (scaledPointCutoffTest_hasCompactSupport b r hr φ) hφ
    (scaledPointCutoffTest_eventuallyEq b r hr φ)

set_option maxHeartbeats 800000 in
/-- The complex-valued Schwartz realization of a real smooth bump. -/
def pointBumpSchwartz (b : ContDiffBump (0 : Euclidean d)) : 𝓢(Euclidean d, ℂ) :=
  compactSchwartz (fun x => (b x : ℂ)) (Complex.ofRealCLM.contDiff.comp b.contDiff)
    (b.hasCompactSupport.comp_left Complex.ofReal_zero)

@[simp] theorem pointBumpSchwartz_apply (b : ContDiffBump (0 : Euclidean d)) (x : Euclidean d) :
    pointBumpSchwartz b x = (b x : ℂ) := rfl

/-- Scaled cutoff tests remain supported in a correspondingly scaled ball. -/
theorem scaledPointCutoffTest_tsupport_subset (b : ContDiffBump (0 : Euclidean d))
    (r : ℝ) (hr : 0 < r) (φ : 𝓢(Euclidean d, ℂ)) :
    tsupport (scaledPointCutoffTest b r hr.ne' φ : Euclidean d → ℂ) ⊆
      Metric.closedBall 0 (r * b.rOut) := by
  apply closure_minimal _ Metric.isClosed_closedBall
  intro x hx
  have hb : r⁻¹ • x ∈ Function.support (b : Euclidean d → ℝ) := by
    intro hz
    exact hx (by simp only [scaledPointCutoffTest_apply, hz, Complex.ofReal_zero, zero_mul])
  rw [b.support_eq, Metric.mem_ball, dist_zero_right] at hb
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr)] at hb
  have hh : ‖x‖ < r * b.rOut := by
    have hb' : ‖x‖ / r < b.rOut := by simpa only [div_eq_inv_mul] using hb
    have := (div_lt_iff₀ hr).mp hb'
    simpa only [mul_comm] using this
  exact Metric.mem_closedBall.mpr (by simpa only [dist_zero_right] using hh.le)

/-- A Leibniz estimate for a shrinking cutoff, with the cutoff derivative
scaling exposed separately from the derivatives of the test. -/
theorem scaledPointCutoffTest_derivative_bound (b : ContDiffBump (0 : Euclidean d))
    (r : ℝ) (hr : 0 < r) (φ : 𝓢(Euclidean d, ℂ)) (n : ℕ) (x : Euclidean d) :
    ‖iteratedFDeriv ℝ n (scaledPointCutoffTest b r hr.ne' φ) x‖ ≤
      ‖(ContinuousLinearMap.mul ℂ ℂ).bilinearRestrictScalars ℝ‖ *
        ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i φ x‖ *
          (SchwartzMap.seminorm ℂ 0 (n - i) (pointBumpSchwartz b) * (r⁻¹) ^ (n - i)) := by
  let B := (ContinuousLinearMap.mul ℂ ℂ).bilinearRestrictScalars ℝ
  have hc : ContDiff ℝ ∞ (fun y : Euclidean d => pointBumpSchwartz b (r⁻¹ • y)) :=
    (pointBumpSchwartz b).smooth'.comp (contDiff_const.smul contDiff_id)
  have hn := B.norm_iteratedFDeriv_le_of_bilinear φ.smooth' hc x
    (n := n) (by exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤))
  have hfun : (fun y => B (φ.toFun y) (pointBumpSchwartz b (r⁻¹ • y))) =
      (scaledPointCutoffTest b r hr.ne' φ : Euclidean d → ℂ) := by
    funext y
    exact mul_comm _ _
  rw [hfun] at hn
  apply hn.trans
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg B)
  apply Finset.sum_le_sum
  intro i _
  exact mul_le_mul_of_nonneg_left
    (scaled_schwartz_iteratedFDeriv_bound (pointBumpSchwartz b) r hr (n - i) x)
    (by positivity)

/-- A radius-independent constant in the Leibniz estimate for a fixed cutoff. -/
def cutoffLeibnizConstant (b : ContDiffBump (0 : Euclidean d)) (n : ℕ) : ℝ :=
  ‖(ContinuousLinearMap.mul ℂ ℂ).bilinearRestrictScalars ℝ‖ *
    ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
      SchwartzMap.seminorm ℂ 0 (n - i) (pointBumpSchwartz b)

theorem cutoffLeibnizConstant_nonneg (b : ContDiffBump (0 : Euclidean d)) (n : ℕ) :
    0 ≤ cutoffLeibnizConstant b n := by
  apply mul_nonneg (norm_nonneg _)
  exact Finset.sum_nonneg (fun i _ => mul_nonneg (by positivity) (apply_nonneg _ _))

/-- Quantified shrinking-cutoff control for a Taylor-flat test. This estimate
contains the cancellation between inverse cutoff scales and Taylor powers. -/
theorem scaledPointCutoffTest_seminorm_bound (b : ContDiffBump (0 : Euclidean d))
    (hb : b.rOut = 1) (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1)
    (φ : 𝓢(Euclidean d, ℂ)) (N : ℕ) (a : ℝ) (ha : 0 ≤ a)
    (hflat : ∀ i ≤ N, ∀ x : Euclidean d, ‖x‖ ≤ r →
      ‖iteratedFDeriv ℝ i φ x‖ ≤ a * ‖x‖ ^ (N - i)) (j : ℕ) (hj : j ≤ N) :
    SchwartzMap.seminorm ℂ 0 j (scaledPointCutoffTest b r hr.ne' φ) ≤
      a * cutoffLeibnizConstant b j := by
  apply SchwartzMap.seminorm_le_bound ℂ 0 j _
    (mul_nonneg ha (cutoffLeibnizConstant_nonneg b j))
  intro x
  simp only [pow_zero, one_mul]
  by_cases hx : ‖x‖ ≤ r
  · apply (scaledPointCutoffTest_derivative_bound b r hr φ j x).trans
    have hsum : (∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) *
        ‖iteratedFDeriv ℝ i φ x‖ *
          (SchwartzMap.seminorm ℂ 0 (j - i) (pointBumpSchwartz b) * (r⁻¹) ^ (j - i))) ≤
        a * ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) *
          SchwartzMap.seminorm ℂ 0 (j - i) (pointBumpSchwartz b) := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro i hi
      have hij : i ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      have hiN : i ≤ N := hij.trans hj
      let M := SchwartzMap.seminorm ℂ 0 (j - i) (pointBumpSchwartz b)
      have hM : 0 ≤ M := apply_nonneg _ _
      have hexp : N - i = (j - i) + (N - j) := by omega
      calc
        (j.choose i : ℝ) * ‖iteratedFDeriv ℝ i φ x‖ * (M * (r⁻¹) ^ (j - i))
            ≤ (j.choose i : ℝ) * (a * ‖x‖ ^ (N - i)) * (M * (r⁻¹) ^ (j - i)) := by
              gcongr
              exact hflat i hiN x hx
        _ ≤ (j.choose i : ℝ) * (a * r ^ (N - i)) * (M * (r⁻¹) ^ (j - i)) := by
              gcongr
        _ = a * ((j.choose i : ℝ) * M) * r ^ (N - j) := by
              rw [hexp, pow_add, inv_pow]
              have hcancel : r ^ (j - i) * (r ^ (j - i))⁻¹ = 1 :=
                mul_inv_cancel₀ (pow_ne_zero _ hr.ne')
              calc
                _ = a * ((j.choose i : ℝ) * M) * r ^ (N - j) *
                    (r ^ (j - i) * (r ^ (j - i))⁻¹) := by ring
                _ = _ := by rw [hcancel, mul_one]
        _ ≤ a * ((j.choose i : ℝ) * M) :=
              mul_le_of_le_one_right (mul_nonneg ha (mul_nonneg (by positivity) hM))
                (pow_le_one₀ hr.le hr1)
    calc
      _ ≤ ‖(ContinuousLinearMap.mul ℂ ℂ).bilinearRestrictScalars ℝ‖ *
          (a * ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) *
            SchwartzMap.seminorm ℂ 0 (j - i) (pointBumpSchwartz b)) :=
        mul_le_mul_of_nonneg_left hsum (norm_nonneg _)
      _ = a * cutoffLeibnizConstant b j := by unfold cutoffLeibnizConstant; ring
  · have hsupport : tsupport (scaledPointCutoffTest b r hr.ne' φ : Euclidean d → ℂ) ⊆
        Metric.closedBall 0 r := by
      simpa only [hb, mul_one] using scaledPointCutoffTest_tsupport_subset b r hr φ
    have hz : iteratedFDeriv ℝ j (scaledPointCutoffTest b r hr.ne' φ) x = 0 :=
      image_eq_zero_of_nmem_tsupport (fun h => hx (by
        simpa only [Metric.mem_closedBall, dist_zero_right] using
          hsupport (tsupport_iteratedFDeriv_subset j h)))
    rw [hz, norm_zero]
    exact mul_nonneg ha (cutoffLeibnizConstant_nonneg b j)

/-- Flat jets yield simultaneous derivative bounds on a sufficiently small
closed ball. -/
theorem flat_jet_uniform_derivative_bound (φ : 𝓢(Euclidean d, ℂ)) (N : ℕ)
    (hzero : ∀ j ≤ N, iteratedFDeriv ℝ j φ 0 = 0) (a : ℝ) (ha : 0 < a) :
    ∃ r : ℝ, 0 < r ∧ ∀ i ≤ N, ∀ x : Euclidean d, ‖x‖ ≤ r →
      ‖iteratedFDeriv ℝ i φ x‖ ≤ a * ‖x‖ ^ (N - i) := by
  have he : ∀ i ∈ Finset.range (N + 1), ∀ᶠ x in 𝓝 (0 : Euclidean d),
      ‖iteratedFDeriv ℝ i φ x‖ ≤ a * ‖x‖ ^ (N - i) := by
    intro i hi
    have hiN : i ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have hh := flat_jet_iteratedFDeriv_isLittleO φ i (N - i)
      (fun j hj => hzero j (by omega))
    have hh' := (Asymptotics.isLittleO_iff.mp hh) ha
    simpa only [norm_pow, norm_norm] using hh'
  have hall : ∀ᶠ x in 𝓝 (0 : Euclidean d), ∀ i ∈ Finset.range (N + 1),
      ‖iteratedFDeriv ℝ i φ x‖ ≤ a * ‖x‖ ^ (N - i) :=
    (eventually_all_finset _).mpr he
  obtain ⟨r, hr, hball⟩ := Metric.nhds_basis_closedBall.mem_iff.mp hall
  refine ⟨r, hr, ?_⟩
  intro i hi x hx
  exact hball (by simpa only [Metric.mem_closedBall, dist_zero_right] using hx)
    i (Finset.mem_range.mpr (by omega))

/-- A point-supported distribution annihilates every compact test with a
sufficiently long vanishing jet. -/
theorem DistributionSupportedIn.exists_order_compact_flat_annihilation
    {u : TemperedDistribution d} (hu : DistributionSupportedIn u {(0 : Euclidean d)}) :
    ∃ N : ℕ, ∀ φ : 𝓢(Euclidean d, ℂ), HasCompactSupport (φ : Euclidean d → ℂ) →
      (∀ j ≤ N, iteratedFDeriv ℝ j φ 0 = 0) → u φ = 0 := by
  obtain ⟨N, C, hC, hbound⟩ := distribution_local_finite_order_bound u
  let b : ContDiffBump (0 : Euclidean d) :=
    { rIn := 1 / 2
      rOut := 1
      rIn_pos := by norm_num
      rIn_lt_rOut := by norm_num }
  let K := 1 + ∑ j ∈ Finset.range (N + 1), cutoffLeibnizConstant b j
  have hK : 0 < K := by
    have hh : 0 ≤ ∑ j ∈ Finset.range (N + 1), cutoffLeibnizConstant b j :=
      Finset.sum_nonneg (fun j _ => cutoffLeibnizConstant_nonneg b j)
    dsimp only [K]
    linarith
  have hKj : ∀ j ≤ N, cutoffLeibnizConstant b j ≤ K := by
    intro j hj
    have hh : cutoffLeibnizConstant b j ≤
        ∑ j ∈ Finset.range (N + 1), cutoffLeibnizConstant b j :=
      Finset.single_le_sum (fun i _ => cutoffLeibnizConstant_nonneg b i)
        (Finset.mem_range.mpr (by omega))
    dsimp only [K]
    linarith
  refine ⟨N, ?_⟩
  intro φ hφ hzero
  apply norm_eq_zero.mp
  apply le_antisymm _ (norm_nonneg _)
  apply le_of_forall_pos_le_add
  intro ε hε
  let a := ε / (C * K)
  have ha : 0 < a := div_pos hε (mul_pos hC hK)
  obtain ⟨δ, hδ, hflat⟩ := flat_jet_uniform_derivative_bound φ N hzero a ha
  let r := min δ 1
  have hr : 0 < r := lt_min hδ (by norm_num)
  have hr1 : r ≤ 1 := min_le_right _ _
  have hsr : tsupport (scaledPointCutoffTest b r hr.ne' φ : Euclidean d → ℂ) ⊆
      Metric.closedBall 0 1 := by
    apply (scaledPointCutoffTest_tsupport_subset b r hr φ).trans
    exact Metric.closedBall_subset_closedBall (by simpa only [b, mul_one] using hr1)
  rw [← hu.compact_scaled_cutoff b r hr.ne' φ hφ]
  apply (hbound _ hsr).trans
  have hseminorm : (Finset.range (N + 1)).sup (fun j => SchwartzMap.seminorm ℂ 0 j)
      (scaledPointCutoffTest b r hr.ne' φ) ≤ a * K := by
    apply Seminorm.finset_sup_apply_le (mul_nonneg ha.le hK.le)
    intro j hj
    have hjN : j ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    apply (scaledPointCutoffTest_seminorm_bound b rfl r hr hr1 φ N a ha.le
      (fun i hi x hx => hflat i hi x (hx.trans (min_le_left _ _))) j hjN).trans
    exact mul_le_mul_of_nonneg_left (hKj j hjN) ha.le
  calc
    _ ≤ C * (a * K) := mul_le_mul_of_nonneg_left hseminorm hC.le
    _ = 0 + ε := by dsimp only [a]; field_simp [hC.ne', hK.ne']; ring

/-- Finite coordinate derivative jets through order `N`. Repeated directions
are allowed, so the indexing covers mixed partial derivatives. -/
abbrev PointJetIndex (d N : ℕ) := Σ n : Fin (N + 1), Fin n.val → Fin d

/-- The coordinate directions of one derivative jet. -/
def pointJetDirections {N : ℕ} (i : PointJetIndex d N) : Fin i.1.val → Euclidean d :=
  fun j => (EuclideanSpace.basisFun (Fin d) ℝ) (i.2 j)

/-- Evaluation at zero of an actual iterated coordinate derivative. -/
def pointJetDistribution (N : ℕ) (i : PointJetIndex d N) : TemperedDistribution d :=
  (distributionDelta (0 : Euclidean d)).comp (SchwartzMap.iteratedPDeriv ℂ (pointJetDirections i))

@[simp] theorem pointJetDistribution_apply (N : ℕ) (i : PointJetIndex d N)
    (φ : 𝓢(Euclidean d, ℂ)) :
    pointJetDistribution N i φ = iteratedFDeriv ℝ i.1.val φ 0 (pointJetDirections i) := by
  simp only [pointJetDistribution, ContinuousLinearMap.comp_apply,
    distributionDelta_apply, SchwartzMap.iteratedPDeriv_eq_iteratedFDeriv]

/-- The compact tests form a genuine complex linear subspace of Schwartz space. -/
def compactTestSubmodule (d : ℕ) : Submodule ℂ 𝓢(Euclidean d, ℂ) where
  carrier := {φ | HasCompactSupport (φ : Euclidean d → ℂ)}
  zero_mem' := by
    change HasCompactSupport (fun _ : Euclidean d => (0 : ℂ))
    simp [HasCompactSupport, tsupport]
  add_mem' := fun hφ hψ => hφ.add hψ
  smul_mem' := by
    intro c φ hφ
    change HasCompactSupport (fun x => c • φ x)
    exact hφ.comp_left (smul_zero c : c • (0 : ℂ) = 0)

/-- Finite derivative classification on compact tests, obtained from the
kernel/span theorem for finitely many linear forms. -/
theorem DistributionSupportedIn.exists_finite_derivatives_compact
    {u : TemperedDistribution d} (hu : DistributionSupportedIn u {(0 : Euclidean d)}) :
    ∃ N : ℕ, ∃ c : PointJetIndex d N → ℂ,
      ∀ φ : 𝓢(Euclidean d, ℂ), HasCompactSupport (φ : Euclidean d → ℂ) →
        u φ = ∑ i : PointJetIndex d N, c i * pointJetDistribution N i φ := by
  classical
  obtain ⟨N, hann⟩ := hu.exists_order_compact_flat_annihilation
  let L : PointJetIndex d N → compactTestSubmodule d →ₗ[ℂ] ℂ := fun i =>
    (pointJetDistribution N i).toLinearMap.comp (compactTestSubmodule d).subtype
  let K : compactTestSubmodule d →ₗ[ℂ] ℂ :=
    u.toLinearMap.comp (compactTestSubmodule d).subtype
  have hker : (⨅ i, LinearMap.ker (L i)) ≤ LinearMap.ker K := by
    intro φ hφ
    apply hann φ.val φ.property
    intro n hn
    apply ContinuousMultilinearMap.toMultilinearMap_injective
    apply (EuclideanSpace.basisFun (Fin d) ℝ).toBasis.ext_multilinear
    intro dirs
    let i : PointJetIndex d N := ⟨⟨n, by omega⟩, dirs⟩
    have hz := (Submodule.mem_iInf (fun i => LinearMap.ker (L i))).mp hφ i
    change pointJetDistribution N i φ.val = 0 at hz
    simpa only [pointJetDistribution_apply, pointJetDirections, i,
      ContinuousMultilinearMap.zero_apply, MultilinearMap.zero_apply] using hz
  have hspan := mem_span_of_iInf_ker_le_ker hker
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hspan
  refine ⟨N, c, ?_⟩
  intro φ hφ
  have hh := LinearMap.congr_fun hc (⟨φ, hφ⟩ : compactTestSubmodule d)
  simpa only [LinearMap.sum_apply, LinearMap.smul_apply, L, K, LinearMap.comp_apply,
    Submodule.subtype_apply, ContinuousLinearMap.coe_coe, smul_eq_mul] using hh.symm

/-- A distribution supported at the origin is an actual finite linear combination
of coordinate derivative evaluations there. Compact-test density upgrades the
classification to equality of continuous functionals on the whole Schwartz space. -/
theorem DistributionSupportedIn.eq_sum_pointJets {u : TemperedDistribution d}
    (hu : DistributionSupportedIn u {(0 : Euclidean d)}) :
    ∃ N : ℕ, ∃ c : PointJetIndex d N → ℂ,
      u = ∑ i : PointJetIndex d N, c i • pointJetDistribution N i := by
  classical
  obtain ⟨N, c, hc⟩ := hu.exists_finite_derivatives_compact
  refine ⟨N, c, distribution_eq_of_compact_tests ?_⟩
  intro φ hφ
  simpa only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
    using hc φ hφ

/-- The same classification written explicitly as a finite sum of derivatives
of an arbitrary Schwartz test at zero. -/
theorem DistributionSupportedIn.exists_finite_derivatives {u : TemperedDistribution d}
    (hu : DistributionSupportedIn u {(0 : Euclidean d)}) :
    ∃ N : ℕ, ∃ c : PointJetIndex d N → ℂ, ∀ φ : 𝓢(Euclidean d, ℂ),
      u φ = ∑ i : PointJetIndex d N,
        c i * iteratedFDeriv ℝ i.1.val φ 0 (pointJetDirections i) := by
  classical
  obtain ⟨N, c, rfl⟩ := hu.eq_sum_pointJets
  exact ⟨N, c, fun φ => by simp only [ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul, pointJetDistribution_apply]⟩

/-- Every individual coordinate derivative evaluation is supported at zero. -/
theorem pointJetDistribution_supported (N : ℕ) (i : PointJetIndex d N) :
    DistributionSupportedIn (pointJetDistribution N i) {(0 : Euclidean d)} := by
  intro φ _ hdisj
  rw [pointJetDistribution_apply]
  have hnot : (0 : Euclidean d) ∉ tsupport (φ : Euclidean d → ℂ) :=
    Set.disjoint_singleton_right.mp hdisj
  have hz : iteratedFDeriv ℝ i.1.val φ 0 = 0 := image_eq_zero_of_nmem_tsupport
    (fun h => hnot (tsupport_iteratedFDeriv_subset i.1.val h))
  simp only [hz, ContinuousMultilinearMap.zero_apply]

/-- Point support is equivalent to the finite derivative classification, with
no support or classification hypothesis encoded in a structure. -/
theorem distributionSupportedIn_origin_iff_sum_pointJets (u : TemperedDistribution d) :
    DistributionSupportedIn u {(0 : Euclidean d)} ↔
      ∃ N : ℕ, ∃ c : PointJetIndex d N → ℂ,
        u = ∑ i : PointJetIndex d N, c i • pointJetDistribution N i := by
  classical
  constructor
  · exact DistributionSupportedIn.eq_sum_pointJets
  · rintro ⟨N, c, rfl⟩
    intro φ hφ hdisj
    simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
    apply Finset.sum_eq_zero
    intro i _
    rw [pointJetDistribution_supported N i φ hφ hdisj, mul_zero]

end RieszEuclidean.CompleteMinimal
