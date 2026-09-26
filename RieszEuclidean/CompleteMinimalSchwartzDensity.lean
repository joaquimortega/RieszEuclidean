import RieszEuclidean.CompleteMinimalDistributions
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-! Compact smooth tests are dense in the Schwartz seminorm topology. -/
noncomputable section
open SchwartzMap Filter Topology
open scoped SchwartzMap ContDiff
namespace RieszEuclidean.CompleteMinimal
set_option maxHeartbeats 800000
variable {d : ℕ}

private def densityBump : ContDiffBump (0 : Euclidean d) :=
  { rIn := 1, rOut := 2, rIn_pos := by norm_num, rIn_lt_rOut := by norm_num }

private def densityCutoff : 𝓢(Euclidean d, ℂ) :=
  compactSchwartz (fun x => ((densityBump (d := d)) x : ℂ))
    (Complex.ofRealCLM.contDiff.comp (densityBump (d := d)).contDiff)
    ((densityBump (d := d)).hasCompactSupport.comp_left Complex.ofReal_zero)

/-- Multiplication by a fixed bump expanded to radius `n + 1`. -/
def compactSchwartzApprox (φ : 𝓢(Euclidean d, ℂ)) (n : ℕ) : 𝓢(Euclidean d, ℂ) :=
  compactSchwartz (fun x => ((densityBump (d := d)) (((n : ℝ) + 1)⁻¹ • x) : ℂ) * φ x)
    ((Complex.ofRealCLM.contDiff.comp
      ((densityBump (d := d)).contDiff.comp (contDiff_const.smul contDiff_id))).mul φ.smooth')
    ((((densityBump (d := d)).hasCompactSupport.comp_left Complex.ofReal_zero).comp_homeomorph
      (Homeomorph.smulOfNeZero (((n : ℝ) + 1)⁻¹) (by positivity))).mul_right)

theorem compactSchwartzApprox_hasCompactSupport (φ : 𝓢(Euclidean d, ℂ)) (n : ℕ) :
    HasCompactSupport (compactSchwartzApprox φ n : Euclidean d → ℂ) :=
  (((densityBump (d := d)).hasCompactSupport.comp_left Complex.ofReal_zero).comp_homeomorph
    (Homeomorph.smulOfNeZero (((n : ℝ) + 1)⁻¹) (by positivity))).mul_right

private theorem density_scaled_derivative (r : ℝ) (hr : 1 ≤ r) (i : ℕ)
    (x : Euclidean d) :
    ‖iteratedFDeriv ℝ i (fun y => (densityCutoff (d := d)) (r⁻¹ • y)) x‖ ≤
      SchwartzMap.seminorm ℂ 0 i (densityCutoff (d := d)) := by
  let g : Euclidean d →L[ℝ] Euclidean d := r⁻¹ • ContinuousLinearMap.id ℝ _
  have hg : ‖g‖ ≤ 1 := by
    calc
      ‖g‖ ≤ |r⁻¹| * ‖ContinuousLinearMap.id ℝ (Euclidean d)‖ := by
        simpa only [g, Real.norm_eq_abs] using
          ContinuousLinearMap.opNorm_smul_le r⁻¹ (ContinuousLinearMap.id ℝ (Euclidean d))
      _ ≤ |r⁻¹| * 1 := mul_le_mul_of_nonneg_left ContinuousLinearMap.norm_id_le (abs_nonneg _)
      _ ≤ 1 := by rw [mul_one, abs_of_nonneg (by positivity)]; exact inv_le_one_of_one_le₀ hr
  change ‖iteratedFDeriv ℝ i ((densityCutoff (d := d)).toFun ∘ g) x‖ ≤ _
  rw [g.iteratedFDeriv_comp_right (densityCutoff (d := d)).smooth' x (by exact_mod_cast (le_top : (i : ℕ∞) ≤ ⊤))]
  apply (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  calc
    ‖iteratedFDeriv ℝ i (densityCutoff (d := d)) (g x)‖ * ‖g‖ ^ i ≤
        SchwartzMap.seminorm ℂ 0 i (densityCutoff (d := d)) * 1 :=
      mul_le_mul (SchwartzMap.norm_iteratedFDeriv_le_seminorm ℂ (densityCutoff (d := d)) i (g x))
        (pow_le_one₀ (norm_nonneg _) hg) (by positivity) (apply_nonneg _ _)
    _ = _ := mul_one _

private theorem density_error_derivative (r : ℝ) (hr : 1 ≤ r) (i : ℕ)
    (x : Euclidean d) :
    ‖iteratedFDeriv ℝ i (fun y => (densityCutoff (d := d)) (r⁻¹ • y) - 1) x‖ ≤
      SchwartzMap.seminorm ℂ 0 i (densityCutoff (d := d)) + 1 := by
  have hs : ContDiff ℝ ∞ (fun y : Euclidean d => (densityCutoff (d := d)) (r⁻¹ • y)) :=
    (densityCutoff (d := d)).smooth'.comp (contDiff_const.smul contDiff_id)
  by_cases hi : i = 0
  · subst i
    simp only [norm_iteratedFDeriv_zero]
    exact (norm_sub_le _ _).trans (by
      simpa only [norm_iteratedFDeriv_zero, norm_one] using
        (add_le_add_right (density_scaled_derivative r hr 0 x) (1 : ℝ)))
  · simp only [sub_eq_add_neg]
    rw [iteratedFDeriv_add_apply' (hs.of_le (by exact_mod_cast (le_top : (i : ℕ∞) ≤ ⊤))).contDiffAt
      contDiffAt_const, iteratedFDeriv_const_of_ne hi, Pi.zero_apply, add_zero]
    exact (density_scaled_derivative r hr i x).trans (le_add_of_nonneg_right zero_le_one)

private theorem density_error_zero (φ : 𝓢(Euclidean d, ℂ)) (n : ℕ)
    (x : Euclidean d) (hx : ‖x‖ < (n : ℝ) + 1) :
    (compactSchwartzApprox φ n - φ : Euclidean d → ℂ) =ᶠ[𝓝 x] 0 := by
  have hr : 0 < (n : ℝ) + 1 := by positivity
  have hball : x ∈ Metric.ball 0 ((n : ℝ) + 1) := by simpa using hx
  filter_upwards [Metric.isOpen_ball.mem_nhds hball] with y hy
  have hnorm : ‖y‖ ≤ (n : ℝ) + 1 := (by simpa using hy : ‖y‖ < (n : ℝ) + 1).le
  have hb : (((n : ℝ) + 1)⁻¹ • y) ∈ Metric.closedBall (0 : Euclidean d) (densityBump (d := d)).rIn := by
    change _ ∈ Metric.closedBall 0 1
    simp only [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hr)]
    exact (inv_mul_le_one₀ hr).mpr hnorm
  change ((densityBump (d := d)) (((n : ℝ) + 1)⁻¹ • y) : ℂ) * φ y - φ y = 0
  rw [(densityBump (d := d)).one_of_mem_closedBall hb]
  simp

/-- Quantitative convergence in each individual Schwartz seminorm. -/
theorem compactSchwartzApprox_seminorm_bound (φ : 𝓢(Euclidean d, ℂ)) (k j n : ℕ) :
    SchwartzMap.seminorm ℂ k j (compactSchwartzApprox φ n - φ) ≤
      (∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) *
        (SchwartzMap.seminorm ℂ 0 i (densityCutoff (d := d)) + 1) *
        SchwartzMap.seminorm ℂ (k + 1) (j - i) φ) / ((n : ℝ) + 1) := by
  let C := ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) *
        (SchwartzMap.seminorm ℂ 0 i (densityCutoff (d := d)) + 1) *
        SchwartzMap.seminorm ℂ (k + 1) (j - i) φ
  have hC : 0 ≤ C := Finset.sum_nonneg (fun i _ => by positivity)
  have hr : 0 < (n : ℝ) + 1 := by positivity
  apply SchwartzMap.seminorm_le_bound ℂ k j _ (div_nonneg hC hr.le)
  intro x
  have hco : ((compactSchwartzApprox φ n - φ : 𝓢(Euclidean d, ℂ)) : Euclidean d → ℂ) =
      (compactSchwartzApprox φ n : Euclidean d → ℂ) - φ := by ext y; rfl
  rw [hco]
  by_cases hx : ‖x‖ < (n : ℝ) + 1
  · have heq := density_error_zero φ n x hx
    have heqw : (compactSchwartzApprox φ n - φ : Euclidean d → ℂ) =ᶠ[𝓝[Set.univ] x] 0 := by
      simpa only [nhdsWithin_univ] using heq
    have hz := heqw.iteratedFDerivWithin_eq (𝕜 := ℝ) heq.eq_of_nhds j
    simp only [iteratedFDerivWithin_univ] at hz
    rw [hz]
    simp only [Pi.zero_def, iteratedFDeriv_zero_fun, Pi.zero_apply, norm_zero, mul_zero]
    exact div_nonneg hC hr.le
  · have hxr : (n : ℝ) + 1 ≤ ‖x‖ := le_of_not_gt hx
    have hs : ContDiff ℝ ∞ (fun y : Euclidean d => (densityCutoff (d := d)) (((n : ℝ) + 1)⁻¹ • y) - 1) :=
      ((densityCutoff (d := d)).smooth'.comp (contDiff_const.smul contDiff_id)).sub contDiff_const
    have heq : (compactSchwartzApprox φ n - φ : Euclidean d → ℂ) =
        fun y => ((densityCutoff (d := d)) (((n : ℝ) + 1)⁻¹ • y) - 1) * φ y := by
      ext y
      change ((densityBump (d := d)) _ : ℂ) * φ y - φ y = (((densityBump (d := d)) _ : ℂ) - 1) * φ y
      ring
    rw [heq, le_div_iff₀ hr]
    have hp := norm_iteratedFDeriv_mul_le hs φ.smooth' x
      (by exact_mod_cast (le_top : (j : ℕ∞) ≤ ⊤))
    calc
      ‖x‖ ^ k * ‖iteratedFDeriv ℝ j (fun y =>
          ((densityCutoff (d := d)) (((n : ℝ) + 1)⁻¹ • y) - 1) * φ y) x‖ * ((n : ℝ) + 1)
          ≤ ‖x‖ ^ (k + 1) * ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) *
              ‖iteratedFDeriv ℝ i (fun y => (densityCutoff (d := d)) (((n : ℝ) + 1)⁻¹ • y) - 1) x‖ *
              ‖iteratedFDeriv ℝ (j - i) φ x‖ := by
        calc
          _ ≤ ‖x‖ ^ k * (∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) *
              ‖iteratedFDeriv ℝ i (fun y => (densityCutoff (d := d)) (((n : ℝ) + 1)⁻¹ • y) - 1) x‖ *
              ‖iteratedFDeriv ℝ (j - i) φ x‖) * ‖x‖ := by
            gcongr
            exact hp
          _ = _ := by rw [pow_succ]; ring
      _ = ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) *
              ‖iteratedFDeriv ℝ i (fun y => (densityCutoff (d := d)) (((n : ℝ) + 1)⁻¹ • y) - 1) x‖ *
              (‖x‖ ^ (k + 1) * ‖iteratedFDeriv ℝ (j - i) φ x‖) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ ≤ C := by
        apply Finset.sum_le_sum
        intro i _
        apply mul_le_mul
        · apply mul_le_mul_of_nonneg_left (density_error_derivative _ (by linarith) i x)
            (by positivity)
        · exact SchwartzMap.le_seminorm ℂ (k + 1) (j - i) φ x
        · positivity
        · positivity

/-- The expanded compact smooth cutoffs converge in the Schwartz topology. -/
theorem compactSchwartzApprox_tendsto (φ : 𝓢(Euclidean d, ℂ)) :
    Tendsto (compactSchwartzApprox φ) atTop (𝓝 φ) := by
  apply (schwartz_withSeminorms ℂ (Euclidean d) ℂ).tendsto_nhds_atTop _ _ |>.mpr
  intro i ε hε
  let C := ∑ l ∈ Finset.range (i.2 + 1), (i.2.choose l : ℝ) *
        (SchwartzMap.seminorm ℂ 0 l (densityCutoff (d := d)) + 1) *
        SchwartzMap.seminorm ℂ (i.1 + 1) (i.2 - l) φ
  obtain ⟨N, hN⟩ := exists_nat_gt (C / ε)
  refine ⟨N, fun n hn => ?_⟩
  apply (compactSchwartzApprox_seminorm_bound φ i.1 i.2 n).trans_lt
  change C / ((n : ℝ) + 1) < ε
  rw [div_lt_iff₀ (by positivity)]
  have hNc : (N : ℝ) ≤ n := Nat.cast_le.mpr hn
  have hC : C < (N : ℝ) * ε := (div_lt_iff₀ hε).mp hN
  nlinarith

/-- Compact smooth tests form a dense subset of Schwartz space. -/
theorem compactSchwartz_dense (d : ℕ) :
    Dense {φ : 𝓢(Euclidean d, ℂ) | HasCompactSupport (φ : Euclidean d → ℂ)} := by
  intro φ
  exact mem_closure_of_tendsto (compactSchwartzApprox_tendsto φ)
    (Eventually.of_forall (compactSchwartzApprox_hasCompactSupport φ))

theorem compactSchwartzApprox_tsupport_subset (φ : 𝓢(Euclidean d, ℂ)) (n : ℕ) :
    tsupport (compactSchwartzApprox φ n : Euclidean d → ℂ) ⊆
      tsupport (φ : Euclidean d → ℂ) := by
  apply closure_mono
  intro x hx
  change (densityBump (d := d) (((n : ℝ) + 1)⁻¹ • x) : ℂ) * φ x ≠ 0 at hx
  exact fun hz => hx (by simp [hz])

/-- The support definition extends from compact tests to all Schwartz tests. -/
theorem DistributionSupportedIn.schwartz_test {u : TemperedDistribution d}
    {S : Set (Euclidean d)} (hu : DistributionSupportedIn u S)
    (φ : 𝓢(Euclidean d, ℂ)) (hφ : Disjoint (tsupport (φ : Euclidean d → ℂ)) S) :
    u φ = 0 := by
  have ht := u.continuous.tendsto φ |>.comp (compactSchwartzApprox_tendsto φ)
  have hz : ∀ n, u (compactSchwartzApprox φ n) = 0 := fun n =>
    hu _ (compactSchwartzApprox_hasCompactSupport φ n)
      (hφ.mono_left (compactSchwartzApprox_tsupport_subset φ n))
  have ht0 : Tendsto (fun n => u (compactSchwartzApprox φ n)) atTop (𝓝 0) :=
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℂ)) atTop (𝓝 0)).congr
      (fun n => (hz n).symm)
  exact tendsto_nhds_unique ht ht0

/-- Every point-supported distribution depends only on the germ of a Schwartz test. -/
theorem DistributionSupportedIn.schwartz_locality {u : TemperedDistribution d}
    (hu : DistributionSupportedIn u {(0 : Euclidean d)})
    (φ ψ : 𝓢(Euclidean d, ℂ))
    (heq : (φ : Euclidean d → ℂ) =ᶠ[𝓝 0] ψ) : u φ = u ψ := by
  have hzero : (φ - ψ : Euclidean d → ℂ) =ᶠ[𝓝 0] 0 := by
    filter_upwards [heq] with x hx
    change φ x - ψ x = 0
    exact sub_eq_zero.mpr hx
  have hnot := not_mem_tsupport_iff_eventuallyEq.mpr hzero
  have hz := hu.schwartz_test (φ - ψ) (Set.disjoint_singleton_right.mpr hnot)
  exact sub_eq_zero.mp ((map_sub u φ ψ).symm.trans hz)

/-- Continuous distributions are determined by their values on compact smooth tests. -/
theorem distribution_eq_of_compact_tests {u v : TemperedDistribution d}
    (h : ∀ φ : 𝓢(Euclidean d, ℂ), HasCompactSupport (φ : Euclidean d → ℂ) → u φ = v φ) :
    u = v := by
  ext φ
  apply tendsto_nhds_unique
    (u.continuous.tendsto φ |>.comp (compactSchwartzApprox_tendsto φ))
  have ht := v.continuous.tendsto φ |>.comp (compactSchwartzApprox_tendsto φ)
  exact ht.congr' (Eventually.of_forall (fun n =>
    (h _ (compactSchwartzApprox_hasCompactSupport φ n)).symm))

end RieszEuclidean.CompleteMinimal
