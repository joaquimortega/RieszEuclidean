import RieszEuclidean.Basic
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

/-!
# Disk primitives for the logarithmic circle inequalities

The radial primitive construction below uses the pinned Mathlib differentiation
under the integral sign and fundamental theorem of calculus. No harmonic or
Jensen inequality is assumed in its construction.
-/

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped Interval

namespace RieszEuclidean.CompleteMinimal

/-- Radial integration from the origin in a complex disk. -/
def diskPrimitive (q : ℂ → ℂ) (z : ℂ) : ℂ :=
  ∫ t in (0 : ℝ)..1, z * q ((t : ℂ) * z)

private theorem disk_segment_mem {R : ℝ} {z : ℂ} (hz : ‖z‖ < R)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : (t : ℂ) * z ∈ ball (0 : ℂ) R := by
  rw [mem_ball, dist_zero_right, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg ht.1]
  exact (mul_le_mul_of_nonneg_right ht.2 (norm_nonneg z)).trans_lt (by simpa using hz)

private theorem continuousOn_disk_integrand {q : ℂ → ℂ} {R : ℝ}
    (hq : DifferentiableOn ℂ q (ball (0 : ℂ) R)) {z : ℂ} (hz : ‖z‖ < R) :
    ContinuousOn (fun t : ℝ => z * q ((t : ℂ) * z)) (Icc (0 : ℝ) 1) := by
  apply continuousOn_const.mul
  apply hq.continuousOn.comp
    ((Complex.continuous_ofReal.mul continuous_const).continuousOn)
  exact fun t ht => disk_segment_mem hz ht

/-- Radial integration gives a complex primitive on the disk. -/
theorem hasDerivAt_diskPrimitive {q : ℂ → ℂ} {R : ℝ}
    (hq : DifferentiableOn ℂ q (ball (0 : ℂ) R)) {z : ℂ} (hz : z ∈ ball (0 : ℂ) R) :
    HasDerivAt (diskPrimitive q) (q z) z := by
  have hzR : ‖z‖ < R := by simpa only [mem_ball, dist_zero_right] using hz
  let ρ : ℝ := (R + ‖z‖) / 2
  let ε : ℝ := (R - ‖z‖) / 2
  have hε : 0 < ε := by dsimp [ε]; linarith
  have hρ : ρ < R := by dsimp [ρ]; linarith
  have hρpos : 0 < ρ := by dsimp [ρ]; linarith [norm_nonneg z]
  have hxρ : ∀ x ∈ ball z ε, ‖x‖ ≤ ρ := by
    intro x hx
    have hnorm := norm_sub_norm_le x z
    rw [← dist_eq_norm] at hnorm
    have hdist : dist x z < ε := hx
    dsimp [ρ, ε] at *
    linarith
  have hq' : DifferentiableOn ℂ (deriv q) (ball (0 : ℂ) R) := hq.deriv isOpen_ball
  have hρsub : closedBall (0 : ℂ) ρ ⊆ ball (0 : ℂ) R := closedBall_subset_ball hρ
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : ℂ) ρ).bddAbove_image
    (hq.continuousOn.mono hρsub).norm
  obtain ⟨N, hN⟩ := (isCompact_closedBall (0 : ℂ) ρ).bddAbove_image
    (hq'.continuousOn.mono hρsub).norm
  let F : ℂ → ℝ → ℂ := fun x t => x * q ((t : ℂ) * x)
  let F' : ℂ → ℝ → ℂ := fun x t => q ((t : ℂ) * x) + x * (deriv q ((t : ℂ) * x) * t)
  have hsegρ : ∀ x ∈ ball z ε, ∀ t ∈ Icc (0 : ℝ) 1,
      (t : ℂ) * x ∈ closedBall (0 : ℂ) ρ := by
    intro x hx t ht
    rw [mem_closedBall, dist_zero_right, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg ht.1]
    exact (mul_le_mul_of_nonneg_right ht.2 (norm_nonneg x)).trans (by simpa using hxρ x hx)
  have hFint : ∀ x ∈ ball z ε, IntervalIntegrable (F x) volume 0 1 := by
    intro x hx
    apply ContinuousOn.intervalIntegrable
    simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using
      continuousOn_disk_integrand hq ((hxρ x hx).trans_lt hρ)
  have hF'cont : ContinuousOn (F' z) (Icc (0 : ℝ) 1) := by
    have hmap : MapsTo (fun t : ℝ => (t : ℂ) * z) (Icc (0 : ℝ) 1) (ball (0 : ℂ) R) :=
      fun t ht => disk_segment_mem hzR ht
    have harg : ContinuousOn (fun t : ℝ => (t : ℂ) * z) (Icc (0 : ℝ) 1) :=
      (Complex.continuous_ofReal.mul continuous_const).continuousOn
    exact (hq.continuousOn.comp harg hmap).add
      (continuousOn_const.mul ((hq'.continuousOn.comp harg hmap).mul
        Complex.continuous_ofReal.continuousOn))
  have hdiff : ∀ x ∈ ball z ε, ∀ t ∈ Icc (0 : ℝ) 1,
      HasDerivAt (fun x => F x t) (F' x t) x := by
    intro x hx t ht
    have htx := hρsub (hsegρ x hx t ht)
    have hdq := hq.hasDerivAt (isOpen_ball.mem_nhds htx)
    simpa only [F, F', Function.comp_def, id_eq, one_mul, mul_one] using
      (hasDerivAt_id x).mul (hdq.comp x ((hasDerivAt_id x).const_mul (t : ℂ)))
  have hFbound : ∀ x ∈ ball z ε, ∀ t ∈ Icc (0 : ℝ) 1, ‖F' x t‖ ≤ M + ρ * N := by
    intro x hx t ht
    have htx := hsegρ x hx t ht
    have hMq : ‖q ((t : ℂ) * x)‖ ≤ M := hM ⟨_, htx, rfl⟩
    have hNq : ‖deriv q ((t : ℂ) * x)‖ ≤ N := hN ⟨_, htx, rfl⟩
    have hNp : 0 ≤ N := (norm_nonneg _).trans hNq
    have htNorm : ‖(t : ℂ)‖ ≤ 1 := by simpa [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht.1] using ht.2
    have hprod : ‖deriv q ((t : ℂ) * x)‖ * ‖(t : ℂ)‖ ≤ N := by
      simpa only [mul_one] using mul_le_mul hNq htNorm (norm_nonneg _) hNp
    calc
      ‖F' x t‖ ≤ ‖q ((t : ℂ) * x)‖ + ‖x * (deriv q ((t : ℂ) * x) * t)‖ := norm_add_le _ _
      _ ≤ M + ρ * N := by
        rw [norm_mul, norm_mul]
        exact add_le_add hMq (mul_le_mul (hxρ x hx) hprod (by positivity) hρpos.le)
  have hzε : z ∈ ball z ε := mem_ball_self hε
  have hF'int : IntervalIntegrable (F' z) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hF'cont
  obtain ⟨hint, hderiv⟩ := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := F) (F' := F') (bound := fun _ => M + ρ * N) hε
    (by
      filter_upwards [ball_mem_nhds z hε] with x hx
      exact (intervalIntegrable_iff.mp (hFint x hx)).aestronglyMeasurable)
    (hFint z hzε) (intervalIntegrable_iff.mp hF'int).aestronglyMeasurable
    (by
      filter_upwards with t ht x hx
      exact hFbound x hx t (Ioc_subset_Icc_self (by simpa only [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using ht)))
    intervalIntegrable_const
    (by
      filter_upwards with t ht x hx
      exact hdiff x hx t (Ioc_subset_Icc_self (by simpa only [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using ht)))
  have hFTC : (∫ t in (0 : ℝ)..1, F' z t) = q z := by
    have hd : ∀ t ∈ uIcc (0 : ℝ) 1,
        HasDerivAt (fun t : ℝ => (t : ℂ) * q ((t : ℂ) * z)) (F' z t) t := by
      intro t ht
      have ht' : t ∈ Icc (0 : ℝ) 1 := by simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using ht
      have hqderiv := hq.hasDerivAt (isOpen_ball.mem_nhds (disk_segment_mem hzR ht'))
      have h := (hasDerivAt_id (t : ℂ)).mul
        (hqderiv.comp (t : ℂ) ((hasDerivAt_id (t : ℂ)).mul_const z))
      convert h.comp_ofReal using 1
      dsimp [F']
      ring
    simpa [F'] using intervalIntegral.integral_eq_sub_of_hasDerivAt hd hint
  rw [hFTC] at hderiv
  exact hderiv

@[simp] theorem diskPrimitive_zero (q : ℂ → ℂ) : diskPrimitive q 0 = 0 := by
  simp [diskPrimitive]

theorem differentiableOn_diskPrimitive {q : ℂ → ℂ} {R : ℝ}
    (hq : DifferentiableOn ℂ q (ball (0 : ℂ) R)) :
    DifferentiableOn ℂ (diskPrimitive q) (ball (0 : ℂ) R) :=
  fun _ hz => (hasDerivAt_diskPrimitive hq hz).differentiableAt.differentiableWithinAt

/-- A zero-free holomorphic function on a disk has a holomorphic logarithm.
The logarithm is constructed from the radial primitive of `f'/f`. -/
theorem exists_disk_logarithm {f : ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (hf : DifferentiableOn ℂ f (ball (0 : ℂ) R))
    (hfn : ∀ z ∈ ball (0 : ℂ) R, f z ≠ 0) :
    ∃ L : ℂ → ℂ, DifferentiableOn ℂ L (ball (0 : ℂ) R) ∧
      ∀ z ∈ ball (0 : ℂ) R, Complex.exp (L z) = f z := by
  let q : ℂ → ℂ := fun z => deriv f z / f z
  have hq : DifferentiableOn ℂ q (ball (0 : ℂ) R) :=
    (hf.deriv isOpen_ball).div hf hfn
  let g : ℂ → ℂ := fun z => f z * Complex.exp (-diskPrimitive q z)
  have hgd : ∀ z ∈ ball (0 : ℂ) R, HasDerivAt g 0 z := by
    intro z hz
    have hfd := hf.hasDerivAt (isOpen_ball.mem_nhds hz)
    have hpd := hasDerivAt_diskPrimitive hq hz
    have hderiv := hfd.mul hpd.neg.cexp
    convert hderiv using 1
    dsimp [q]
    field_simp [hfn z hz]
    ring
  have hgz : ∀ z ∈ ball (0 : ℂ) R, g z = f 0 := by
    intro z hz
    have h := isOpen_ball.is_const_of_deriv_eq_zero (convex_ball (0 : ℂ) R).isPreconnected
      (fun z hz => (hgd z hz).differentiableAt.differentiableWithinAt)
      (fun z hz => (hgd z hz).deriv) hz (mem_ball_self hR)
    simpa only [g, diskPrimitive_zero, neg_zero, Complex.exp_zero, mul_one] using h
  have hf0 : f 0 ≠ 0 := hfn 0 (mem_ball_self hR)
  refine ⟨fun z => diskPrimitive q z + Complex.log (f 0),
    (differentiableOn_diskPrimitive hq).add_const _, ?_⟩
  intro z hz
  rw [Complex.exp_add, Complex.exp_log hf0]
  have h := hgz z hz
  dsimp only [g] at h
  rw [Complex.exp_neg, ← div_eq_mul_inv] at h
  exact (mul_comm _ _).trans ((div_eq_iff (Complex.exp_ne_zero _)).mp h).symm

/-- The logarithm of the norm is the real part of that holomorphic logarithm. -/
theorem exists_disk_log_norm {f : ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (hf : DifferentiableOn ℂ f (ball (0 : ℂ) R))
    (hfn : ∀ z ∈ ball (0 : ℂ) R, f z ≠ 0) :
    ∃ L : ℂ → ℂ, DifferentiableOn ℂ L (ball (0 : ℂ) R) ∧
      ∀ z ∈ ball (0 : ℂ) R, Real.log ‖f z‖ = (L z).re := by
  obtain ⟨L, hL, hexp⟩ := exists_disk_logarithm hR hf hfn
  refine ⟨L, hL, ?_⟩
  intro z hz
  rw [← hexp z hz, Complex.norm_exp, Real.log_exp]

/-- Removing the full finite order of a zero leaves a holomorphic function
nonzero at that zero. This is a local analytic factorization extended by division
at every other point of the disk. -/
theorem remove_disk_zero {f : ℂ → ℂ} {R : ℝ}
    (hf : DifferentiableOn ℂ f (ball (0 : ℂ) R)) {a w : ℂ}
    (ha : a ∈ ball (0 : ℂ) R) (hfa : f a = 0)
    (hw : w ∈ ball (0 : ℂ) R) (hfw : f w ≠ 0) :
    ∃ n : ℕ, 0 < n ∧ ∃ g : ℂ → ℂ,
      DifferentiableOn ℂ g (ball (0 : ℂ) R) ∧ g a ≠ 0 ∧
        ∀ z ∈ ball (0 : ℂ) R, f z = (z - a)^n * g z := by
  have han : AnalyticOnNhd ℂ f (ball (0 : ℂ) R) := hf.analyticOnNhd isOpen_ball
  have hnot : ¬∀ᶠ z in 𝓝 a, f z = 0 := by
    intro h
    have heq := han.eqOn_of_preconnected_of_eventuallyEq analyticOnNhd_const
      (convex_ball (0 : ℂ) R).isPreconnected ha h
    exact hfw (heq hw)
  obtain ⟨n, j, hj, hja, heq⟩ :=
    (han a ha).exists_eventuallyEq_pow_smul_nonzero_iff.mpr hnot
  have hapos : 0 < n := by
    by_contra hn
    have hn0 : n = 0 := by omega
    have hat := (show f =ᶠ[𝓝 a] (fun z => (z - a)^n • j z) from heq).eq_of_nhds
    exact hja (by simpa [hn0, hfa] using hat.symm)
  let g : ℂ → ℂ := fun z => if z = a then j a else f z / (z - a)^n
  have hgj : g =ᶠ[𝓝 a] j := by
    filter_upwards [heq] with z hz
    dsimp only [g]
    by_cases hza : z = a
    · simp [hza]
    · rw [if_neg hza]
      simp only [smul_eq_mul] at hz
      rw [hz]
      exact mul_div_cancel_left₀ _ (pow_ne_zero n (sub_ne_zero.mpr hza))
  have hgd : DifferentiableOn ℂ g (ball (0 : ℂ) R) := by
    intro z hz
    by_cases hza : z = a
    · subst z
      exact (hj.congr hgj.symm).differentiableAt.differentiableWithinAt
    · have hquot := (hf.differentiableAt (isOpen_ball.mem_nhds hz)).div
        ((differentiableAt_id.sub_const a).pow n) (pow_ne_zero n (sub_ne_zero.mpr hza))
      apply (hquot.congr_of_eventuallyEq ?_).differentiableWithinAt
      filter_upwards [eventually_ne_nhds hza] with z hz
      simp only [g, if_neg hz, id_eq]
  refine ⟨n, hapos, g, hgd, by simpa only [g, if_pos rfl] using hja, ?_⟩
  intro z _
  by_cases hza : z = a
  · simp [hza, hfa, hapos.ne']
  · dsimp only [g]
    rw [if_neg hza]
    field_simp [pow_ne_zero n (sub_ne_zero.mpr hza)]

/-- A nonzero holomorphic function has finitely many zeros in each smaller
closed disk, using the pinned isolated-zero theorem. -/
theorem disk_finite_zeros {f : ℂ → ℂ} {R ρ : ℝ} (hρR : ρ < R)
    (hf : DifferentiableOn ℂ f (ball (0 : ℂ) R)) {w : ℂ}
    (hw : w ∈ ball (0 : ℂ) R) (hfw : f w ≠ 0) :
    (closedBall (0 : ℂ) ρ ∩ {z : ℂ | f z = 0}).Finite := by
  have ha : AnalyticOnNhd ℂ f (ball (0 : ℂ) R) := hf.analyticOnNhd isOpen_ball
  have hcod : {z : ℂ | f z ≠ 0} ∈ Filter.codiscreteWithin (ball (0 : ℂ) R) := by
    rcases ha.eqOn_zero_or_eventually_ne_zero_of_preconnected
        (convex_ball (0 : ℂ) R).isPreconnected with h | h
    · exact False.elim (hfw (h hw))
    · exact h
  have hsub : closedBall (0 : ℂ) ρ ⊆ ball (0 : ℂ) R := closedBall_subset_ball hρR
  have hclosed : IsClosed (closedBall (0 : ℂ) ρ ∩ {z : ℂ | f z = 0}) := by
    simpa only [Set.preimage, Set.mem_singleton_iff] using
      (hf.continuousOn.mono hsub).preimage_isClosed_of_isClosed isClosed_closedBall
        (isClosed_singleton (x := (0 : ℂ)))
  have hcompact : IsCompact (closedBall (0 : ℂ) ρ ∩ {z : ℂ | f z = 0}) :=
    (isCompact_closedBall (0 : ℂ) ρ).of_isClosed_subset hclosed Set.inter_subset_left
  apply hcompact.finite
  apply DiscreteTopology.of_subset (discreteTopology_of_codiscreteWithin hcod)
  intro z hz
  exact ⟨by simpa using hz.2, closedBall_subset_ball hρR hz.1⟩

private theorem factor_disk_zeros_on_finite_set {R ρ : ℝ} (hρR : ρ < R) {w : ℂ}
    (hw : w ∈ ball (0 : ℂ) R) (S : Set ℂ) (hS : S.Finite) :
    ∀ (f : ℂ → ℂ), DifferentiableOn ℂ f (ball (0 : ℂ) R) → f w ≠ 0 →
      S ⊆ ball (0 : ℂ) ρ → (∀ z ∈ ball (0 : ℂ) ρ, f z = 0 → z ∈ S) →
      ∃ l : List (ℂ × ℕ), (∀ p ∈ l, p.1 ∈ ball (0 : ℂ) ρ ∧ 0 < p.2) ∧
        ∃ g : ℂ → ℂ, DifferentiableOn ℂ g (ball (0 : ℂ) R) ∧
          (∀ z ∈ ball (0 : ℂ) ρ, g z ≠ 0) ∧
          ∀ z ∈ ball (0 : ℂ) R, f z = (l.map (fun p => (z - p.1)^p.2)).prod * g z := by
  induction S, hS using Set.Finite.induction_on with
  | empty =>
      intro f hf _ _ hzero
      refine ⟨[], by simp, f, hf, ?_, ?_⟩
      · intro z hz hfz
        exact Set.not_mem_empty z (hzero z hz hfz)
      · simp
  | @insert a S ha hS ih =>
      intro f hf hfw hSb hzero
      have hSb' : S ⊆ ball (0 : ℂ) ρ := fun z hz => hSb (Set.mem_insert_of_mem a hz)
      by_cases hfa : f a = 0
      · have haρ : a ∈ ball (0 : ℂ) ρ := hSb (Set.mem_insert a S)
        obtain ⟨n, hn, j, hj, hja, hfj⟩ := remove_disk_zero hf
          (ball_subset_ball hρR.le haρ) hfa hw hfw
        have hjw : j w ≠ 0 := by
          intro heq
          exact hfw (by rw [hfj w hw, heq, mul_zero])
        have hjzeros : ∀ z ∈ ball (0 : ℂ) ρ, j z = 0 → z ∈ S := by
          intro z hz hjz
          have hfz : f z = 0 := by rw [hfj z (ball_subset_ball hρR.le hz), hjz, mul_zero]
          rcases Set.mem_insert_iff.mp (hzero z hz hfz) with hza | hzS
          · exact False.elim (hja (hza ▸ hjz))
          · exact hzS
        obtain ⟨l, hl, g, hg, hgn, hjg⟩ := ih j hj hjw hSb' hjzeros
        refine ⟨(a, n) :: l, ?_, g, hg, hgn, ?_⟩
        · intro p hp
          rcases List.mem_cons.mp hp with rfl | hp
          · exact ⟨haρ, hn⟩
          · exact hl p hp
        · intro z hz
          rw [hfj z hz, hjg z hz]
          simp only [List.map_cons, List.prod_cons]
          ring
      · apply ih f hf hfw hSb'
        intro z hz hfz
        rcases Set.mem_insert_iff.mp (hzero z hz hfz) with hza | hzS
        · exact False.elim (hfa (hza ▸ hfz))
        · exact hzS

/-- Factoring all zeros in a smaller disk leaves a zero-free holomorphic
remainder there, with finitely many linear factors and their actual orders. -/
theorem factor_disk_zeros {f : ℂ → ℂ} {R ρ : ℝ} (hρR : ρ < R)
    (hf : DifferentiableOn ℂ f (ball (0 : ℂ) R)) {w : ℂ}
    (hw : w ∈ ball (0 : ℂ) R) (hfw : f w ≠ 0) :
    ∃ l : List (ℂ × ℕ), (∀ p ∈ l, p.1 ∈ ball (0 : ℂ) ρ ∧ 0 < p.2) ∧
      ∃ g : ℂ → ℂ, DifferentiableOn ℂ g (ball (0 : ℂ) R) ∧
        (∀ z ∈ ball (0 : ℂ) ρ, g z ≠ 0) ∧
        ∀ z ∈ ball (0 : ℂ) R, f z = (l.map (fun p => (z - p.1)^p.2)).prod * g z := by
  let S : Set ℂ := ball (0 : ℂ) ρ ∩ {z : ℂ | f z = 0}
  have hS : S.Finite := (disk_finite_zeros hρR hf hw hfw).subset
    (Set.inter_subset_inter_left _ ball_subset_closedBall)
  exact factor_disk_zeros_on_finite_set hρR hw S hS f hf hfw
    Set.inter_subset_left (fun z hz hfz => ⟨hz, hfz⟩)

end RieszEuclidean.CompleteMinimal
