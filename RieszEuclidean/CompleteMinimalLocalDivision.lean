import RieszEuclidean.CompleteMinimalQuadric
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

/-! Local analytic coordinate graphs for the positive-radius complex quadrics. -/

noncomputable section
open scoped Topology ENNReal NNReal
open Set Filter

namespace RieszEuclidean.CompleteMinimal

/-- The square of the selected coordinate on the radius-`r` complex quadric. -/
def quadricRadicand {n : ℕ} (r : ℝ) (j : Fin n) (z : Fin n → ℂ) : ℂ :=
  (r : ℂ) ^ 2 - ∑ i ∈ Finset.univ.erase j, z i ^ 2

theorem quadricRadicand_analyticAt {n : ℕ} (r : ℝ) (j : Fin n) (z : Fin n → ℂ) :
    AnalyticAt ℂ (quadricRadicand r j) z := by
  unfold quadricRadicand
  exact analyticAt_const.sub (Finset.analyticAt_sum _ (fun i _ =>
    ((ContinuousLinearMap.proj (R := ℂ) i).analyticAt z).pow 2))

theorem squareSum_sub_eq_coordinate {n : ℕ} (r : ℝ) (j : Fin n) (z : Fin n → ℂ) :
    squareSum z - (r : ℂ) ^ 2 = z j ^ 2 - quadricRadicand r j z := by
  unfold squareSum quadricRadicand
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j)]
  ring

theorem quadricRadicand_at_quadric {n : ℕ} (r : ℝ) (j : Fin n) (z : Fin n → ℂ)
    (hz : squareSum z = (r : ℂ) ^ 2) : quadricRadicand r j z = z j ^ 2 := by
  have h := squareSum_sub_eq_coordinate r j z
  rw [hz, sub_self] at h
  exact (sub_eq_zero.mp h.symm).symm

/-- The local square-root branch taking value `a` when the radicand is `a²`. -/
def quadricRoot {n : ℕ} (r : ℝ) (j : Fin n) (a : ℂ) (z : Fin n → ℂ) : ℂ :=
  a * Complex.exp (Complex.log (quadricRadicand r j z / a ^ 2) / 2)

/-- The open slit-plane domain of the selected square-root branch. -/
def quadricRootDomain {n : ℕ} (r : ℝ) (j : Fin n) (a : ℂ) : Set (Fin n → ℂ) :=
  (fun z => quadricRadicand r j z / a ^ 2) ⁻¹' Complex.slitPlane

theorem quadricRootDomain_isOpen {n : ℕ} (r : ℝ) (j : Fin n) (a : ℂ) :
    IsOpen (quadricRootDomain r j a) := by
  apply Complex.isOpen_slitPlane.preimage
  have hg : Continuous (quadricRadicand r j) := continuous_iff_continuousAt.mpr
    (fun z => (quadricRadicand_analyticAt r j z).continuousAt)
  exact hg.div_const _

theorem quadricRoot_analyticOnNhd {n : ℕ} (r : ℝ) (j : Fin n) (a : ℂ) (ha : a ≠ 0) :
    AnalyticOnNhd ℂ (quadricRoot r j a) (quadricRootDomain r j a) := by
  intro z hz
  unfold quadricRoot
  apply analyticAt_const.mul
  exact (((quadricRadicand_analyticAt r j z).fun_div analyticAt_const
    (pow_ne_zero 2 ha)).clog hz).fun_div analyticAt_const (by norm_num) |>.cexp

theorem quadricRoot_sq {n : ℕ} (r : ℝ) (j : Fin n) (a : ℂ) (ha : a ≠ 0)
    (z : Fin n → ℂ) (hz : z ∈ quadricRootDomain r j a) :
    quadricRoot r j a z ^ 2 = quadricRadicand r j z := by
  unfold quadricRoot
  rw [mul_pow, ← Complex.exp_nat_mul]
  norm_num only [Nat.cast_ofNat]
  have htwo : (2 : ℂ) * (Complex.log (quadricRadicand r j z / a ^ 2) / 2) =
      Complex.log (quadricRadicand r j z / a ^ 2) := by ring
  rw [htwo, Complex.exp_log (Complex.slitPlane_ne_zero hz)]
  field_simp

theorem quadricRoot_at_quadric {n : ℕ} (r : ℝ) (j : Fin n) (z : Fin n → ℂ)
    (hz : squareSum z = (r : ℂ) ^ 2) (hj : z j ≠ 0) :
    z ∈ quadricRootDomain r j (z j) ∧ quadricRoot r j (z j) z = z j := by
  have hg := quadricRadicand_at_quadric r j z hz
  constructor
  · change quadricRadicand r j z / z j ^ 2 ∈ Complex.slitPlane
    rw [hg, div_self (pow_ne_zero 2 hj)]
    exact Complex.one_mem_slitPlane
  · simp [quadricRoot, hg, div_self (pow_ne_zero 2 hj)]

theorem quadric_local_factorization {n : ℕ} (r : ℝ) (j : Fin n) (a : ℂ) (ha : a ≠ 0)
    (z : Fin n → ℂ) (hz : z ∈ quadricRootDomain r j a) :
    squareSum z - (r : ℂ) ^ 2 =
      (z j - quadricRoot r j a z) * (z j + quadricRoot r j a z) := by
  rw [squareSum_sub_eq_coordinate, ← quadricRoot_sq r j a ha z hz]
  ring

theorem quadricRadicand_update {n : ℕ} (r : ℝ) (j : Fin n) (z : Fin n → ℂ) (v : ℂ) :
    quadricRadicand r j (Function.update z j v) = quadricRadicand r j z := by
  unfold quadricRadicand
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]

theorem quadricRoot_update {n : ℕ} (r : ℝ) (j : Fin n) (a : ℂ) (z : Fin n → ℂ) (v : ℂ) :
    quadricRoot r j a (Function.update z j v) = quadricRoot r j a z := by
  simp only [quadricRoot, quadricRadicand_update]

/-- Subtract the analytic graph from the selected coordinate. -/
def quadricFlatten {n : ℕ} (r : ℝ) (j : Fin n) (a : ℂ) (z : Fin n → ℂ) : Fin n → ℂ :=
  Function.update z j (z j - quadricRoot r j a z)

/-- Add the analytic graph back to the selected coordinate. -/
def quadricUnflatten {n : ℕ} (r : ℝ) (j : Fin n) (a : ℂ) (z : Fin n → ℂ) : Fin n → ℂ :=
  Function.update z j (z j + quadricRoot r j a z)

@[simp] theorem quadricFlatten_unflatten {n : ℕ} (r : ℝ) (j : Fin n) (a : ℂ)
    (z : Fin n → ℂ) : quadricFlatten r j a (quadricUnflatten r j a z) = z := by
  simp [quadricFlatten, quadricUnflatten, quadricRoot_update]

@[simp] theorem quadricUnflatten_flatten {n : ℕ} (r : ℝ) (j : Fin n) (a : ℂ)
    (z : Fin n → ℂ) : quadricUnflatten r j a (quadricFlatten r j a z) = z := by
  simp [quadricFlatten, quadricUnflatten, quadricRoot_update]

theorem quadricFlatten_analyticOnNhd {n : ℕ} (r : ℝ) (j : Fin n) (a : ℂ) (ha : a ≠ 0) :
    AnalyticOnNhd ℂ (quadricFlatten r j a) (quadricRootDomain r j a) := by
  intro z hz
  apply AnalyticAt.pi
  intro i
  by_cases hi : i = j
  · subst i
    simp only [quadricFlatten, Function.update_self]
    exact ((ContinuousLinearMap.proj (R := ℂ) j).analyticAt z).sub
      (quadricRoot_analyticOnNhd r j a ha z hz)
  · simp only [quadricFlatten, Function.update_of_ne hi]
    exact (ContinuousLinearMap.proj (R := ℂ) i).analyticAt z

theorem quadricUnflatten_analyticOnNhd {n : ℕ} (r : ℝ) (j : Fin n) (a : ℂ) (ha : a ≠ 0) :
    AnalyticOnNhd ℂ (quadricUnflatten r j a) (quadricRootDomain r j a) := by
  intro z hz
  apply AnalyticAt.pi
  intro i
  by_cases hi : i = j
  · subst i
    simp only [quadricUnflatten, Function.update_self]
    exact ((ContinuousLinearMap.proj (R := ℂ) j).analyticAt z).add
      (quadricRoot_analyticOnNhd r j a ha z hz)
  · simp only [quadricUnflatten, Function.update_of_ne hi]
    exact (ContinuousLinearMap.proj (R := ℂ) i).analyticAt z

theorem quadricUnflatten_mem_rootDomain {n : ℕ} (r : ℝ) (j : Fin n) (a : ℂ)
    (z : Fin n → ℂ) : quadricUnflatten r j a z ∈ quadricRootDomain r j a ↔
      z ∈ quadricRootDomain r j a := by
  simp only [quadricUnflatten, quadricRootDomain, mem_preimage, quadricRadicand_update]

theorem quadricUnflatten_factorization {n : ℕ} (r : ℝ) (j : Fin n) (a : ℂ) (ha : a ≠ 0)
    (z : Fin n → ℂ) (hz : z ∈ quadricRootDomain r j a) :
    squareSum (quadricUnflatten r j a z) - (r : ℂ) ^ 2 =
      z j * (z j + 2 * quadricRoot r j a z) := by
  rw [quadric_local_factorization r j a ha _ ((quadricUnflatten_mem_rootDomain r j a z).mpr hz)]
  simp only [quadricUnflatten, Function.update_self, quadricRoot_update]
  ring

/-- At a nonsingular quadric point, the second factor in the graph factorization is a unit
on a whole open neighborhood. -/
theorem quadric_root_unit_neighborhood {n : ℕ} (r : ℝ) (j : Fin n) (z₀ : Fin n → ℂ)
    (hz₀ : squareSum z₀ = (r : ℂ) ^ 2) (hj : z₀ j ≠ 0) :
    ∃ U : Set (Fin n → ℂ), IsOpen U ∧ z₀ ∈ U ∧
      AnalyticOnNhd ℂ (quadricRoot r j (z₀ j)) U ∧
      ∀ z ∈ U, quadricRoot r j (z₀ j) z ^ 2 = quadricRadicand r j z ∧
        z j + quadricRoot r j (z₀ j) z ≠ 0 := by
  let D := quadricRootDomain r j (z₀ j)
  let b := quadricRoot r j (z₀ j)
  let U := D ∩ (fun z => z j + b z) ⁻¹' ({0}ᶜ : Set ℂ)
  have hD : IsOpen D := quadricRootDomain_isOpen r j (z₀ j)
  have hb : AnalyticOnNhd ℂ b D := quadricRoot_analyticOnNhd r j (z₀ j) hj
  have hc : ContinuousOn (fun z => z j + b z) D :=
    (continuous_apply j).continuousOn.add hb.continuousOn
  obtain ⟨hzD, hb₀⟩ := quadricRoot_at_quadric r j z₀ hz₀ hj
  have hunit : z₀ j + b z₀ ≠ 0 := by
    change z₀ j + quadricRoot r j (z₀ j) z₀ ≠ 0
    rw [hb₀, ← two_mul]
    exact mul_ne_zero (by norm_num) hj
  refine ⟨U, hc.isOpen_inter_preimage hD isClosed_singleton.isOpen_compl,
    ⟨hzD, hunit⟩, hb.mono inter_subset_left, ?_⟩
  intro z hz
  exact ⟨quadricRoot_sq r j (z₀ j) hj z hz.1, hz.2⟩

section TaylorDivision

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- A bounded Taylor-coefficient division operator. It telescopes the difference between
a homogeneous polynomial at `z` and at `P z`, with `e` the removed coordinate direction. -/
def telescopicDivisionOperator (P : E →L[ℂ] E) (e : E) (hP : ‖P‖ ≤ 1) (he : ‖e‖ ≤ 1) :
    (m : ℕ) → {D : (E [×(m + 1)]→L[ℂ] ℂ) →L[ℂ] (E [×m]→L[ℂ] ℂ) // ‖D‖ ≤ m + 1}
  | 0 => by
    let L : (E [×1]→L[ℂ] ℂ) →ₗ[ℂ] (E [×0]→L[ℂ] ℂ) :=
      { toFun := fun p => p.curryLeft e
        map_add' := by
          intro p q
          ext v
          simp only [ContinuousMultilinearMap.curryLeft_apply,
            ContinuousMultilinearMap.add_apply]
        map_smul' := by
          intro c p
          ext v
          simp only [ContinuousMultilinearMap.curryLeft_apply,
            ContinuousMultilinearMap.smul_apply, RingHom.id_apply] }
    have hL : ∀ p, ‖L p‖ ≤ 1 * ‖p‖ := by
      intro p
      change ‖p.curryLeft e‖ ≤ _
      calc
        ‖p.curryLeft e‖ ≤ ‖p.curryLeft‖ * ‖e‖ := p.curryLeft.le_opNorm e
        _ ≤ ‖p‖ * 1 := by rw [ContinuousMultilinearMap.curryLeft_norm]; gcongr
        _ = 1 * ‖p‖ := by ring
    refine ⟨L.mkContinuous 1 hL, ?_⟩
    simpa using LinearMap.mkContinuous_norm_le L (C := 1) (by norm_num) hL
  | m + 1 => by
    let D := (telescopicDivisionOperator P e hP he m).val
    have hD : ‖D‖ ≤ m + 1 := (telescopicDivisionOperator P e hP he m).property
    let L : (E [×(m + 1 + 1)]→L[ℂ] ℂ) →ₗ[ℂ] (E [×(m + 1)]→L[ℂ] ℂ) :=
      { toFun := fun p => p.curryLeft e + (D.comp (p.curryLeft.comp P)).uncurryLeft
        map_add' := by
          intro p q
          have hcur : (p + q).curryLeft = p.curryLeft + q.curryLeft := by
            ext x v
            simp only [ContinuousMultilinearMap.curryLeft_apply,
              ContinuousLinearMap.add_apply, ContinuousMultilinearMap.add_apply]
          ext v
          simp only [ContinuousMultilinearMap.add_apply,
            ContinuousMultilinearMap.curryLeft_apply,
            ContinuousLinearMap.uncurryLeft_apply, ContinuousLinearMap.comp_apply,
            hcur, ContinuousLinearMap.add_apply, map_add]
          ring
        map_smul' := by
          intro c p
          have hcur : (c • p).curryLeft = c • p.curryLeft := by
            ext x v
            simp only [ContinuousMultilinearMap.curryLeft_apply,
              ContinuousLinearMap.smul_apply, ContinuousMultilinearMap.smul_apply]
          ext v
          simp only [ContinuousMultilinearMap.smul_apply,
            ContinuousMultilinearMap.add_apply, ContinuousMultilinearMap.curryLeft_apply,
            ContinuousLinearMap.uncurryLeft_apply, ContinuousLinearMap.comp_apply,
            hcur, ContinuousLinearMap.smul_apply,
            map_smul, RingHom.id_apply, smul_add] }
    have hL : ∀ p, ‖L p‖ ≤ ((m + 1 + 1 : ℕ) : ℝ) * ‖p‖ := by
      intro p
      change ‖p.curryLeft e + (D.comp (p.curryLeft.comp P)).uncurryLeft‖ ≤ _
      calc
        _ ≤ ‖p.curryLeft e‖ + ‖(D.comp (p.curryLeft.comp P)).uncurryLeft‖ := norm_add_le _ _
        _ ≤ ‖p‖ + ((m : ℝ) + 1) * ‖p‖ := by
          apply add_le_add
          · calc
              ‖p.curryLeft e‖ ≤ ‖p.curryLeft‖ * ‖e‖ := p.curryLeft.le_opNorm e
              _ ≤ ‖p‖ * 1 := by rw [ContinuousMultilinearMap.curryLeft_norm]; gcongr
              _ = ‖p‖ := mul_one _
          · rw [ContinuousLinearMap.uncurryLeft_norm]
            calc
              ‖D.comp (p.curryLeft.comp P)‖ ≤ ‖D‖ * ‖p.curryLeft.comp P‖ :=
                ContinuousLinearMap.opNorm_comp_le _ _
              _ ≤ ((m : ℝ) + 1) * (‖p‖ * 1) := by
                apply mul_le_mul
                · exact hD
                · calc
                    ‖p.curryLeft.comp P‖ ≤ ‖p.curryLeft‖ * ‖P‖ :=
                      ContinuousLinearMap.opNorm_comp_le _ _
                    _ ≤ ‖p‖ * 1 := by rw [ContinuousMultilinearMap.curryLeft_norm]; gcongr
                · exact norm_nonneg (p.curryLeft.comp P)
                · positivity
              _ = ((m : ℝ) + 1) * ‖p‖ := by rw [mul_one]
        _ = _ := by push_cast; ring
    refine ⟨L.mkContinuous ((m + 1 + 1 : ℕ) : ℝ) hL, ?_⟩
    simpa using LinearMap.mkContinuous_norm_le L (C := ((m + 1 + 1 : ℕ) : ℝ))
      (by positivity) hL

theorem telescopicDivisionOperator_eval (P : E →L[ℂ] E) (e : E)
    (hP : ‖P‖ ≤ 1) (he : ‖e‖ ≤ 1) (ℓ : E →L[ℂ] ℂ)
    (hdecomp : ∀ z, z = P z + ℓ z • e) (m : ℕ)
    (p : E [×(m + 1)]→L[ℂ] ℂ) (z : E) :
    ℓ z * (telescopicDivisionOperator P e hP he m).val p (fun _ => z) =
      p (fun _ => z) - p (fun _ => P z) := by
  induction m with
  | zero =>
    change ℓ z * p (Fin.cons e (fun _ : Fin 0 => z)) = _
    have hcons : ∀ v : E, Fin.cons v (fun _ : Fin 0 => z) = (fun _ : Fin 1 => v) := by
      intro v
      funext i
      exact Fin.cases rfl (fun i => Fin.elim0 i) i
    rw [← smul_eq_mul, ← p.cons_smul, hcons]
    have h := p.cons_add (fun _ : Fin 0 => z) (P z) (ℓ z • e)
    simp only [hcons, ← hdecomp z] at h
    exact eq_sub_of_add_eq' h.symm
  | succ m ih =>
    change ℓ z * (p.curryLeft e (fun _ => z) +
      (telescopicDivisionOperator P e hP he m).val (p.curryLeft (P z)) (fun _ => z)) = _
    rw [mul_add, ih]
    simp only [ContinuousMultilinearMap.curryLeft_apply]
    rw [← smul_eq_mul, ← p.cons_smul]
    have hzcons : Fin.cons z (fun _ : Fin (m + 1) => z) = (fun _ => z) := by
      funext i
      exact Fin.cases rfl (fun _ => rfl) i
    have hPcons : Fin.cons (P z) (fun _ : Fin (m + 1) => P z) = (fun _ => P z) := by
      funext i
      exact Fin.cases rfl (fun _ => rfl) i
    have h := p.cons_add (fun _ : Fin (m + 1) => z) (P z) (ℓ z • e)
    rw [← hdecomp z, hzcons] at h
    rw [hPcons]
    linear_combination -h

/-- The convergent quotient series obtained by applying the coefficient division operators. -/
def telescopicDivisionSeries (P : E →L[ℂ] E) (e : E) (hP : ‖P‖ ≤ 1) (he : ‖e‖ ≤ 1)
    (p : FormalMultilinearSeries ℂ E ℂ) : FormalMultilinearSeries ℂ E ℂ :=
  fun m => (telescopicDivisionOperator P e hP he m).val (p (m + 1))

theorem telescopicDivisionSeries_radius_pos (P : E →L[ℂ] E) (e : E)
    (hP : ‖P‖ ≤ 1) (he : ‖e‖ ≤ 1) (p : FormalMultilinearSeries ℂ E ℂ)
    (hp : 0 < p.radius) : 0 < (telescopicDivisionSeries P e hP he p).radius := by
  obtain ⟨C, A, hC, hA, hpbound⟩ := p.le_mul_pow_of_radius_pos hp
  let q := telescopicDivisionSeries P e hP he p
  have hqbound : ∀ m : ℕ, ‖q m‖ ≤ C * A * (2 * A) ^ m := by
    intro m
    have hm : (m : ℝ) + 1 ≤ (2 : ℝ) ^ m := by
      exact_mod_cast (Nat.succ_le_of_lt (Nat.lt_two_pow_self (n := m)))
    calc
      ‖q m‖ ≤ ‖(telescopicDivisionOperator P e hP he m).val‖ * ‖p (m + 1)‖ :=
        (telescopicDivisionOperator P e hP he m).val.le_opNorm _
      _ ≤ ((m : ℝ) + 1) * (C * A ^ (m + 1)) := by
        apply mul_le_mul (telescopicDivisionOperator P e hP he m).property (hpbound _)
          (norm_nonneg _) (by positivity)
      _ ≤ (2 : ℝ) ^ m * (C * A ^ (m + 1)) := by gcongr
      _ = C * A * (2 * A) ^ m := by rw [mul_pow, pow_succ]; ring
  let ρ : ℝ≥0 := ⟨(2 * A)⁻¹, le_of_lt (inv_pos.mpr (by positivity))⟩
  have hρ : (0 : ℝ≥0∞) < ρ := by
    simp only [ENNReal.coe_pos]
    change (0 : ℝ) < (2 * A)⁻¹
    exact inv_pos.mpr (mul_pos (by norm_num) hA)
  apply lt_of_lt_of_le hρ
  apply q.le_radius_of_bound (C * A)
  intro m
  calc
    ‖q m‖ * (ρ : ℝ) ^ m ≤ (C * A * (2 * A) ^ m) * (ρ : ℝ) ^ m := by gcongr; exact hqbound m
    _ = C * A := by
      change (C * A * (2 * A) ^ m) * ((2 * A)⁻¹) ^ m = _
      rw [mul_assoc, ← mul_pow, mul_inv_cancel₀ (by positivity), one_pow, mul_one]

/-- Analytic Hadamard division by a contractive scalar coordinate, proved directly on
convergent multilinear Taylor series. -/
theorem analytic_hyperplane_division_zero (P : E →L[ℂ] E) (e : E)
    (hP : ‖P‖ ≤ 1) (he : ‖e‖ ≤ 1) (ℓ : E →L[ℂ] ℂ)
    (hdecomp : ∀ z, z = P z + ℓ z • e) (hℓP : ∀ z, ℓ (P z) = 0)
    (f : E → ℂ) (hf : AnalyticAt ℂ f 0)
    (hzero : ∀ᶠ z in 𝓝 (0 : E), ℓ z = 0 → f z = 0) :
    ∃ H : E → ℂ, AnalyticAt ℂ H 0 ∧ ∀ᶠ z in 𝓝 0, f z = ℓ z * H z := by
  obtain ⟨p, hp⟩ := hf
  let q := telescopicDivisionSeries P e hP he p
  have hqpos : 0 < q.radius := telescopicDivisionSeries_radius_pos P e hP he p hp.radius_pos
  have hq := q.hasFPowerSeriesOnBall hqpos
  refine ⟨q.sum, hq.analyticAt, ?_⟩
  have hpsum : ∀ᶠ z in 𝓝 (0 : E), HasSum (fun m => p m (fun _ => z)) (f z) := by
    simpa only [zero_add] using hp.eventually_hasSum
  have hqsum : ∀ᶠ z in 𝓝 (0 : E), HasSum (fun m => q m (fun _ => z)) (q.sum z) := by
    simpa only [zero_add] using hq.eventually_hasSum
  have ht : Tendsto P (𝓝 (0 : E)) (𝓝 0) := by simpa only [map_zero] using P.continuous.tendsto 0
  have hPsum := ht.eventually hpsum
  have hPzero := ht.eventually hzero
  filter_upwards [hpsum, hqsum, hPsum, hPzero] with z hsum hqsum hPsum hPzero
  have hdiff := hsum.sub hPsum
  have hfirst : p 0 (fun _ => z) - p 0 (fun _ => P z) = 0 := by
    apply sub_eq_zero.mpr
    congr 1
    exact funext fun i => Fin.elim0 i
  have htail : HasSum (fun m => p (m + 1) (fun _ => z) - p (m + 1) (fun _ => P z))
      (f z - f (P z)) := by
    apply (hasSum_nat_add_iff (f := fun m : ℕ => p m (fun _ => z) - p m (fun _ => P z)) 1).mpr
    simpa only [Finset.sum_range_one, hfirst, add_zero] using hdiff
  have hqmul := hqsum.mul_left (ℓ z)
  have hterms : (fun m => ℓ z * q m (fun _ => z)) =
      (fun m => p (m + 1) (fun _ => z) - p (m + 1) (fun _ => P z)) := by
    funext m
    exact telescopicDivisionOperator_eval P e hP he ℓ hdecomp m (p (m + 1)) z
  rw [hterms] at hqmul
  have h := htail.unique hqmul
  rw [hPzero (hℓP z), sub_zero] at h
  exact h

end TaylorDivision

/-- The contractive projection that zeros the chosen coordinate. -/
def eraseCoordinateCLM {n : ℕ} (j : Fin n) : (Fin n → ℂ) →L[ℂ] (Fin n → ℂ) :=
  ContinuousLinearMap.pi (fun i => if i = j then 0 else ContinuousLinearMap.proj i)

@[simp] theorem eraseCoordinateCLM_apply {n : ℕ} (j : Fin n) (z : Fin n → ℂ) (i : Fin n) :
    eraseCoordinateCLM j z i = if i = j then 0 else z i := by
  by_cases hi : i = j <;> simp [eraseCoordinateCLM, hi]

theorem eraseCoordinateCLM_norm_le {n : ℕ} (j : Fin n) : ‖eraseCoordinateCLM j‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro z
  rw [one_mul]
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg z)).mpr
  intro i
  rw [eraseCoordinateCLM_apply]
  split_ifs
  · exact (norm_zero : ‖(0 : ℂ)‖ = 0) ▸ norm_nonneg z
  · exact norm_le_pi_norm z i

/-- Analytic coordinate division at a point of a coordinate hyperplane. -/
theorem analytic_coordinate_division {n : ℕ} (j : Fin n) (w₀ : Fin n → ℂ) (hw₀ : w₀ j = 0)
    (f : (Fin n → ℂ) → ℂ) (hf : AnalyticAt ℂ f w₀)
    (hzero : ∀ᶠ w in 𝓝 w₀, w j = 0 → f w = 0) :
    ∃ H : (Fin n → ℂ) → ℂ, AnalyticAt ℂ H w₀ ∧
      ∀ᶠ w in 𝓝 w₀, f w = w j * H w := by
  let P := eraseCoordinateCLM j
  let e : Fin n → ℂ := Pi.single j 1
  let ℓ : (Fin n → ℂ) →L[ℂ] ℂ := ContinuousLinearMap.proj j
  have he : ‖e‖ ≤ 1 := by simp only [e, Pi.norm_single, norm_one, le_refl]
  have hdecomp : ∀ z, z = P z + ℓ z • e := by
    intro z
    funext i
    by_cases hi : i = j <;> simp [P, ℓ, e, hi]
  have hℓP : ∀ z, ℓ (P z) = 0 := by intro z; simp [P, ℓ]
  let g : (Fin n → ℂ) → ℂ := fun v => f (w₀ + v)
  have hg : AnalyticAt ℂ g 0 := by
    have ha : AnalyticAt ℂ (fun v : Fin n → ℂ => w₀ + v) 0 := analyticAt_const.fun_add analyticAt_id
    have hf' : AnalyticAt ℂ f (w₀ + 0) := by simpa only [add_zero] using hf
    exact hf'.comp ha
  have ht : Tendsto (fun v : Fin n → ℂ => w₀ + v) (𝓝 0) (𝓝 w₀) := by
    have hc : Continuous (fun v : Fin n → ℂ => w₀ + v) := continuous_const.add continuous_id
    simpa only [add_zero] using hc.tendsto (0 : Fin n → ℂ)
  have hgzero : ∀ᶠ v in 𝓝 (0 : Fin n → ℂ), ℓ v = 0 → g v = 0 := by
    filter_upwards [ht.eventually hzero] with v hv hvj
    apply hv
    change w₀ j + v j = 0
    simpa only [hw₀, zero_add] using hvj
  obtain ⟨K, hK, hKeq⟩ := analytic_hyperplane_division_zero P e
    (eraseCoordinateCLM_norm_le j) he ℓ hdecomp hℓP g hg hgzero
  let H : (Fin n → ℂ) → ℂ := fun w => K (w - w₀)
  have hH : AnalyticAt ℂ H w₀ := by
    have ha : AnalyticAt ℂ (fun w : Fin n → ℂ => w - w₀) w₀ := analyticAt_id.fun_sub analyticAt_const
    have hK' : AnalyticAt ℂ K (w₀ - w₀) := by simpa only [sub_self] using hK
    exact hK'.comp (f := fun w : Fin n → ℂ => w - w₀) ha
  refine ⟨H, hH, ?_⟩
  have ht' : Tendsto (fun w : Fin n → ℂ => w - w₀) (𝓝 w₀) (𝓝 0) := by
    have hc : Continuous (fun w : Fin n → ℂ => w - w₀) := continuous_id.sub continuous_const
    simpa only [sub_self] using hc.tendsto w₀
  filter_upwards [ht'.eventually hKeq] with w hw
  simpa only [g, H, ℓ, add_sub_cancel, ContinuousLinearMap.proj_apply, Pi.sub_apply,
    hw₀, sub_zero] using hw

/-- Genuine local analytic division by the positive-radius quadratic. No quotient or
division theorem is assumed: the proof uses the square-root graph and Taylor division. -/
theorem quadric_local_analytic_division_coords {n : ℕ} (F : (Fin n → ℂ) → ℂ)
    (r : ℝ) (hr : 0 < r) (z₀ : Fin n → ℂ)
    (hz₀ : squareSum z₀ = (r : ℂ) ^ 2) (hF : AnalyticAt ℂ F z₀)
    (hzero : ∀ z, squareSum z = (r : ℂ) ^ 2 → F z = 0) :
    ∃ (U : Set (Fin n → ℂ)) (H : (Fin n → ℂ) → ℂ), IsOpen U ∧ z₀ ∈ U ∧
      AnalyticOnNhd ℂ H U ∧ ∀ z ∈ U, F z = (squareSum z - (r : ℂ) ^ 2) * H z := by
  obtain ⟨j, hj⟩ := quadric_exists_nonzero_coordinate z₀ r hr hz₀
  let a := z₀ j
  let b := quadricRoot r j a
  let D := quadricRootDomain r j a
  let φ := quadricFlatten r j a
  let ψ := quadricUnflatten r j a
  let w₀ := φ z₀
  obtain ⟨hzD, hb₀⟩ := quadricRoot_at_quadric r j z₀ hz₀ hj
  have hwD : w₀ ∈ D := by
    simpa only [w₀, φ, quadricFlatten, D, a, quadricRootDomain, mem_preimage,
      quadricRadicand_update] using hzD
  have hwj : w₀ j = 0 := by
    simp only [w₀, φ, quadricFlatten, Function.update_self, a, hb₀, sub_self]
  let f : (Fin n → ℂ) → ℂ := fun w => F (ψ w)
  have hf : AnalyticAt ℂ f w₀ := by
    have hF' : AnalyticAt ℂ F (ψ w₀) := by
      simpa only [ψ, w₀, φ, quadricUnflatten_flatten] using hF
    exact hF'.comp (quadricUnflatten_analyticOnNhd r j a hj w₀ hwD)
  have hzero' : ∀ᶠ w in 𝓝 w₀, w j = 0 → f w = 0 := by
    filter_upwards [(quadricRootDomain_isOpen r j a).mem_nhds hwD] with w hw hwj
    apply hzero
    apply sub_eq_zero.mp
    rw [quadricUnflatten_factorization r j a hj w hw, hwj, zero_mul]
  obtain ⟨K, hK, hKeq⟩ := analytic_coordinate_division j w₀ hwj f hf hzero'
  have hφ : AnalyticAt ℂ φ z₀ := quadricFlatten_analyticOnNhd r j a hj z₀ hzD
  have hb : AnalyticAt ℂ b z₀ := quadricRoot_analyticOnNhd r j a hj z₀ hzD
  have hden : AnalyticAt ℂ (fun z : Fin n → ℂ => z j + b z) z₀ :=
    ((ContinuousLinearMap.proj (R := ℂ) j).analyticAt z₀).fun_add hb
  have hunit : z₀ j + b z₀ ≠ 0 := by
    change z₀ j + quadricRoot r j (z₀ j) z₀ ≠ 0
    rw [hb₀, ← two_mul]
    exact mul_ne_zero (by norm_num) hj
  let H : (Fin n → ℂ) → ℂ := fun z => K (φ z) / (z j + b z)
  have hH : AnalyticAt ℂ H z₀ :=
    (hK.comp hφ).fun_div hden hunit
  have heq : ∀ᶠ z in 𝓝 z₀, F z = (squareSum z - (r : ℂ) ^ 2) * H z := by
    have hφt : Tendsto φ (𝓝 z₀) (𝓝 w₀) := hφ.continuousAt.tendsto
    filter_upwards [(quadricRootDomain_isOpen r j a).mem_nhds hzD,
      hφt.eventually hKeq, hden.continuousAt.eventually_ne hunit] with z hz hk hu
    have hk' : F z = (z j - b z) * K (φ z) := by
      change F (quadricUnflatten r j a (quadricFlatten r j a z)) =
        quadricFlatten r j a z j * K (φ z) at hk
      rw [quadricUnflatten_flatten] at hk
      simpa only [quadricFlatten, Function.update_self, b] using hk
    rw [hk', quadric_local_factorization r j a hj z hz]
    change (z j - b z) * K (φ z) = (z j - b z) * (z j + b z) *
      (K (φ z) / (z j + b z))
    field_simp
    ring
  obtain ⟨U, hU, hUopen, hzU⟩ := eventually_nhds_iff.mp (hH.eventually_analyticAt.and heq)
  exact ⟨U, H, hUopen, hzU, fun z hz => (hU z hz).1, fun z hz => (hU z hz).2⟩

/-- Local analytic quadratic division in the shared complex Euclidean space. -/
theorem quadric_local_analytic_division {n : ℕ} (F : ComplexEuclidean n → ℂ)
    (r : ℝ) (hr : 0 < r) (z₀ : ComplexEuclidean n)
    (hz₀ : squareSum (fun i => z₀ i) = (r : ℂ) ^ 2) (hF : AnalyticAt ℂ F z₀)
    (hzero : ∀ z : ComplexEuclidean n, squareSum (fun i => z i) = (r : ℂ) ^ 2 → F z = 0) :
    ∃ (U : Set (ComplexEuclidean n)) (H : ComplexEuclidean n → ℂ), IsOpen U ∧ z₀ ∈ U ∧
      AnalyticOnNhd ℂ H U ∧
      ∀ z ∈ U, F z = (squareSum (fun i => z i) - (r : ℂ) ^ 2) * H z := by
  let e := EuclideanSpace.equiv (Fin n) ℂ
  have hf : AnalyticAt ℂ (F ∘ e.symm) (e z₀) := by
    apply hF.comp_of_eq (e.symm.analyticAt (e z₀))
    exact e.symm_apply_apply z₀
  have hzero' : ∀ z : Fin n → ℂ, squareSum z = (r : ℂ) ^ 2 → (F ∘ e.symm) z = 0 := by
    intro z hz
    exact hzero (e.symm z) hz
  obtain ⟨V, K, hV, hzV, hK, hKeq⟩ := quadric_local_analytic_division_coords
    (F ∘ e.symm) r hr (e z₀) hz₀ hf hzero'
  refine ⟨e ⁻¹' V, K ∘ e, hV.preimage e.continuous, hzV, ?_, ?_⟩
  · intro z hz
    exact (hK (e z) hz).comp (e.analyticAt z)
  · intro z hz
    simpa only [Function.comp_apply, ContinuousLinearEquiv.symm_apply_apply] using hKeq (e z) hz

/-- Real-sphere vanishing gives an analytic local quadratic quotient at every
point of the complex quadric. -/
theorem real_sphere_local_analytic_division {n : ℕ} (F : ComplexEuclidean n → ℂ)
    (hF : AnalyticOnNhd ℂ F univ) (r : ℝ) (hr : 0 < r)
    (hreal : ∀ x : Euclidean n, ‖x‖ = r → F (realToComplex x) = 0)
    (z₀ : ComplexEuclidean n) (hz₀ : squareSum (fun i => z₀ i) = (r : ℂ) ^ 2) :
    ∃ (U : Set (ComplexEuclidean n)) (H : ComplexEuclidean n → ℂ), IsOpen U ∧ z₀ ∈ U ∧
      AnalyticOnNhd ℂ H U ∧
      ∀ z ∈ U, F z = (squareSum (fun i => z i) - (r : ℂ) ^ 2) * H z := by
  have hd : Differentiable ℂ F := differentiableOn_univ.mp hF.differentiableOn
  exact quadric_local_analytic_division F r hr z₀ hz₀ (hF z₀ (mem_univ z₀))
    (fun z hz => entire_zero_on_quadric F hd r hr hreal z hz)

end RieszEuclidean.CompleteMinimal
