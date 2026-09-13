import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.Linarith

/-! Blueprint: blueprint/README.md#projection-gap. -/
noncomputable section
namespace RieszEuclidean

variable (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- A bounded orthogonal projection; closed range follows from idempotence. -/
structure OrthProjection where
  /-- The bounded complex linear operator underlying the projection. -/
  op : H →L[ℂ] H
  idempotent : op.comp op = op
  symmetric : ∀ x y : H, inner (𝕜 := ℂ) (op x) y = inner (𝕜 := ℂ) x (op y)

namespace OrthProjection
variable {H}

/-- The range submodule of the projection. -/
def range (P : OrthProjection H) : Submodule ℂ H := LinearMap.range P.op

/-- The restriction of P to the range of Q is a continuous linear equivalence. -/
def RangeIso (P Q : OrthProjection H) : Prop :=
  ∃ e : Q.range ≃L[ℂ] P.range, ∀ x : Q.range, (e x : H) = P.op x

/-- Pointwise norm convergence of a sequence of bounded operators. -/
def StronglyConverges (P : ℕ → H →L[ℂ] H) (R : H →L[ℂ] H) : Prop :=
  ∀ x, Filter.Tendsto (fun n => P n x) Filter.atTop (nhds (R x))

theorem apply_idempotent (P : OrthProjection H) (x : H) : P.op (P.op x) = P.op x :=
  DFunLike.congr_fun P.idempotent x

/-- Transport a projection through a linear isometry onto its ambient space. -/
def conjugate {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    (P : OrthProjection H) (e : K ≃ₗᵢ[ℂ] H) : OrthProjection K where
  op := e.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (P.op.comp e.toContinuousLinearEquiv.toContinuousLinearMap)
  idempotent := by
    ext x
    change e.symm (P.op (e (e.symm (P.op (e x))))) = e.symm (P.op (e x))
    rw [e.apply_symm_apply, P.apply_idempotent]
  symmetric := by
    intro x y
    rw [← e.inner_map_map, ← e.inner_map_map]
    change inner (𝕜 := ℂ) (e (e.symm (P.op (e x)))) (e y) =
      inner (𝕜 := ℂ) (e x) (e (e.symm (P.op (e y))))
    simp only [e.apply_symm_apply]
    exact P.symmetric (e x) (e y)

theorem mem_range_iff (P : OrthProjection H) (x : H) : x ∈ P.range ↔ P.op x = x := by
  constructor
  · rintro ⟨y, rfl⟩
    exact P.apply_idempotent y
  · intro hx
    exact ⟨x, hx⟩

theorem inner_op_sub_op (P : OrthProjection H) (x y : H) :
    inner (𝕜 := ℂ) (P.op x) (y - P.op y) = 0 := by
  rw [P.symmetric, map_sub, P.apply_idempotent, _root_.sub_self, inner_zero_right]

theorem norm_sq_decomposition (P : OrthProjection H) (x : H) :
    ‖P.op x‖ ^ 2 + ‖x - P.op x‖ ^ 2 = ‖x‖ ^ 2 := by
  have h := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
    (P.op x) (x - P.op x) (P.inner_op_sub_op x x)
  simpa only [add_sub_cancel, pow_two] using h.symm

theorem norm_op_apply_le (P : OrthProjection H) (x : H) : ‖P.op x‖ ≤ ‖x‖ := by
  have h := P.norm_sq_decomposition x
  nlinarith [sq_nonneg ‖x - P.op x‖, norm_nonneg (P.op x), norm_nonneg x]

theorem norm_sub_op_apply_le (P : OrthProjection H) (x : H) : ‖x - P.op x‖ ≤ ‖x‖ := by
  have h := P.norm_sq_decomposition x
  nlinarith [sq_nonneg ‖P.op x‖, norm_nonneg (x - P.op x), norm_nonneg x]

theorem norm_sub_apply_sq (P Q : OrthProjection H) (x : H) :
    ‖(P.op - Q.op) x‖ ^ 2 =
      ‖P.op (x - Q.op x)‖ ^ 2 + ‖Q.op x - P.op (Q.op x)‖ ^ 2 := by
  have h := norm_sub_sq (𝕜 := ℂ) (P.op (x - Q.op x)) (Q.op x - P.op (Q.op x))
  rw [P.inner_op_sub_op, map_zero, mul_zero, sub_zero] at h
  simpa only [ContinuousLinearMap.sub_apply, map_sub, sub_sub_sub_cancel_right] using h

instance range_completeSpace [CompleteSpace H] (P : OrthProjection H) :
    CompleteSpace P.range := by
  have h : IsClosed (P.range : Set H) := by
    have heq : (P.range : Set H) = {x | P.op x = x} := by
      ext x
      exact P.mem_range_iff x
    rw [heq]
    exact isClosed_eq P.op.continuous continuous_id
  exact h.completeSpace_coe

/-- The actual restriction of one projection to the range of another. -/
def between (P Q : OrthProjection H) : Q.range →L[ℂ] P.range :=
  (P.op.comp Q.range.subtypeL).codRestrict P.range (fun x => ⟨x, rfl⟩)

theorem rangeIso_of_gap [CompleteSpace H] (P Q : OrthProjection H)
    (hgap : ‖P.op - Q.op‖ < 1) : RangeIso P Q := by
  let A := P.between Q
  let B := Q.between P
  have hnorm : ‖1 - A.comp B‖ ≤ ‖P.op - Q.op‖ := by
    apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro x
    have hx : P.op x = x := (P.mem_range_iff x).mp x.property
    change ‖(x : H) - P.op (Q.op x)‖ ≤ ‖P.op - Q.op‖ * ‖(x : H)‖
    calc
      ‖(x : H) - P.op (Q.op x)‖ = ‖P.op ((P.op - Q.op) x)‖ := by
        simp only [ContinuousLinearMap.sub_apply, map_sub, P.apply_idempotent, hx]
      _ ≤ ‖(P.op - Q.op) x‖ := P.norm_op_apply_le _
      _ ≤ ‖P.op - Q.op‖ * ‖(x : H)‖ := (P.op - Q.op).le_opNorm x
  have hunit : IsUnit (A.comp B) := by
    simpa only [sub_sub_cancel] using
      isUnit_one_sub_of_norm_lt_one (x := 1 - A.comp B) (hnorm.trans_lt hgap)
  have hsurj : Function.Surjective A := by
    have hAB := (ContinuousLinearMap.isUnit_iff_bijective.mp hunit).surjective
    intro y
    obtain ⟨x, hx⟩ := hAB y
    exact ⟨B x, hx⟩
  have hinj : Function.Injective A := by
    apply (injective_iff_map_eq_zero A).mpr
    intro x hx
    have hPx : P.op x = 0 := congrArg Subtype.val hx
    have hQx : Q.op x = x := (Q.mem_range_iff x).mp x.property
    have hbound := (P.op - Q.op).le_opNorm (x : H)
    simp only [ContinuousLinearMap.sub_apply, hPx, hQx, _root_.zero_sub, norm_neg] at hbound
    have hxzero : ‖(x : H)‖ = 0 := by
      nlinarith [norm_nonneg (x : H)]
    exact Subtype.ext (norm_eq_zero.mp hxzero)
  exact ⟨ContinuousLinearEquiv.ofBijective A
    (LinearMap.ker_eq_bot.mpr hinj) (LinearMap.range_eq_top.mpr hsurj), fun _ => rfl⟩

theorem lower_bounds_of_rangeIso (P Q : OrthProjection H) (h : RangeIso P Q) :
    ∃ c : ℝ, 0 < c ∧ c ≤ 1 ∧
      (∀ x ∈ Q.range, c * ‖x‖ ≤ ‖P.op x‖) ∧
      (∀ y ∈ P.range, c * ‖y‖ ≤ ‖Q.op y‖) := by
  obtain ⟨e, he⟩ := h
  let K := ‖e.symm.toContinuousLinearMap‖ + 1
  have hK : 0 < K := by dsimp [K]; positivity
  have hKnorm : ‖e.symm.toContinuousLinearMap‖ ≤ K := by dsimp [K]; linarith
  have hxbound (x : Q.range) : ‖(x : H)‖ ≤ K * ‖P.op x‖ := by
    have hnorm := e.symm.toContinuousLinearMap.le_opNorm (e x)
    have heq : ‖e x‖ = ‖P.op x‖ := congrArg norm (he x)
    simp only [ContinuousLinearEquiv.coe_coe, e.symm_apply_apply, heq] at hnorm
    exact hnorm.trans (mul_le_mul_of_nonneg_right hKnorm (norm_nonneg _))
  have hybound (y : P.range) : ‖(y : H)‖ ≤ K * ‖Q.op y‖ := by
    let x := e.symm y
    have hPx : P.op x = y := by rw [← he, e.apply_symm_apply]
    have hQx : Q.op x = x := (Q.mem_range_iff x).mp x.property
    have hPy : P.op y = y := (P.mem_range_iff y).mp y.property
    have hinner : inner (𝕜 := ℂ) (x : H) (Q.op y) = inner (𝕜 := ℂ) (y : H) y := by
      calc
        inner (𝕜 := ℂ) (x : H) (Q.op y) = inner (𝕜 := ℂ) (Q.op x) (y : H) :=
          (Q.symmetric x y).symm
        _ = inner (𝕜 := ℂ) (x : H) (y : H) := by rw [hQx]
        _ = inner (𝕜 := ℂ) (x : H) (P.op y) := by rw [hPy]
        _ = inner (𝕜 := ℂ) (P.op x) (y : H) := (P.symmetric x y).symm
        _ = inner (𝕜 := ℂ) (y : H) y := by rw [hPx]
    have hCS := re_inner_le_norm (𝕜 := ℂ) (x : H) (Q.op y)
    rw [hinner, inner_self_eq_norm_sq] at hCS
    have hx := hxbound x
    rw [hPx] at hx
    have hprod := hCS.trans (mul_le_mul_of_nonneg_right hx (norm_nonneg (Q.op y)))
    by_cases hy : ‖(y : H)‖ = 0
    · rw [hy]
      exact mul_nonneg hK.le (norm_nonneg _)
    · have hypos : 0 < ‖(y : H)‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hy)
      apply (mul_le_mul_left hypos).mp
      nlinarith only [hprod]
  refine ⟨1 / K, div_pos zero_lt_one hK, ?_, ?_, ?_⟩
  · apply (div_le_one hK).mpr
    dsimp [K]
    linarith [norm_nonneg e.symm.toContinuousLinearMap]
  · intro x hx
    have hbound := hxbound ⟨x, hx⟩
    calc
      1 / K * ‖x‖ = ‖x‖ / K := by ring
      _ ≤ ‖P.op x‖ := (div_le_iff₀ hK).mpr (by simpa only [mul_comm] using hbound)
  · intro y hy
    have hbound := hybound ⟨y, hy⟩
    calc
      1 / K * ‖y‖ = ‖y‖ / K := by ring
      _ ≤ ‖Q.op y‖ := (div_le_iff₀ hK).mpr (by simpa only [mul_comm] using hbound)

theorem complement_bound_of_lower (P Q : OrthProjection H) {c b : ℝ}
    (hc : 0 ≤ c) (hb : 0 ≤ b) (hcb : b ^ 2 = 1 - c ^ 2)
    (hlower : ∀ x ∈ Q.range, c * ‖x‖ ≤ ‖P.op x‖) (x : H) (hx : x ∈ Q.range) :
    ‖x - P.op x‖ ≤ b * ‖x‖ := by
  have hlowersq := pow_le_pow_left₀ (mul_nonneg hc (norm_nonneg x)) (hlower x hx) 2
  have hsq : ‖x - P.op x‖ ^ 2 ≤ (b * ‖x‖) ^ 2 := by
    calc
      ‖x - P.op x‖ ^ 2 = ‖x‖ ^ 2 - ‖P.op x‖ ^ 2 := by
        linarith [P.norm_sq_decomposition x]
      _ ≤ ‖x‖ ^ 2 - (c * ‖x‖) ^ 2 := sub_le_sub_left hlowersq _
      _ = (b * ‖x‖) ^ 2 := by rw [mul_pow, mul_pow, hcb]; ring
  nlinarith [mul_nonneg hb (norm_nonneg x), norm_nonneg (x - P.op x)]

theorem bound_on_kernel_of_complement_bound (P Q : OrthProjection H) {b : ℝ}
    (hb : 0 ≤ b) (hbound : ∀ y ∈ P.range, ‖y - Q.op y‖ ≤ b * ‖y‖)
    (z : H) (hz : Q.op z = 0) : ‖P.op z‖ ≤ b * ‖z‖ := by
  have hinner : inner (𝕜 := ℂ) (P.op z - Q.op (P.op z)) z =
      inner (𝕜 := ℂ) (P.op z) (P.op z) := by
    rw [inner_sub_left, Q.symmetric, hz, inner_zero_right, sub_zero]
    exact sub_eq_zero.mp (by simpa only [inner_sub_right] using P.inner_op_sub_op z z)
  have hCS := re_inner_le_norm (𝕜 := ℂ) (P.op z - Q.op (P.op z)) z
  rw [hinner, inner_self_eq_norm_sq] at hCS
  have hprod := hCS.trans (mul_le_mul_of_nonneg_right
    (hbound (P.op z) ⟨z, rfl⟩) (norm_nonneg z))
  by_cases hp : ‖P.op z‖ = 0
  · rw [hp]
    exact mul_nonneg hb (norm_nonneg z)
  · have hpos : 0 < ‖P.op z‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hp)
    apply (mul_le_mul_left hpos).mp
    nlinarith only [hprod]

theorem gap_of_rangeIso (P Q : OrthProjection H) (h : RangeIso P Q) :
    ‖P.op - Q.op‖ < 1 := by
  obtain ⟨c, hc, hc₁, hP, hQ⟩ := P.lower_bounds_of_rangeIso Q h
  let b := Real.sqrt (1 - c ^ 2)
  have hb : 0 ≤ b := Real.sqrt_nonneg _
  have hb_sq : b ^ 2 = 1 - c ^ 2 := Real.sq_sqrt (by nlinarith)
  have hb₁ : b < 1 := by nlinarith [sq_pos_of_pos hc]
  have hPcomp := P.complement_bound_of_lower Q hc.le hb hb_sq hP
  have hQcomp := Q.complement_bound_of_lower P hc.le hb hb_sq hQ
  apply lt_of_le_of_lt _ hb₁
  apply ContinuousLinearMap.opNorm_le_bound _ hb
  intro x
  have h₁ := P.bound_on_kernel_of_complement_bound Q hb hQcomp (x - Q.op x)
    (by rw [map_sub, Q.apply_idempotent, _root_.sub_self])
  have h₂ := hPcomp (Q.op x) ⟨x, rfl⟩
  have h₁sq := pow_le_pow_left₀ (norm_nonneg _) h₁ 2
  have h₂sq := pow_le_pow_left₀ (norm_nonneg _) h₂ 2
  have hsq : ‖(P.op - Q.op) x‖ ^ 2 ≤ (b * ‖x‖) ^ 2 := by
    calc
      ‖(P.op - Q.op) x‖ ^ 2 =
          ‖P.op (x - Q.op x)‖ ^ 2 + ‖Q.op x - P.op (Q.op x)‖ ^ 2 :=
        P.norm_sub_apply_sq Q x
      _ ≤ (b * ‖x - Q.op x‖) ^ 2 + (b * ‖Q.op x‖) ^ 2 := add_le_add h₁sq h₂sq
      _ = b ^ 2 * (‖Q.op x‖ ^ 2 + ‖x - Q.op x‖ ^ 2) := by ring
      _ = (b * ‖x‖) ^ 2 := by rw [Q.norm_sq_decomposition, mul_pow]
  nlinarith [mul_nonneg hb (norm_nonneg x), norm_nonneg ((P.op - Q.op) x)]

/-- GAP-01: manuscript Lemma 2.1. -/
theorem gap_iff_rangeIso [CompleteSpace H] (P Q : OrthProjection H) :
    ‖P.op - Q.op‖ < 1 ↔ RangeIso P Q := by
  exact ⟨P.rangeIso_of_gap Q, P.gap_of_rangeIso Q⟩

/-- GAP-02: Lemma 2.2; infinite-dimensional nesting, not rank counting. -/
theorem nested_not_both_gap [CompleteSpace H] (Rminus Rplus M : OrthProjection H)
    (hnest : Rminus.range < Rplus.range) :
    ¬ (‖Rminus.op - M.op‖ < 1 ∧ ‖Rplus.op - M.op‖ < 1) := by
  rintro ⟨hminus, hplus⟩
  have hm : ‖M.op - Rminus.op‖ < 1 := by
    rwa [norm_sub_rev]
  have hp : ‖M.op - Rplus.op‖ < 1 := by
    rwa [norm_sub_rev]
  obtain ⟨eminus, heminus⟩ := (gap_iff_rangeIso M Rminus).mp hm
  obtain ⟨eplus, heplus⟩ := (gap_iff_rangeIso M Rplus).mp hp
  obtain ⟨w, hwplus, hwminus⟩ := SetLike.exists_of_lt hnest
  let wplus : Rplus.range := ⟨w, hwplus⟩
  obtain ⟨u, hu⟩ := eminus.surjective (eplus wplus)
  let uplus : Rplus.range := ⟨u, hnest.le u.property⟩
  have heq : eplus uplus = eplus wplus := by
    apply Subtype.ext
    calc
      (eplus uplus : H) = M.op uplus := heplus uplus
      _ = (eminus u : H) := (heminus u).symm
      _ = (eplus wplus : H) := congrArg Subtype.val hu
  have huw : (u : H) = w := congrArg Subtype.val (eplus.injective heq)
  exact hwminus (huw ▸ u.property)

/-- GAP-03: the distance between two orthogonal projections is at most one. -/
theorem distance_le_one (P Q : OrthProjection H) : ‖P.op - Q.op‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  rw [one_mul]
  have h := P.norm_sub_apply_sq Q x
  have h₁ := P.norm_sq_decomposition (x - Q.op x)
  have h₂ := P.norm_sq_decomposition (Q.op x)
  have h₃ := Q.norm_sq_decomposition x
  nlinarith [sq_nonneg ‖x - Q.op x - P.op (x - Q.op x)‖,
    sq_nonneg ‖P.op (Q.op x)‖, norm_nonneg ((P.op - Q.op) x), norm_nonneg x]

/-- GAP-04: a UNIFORM non-strict norm bound survives a strong limit. -/
theorem gap_le_of_strong_limit (P : ℕ → H →L[ℂ] H) (R M : H →L[ℂ] H)
    (γ : ℝ) (hlim : StronglyConverges P R) (hgap : ∀ n, ‖P n - M‖ ≤ γ) :
    ‖R - M‖ ≤ γ := by
  have hγ : 0 ≤ γ := (norm_nonneg (P 0 - M)).trans (hgap 0)
  apply ContinuousLinearMap.opNorm_le_bound (R - M) hγ
  intro x
  have hx := ((hlim x).sub_const (M x)).norm
  change Filter.Tendsto (fun n => ‖(P n - M) x‖) Filter.atTop
    (nhds ‖(R - M) x‖) at hx
  apply le_of_tendsto' hx
  intro n
  exact ((P n - M).le_opNorm x).trans
    (mul_le_mul_of_nonneg_right (hgap n) (norm_nonneg x))

end OrthProjection
end RieszEuclidean
