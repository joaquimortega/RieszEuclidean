import RieszEuclidean.CompleteMinimalBesselAsymptotic
import RieszEuclidean.CompleteMinimalBesselComplexZeros
import Mathlib.Order.OrderIsoNat
import Mathlib.Order.Hom.Set
import Mathlib.Data.Set.Card
import Mathlib.Analysis.PSeries

/-! # The ordered positive zeros of the actual ball Fourier transform -/

noncomputable section
open Set Filter Topology
open scoped BigOperators

namespace RieszEuclidean.CompleteMinimal

/-- The positive real zeros before physical Fourier-frequency scaling. -/
def positiveBallZeros (n : ℕ) : Set ℝ :=
  {s | 0 < s ∧ realRadialBallFourier n s = 0}

theorem compact_inter_finite_of_locallyFinite {X : Type*} [TopologicalSpace X]
    (s : Set X) (hlocal : ∀ x, ∃ U ∈ 𝓝 x, (U ∩ s).Finite)
    {K : Set X} (hK : IsCompact K) : (K ∩ s).Finite := by
  classical
  choose U hU hf using hlocal
  obtain ⟨t, _, hcover⟩ := hK.elim_nhds_subcover U (fun x _ => hU x)
  apply (t.finite_toSet.biUnion (fun x _ => hf x)).subset
  rintro x ⟨hxK, hxs⟩
  obtain ⟨a, hat, hxa⟩ := mem_iUnion₂.mp (hcover hxK)
  exact mem_biUnion hat ⟨hxa, hxs⟩

theorem positiveBallZeros_locallyFinite (n : ℕ) (s : ℝ) :
    ∃ U ∈ 𝓝 s, (U ∩ positiveBallZeros n).Finite := by
  obtain ⟨U, hU, hf⟩ := radialBallFourier_zeros_locallyFinite n (s : ℂ)
  refine ⟨Complex.ofReal ⁻¹' U, Complex.continuous_ofReal.continuousAt.preimage_mem_nhds hU, ?_⟩
  apply (hf.preimage Complex.ofReal_injective.injOn).subset
  rintro t ⟨htU, ht⟩
  refine ⟨htU, ?_⟩
  change radialBallFourier n (t : ℂ) = 0
  rw [radialBallFourier_ofReal_eq, ht.2]
  rfl

theorem positiveBallZeros_finite_below (n : ℕ) (b : ℝ) :
    (positiveBallZeros n ∩ Iic b).Finite := by
  apply (compact_inter_finite_of_locallyFinite (positiveBallZeros n)
    (positiveBallZeros_locallyFinite n) (isCompact_Icc : IsCompact (Icc (0 : ℝ) b))).subset
  rintro t ⟨ht, htb⟩
  exact ⟨⟨ht.1.le, htb⟩, ht⟩

theorem positiveBallZeros_unbounded (n : ℕ) : ¬ BddAbove (positiveBallZeros n) := by
  rintro ⟨b, hb⟩
  obtain ⟨s, hs, hz⟩ := realRadialBallFourier_zeros_unbounded n b
  exact (lt_of_le_of_lt (le_max_right 0 b) hs).not_le (hb ⟨lt_of_le_of_lt (le_max_left 0 b) hs, hz⟩)

theorem positiveBallZeros_infinite (n : ℕ) : (positiveBallZeros n).Infinite := by
  intro hf
  exact positiveBallZeros_unbounded n hf.bddAbove

/-- The finite number of positive zeros up to a given zero. -/
def positiveBallZeroRank (n : ℕ) (s : positiveBallZeros n) : ℕ :=
  (positiveBallZeros n ∩ Iic (s : ℝ)).ncard

theorem positiveBallZeroRank_strictMono (n : ℕ) : StrictMono (positiveBallZeroRank n) := by
  intro a b hab
  change (a : ℝ) < (b : ℝ) at hab
  apply Set.ncard_lt_ncard _ (positiveBallZeros_finite_below n b)
  refine ⟨?_, ?_⟩
  · rintro t ⟨ht, hta⟩
    exact ⟨ht, (show t ≤ (a : ℝ) from hta).trans hab.le⟩
  · intro hsub
    have h := hsub ⟨b.prop, show (b : ℝ) ≤ (b : ℝ) from le_rfl⟩
    exact hab.not_le h.2

/-- The exact increasing enumeration of all positive zeros. -/
def positiveBallZeroOrderIso (n : ℕ) : ℕ ≃o positiveBallZeros n := by
  haveI : Infinite (positiveBallZeros n) := infinite_coe_iff.mpr (positiveBallZeros_infinite n)
  haveI : Infinite (Set.range (positiveBallZeroRank n)) := infinite_coe_iff.mpr
    (Set.infinite_range_of_injective (positiveBallZeroRank_strictMono n).injective)
  exact (Nat.Subtype.orderIsoOfNat (Set.range (positiveBallZeroRank n))).trans
    ((positiveBallZeroRank_strictMono n).orderIso (positiveBallZeroRank n)).symm

/-- The `j`th positive zero, starting at index zero. -/
def positiveBallZero (n j : ℕ) : ℝ := positiveBallZeroOrderIso n j

theorem positiveBallZero_pos (n j : ℕ) : 0 < positiveBallZero n j :=
  (positiveBallZeroOrderIso n j).prop.1

theorem positiveBallZero_isZero (n j : ℕ) : realRadialBallFourier n (positiveBallZero n j) = 0 :=
  (positiveBallZeroOrderIso n j).prop.2

theorem positiveBallZero_strictMono (n : ℕ) : StrictMono (positiveBallZero n) := by
  intro a b hab
  exact (positiveBallZeroOrderIso n).strictMono hab

theorem positiveBallZero_range (n : ℕ) : range (positiveBallZero n) = positiveBallZeros n := by
  ext s
  constructor
  · rintro ⟨j, rfl⟩
    exact (positiveBallZeroOrderIso n j).prop
  · intro hs
    obtain ⟨j, hj⟩ := (positiveBallZeroOrderIso n).surjective ⟨s, hs⟩
    exact ⟨j, congrArg Subtype.val hj⟩

theorem positiveBallZero_tendsto (n : ℕ) : Tendsto (positiveBallZero n) atTop atTop := by
  apply (positiveBallZero_strictMono n).monotone.tendsto_atTop_atTop
  intro b
  obtain ⟨s, hs, hz⟩ := realRadialBallFourier_zeros_unbounded n b
  obtain ⟨j, rfl⟩ := (positiveBallZero_range n).symm ▸
    (show s ∈ positiveBallZeros n from ⟨lt_of_le_of_lt (le_max_left 0 b) hs, hz⟩)
  exact ⟨j, (lt_of_le_of_lt (le_max_right 0 b) hs).le⟩

/-- The manuscript's physical Fourier radii, with the zero index reserved for the origin. -/
def ballZeroRadius (n : ℕ) : ℕ → ℝ
  | 0 => 0
  | j + 1 => positiveBallZero n j / (2 * Real.pi)

@[simp]
theorem ballZeroRadius_zero (n : ℕ) : ballZeroRadius n 0 = 0 := rfl

theorem ballZeroRadius_pos (n : ℕ) {j : ℕ} (hj : 0 < j) : 0 < ballZeroRadius n j := by
  cases j with
  | zero => omega
  | succ j => exact div_pos (positiveBallZero_pos n j) (mul_pos (by norm_num) Real.pi_pos)

theorem ballZeroRadius_strictMono (n : ℕ) : StrictMono (ballZeroRadius n) := by
  apply strictMono_nat_of_lt_succ
  intro j
  cases j with
  | zero => simpa only [ballZeroRadius_zero] using ballZeroRadius_pos n (by omega : 0 < 1)
  | succ j =>
    exact (div_lt_div_iff_of_pos_right (mul_pos (by norm_num) Real.pi_pos)).mpr
      (positiveBallZero_strictMono n (Nat.lt_succ_self j))

theorem ballZeroRadius_tendsto (n : ℕ) : Tendsto (ballZeroRadius n) atTop atTop := by
  apply (ballZeroRadius_strictMono n).monotone.tendsto_atTop_atTop
  intro b
  obtain ⟨s, hs, hz⟩ := realRadialBallFourier_zeros_unbounded n (b * (2 * Real.pi))
  obtain ⟨j, rfl⟩ := (positiveBallZero_range n).symm ▸
    (show s ∈ positiveBallZeros n from ⟨lt_of_le_of_lt (le_max_left 0 _) hs, hz⟩)
  refine ⟨j + 1, (le_div_iff₀ (mul_pos (by norm_num) Real.pi_pos)).mpr ?_⟩
  exact (lt_of_le_of_lt (le_max_right 0 _) hs).le

theorem ballZeroRadius_isZero (n : ℕ) {j : ℕ} (hj : 0 < j) :
    realRadialBallFourier n (2 * Real.pi * ballZeroRadius n j) = 0 := by
  cases j with
  | zero => omega
  | succ j =>
    rw [ballZeroRadius, mul_div_cancel₀ _ (mul_ne_zero (by norm_num) Real.pi_ne_zero)]
    exact positiveBallZero_isZero n j

theorem exists_ballZeroRadius_of_real_zero (n : ℕ) {s : ℝ} (hs : 0 < s)
    (hz : realRadialBallFourier n s = 0) :
    ∃ j : ℕ, 0 < j ∧ s = 2 * Real.pi * ballZeroRadius n j := by
  obtain ⟨j, rfl⟩ := (positiveBallZero_range n).symm ▸
    (show s ∈ positiveBallZeros n from ⟨hs, hz⟩)
  refine ⟨j + 1, by omega, ?_⟩
  rw [ballZeroRadius, mul_div_cancel₀ _ (mul_ne_zero (by norm_num) Real.pi_ne_zero)]

/-- All real Fourier zeros are precisely the enumerated positive-radius spheres. -/
theorem normalizedBallFourier_real_zero_iff (n : ℕ) (ξ : Euclidean (n + 1)) :
    normalizedBallFourier (n + 1) (realToComplex ξ) = 0 ↔
      ∃ j : ℕ, 0 < j ∧ ‖ξ‖ = ballZeroRadius n j := by
  have hπ : 0 < 2 * Real.pi := mul_pos (by norm_num) Real.pi_pos
  rw [normalizedBallFourier_real_radial, radialBallFourier_ofReal_eq, Complex.ofReal_eq_zero]
  constructor
  · intro hz
    have hx : 0 < ‖ξ‖ := by
      by_contra h
      have hn : ‖ξ‖ = 0 := le_antisymm (le_of_not_gt h) (norm_nonneg _)
      rw [hn, mul_zero, realRadialBallFourier_zero] at hz
      norm_num at hz
    obtain ⟨j, hj, he⟩ := exists_ballZeroRadius_of_real_zero n (mul_pos hπ hx) hz
    exact ⟨j, hj, (mul_left_cancel₀ hπ.ne' he)⟩
  · rintro ⟨j, hj, hnorm⟩
    rw [hnorm]
    exact ballZeroRadius_isZero n hj

theorem ballZeroRadius_gap (n : ℕ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ j : ℕ, δ ≤ ballZeroRadius n (j + 1) - ballZeroRadius n j := by
  have hπ : 0 < 2 * Real.pi := mul_pos (by norm_num) Real.pi_pos
  obtain ⟨η, hη, hgap⟩ := realRadialBallFourier_zeros_separated n (positiveBallZero_pos n 0)
  let δ : ℝ := min (ballZeroRadius n 1) (η / (2 * Real.pi))
  refine ⟨δ, lt_min (ballZeroRadius_pos n (by omega : 0 < 1)) (div_pos hη hπ), ?_⟩
  intro j
  cases j with
  | zero =>
    simpa only [Nat.zero_add, ballZeroRadius_zero, sub_zero] using
      min_le_left (ballZeroRadius n 1) (η / (2 * Real.pi))
  | succ j =>
    apply (min_le_right (ballZeroRadius n 1) (η / (2 * Real.pi))).trans
    change η / (2 * Real.pi) ≤ positiveBallZero n (j + 1) / (2 * Real.pi) -
      positiveBallZero n j / (2 * Real.pi)
    rw [← sub_div]
    apply (div_le_div_iff_of_pos_right hπ).mpr
    exact hgap _ _ ((positiveBallZero_strictMono n).monotone (Nat.zero_le j))
      (positiveBallZero_strictMono n (Nat.lt_succ_self _))
      (positiveBallZero_isZero n j) (positiveBallZero_isZero n (j + 1))

theorem ballZeroRadius_linear_lower (n : ℕ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ j : ℕ, (j : ℝ) * δ ≤ ballZeroRadius n j := by
  obtain ⟨δ, hδ, hgap⟩ := ballZeroRadius_gap n
  refine ⟨δ, hδ, ?_⟩
  intro j
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Nat.cast_succ]
    have h := hgap j
    nlinarith

theorem ballZeroRadius_reciprocal_sq_summable (n : ℕ) :
    Summable (fun j : ℕ => 1 / (ballZeroRadius n (j + 1)) ^ (2 : ℕ)) := by
  obtain ⟨δ, hδ, hlinear⟩ := ballZeroRadius_linear_lower n
  have hs : Summable (fun j : ℕ => 1 / ((j + 1 : ℕ) : ℝ) ^ (2 : ℕ)) :=
    (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2))
  apply Summable.of_nonneg_of_le (fun _ => by positivity) _ (hs.mul_left (1 / δ ^ (2 : ℕ)))
  intro j
  calc
    1 / ballZeroRadius n (j + 1) ^ (2 : ℕ) ≤ 1 / (((j + 1 : ℕ) : ℝ) * δ) ^ (2 : ℕ) :=
      one_div_le_one_div_of_le (by positivity)
        (pow_le_pow_left₀ (by positivity) (hlinear (j + 1)) 2)
    _ = (1 / δ ^ (2 : ℕ)) * (1 / ((j + 1 : ℕ) : ℝ) ^ (2 : ℕ)) := by
      rw [mul_pow, one_div_mul_one_div, mul_comm]

/-- The full physical radius sequence covers the actual simple complex quadrics. -/
theorem normalizedBallFourier_hasSimpleQuadricZeros (n : ℕ) :
    HasSimpleQuadricZeros (normalizedBallFourier (n + 1)) (ballZeroRadius n) := by
  apply normalizedBallFourier_hasSimpleQuadricZeros_of_cover
  intro s hs hz
  obtain ⟨j, _, hj⟩ := exists_ballZeroRadius_of_real_zero n hs hz
  exact ⟨j, hj⟩

/-- Using only positive indices gives the geometry and positivity inputs of analytic division. -/
theorem normalizedBallFourier_hasSimpleQuadricZeros_positive (n : ℕ) :
    HasSimpleQuadricZeros (normalizedBallFourier (n + 1))
      (fun j => ballZeroRadius n (j + 1)) := by
  apply normalizedBallFourier_hasSimpleQuadricZeros_of_cover
  intro s hs hz
  obtain ⟨j, hj, he⟩ := exists_ballZeroRadius_of_real_zero n hs hz
  cases j with
  | zero => omega
  | succ j => exact ⟨j, he⟩

theorem ballZeroRadius_positive_indices (n j : ℕ) : 0 < ballZeroRadius n (j + 1) :=
  ballZeroRadius_pos n (Nat.succ_pos _)

end RieszEuclidean.CompleteMinimal
