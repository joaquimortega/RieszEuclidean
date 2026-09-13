import RieszEuclidean.FejerWeights
open Set MeasureTheory
namespace RieszEuclidean
/-- Membership in a positive-radius coordinate box is a coordinatewise bound. -/
theorem mem_euclideanBox_iff_coordinates {d : ℕ} {R : ℝ} (hR : 0 ≤ R)
    (x : Euclidean d) : x ∈ euclideanBox d R ↔ ∀ j, |x j| ≤ R := by
  rw [mem_euclideanBox_iff]
  exact pi_norm_le_iff_of_nonneg hR
/-- The intersection with the translate `C_R - y` is an actual coordinate rectangle. -/
theorem euclideanBox_inter_translate_eq {d : ℕ} {R : ℝ} (hR : 0 ≤ R)
    (y : Euclidean d) :
    euclideanBox d R ∩ translate y (euclideanBox d R) =
      (EuclideanSpace.measurableEquiv (Fin d)) ⁻¹'
        Icc (fun j => max (-R) (-R - y j)) (fun j => min R (R - y j)) := by
  ext x
  change (x ∈ euclideanBox d R ∧ x + y ∈ euclideanBox d R) ↔ _
  rw [mem_euclideanBox_iff_coordinates hR, mem_euclideanBox_iff_coordinates hR]
  change ((∀ j, |x j| ≤ R) ∧ (∀ j, |x j + y j| ≤ R)) ↔
    ((∀ j, max (-R) (-R - y j) ≤ x j) ∧ (∀ j, x j ≤ min R (R - y j)))
  simp only [abs_le, max_le_iff, le_min_iff]
  constructor
  · rintro ⟨hx, hxy⟩
    constructor
    · intro j; constructor
      · exact (hx j).1
      · linarith [(hxy j).1]
    · intro j; constructor
      · exact (hx j).2
      · linarith [(hxy j).2]
  · rintro ⟨hl, hu⟩
    constructor
    · intro j; exact ⟨(hl j).1, (hu j).1⟩
    · intro j; constructor <;> linarith [(hl j).2, (hu j).2]
/-- The signed length of the intersection interval has the usual triangular profile. -/
theorem overlap_interval_length (R t : ℝ) :
    min R (R - t) - max (-R) (-R - t) = 2 * R - |t| := by
  by_cases ht : 0 ≤ t
  · rw [abs_of_nonneg ht, min_eq_right (by linarith), max_eq_left (by linarith)]
    ring
  · have ht' : t ≤ 0 := le_of_not_ge ht
    rw [abs_of_nonpos ht', min_eq_left (by linarith), max_eq_right (by linarith)]
    ring
/-- Lebesgue volume of the box overlap, including empty coordinate intersections. -/
theorem volume_euclideanBox_inter_translate {d : ℕ} {R : ℝ} (hR : 0 ≤ R)
    (y : Euclidean d) :
    volume (euclideanBox d R ∩ translate y (euclideanBox d R)) =
      ∏ j : Fin d, ENNReal.ofReal (2 * R - |y j|) := by
  rw [euclideanBox_inter_translate_eq hR y,
    (EuclideanSpace.volume_preserving_measurableEquiv (Fin d)).measure_preimage
      measurableSet_Icc.nullMeasurableSet, Real.volume_Icc_pi]
  simp only [overlap_interval_length]
/-- The real volume of the overlap is the product of nonnegative interval lengths. -/
theorem volume_real_euclideanBox_inter_translate {d : ℕ} {R : ℝ} (hR : 0 ≤ R)
    (y : Euclidean d) :
    volume.real (euclideanBox d R ∩ translate y (euclideanBox d R)) =
      ∏ j : Fin d, max 0 (2 * R - |y j|) := by
  rw [Measure.real, volume_euclideanBox_inter_translate hR y, ENNReal.toReal_prod]
  simp only [ENNReal.toReal_ofReal', max_comm]
/-- The explicit Fejér weight is exactly the normalized volume of the translated-box overlap. -/
theorem fejerWeight_eq_normalized_overlap {d : ℕ} {R : ℝ} (hR : 0 < R)
    (y : Euclidean d) :
    fejerWeight R y = volume.real (euclideanBox d R ∩ translate y (euclideanBox d R)) /
      volume.real (euclideanBox d R) := by
  rw [volume_real_euclideanBox_inter_translate hR.le y, volume_real_euclideanBox d hR.le]
  have hden : (2 * R) ^ d = ∏ _j : Fin d, 2 * R := by simp
  rw [hden, ← Finset.prod_div_distrib]
  apply Finset.prod_congr rfl
  intro j _
  rw [← max_div_div_right (le_of_lt (show 0 < 2 * R by positivity))]
  simp only [zero_div]
  congr 1
  rw [sub_div, div_self (show 2 * R ≠ 0 by positivity)]
end RieszEuclidean
