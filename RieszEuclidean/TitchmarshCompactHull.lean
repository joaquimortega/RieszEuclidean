import RieszEuclidean.Basic
import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.Analysis.Convex.Topology
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.Data.NNReal.Basic

noncomputable section

open Set

namespace RieszEuclidean.Titchmarsh

theorem pad_finite_convex_combination
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    {ι : Type*} [Fintype ι] {N : ℕ}
    (hcard : Fintype.card ι ≤ N)
    (C : Set E) (hC : C.Nonempty)
    (x : ι → C) (w : ι → NNReal)
    (hw : ∑ i, w i = 1) :
    ∃ x' : Fin N → C, ∃ w' : Fin N → NNReal,
      (∑ i, w' i = 1) ∧
      (∑ i, (w' i : ℝ) • (x' i : E) = ∑ i, (w i : ℝ) • (x i : E)) := by
  classical
  let emb : ι ↪ Fin N := Classical.choice <|
    Function.Embedding.nonempty_of_card_le (by simpa using hcard)
  let e : ι ≃ Set.range emb := Equiv.ofInjective emb emb.injective
  obtain ⟨c₀, hc₀⟩ := hC
  let c₀' : C := ⟨c₀, hc₀⟩
  let x' : Fin N → C := fun j =>
    if hj : j ∈ Set.range emb then x (e.symm ⟨j, hj⟩) else c₀'
  let w' : Fin N → NNReal := fun j =>
    if hj : j ∈ Set.range emb then w (e.symm ⟨j, hj⟩) else 0
  have hx' (i : ι) : x' (emb i) = x i := by
    simp [x', e]
  have hw' (i : ι) : w' (emb i) = w i := by
    simp [w', e]
  have hsumw : ∑ j : Fin N, w' j = ∑ i, w i := by
    classical
    calc
      ∑ j : Fin N, w' j = ∑ j ∈ (Finset.univ.filter fun j : Fin N => j ∈ Set.range emb), w' j := by
        symm
        apply Finset.sum_subset (Finset.filter_subset _ _)
        intro j hj hnot
        have hnot' : j ∉ Set.range emb := fun hjr =>
          hnot (Finset.mem_filter.mpr ⟨by simp, hjr⟩)
        change (if hj : j ∈ Set.range emb then w (e.symm ⟨j, hj⟩) else 0) = 0
        rw [dif_neg hnot']
      _ = ∑ j : {j : Fin N // j ∈ Set.range emb}, w' j := by
        exact Finset.sum_subtype _ (by intro j; simp) w'
      _ = ∑ i, w i := by
        apply Fintype.sum_equiv e.symm
        intro i
        have hi : emb (e.symm i) = (i : Fin N) :=
          congrArg Subtype.val (e.apply_symm_apply i)
        rw [← hi, hw']
  have hsumx :
      (∑ j : Fin N, (w' j : ℝ) • (x' j : E)) =
        ∑ i, (w i : ℝ) • (x i : E) := by
    classical
    calc
      ∑ j : Fin N, (w' j : ℝ) • (x' j : E) =
          ∑ j ∈ (Finset.univ.filter fun j : Fin N => j ∈ Set.range emb),
            (w' j : ℝ) • (x' j : E) := by
        symm
        apply Finset.sum_subset (Finset.filter_subset _ _)
        intro j hj hnot
        have hnot' : j ∉ Set.range emb := fun hjr =>
          hnot (Finset.mem_filter.mpr ⟨by simp, hjr⟩)
        simp only [w', dif_neg hnot', NNReal.coe_zero, zero_smul]
      _ = ∑ j : {j : Fin N // j ∈ Set.range emb},
            (w' j : ℝ) • (x' j : E) := by
        exact Finset.sum_subtype _ (by intro j; simp) _
      _ = ∑ i, (w i : ℝ) • (x i : E) := by
        apply Fintype.sum_equiv e.symm
        intro i
        have hi : emb (e.symm i) = (i : Fin N) :=
          congrArg Subtype.val (e.apply_symm_apply i)
        rw [← hi, hw', hx']
  exact ⟨x', w', hsumw.trans hw, hsumx⟩

/-- The algebraic convex hull of a compact set in a finite-dimensional real normed space is
compact. The proof uses Carathéodory's theorem and realizes the hull as a finite-dimensional
simplex image. -/
theorem isCompact_convexHull_of_compact
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {C : Set E} (hC : IsCompact C) :
    IsCompact (convexHull ℝ C) := by
  classical
  by_cases hne : C.Nonempty
  · let N := Module.finrank ℝ E + 1
    letI : CompactSpace C := isCompact_iff_compactSpace.mp hC
    letI : CompactSpace (Fin N → C) := inferInstance
    letI : CompactSpace (stdSimplex ℝ (Fin N)) :=
      isCompact_iff_compactSpace.mp (isCompact_stdSimplex (Fin N))
    letI : CompactSpace (stdSimplex ℝ (Fin N) × (Fin N → C)) := inferInstance
    let Φ : stdSimplex ℝ (Fin N) × (Fin N → C) → E := fun p =>
      ∑ i, (p.1.1 i) • (p.2 i : E)
    have hΦ : Continuous Φ := by
      unfold Φ
      apply continuous_finset_sum Finset.univ
      intro i hi
      exact (((continuous_apply i).comp (continuous_subtype_val.comp continuous_fst)).smul
        (continuous_subtype_val.comp ((continuous_apply i).comp continuous_snd)))
    have hcompact : IsCompact (Set.range Φ) := isCompact_range hΦ
    have heq : convexHull ℝ C = Set.range Φ := by
      apply Set.Subset.antisymm
      · intro y hy
        obtain ⟨ι, hι, z, w, hz, hind, hwp, hw1, hyz⟩ :=
          eq_pos_convex_span_of_mem_convexHull hy
        letI : Fintype ι := hι
        have hcard : Fintype.card ι ≤ N := by
          calc
            Fintype.card ι ≤ Module.finrank ℝ (vectorSpan ℝ (Set.range z)) + 1 :=
              hind.card_le_finrank_succ
            _ ≤ Module.finrank ℝ E + 1 := by
              exact Nat.add_le_add_right (Submodule.finrank_le _) 1
        let xc : ι → C := fun i => ⟨z i, hz ⟨i, rfl⟩⟩
        let wn : ι → NNReal := fun i => ⟨w i, (hwp i).le⟩
        have hwn : ∑ i, wn i = 1 := by
          apply NNReal.coe_injective
          simpa [wn] using hw1
        have hsum : ∑ i, (wn i : ℝ) • (xc i : E) = y := by
          simpa [wn, xc] using hyz
        obtain ⟨x', w', hw'sum, hw'vec⟩ :=
          pad_finite_convex_combination hcard C hne xc wn hwn
        have hw'nonneg : ∀ i : Fin N, 0 ≤ (w' i : ℝ) := fun i => (w' i).property
        have hw'simplex : (fun i => (w' i : ℝ)) ∈ stdSimplex ℝ (Fin N) :=
          ⟨hw'nonneg, by
            have hcast := congrArg (fun a : NNReal => (a : ℝ)) hw'sum
            simpa using hcast⟩
        refine ⟨(⟨(fun i => (w' i : ℝ)), hw'simplex⟩, x'), ?_⟩
        change ∑ i, (w' i : ℝ) • (x' i : E) = y
        exact hw'vec.trans hsum
      · rintro y ⟨p, rfl⟩
        apply mem_convexHull_of_exists_fintype (fun i => p.1.1 i)
          (fun i => (p.2 i : E))
        · exact fun i => (p.1.2.1 i)
        · exact p.1.2.2
        · exact fun i => (p.2 i).property
        · rfl
    rw [heq]
    exact hcompact
  · have hCempty : C = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    simp [hCempty]

end RieszEuclidean.Titchmarsh
