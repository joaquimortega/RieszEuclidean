import RieszEuclidean.CompleteMinimalConvolutionSupport
import RieszEuclidean.CompleteMinimalSchwartzDensity
import RieszEuclidean.Bumps

noncomputable section
open MeasureTheory Set SchwartzMap
open scoped SchwartzMap Pointwise

namespace RieszEuclidean.CompleteMinimal

variable {d : ℕ}

private theorem translatedTest_tsupport_subset (x : Euclidean d) (φ : 𝓢(Euclidean d, ℂ)) :
    tsupport (schwartzTranslateCLM x φ : Euclidean d → ℂ) ⊆
      (fun y => x + y) ⁻¹' tsupport (φ : Euclidean d → ℂ) := by
  change closure (Function.support (schwartzTranslateCLM x φ : Euclidean d → ℂ)) ⊆ _
  apply IsClosed.closure_subset_iff
    (isClosed_tsupport _ |>.preimage (continuous_const.add continuous_id)) |>.mpr
  intro y hy
  exact subset_tsupport _ (show φ (x + y) ≠ 0 from hy)

/-- Translation moves the exact distribution support by the same physical vector. -/
private theorem distributionSupport_translate_subset (x : Euclidean d) (u : TemperedDistribution d) :
    distributionSupport (distributionTranslate x u) ⊆
      (fun y : Euclidean d => x + y) '' distributionSupport u := by
  let H : Euclidean d ≃ₜ Euclidean d := Homeomorph.addLeft x
  have himage : (fun y : Euclidean d => x + y) '' distributionSupport u =
      (fun y : Euclidean d => -x + y) ⁻¹' distributionSupport u := by
    ext y
    constructor
    · intro hy
      obtain ⟨z, hz, hzy⟩ := hy
      rw [← hzy]
      simpa [add_assoc] using hz
    · intro hy
      refine ⟨-x + y, hy, ?_⟩
      simp [add_assoc]
  have hclosed : IsClosed ((fun y : Euclidean d => x + y) '' distributionSupport u) := by
    rw [himage]
    exact (distributionSupport_isClosed u).preimage (continuous_const.add continuous_id)
  apply (distributionSupportedIn_iff_support_subset _ _ hclosed).mp
  intro φ hφ hdisj
  have hcompact : HasCompactSupport (schwartzTranslateCLM x φ : Euclidean d → ℂ) :=
    hφ.comp_homeomorph H
  have htest : Disjoint (tsupport (schwartzTranslateCLM x φ : Euclidean d → ℂ))
      (distributionSupport u) := by
    apply Set.disjoint_left.mpr
    intro y hy hyu
    have hxφ := translatedTest_tsupport_subset x φ hy
    have hxφ' : x + y ∈ tsupport (φ : Euclidean d → ℂ) := by
      change y ∈ (fun z => x + z) ⁻¹' tsupport (φ : Euclidean d → ℂ) at hxφ
      exact hxφ
    exact Set.disjoint_left.mp hdisj hxφ' ⟨y, hyu, rfl⟩
  exact (distributionSupportedIn_support u) _ hcompact htest

theorem distributionSupport_translate (x : Euclidean d) (u : TemperedDistribution d) :
    distributionSupport (distributionTranslate x u) =
      (fun y : Euclidean d => x + y) '' distributionSupport u := by
  apply Set.Subset.antisymm (distributionSupport_translate_subset x u)
  intro y hy
  obtain ⟨z, hz, rfl⟩ := hy
  have hcomp : distributionTranslate (-x) (distributionTranslate x u) = u := by
    ext φ
    change u (schwartzTranslateCLM x (schwartzTranslateCLM (-x) φ)) = u φ
    congr 1
    ext q
    simp only [schwartzTranslateCLM_apply]
    congr 1
    abel
  have hback := distributionSupport_translate_subset (-x) (distributionTranslate x u)
  rw [hcomp] at hback
  have hz' := hback hz
  obtain ⟨q, hq, hqeq⟩ := hz'
  have hqval : q = x + z := by
    change -x + q = z at hqeq
    calc
      q = x + (-x + q) := by abel
      _ = x + z := by rw [hqeq]
  simpa [hqval] using hq

/-- A Dirac distribution has support exactly at its evaluation point. -/
theorem distributionSupport_delta (x : Euclidean d) :
    distributionSupport (distributionDelta x) = {x} := by
  apply Set.Subset.antisymm
  · exact (distributionDelta_supported x).support_subset isClosed_singleton
  · intro y hy
    have hyx : y = x := Set.mem_singleton_iff.mp hy
    subst y
    change ∀ U : Set (Euclidean d), IsOpen U → x ∈ U →
      ∃ φ : 𝓢(Euclidean d, ℂ), HasCompactSupport (φ : Euclidean d → ℂ) ∧
        tsupport (φ : Euclidean d → ℂ) ⊆ U ∧ distributionDelta x φ ≠ 0
    intro U hU hxU
    obtain ⟨R, hR, hball⟩ := Metric.isOpen_iff.mp hU x hxU
    obtain ⟨b, hbcompact, hb0, _, hbsupp⟩ :=
      RieszEuclidean.exists_schwartz_bump (d := d) (show 0 < R / 2 by positivity)
    let φ := schwartzTranslateCLM (-x) b
    refine ⟨φ, ?_, ?_, ?_⟩
    · exact hbcompact.comp_homeomorph (Homeomorph.addLeft (-x))
    · have hts : tsupport (φ : Euclidean d → ℂ) ⊆ Metric.closedBall x (R / 2) := by
        apply closure_minimal _ (Metric.isClosed_closedBall)
        intro y hy
        change b (-x + y) ≠ 0 at hy
        apply Metric.mem_closedBall.mpr
        have hnorm : ‖-x + y‖ ≤ R / 2 := by
          by_contra hn
          have ht : R / 2 < ‖-x + y‖ := lt_of_not_ge hn
          exact hy (hbsupp (-x + y) ht.le)
        simpa [dist_eq_norm, sub_eq_add_neg, add_comm] using hnorm
      exact hts.trans (fun y hy => hball (Metric.mem_ball.mpr (by
        have hy' := Metric.mem_closedBall.mp hy
        change dist y x ≤ R / 2 at hy'
        change dist y x < R
        linarith [hR])))
    · change φ x ≠ 0
      simp [φ, schwartzTranslateCLM_apply, hb0]

/-- A nonzero compactly supported distribution has nonempty exact support. -/
theorem distributionSupport_nonempty {u : TemperedDistribution d} (hu0 : u ≠ 0) :
    (distributionSupport u).Nonempty := by
  by_contra hne
  have hempty : distributionSupport u = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
  apply hu0
  apply distribution_eq_of_compact_tests
  intro φ hφ
  have hs := (distributionSupportedIn_support u) φ hφ (by rw [hempty]; simp)
  simpa using hs

end RieszEuclidean.CompleteMinimal
