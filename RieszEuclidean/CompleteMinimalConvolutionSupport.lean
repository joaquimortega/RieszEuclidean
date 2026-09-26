import RieszEuclidean.CompleteMinimalDistributions
import RieszEuclidean.CompleteMinimalEllipsoid
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Geometry.Manifold.PartitionOfUnity

/-!
# The Titchmarsh–Lions hypothesis and its John-ellipsoid consequence

Distribution support is defined by actual local compact Schwartz tests. The
convolution relation is the iterated action on `φ(x+y)`; its definition contains
no support assertion. `TitchmarshLions` is an explicit proposition to be supplied
as a hypothesis, not an axiom or a theorem asserted without proof.
-/

noncomputable section
open MeasureTheory Set SchwartzMap
open scoped SchwartzMap Pointwise Manifold

namespace RieszEuclidean.CompleteMinimal

variable {d : ℕ}

/-- A point belongs to distribution support when every open neighborhood admits
a compactly supported smooth test on which the distribution does not vanish. -/
def distributionSupport (u : TemperedDistribution d) : Set (Euclidean d) :=
  {x | ∀ U : Set (Euclidean d), IsOpen U → x ∈ U →
    ∃ φ : 𝓢(Euclidean d, ℂ), HasCompactSupport (φ : Euclidean d → ℂ) ∧
      tsupport (φ : Euclidean d → ℂ) ⊆ U ∧ u φ ≠ 0}

theorem distributionSupport_isClosed (u : TemperedDistribution d) :
    IsClosed (distributionSupport u) := by
  rw [← isOpen_compl_iff]
  apply isOpen_iff_forall_mem_open.mpr
  intro x hx
  change ¬ ∀ U : Set (Euclidean d), IsOpen U → x ∈ U →
    ∃ φ : 𝓢(Euclidean d, ℂ), HasCompactSupport (φ : Euclidean d → ℂ) ∧
      tsupport (φ : Euclidean d → ℂ) ⊆ U ∧ u φ ≠ 0 at hx
  push_neg at hx
  obtain ⟨U, hU, hxU, hzero⟩ := hx
  refine ⟨U, ?_, hU, hxU⟩
  intro y hy
  change y ∉ distributionSupport u
  intro hys
  obtain ⟨φ, hc, hs, hn⟩ := hys U hU hy
  exact hn (hzero φ hc hs)

/-- A closed supporting set contains the exact local-test support. -/
theorem DistributionSupportedIn.support_subset {u : TemperedDistribution d}
    {S : Set (Euclidean d)} (hu : DistributionSupportedIn u S) (hS : IsClosed S) :
    distributionSupport u ⊆ S := by
  intro x hx
  by_contra hn
  obtain ⟨φ, hc, hs, hnonzero⟩ := hx Sᶜ hS.isOpen_compl hn
  apply hnonzero
  apply hu φ hc
  exact Set.disjoint_left.mpr fun y hy hyS => hs hy hyS

/-- A finite smooth partition of unity turns local vanishing into vanishing on
every compact Schwartz test outside the exact distribution support. -/
theorem distributionSupportedIn_support (u : TemperedDistribution d) :
    DistributionSupportedIn u (distributionSupport u) := by
  classical
  intro φ hφ hdisjoint
  have hlocal : ∀ x : tsupport (φ : Euclidean d → ℂ),
      ∃ U : Set (Euclidean d), IsOpen U ∧ x.val ∈ U ∧
        ∀ ψ : 𝓢(Euclidean d, ℂ), HasCompactSupport (ψ : Euclidean d → ℂ) →
          tsupport (ψ : Euclidean d → ℂ) ⊆ U → u ψ = 0 := by
    intro x
    have hx : x.val ∉ distributionSupport u :=
      fun h => Set.disjoint_left.mp hdisjoint x.property h
    change ¬ ∀ U : Set (Euclidean d), IsOpen U → x.val ∈ U →
      ∃ ψ : 𝓢(Euclidean d, ℂ), HasCompactSupport (ψ : Euclidean d → ℂ) ∧
        tsupport (ψ : Euclidean d → ℂ) ⊆ U ∧ u ψ ≠ 0 at hx
    push_neg at hx
    exact hx
  choose U hU hxU hzero using hlocal
  have hcover : tsupport (φ : Euclidean d → ℂ) ⊆ ⋃ i, U i := by
    intro x hx
    exact mem_iUnion.mpr ⟨⟨x, hx⟩, hxU ⟨x, hx⟩⟩
  obtain ⟨J, hJ⟩ := hφ.elim_finite_subcover U hU hcover
  have hcoverJ : tsupport (φ : Euclidean d → ℂ) ⊆ ⋃ i : J, U i.val := by
    intro x hx
    obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp (hJ hx)
    exact mem_iUnion.mpr ⟨⟨i, hi⟩, hxi⟩
  obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate
    𝓘(ℝ, Euclidean d) isClosed_closure (fun i : J => U i.val)
    (fun i => hU i.val) hcoverJ
  let ψ : J → 𝓢(Euclidean d, ℂ) := fun i =>
    compactSchwartz (fun x => ρ i x • φ x)
      ((ρ i).contMDiff.contDiff.smul (φ.smooth ⊤)) hφ.smul_left
  have hz : ∀ i : J, u (ψ i) = 0 := by
    intro i
    apply hzero i.val (ψ i) hφ.smul_left
    exact (tsupport_smul_subset_left (ρ i) φ).trans (hρ i)
  have he : φ = ∑ i : J, ψ i := by
    ext x
    change distributionDelta x φ = distributionDelta x (∑ i : J, ψ i)
    rw [map_sum]
    change φ x = ∑ i : J, ρ i x • φ x
    by_cases hx : φ x = 0
    · simp [hx]
    · have hxs : x ∈ tsupport (φ : Euclidean d → ℂ) := subset_tsupport _ hx
      have hone : (∑ i : J, ρ i x) = 1 := by
        rw [← finsum_eq_sum_of_fintype]
        exact ρ.sum_eq_one hxs
      rw [← Finset.sum_smul, hone, one_smul]
  rw [he, map_sum]
  exact Finset.sum_eq_zero fun i _ => hz i

/-- Exact local support and closed supporting sets give equivalent support conditions. -/
theorem distributionSupportedIn_iff_support_subset (u : TemperedDistribution d)
    (S : Set (Euclidean d)) (hS : IsClosed S) :
    DistributionSupportedIn u S ↔ distributionSupport u ⊆ S :=
  ⟨fun h => h.support_subset hS, fun h => (distributionSupportedIn_support u).mono h⟩

/-- Compact support of a distribution is an actual compact physical supporting set. -/
def CompactlySupportedDistribution (u : TemperedDistribution d) : Prop :=
  ∃ K : Set (Euclidean d), IsCompact K ∧ DistributionSupportedIn u K

theorem CompactlySupportedDistribution.support_isCompact {u : TemperedDistribution d}
    (hu : CompactlySupportedDistribution u) : IsCompact (distributionSupport u) := by
  obtain ⟨K, hK, hs⟩ := hu
  exact hK.of_isClosed_subset (distributionSupport_isClosed u) (hs.support_subset hK.isClosed)

@[simp] theorem distributionSupport_zero :
    distributionSupport (0 : TemperedDistribution d) = ∅ := by
  ext x
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hx
  obtain ⟨φ, _, _, hφ⟩ := hx univ isOpen_univ (mem_univ x)
  exact hφ rfl

theorem distributionDelta_compactlySupported (x : Euclidean d) :
    CompactlySupportedDistribution (distributionDelta x) :=
  ⟨{x}, isCompact_singleton, distributionDelta_supported x⟩

/-- Translation grows at most linearly and is smooth to every order. -/
theorem addLeft_hasTemperateGrowth (x : Euclidean d) :
    Function.HasTemperateGrowth (fun y : Euclidean d => x + y) := by
  apply Function.HasTemperateGrowth.of_fderiv
    (f := fun y : Euclidean d => x + y)
    (k := 1) (C := ‖x‖ + 1)
  · have he : fderiv ℝ (fun y : Euclidean d => x + y) =
        fun _ => ContinuousLinearMap.id ℝ (Euclidean d) := by
      funext y
      simpa using ((hasFDerivAt_const (𝕜 := ℝ) x y).add (hasFDerivAt_id y)).fderiv
    rw [he]
    exact Function.HasTemperateGrowth.const _
  · exact (differentiable_const x).add differentiable_id
  · intro y
    have h := norm_add_le x y
    simp only [pow_one]
    nlinarith [norm_nonneg x, norm_nonneg y]

/-- Translation acts on actual Schwartz functions as a continuous linear map. -/
def schwartzTranslateCLM (x : Euclidean d) :
    𝓢(Euclidean d, ℂ) →L[ℂ] 𝓢(Euclidean d, ℂ) :=
  SchwartzMap.compCLMOfAntilipschitz ℂ (addLeft_hasTemperateGrowth x)
    (show AntilipschitzWith 1 (fun y : Euclidean d => x + y) from by
      intro y z
      simp)

@[simp] theorem schwartzTranslateCLM_apply (x y : Euclidean d) (φ : 𝓢(Euclidean d, ℂ)) :
    schwartzTranslateCLM x φ y = φ (x + y) := rfl

/-- Pushforward translation of a distribution, with the usual test-function convention. -/
def distributionTranslate (x : Euclidean d) (u : TemperedDistribution d) :
    TemperedDistribution d := u.comp (schwartzTranslateCLM x)

@[simp] theorem distributionTranslate_apply (x : Euclidean d) (u : TemperedDistribution d)
    (φ : 𝓢(Euclidean d, ℂ)) : distributionTranslate x u φ = u (schwartzTranslateCLM x φ) := rfl

/-- Honest distribution convolution, expressed relationally through iterated test action.
The outer Schwartz representative is certified by pointwise equality to the inner
distribution action, so this definition does not assert a support theorem. -/
def IsDistributionConvolution (u v w : TemperedDistribution d) : Prop :=
  ∀ φ : 𝓢(Euclidean d, ℂ), ∃ ψ : 𝓢(Euclidean d, ℂ),
    (∀ x : Euclidean d, ψ x = v (schwartzTranslateCLM x φ)) ∧ w φ = u ψ

/-- The relational definition determines the resulting distribution uniquely. -/
theorem IsDistributionConvolution.unique {u v w z : TemperedDistribution d}
    (hw : IsDistributionConvolution u v w) (hz : IsDistributionConvolution u v z) : w = z := by
  ext φ
  obtain ⟨ψ, hψ, hwp⟩ := hw φ
  obtain ⟨χ, hχ, hzp⟩ := hz φ
  have he : ψ = χ := by ext x; exact (hψ x).trans (hχ x).symm
  rw [hwp, hzp, he]

/-- Convolution with a Dirac mass is the actual distribution translation. -/
theorem distributionConvolution_delta_right (u : TemperedDistribution d) (t : Euclidean d) :
    IsDistributionConvolution u (distributionDelta t) (distributionTranslate t u) := by
  intro φ
  refine ⟨schwartzTranslateCLM t φ, ?_, rfl⟩
  intro x
  simp only [schwartzTranslateCLM_apply, distributionDelta_apply, add_comm]

/-- The exact classical Titchmarsh–Lions convex-support theorem, formulated for
nonzero compactly supported distributions and their actual iterated-action convolution. -/
def TitchmarshLions (d : ℕ) : Prop :=
  ∀ u v w : TemperedDistribution d,
    CompactlySupportedDistribution u → CompactlySupportedDistribution v →
    u ≠ 0 → v ≠ 0 → IsDistributionConvolution u v w →
    convexHull ℝ (distributionSupport w) =
      convexHull ℝ (distributionSupport u) + convexHull ℝ (distributionSupport v)

/-- Titchmarsh–Lions makes every point of the second factor's support a physical
translation of the first factor's convex support inside the result's convex support. -/
theorem TitchmarshLions.translated_support_subset (hTL : TitchmarshLions d)
    {u v w : TemperedDistribution d} (hu : CompactlySupportedDistribution u)
    (hv : CompactlySupportedDistribution v) (hu0 : u ≠ 0) (hv0 : v ≠ 0)
    (hc : IsDistributionConvolution u v w) {t : Euclidean d}
    (ht : t ∈ distributionSupport v) :
    (fun x : Euclidean d => t + x) '' convexHull ℝ (distributionSupport u) ⊆
      convexHull ℝ (distributionSupport w) := by
  rintro _ ⟨x, hx, rfl⟩
  rw [hTL u v w hu hv hu0 hv0 hc]
  exact Set.mem_add.mpr ⟨x, hx, t, subset_convexHull ℝ _ ht, add_comm x t⟩

/-- The geometric support step: if the first factor fills a John ellipsoid and
the convolution is supported in the convex body, the second factor is supported
at the origin in the exact local-test sense. -/
theorem TitchmarshLions.support_subset_origin_of_john (hTL : TitchmarshLions d)
    {u v w : TemperedDistribution d} (hu : CompactlySupportedDistribution u)
    (hv : CompactlySupportedDistribution v) (hu0 : u ≠ 0) (hv0 : v ≠ 0)
    (hc : IsDistributionConvolution u v w) {K E : Set (Euclidean d)}
    (hK : Convex ℝ K) (hKclosed : IsClosed K) (hJ : IsJohnEllipsoid K E)
    (hEu : convexHull ℝ (distributionSupport u) = E)
    (hw : DistributionSupportedIn w K) : distributionSupport v ⊆ {0} := by
  intro t ht
  apply Set.mem_singleton_iff.mpr
  apply hJ.eq_zero_of_translated_subset hK
  have hs := hTL.translated_support_subset hu hv hu0 hv0 hc ht
  rw [hEu] at hs
  exact hs.trans (convexHull_min (hw.support_subset hKclosed) hK)

/-- The geometric convolution conclusion in the original test-annihilation support API. -/
theorem TitchmarshLions.supportedIn_origin_of_john (hTL : TitchmarshLions d)
    {u v w : TemperedDistribution d} (hu : CompactlySupportedDistribution u)
    (hv : CompactlySupportedDistribution v) (hu0 : u ≠ 0) (hv0 : v ≠ 0)
    (hc : IsDistributionConvolution u v w) {K E : Set (Euclidean d)}
    (hK : Convex ℝ K) (hKclosed : IsClosed K) (hJ : IsJohnEllipsoid K E)
    (hEu : convexHull ℝ (distributionSupport u) = E)
    (hw : DistributionSupportedIn w K) : DistributionSupportedIn v {0} :=
  (distributionSupportedIn_support v).mono
    (hTL.support_subset_origin_of_john hu hv hu0 hv0 hc hK hKclosed hJ hEu hw)

end RieszEuclidean.CompleteMinimal
