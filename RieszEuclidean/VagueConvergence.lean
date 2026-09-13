import Mathlib.Analysis.RCLike.Basic
import Mathlib.Topology.EMetricSpace.Paracompact
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import RieszEuclidean.ConfigurationMeasure
import RieszEuclidean.ConfigurationTopology
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Topology.ContinuousMap.CompactlySupported
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
open MeasureTheory Set Filter Metric
open scoped ENNReal CompactlySupported
namespace RieszEuclidean
/-- A finitely supported function integrates against counting measure by summation. -/
theorem integral_count_eq_sum {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    (s : Finset α) (f : α → ℝ) (hf : ∀ x, x ∉ s → f x = 0) :
    ∫ x, f x ∂Measure.count = ∑ x ∈ s, f x := by
  have hi : IntegrableOn f (s : Set α) Measure.count := by
    rw [← s.toSet.biUnion_of_singleton]
    simp [integrableOn_finset_iUnion]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := (s : Set α)) hf, integral_finset s f hi]
  simp [measureReal_def]
/-- An injective finite enumeration containing the support gives the counting integral. -/
theorem integral_count_eq_sum_of_injective {α ι : Type*}
    [MeasurableSpace α] [MeasurableSingletonClass α] [Fintype ι]
    (p : ι → α) (hp : Function.Injective p) (f : α → ℝ)
    (hf : ∀ x, x ∉ Set.range p → f x = 0) :
    ∫ x, f x ∂Measure.count = ∑ i, f (p i) := by
  classical
  rw [integral_count_eq_sum (Finset.univ.image p) f (by simpa using hf)]
  rw [Finset.sum_image]
  exact fun i _ j _ hij => hp hij
/-- Configuration integrals are finite sums over any enumeration covering the test support. -/
theorem configurationMeasure_integral_eq_sum {d : ℕ} {ι : Type*} [Fintype ι]
    (Γ : Set (Euclidean d)) (p : ι → Euclidean d) (hp : Function.Injective p)
    (hpΓ : ∀ i, p i ∈ Γ) (f : Euclidean d → ℝ) (hf : Continuous f)
    (hzero : ∀ x ∈ Γ, x ∉ Set.range p → f x = 0) :
    ∫ x, f x ∂configurationMeasure Γ = ∑ i, f (p i) := by
  rw [configurationMeasure, integral_map measurable_subtype_coe.aemeasurable
    hf.aestronglyMeasurable]
  let q : ι → Γ := fun i => ⟨p i, hpΓ i⟩
  apply integral_count_eq_sum_of_injective q
  · intro i j hij
    exact hp (congrArg Subtype.val hij)
  · intro x hx
    apply hzero x x.property
    rintro ⟨i, hi⟩
    exact hx ⟨i, Subtype.ext hi⟩
/-- Separation makes sufficiently close finite point matchings unique and controls
compactly supported test integrals by the oscillation of the test function. -/
theorem configurationMeasure_integral_matching_bound {d : ℕ} {ι : Type*} [Fintype ι]
    {δ r ε : ℝ} {Γ Δ : Set (Euclidean d)} (hΓ : Separated δ Γ) (hΔ : Separated δ Δ)
    (hr : 2 * r ≤ δ) (p : ι → Euclidean d) (hp : Function.Injective p)
    (hpΔ : ∀ i, p i ∈ Δ) (f : Euclidean d → ℝ) (hf : Continuous f)
    (hpzero : ∀ x ∈ Δ, x ∉ Set.range p → f x = 0)
    (hnear : ∀ i, ∃ x ∈ Γ, dist x (p i) < r)
    (hcover : ∀ x ∈ Γ, f x ≠ 0 → ∃ i, dist x (p i) < r)
    (hosc : ∀ x y, dist x y < r → ‖f x - f y‖ ≤ ε) :
    ‖(∫ x, f x ∂configurationMeasure Γ) - ∫ x, f x ∂configurationMeasure Δ‖ ≤
      Fintype.card ι * ε := by
  classical
  choose q hqΓ hqd using hnear
  have hqi : Function.Injective q := by
    intro i j he
    apply hp
    by_contra hn
    have hs := hΔ (hpΔ i) (hpΔ j) hn
    have hi : dist (p i) (q j) < r := by rw [dist_comm, ← he]; exact hqd i
    have hj := hqd j
    have ht := dist_triangle (p i) (q j) (p j)
    linarith
  have hqzero : ∀ x ∈ Γ, x ∉ Set.range q → f x = 0 := by
    intro x hx hn
    by_contra hfx
    obtain ⟨i, hi⟩ := hcover x hx hfx
    have he : x = q i := by
      by_contra hne
      have hs := hΓ hx (hqΓ i) hne
      have hqi' := hqd i
      have ht := dist_triangle x (p i) (q i)
      rw [dist_comm (p i) (q i)] at ht
      linarith
    exact hn ⟨i, he.symm⟩
  rw [configurationMeasure_integral_eq_sum Γ q hqi hqΓ f hf hqzero,
    configurationMeasure_integral_eq_sum Δ p hp hpΔ f hf hpzero, ← Finset.sum_sub_distrib]
  calc
    ‖∑ i, (f (q i) - f (p i))‖ ≤ ∑ i, ‖f (q i) - f (p i)‖ := norm_sum_le _ _
    _ ≤ ∑ _i : ι, ε := Finset.sum_le_sum (fun i _ => hosc _ _ (hqd i))
    _ = Fintype.card ι * ε := by simp
/-- Beurling convergence of uniformly separated configurations implies vague
convergence of their counting measures, tested on actual compactly supported functions. -/
theorem WeaklyConverges.tendsto_configurationMeasure_integral {d : ℕ} {δ : ℝ}
    {Γ : ℕ → Set (Euclidean d)} {Δ : Set (Euclidean d)}
    (h : WeaklyConverges Γ Δ) (hδ : 0 < δ) (hΓ : ∀ n, Separated δ (Γ n))
    (f : C_c(Euclidean d, ℝ)) :
    Tendsto (fun n => ∫ x, f x ∂configurationMeasure (Γ n)) atTop
      (nhds (∫ x, f x ∂configurationMeasure Δ)) := by
  classical
  have hΔ := h.separated hΓ
  obtain ⟨R, hR, hsupp⟩ := f.hasCompactSupport.isBounded.subset_ball_lt 0 (0 : Euclidean d)
  let K := Δ ∩ Metric.closedBall 0 (R + 1)
  have hK : K.Finite := hΔ.finite_inter_compact hδ (isCompact_closedBall 0 (R + 1))
  letI := hK.fintype
  let p : K → Euclidean d := Subtype.val
  have hpzero : ∀ x ∈ Δ, x ∉ Set.range p → f x = 0 := by
    intro x hx hn
    by_contra hf
    have hxR : ‖x‖ < R := by simpa using hsupp (subset_tsupport f hf)
    exact hn ⟨⟨x, hx, by simpa using (by linarith : ‖x‖ ≤ R + 1)⟩, rfl⟩
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  let η : ℝ := ε / (Fintype.card K + 1)
  have hη : 0 < η := div_pos hε (by positivity)
  obtain ⟨a, ha, hfa⟩ := Metric.uniformContinuous_iff.mp
    (CompactlySupportedContinuousMapClass.uniformContinuous f) η hη
  let r := min a (min 1 (δ / 3))
  have hr : 0 < r := lt_min ha (lt_min zero_lt_one (by positivity))
  have hra : r ≤ a := min_le_left _ _
  have hr1 : r ≤ 1 := (min_le_right _ _).trans (min_le_left _ _)
  have hrδ : r ≤ δ / 3 := (min_le_right _ _).trans (min_le_right _ _)
  obtain ⟨N, hN⟩ := h (R + 2) (by linarith) r hr
  refine ⟨N, fun n hn => ?_⟩
  have hnear : ∀ i : K, ∃ x ∈ Γ n, dist x (p i) < r := by
    intro i
    have hi : ‖(i : Euclidean d)‖ ≤ R + 1 := by simpa using i.property.2
    exact (hN n hn).2 i i.property.1 (by linarith)
  have hcover : ∀ x ∈ Γ n, f x ≠ 0 → ∃ i : K, dist x (p i) < r := by
    intro x hx hfx
    have hxR : ‖x‖ < R := by simpa using hsupp (subset_tsupport f hfx)
    obtain ⟨y, hy, hxy⟩ := (hN n hn).1 x hx (by linarith)
    have hyR : ‖y‖ ≤ R + 1 := by
      have ht := norm_sub_norm_le y x
      rw [← dist_eq_norm, dist_comm y x] at ht
      linarith
    exact ⟨⟨y, hy, by simpa using hyR⟩, hxy⟩
  have hbound := configurationMeasure_integral_matching_bound (hΓ n) hΔ
    (by linarith : 2 * r ≤ δ) p Subtype.val_injective (fun i => i.property.1)
    f f.continuous hpzero hnear hcover
    (fun x y hxy => le_of_lt (by simpa only [dist_eq_norm] using hfa (hxy.trans_le hra)))
  have hsmall : (Fintype.card K : ℝ) * η < ε := by
    have hden : (Fintype.card K : ℝ) + 1 ≠ 0 := by positivity
    have he := div_mul_cancel₀ ε hden
    change η * (Fintype.card K + 1) = ε at he
    nlinarith
  simpa only [dist_eq_norm] using hbound.trans_lt hsmall
/-- A point present in one separated configuration and absent from a closed one
is detected by a continuous compactly supported counting-measure test. -/
theorem exists_configurationMeasure_distinguishing_test {d : ℕ} {δ : ℝ}
    {Γ Δ : Set (Euclidean d)} (hΓ : Separated δ Γ) (hδ : 0 < δ) (hΔ : IsClosed Δ)
    {x : Euclidean d} (hx : x ∈ Γ) (hxΔ : x ∉ Δ) :
    ∃ f : C_c(Euclidean d, ℝ), (∫ y, f y ∂configurationMeasure Γ) = 1 ∧
      (∫ y, f y ∂configurationMeasure Δ) = 0 := by
  classical
  obtain ⟨a, ha, hball⟩ := Metric.mem_nhds_iff.mp (hΔ.isOpen_compl.mem_nhds hxΔ)
  let r := min δ a
  have hr : 0 < r := lt_min hδ ha
  let b : ContDiffBump x := ⟨r / 2, r, by positivity, by linarith⟩
  let f : C_c(Euclidean d, ℝ) := ⟨⟨b, b.continuous⟩, b.hasCompactSupport⟩
  refine ⟨f, ?_, ?_⟩
  · have hz : ∀ y ∈ Γ, y ∉ Set.range (fun _ : Unit => x) → f y = 0 := by
      intro y hy hn
      have hne : y ≠ x := by intro he; exact hn ⟨(), he.symm⟩
      have hd := hΓ hy hx hne
      exact b.zero_of_le_dist (show r ≤ dist y x by exact (min_le_left _ _).trans hd)
    rw [configurationMeasure_integral_eq_sum Γ (fun _ : Unit => x)
      (fun i j _ => Subsingleton.elim i j) (fun _ => hx) f f.continuous hz]
    simp only [Fintype.sum_unique]
    exact b.one_of_mem_closedBall (by simpa only [Metric.mem_closedBall, dist_self] using b.rIn_pos.le)
  · have hz : ∀ y ∈ Δ, f y = 0 := by
      intro y hy
      apply b.zero_of_le_dist
      change r ≤ dist y x
      by_contra hn
      have hd : dist y x < a := (lt_of_not_ge hn).trans_le (min_le_right _ _)
      exact (hball hd) hy
    rw [configurationMeasure_integral_eq_sum Δ (fun i : Fin 0 => Fin.elim0 i)
      (fun i => Fin.elim0 i) (fun i => Fin.elim0 i) f f.continuous (fun y hy _ => hz y hy)]
    simp
namespace SeparatedConfiguration
/-- All compactly supported continuous counting-measure tests. -/
noncomputable def countingProfile {d : ℕ} {δ : ℝ} (Γ : SeparatedConfiguration d δ) :
    C_c(Euclidean d, ℝ) → ℝ := fun f => ∫ x, f x ∂configurationMeasure Γ.carrier
/-- Counting-measure tests distinguish separated configurations. -/
theorem countingProfile_injective {d : ℕ} {δ : ℝ} (hδ : 0 < δ) :
    Function.Injective (countingProfile (d := d) (δ := δ)) := by
  intro Γ Δ he
  have hsub : ∀ A B : SeparatedConfiguration d δ, countingProfile A = countingProfile B →
      A.carrier ⊆ B.carrier := by
    intro A B hab x hx
    by_contra hn
    obtain ⟨f, hfA, hfB⟩ := exists_configurationMeasure_distinguishing_test
      A.separated hδ B.isClosed hx hn
    have ht := congrFun hab f
    change (∫ y, f y ∂configurationMeasure A.carrier) =
      ∫ y, f y ∂configurationMeasure B.carrier at ht
    rw [hfA, hfB] at ht
    norm_num at ht
  exact ext (Set.Subset.antisymm (hsub Γ Δ he) (hsub Δ Γ he.symm))
/-- Vague counting-measure tests are continuous in the Beurling configuration topology. -/
theorem continuous_countingProfile {d : ℕ} {δ : ℝ} (hδ : 0 < δ) :
    Continuous (countingProfile (d := d) (δ := δ)) := by
  apply continuous_pi
  intro f
  apply SeqContinuous.continuous
  intro Γ Δ ht
  exact (weaklyConverges_of_tendsto hδ ht).tendsto_configurationMeasure_integral
    hδ (fun n => (Γ n).separated) f
/-- Compactness and separation of configurations show that vague tests induce
exactly the configuration topology. -/
theorem countingProfile_isEmbedding {d : ℕ} {δ : ℝ} (hδ : 0 < δ) :
    Topology.IsEmbedding (countingProfile (d := d) (δ := δ)) := by
  letI := compactSpace (d := d) hδ
  exact ((continuous_countingProfile hδ).isClosedEmbedding (countingProfile_injective hδ)).isEmbedding
/-- Convergence in the configuration topology is exactly vague convergence. -/
theorem tendsto_iff_vague {d : ℕ} {δ : ℝ} (hδ : 0 < δ)
    {Γ : ℕ → SeparatedConfiguration d δ} {Δ : SeparatedConfiguration d δ} :
    Tendsto Γ atTop (nhds Δ) ↔ ∀ f : C_c(Euclidean d, ℝ),
      Tendsto (fun n => ∫ x, f x ∂configurationMeasure (Γ n).carrier) atTop
        (nhds (∫ x, f x ∂configurationMeasure Δ.carrier)) := by
  rw [(countingProfile_isEmbedding hδ).tendsto_nhds_iff]
  exact tendsto_pi_nhds
end SeparatedConfiguration
/-- For a common positive separation bound, Beurling local matching is equivalent
to vague convergence of the actual configuration counting measures. -/
theorem weaklyConverges_iff_vague {d : ℕ} {δ : ℝ} (hδ : 0 < δ)
    {Γ : ℕ → Set (Euclidean d)} {Δ : Set (Euclidean d)}
    (hΓ : ∀ n, Separated δ (Γ n)) (hΔ : Separated δ Δ) :
    WeaklyConverges Γ Δ ↔ ∀ f : C_c(Euclidean d, ℝ),
      Tendsto (fun n => ∫ x, f x ∂configurationMeasure (Γ n)) atTop
        (nhds (∫ x, f x ∂configurationMeasure Δ)) := by
  let A : ℕ → SeparatedConfiguration d δ := fun n => ⟨Γ n, (hΓ n).isClosed hδ, hΓ n⟩
  let B : SeparatedConfiguration d δ := ⟨Δ, hΔ.isClosed hδ, hΔ⟩
  exact (SeparatedConfiguration.tendsto_iff_weaklyConverges (Γ := A) (Γ₀ := B) hδ).symm.trans
    (SeparatedConfiguration.tendsto_iff_vague hδ)
end RieszEuclidean
