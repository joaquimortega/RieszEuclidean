import RieszEuclidean.C2Boundary
import RieszEuclidean.ConvexSupport
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.ContDiff.RCLike

noncomputable section
open MeasureTheory Filter Topology
namespace RieszEuclidean

/-- A supporting hyperplane written using a real linear functional. -/
def FunctionalSupportsAt {n : ℕ} (K : Set (Euclidean n))
    (p : Euclidean n) (L : Euclidean n →L[ℝ] ℝ) : Prop :=
  ∀ z ∈ K, L (z - p) ≤ 0

/-- The exposed face of a supporting functional is a singleton. -/
def FunctionalSingletonFace {n : ℕ} (K : Set (Euclidean n))
    (p : Euclidean n) (L : Euclidean n →L[ℝ] ℝ) : Prop :=
  ∀ z ∈ K, L (z - p) = 0 → z = p

/-- A local defining function of a convex domain has a globally supporting
derivative. The positive tangent cone carries every chord direction. -/
theorem defining_derivative_supports {n : ℕ} {Ω W : Set (Euclidean n)}
    (hΩ : IsOpen Ω) (hc : Convex ℝ Ω) {p : Euclidean n}
    (hp : p ∈ frontier Ω) (hW : IsOpen W) (hpW : p ∈ W)
    {f : Euclidean n → ℝ} {L : Euclidean n →L[ℝ] ℝ}
    (hf : HasFDerivAt f L p) (hf0 : f p = 0)
    (hneg : ∀ x ∈ W, x ∈ Ω ↔ f x < 0)
    (hzero : ∀ x ∈ W, x ∈ frontier Ω ↔ f x = 0) :
    FunctionalSupportsAt (closure Ω) p L := by
  have hm : IsLocalMaxOn f (closure Ω) p := by
    change ∀ᶠ x in nhdsWithin p (closure Ω), f x ≤ f p
    rw [eventually_nhdsWithin_iff]
    filter_upwards [hW.mem_nhds hpW] with x hx
    intro hxK
    rw [hf0]
    by_cases hxΩ : x ∈ Ω
    · exact ((hneg x hx).mp hxΩ).le
    · have hxS : x ∈ frontier Ω := by
        rw [hΩ.frontier_eq]
        exact ⟨hxK, hxΩ⟩
      exact ((hzero x hx).mp hxS).le
  intro z hz
  exact hm.hasFDerivWithinAt_nonpos hf.hasFDerivWithinAt
    (sub_mem_posTangentConeAt_of_segment_subset
      (hc.closure.segment_subset (frontier_subset_closure hp) hz))

/-- Every C² boundary point has a nonzero supporting defining derivative and
a local regular level description. -/
theorem exists_supporting_defining_function {n : ℕ} {Ω : Set (Euclidean n)}
    (hΩ : IsOpen Ω) (hc : Convex ℝ Ω) (hC : HasC2Boundary Ω)
    {p : Euclidean n} (hp : p ∈ frontier Ω) :
    ∃ (f : Euclidean n → ℝ) (L : Euclidean n →L[ℝ] ℝ),
      HasStrictFDerivAt f L p ∧ L ≠ 0 ∧ f p = 0 ∧
      FunctionalSupportsAt (closure Ω) p L ∧
      ∀ᶠ x in nhds p, x ∈ frontier Ω ↔ f x = 0 := by
  obtain ⟨W, f, hW, hpW, hf, hL, hneg, hzero⟩ := hC p hp
  have hd := (hf.contDiffAt (hW.mem_nhds hpW)).hasStrictFDerivAt (by norm_num)
  have hf0 := (hzero p hpW).mp hp
  refine ⟨f, fderiv ℝ f p, hd, hL p hpW, hf0,
    defining_derivative_supports hΩ hc hp hW hpW hd.hasFDerivAt hf0 hneg hzero, ?_⟩
  exact Filter.eventually_of_mem (hW.mem_nhds hpW) hzero

/-- Proportional supporting functionals with a positive factor expose the same
face, so a singleton face forces equality of the support points. -/
theorem functional_support_points_eq {n : ℕ} {K : Set (Euclidean n)}
    {x y : Euclidean n} {L M : Euclidean n →L[ℝ] ℝ} {c : ℝ}
    (hx : x ∈ K) (hy : y ∈ K) (hL : FunctionalSupportsAt K x L)
    (hM : FunctionalSupportsAt K y M) (hface : FunctionalSingletonFace K x L)
    (he : M = c • L) (hc : 0 < c) : y = x := by
  apply hface y hy
  have h₁ := hL y hy
  have h₂ := hM x hx
  rw [he, ContinuousLinearMap.smul_apply, smul_eq_mul, map_sub] at h₂
  rw [map_sub] at h₁ ⊢
  nlinarith

/-- A negative proportionality factor places the two translated domains on
opposite sides of one supporting plane. -/
theorem functional_opposite_inter_subset_singleton {n : ℕ} {K : Set (Euclidean n)}
    {x θ : Euclidean n} {L M : Euclidean n →L[ℝ] ℝ} {c : ℝ}
    (hL : FunctionalSupportsAt K x L) (hM : FunctionalSupportsAt K (x + θ) M)
    (hface : FunctionalSingletonFace K x L) (he : M = c • L) (hc : c < 0) :
    K ∩ translate θ K ⊆ {x} := by
  intro z hz
  apply hface z hz.1
  have h₁ := hL z hz.1
  have h₂ := hM (z + θ) hz.2
  have hsub : z + θ - (x + θ) = z - x := by abel
  rw [he, ContinuousLinearMap.smul_apply, smul_eq_mul, hsub] at h₂
  nlinarith

end RieszEuclidean
