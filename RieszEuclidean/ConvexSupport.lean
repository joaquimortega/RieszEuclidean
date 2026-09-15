import RieszEuclidean.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.NoAtoms
import Mathlib.Analysis.Convex.Topology

noncomputable section
open MeasureTheory Topology
namespace RieszEuclidean

/-- The vector `v` supports `K` at `x`, with the outward sign convention. -/
def SupportsAt {d : ℕ} (K : Set (Euclidean d)) (x v : Euclidean d) : Prop :=
  ∀ z ∈ K, inner (𝕜 := ℝ) v (z - x) ≤ 0

/-- The supporting hyperplane with normal `v` meets `K` only at `x`. -/
def SingletonSupportingFace {d : ℕ} (K : Set (Euclidean d))
    (x v : Euclidean d) : Prop :=
  ∀ z ∈ K, inner (𝕜 := ℝ) v (z - x) = 0 → z = x

/-- Equal outward normals cannot occur at two different supporting points
when one supporting face is a singleton. -/
theorem supporting_points_eq_of_same_normal {d : ℕ} {K : Set (Euclidean d)}
    {x y v : Euclidean d} (hx : x ∈ K) (hy : y ∈ K)
    (hsx : SupportsAt K x v) (hsy : SupportsAt K y v)
    (hface : SingletonSupportingFace K x v) : y = x := by
  apply hface y hy
  have h₁ := hsx y hy
  have h₂ := hsy x hx
  rw [inner_sub_right] at h₁ h₂ ⊢
  linarith

/-- Opposite supporting normals at `x` and `x + θ` force the entire
intersection of the closed domain with its translate into `{x}`. -/
theorem translated_inter_subset_singleton_of_opposite_normals {d : ℕ}
    {K : Set (Euclidean d)} {x θ v : Euclidean d}
    (hsx : SupportsAt K x v) (hsy : SupportsAt K (x + θ) (-v))
    (hface : SingletonSupportingFace K x v) :
    K ∩ translate θ K ⊆ {x} := by
  intro z hz
  apply hface z hz.1
  have h₁ := hsx z hz.1
  have h₂ := hsy (z + θ) hz.2
  have he : z + θ - (x + θ) = z - x := by abel
  rw [he, inner_neg_left] at h₂
  linarith

/-- The normal-case argument in Lemma 8.3. The only analytic input is
nullity of the transverse intersections. Equal normals are impossible;
one pair of opposite normals makes the entire intersection a singleton. -/
theorem patch_translated_inter_null_of_transverse_null {d : ℕ}
    {K S U : Set (Euclidean d)} (hSK : S ⊆ K) (hUS : U ⊆ S)
    (N : Euclidean d → Euclidean d)
    (hs : ∀ x ∈ S, SupportsAt K x (N x))
    (hf : ∀ x ∈ U, SingletonSupportingFace K x (N x))
    (μ : Measure (Euclidean d)) [NoAtoms μ]
    {θ : Euclidean d} (hθ : θ ≠ 0)
    (htransverse : μ {x | x ∈ U ∧ x + θ ∈ S ∧
      N (x + θ) ≠ N x ∧ N (x + θ) ≠ -N x} = 0) :
    μ (U ∩ translate θ S) = 0 := by
  classical
  by_cases hopp : ∃ x ∈ U, x + θ ∈ S ∧ N (x + θ) = -N x
  · obtain ⟨x, hx, hy, he⟩ := hopp
    have hsy : SupportsAt K (x + θ) (-N x) := he ▸ hs (x + θ) hy
    have hsingle := translated_inter_subset_singleton_of_opposite_normals
      (hs x (hUS hx)) hsy (hf x hx)
    apply measure_mono_null (t := {x}) _ (measure_singleton x)
    intro z hz
    exact hsingle ⟨hSK (hUS hz.1), hSK hz.2⟩
  · apply measure_mono_null _ htransverse
    intro x hx
    refine ⟨hx.1, hx.2, ?_, ?_⟩
    · intro he
      have hy := supporting_points_eq_of_same_normal (hSK (hUS hx.1))
        (hSK hx.2) (hs x (hUS hx.1)) (he ▸ hs (x + θ) hx.2) (hf x hx.1)
      apply hθ
      exact add_left_cancel (hy.trans (add_zero x).symm)
    · intro he
      exact hopp ⟨x, hx.1, hx.2, he⟩

/-- For a convex set, a supporting face that is locally a singleton is a
singleton globally. This is the segment argument used after obtaining curvature. -/
theorem singletonSupportingFace_of_local {d : ℕ} {K : Set (Euclidean d)}
    (hc : Convex ℝ K) {x v : Euclidean d} (hx : x ∈ K)
    (hlocal : ∀ᶠ z in nhds x, z ∈ K →
      inner (𝕜 := ℝ) v (z - x) = 0 → z = x) :
    SingletonSupportingFace K x v := by
  intro z hz hf
  by_contra hzx
  have hclosure : x ∈ closure (openSegment ℝ x z) :=
    segment_subset_closure_openSegment (left_mem_segment ℝ x z)
  obtain ⟨w, hwlocal, hwseg⟩ := mem_closure_iff_nhds.mp hclosure _ hlocal
  have hwK := hc.segment_subset hx hz (openSegment_subset_segment ℝ x z hwseg)
  have hwface : inner (𝕜 := ℝ) v (w - x) = 0 := by
    obtain ⟨a, b, _, _, hab, rfl⟩ := hwseg
    rw [inner_sub_right, inner_add_right, inner_smul_right, inner_smul_right]
    rw [inner_sub_right] at hf
    rw [sub_eq_zero.mp hf, ← add_mul, hab, one_mul, _root_.sub_self]
  have hwx := hwlocal hwK hwface
  rw [hwx, left_mem_openSegment_iff] at hwseg
  exact hzx hwseg.symm

/-- At a farthest point, containment in a ball gives a strict supporting face.
This is the global support part of the contact-ball construction; it does not
assert the still separate persistence of positive curvature on a patch. -/
theorem farthest_point_support {d : ℕ} {K : Set (Euclidean d)}
    {p c : Euclidean d} (hfar : ∀ z ∈ K, ‖z - c‖ ≤ ‖p - c‖) :
    SupportsAt K p (p - c) ∧ SingletonSupportingFace K p (p - c) := by
  have he (z : Euclidean d) : ‖z - c‖ ^ 2 =
      ‖p - c‖ ^ 2 + 2 * inner (𝕜 := ℝ) (p - c) (z - p) + ‖z - p‖ ^ 2 := by
    have h : z - c = (p - c) + (z - p) := by abel
    rw [h, norm_add_sq_real]
  constructor
  · intro z hz
    have h := hfar z hz
    have heq := he z
    nlinarith [sq_nonneg ‖z - p‖, norm_nonneg (z - c)]
  · intro z hz hf
    have h := hfar z hz
    have heq := he z
    have hn : ‖z - p‖ = 0 := by
      nlinarith [sq_nonneg ‖z - p‖, norm_nonneg (z - c), norm_nonneg (z - p)]
    exact sub_eq_zero.mp (norm_eq_zero.mp hn)

end RieszEuclidean
