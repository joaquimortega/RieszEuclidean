import RieszEuclidean.SupportingDerivative
import RieszEuclidean.HessianConcavity

noncomputable section
open Filter Topology
namespace RieszEuclidean

/-- Convexity promotes a locally singleton exposed face to a singleton face. -/
theorem functional_singleton_face_of_local {n : ℕ} {K : Set (Euclidean n)}
    (hc : Convex ℝ K) {x : Euclidean n} {J : Euclidean n →L[ℝ] ℝ} (hx : x ∈ K)
    (hlocal : ∀ᶠ z in nhds x, z ∈ K → J (z - x) = 0 → z = x) :
    FunctionalSingletonFace K x J := by
  intro z hz hf
  by_contra hzx
  have hclosure : x ∈ closure (openSegment ℝ x z) :=
    segment_subset_closure_openSegment (left_mem_segment ℝ x z)
  obtain ⟨w, hwlocal, hwseg⟩ := mem_closure_iff_nhds.mp hclosure _ hlocal
  have hwK := hc.segment_subset hx hz (openSegment_subset_segment ℝ x z hwseg)
  have hwface : J (w - x) = 0 := by
    obtain ⟨a, b, _, _, hab, rfl⟩ := hwseg
    rw [map_sub, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
    rw [map_sub] at hf
    rw [sub_eq_zero.mp hf, ← add_mul, hab, one_mul, _root_.sub_self]
  have hwx := hwlocal hwK hwface
  rw [hwx, left_mem_openSegment_iff] at hwseg
  exact hzx hwseg.symm

/-- A chart with a strictly concave linear height cannot contain a nontrivial
straight boundary segment. This yields the singleton supporting faces. -/
theorem strictConcave_chart_singleton_faces {n : ℕ}
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Ω W : Set (Euclidean n)} {D : Set E}
    (hΩ : IsOpen Ω) (hc : Convex ℝ Ω) (hW : IsOpen W) (hcW : Convex ℝ W)
    (φ : E → Euclidean n) (P : Euclidean n →L[ℝ] E) (p : Euclidean n)
    (H : Euclidean n →L[ℝ] ℝ)
    (hconc : StrictConcaveOn ℝ D (fun u => H (φ u)))
    (hinv : ∀ x ∈ W, x ∈ frontier Ω → φ (P (x-p)) = x)
    (hparam : ∀ x ∈ W, P (x-p) ∈ D) :
    ∀ x ∈ W ∩ frontier Ω, ∀ J : Euclidean n →L[ℝ] ℝ,
      J ≠ 0 → FunctionalSupportsAt (closure Ω) x J →
      FunctionalSingletonFace (closure Ω) x J := by
  intro x hx J hJ hs
  apply functional_singleton_face_of_local hc.closure (frontier_subset_closure hx.2)
  filter_upwards [hW.mem_nhds hx.1] with y hyW
  intro hyK hyface
  by_contra hxy
  have hS (z : Euclidean n) (hzK : z ∈ closure Ω) (hzJ : J (z-x) = 0) :
      z ∈ frontier Ω := by
    rw [hΩ.frontier_eq]
    refine ⟨hzK, ?_⟩
    intro hzΩ
    have hh := supporting_functional_strict_interior hΩ hzΩ hJ hs
    rw [hzJ] at hh
    exact lt_irrefl _ hh
  have hyS := hS y hyK hyface
  let m := (1/2 : ℝ) • x + (1/2 : ℝ) • y
  have hmW : m ∈ W := hcW hx.1 hyW (by norm_num) (by norm_num) (by norm_num)
  have hmK : m ∈ closure Ω := hc.closure (frontier_subset_closure hx.2) hyK
    (by norm_num) (by norm_num) (by norm_num)
  have hmface : J (m-x) = 0 := by
    dsimp [m]
    simp only [map_sub, map_add, map_smul, smul_eq_mul] at hyface ⊢
    linarith
  have hmS := hS m hmK hmface
  have hne : P (x-p) ≠ P (y-p) := by
    intro he
    have hh := congrArg φ he
    rw [hinv x hx.1 hx.2, hinv y hyW hyS] at hh
    exact hxy hh.symm
  obtain ⟨_, hstrict⟩ := hconc
  have hh := hstrict (hparam x hx.1) (hparam y hyW) hne
    (by norm_num : (0 : ℝ) < 1/2) (by norm_num : (0 : ℝ) < 1/2) (by norm_num)
  have he : (1/2 : ℝ) • P (x-p) + (1/2 : ℝ) • P (y-p) = P (m-p) := by
    rw [← map_smul, ← map_smul, ← map_add]
    congr 1
    dsimp [m]
    module
  dsimp only at hh
  rw [he, hinv m hmW hmS, hinv x hx.1 hx.2, hinv y hyW hyS] at hh
  simp only [m, map_add, map_smul, lt_self_iff_false] at hh

end RieszEuclidean
