import RieszEuclidean.Basic

noncomputable section
open MeasureTheory Filter Topology
namespace RieszEuclidean

/-- The literal open standard triangle in the Euclidean plane. -/
def standardTriangle (s : ℝ) : Set (Euclidean 2) :=
  {x | 0 < x 0 ∧ 0 < x 1 ∧ x 0 + x 1 < s}

/-- The relative interior of the horizontal edge of the standard triangle. -/
def standardTriangleEdge (s : ℝ) : Set (Euclidean 2) :=
  {x | 0 < x 0 ∧ x 1 = 0 ∧ x 0 < s}

/-- The second coordinate is the fixed inward normal coordinate on the bottom edge. -/
theorem standardTriangleEdge_translation_normal_zero (s : ℝ) (t θ : Euclidean 2)
    (ht : t ∈ standardTriangleEdge s) (htθ : t + θ ∈ standardTriangleEdge s) :
    θ 1 = 0 := by
  have h := htθ.2.1
  simp only [PiLp.add_apply, ht.2.1, zero_add] at h
  exact h

/-- Near each point of the open bottom edge, triangle membership is exactly positivity
of the common inward normal coordinate. -/
theorem standardTriangleEdge_local_halfplane (s : ℝ) (t : Euclidean 2)
    (ht : t ∈ standardTriangleEdge s) :
    ∀ᶠ u in nhds t, u ∈ standardTriangle s ↔ 0 < u 1 := by
  have hc (i : Fin 2) : Continuous (fun x : Euclidean 2 => x i) :=
    (continuous_apply i).comp (PiLp.continuous_equiv 2 (fun _ : Fin 2 => ℝ))
  have hleft : ∀ᶠ u in nhds t, 0 < u 0 :=
    (isOpen_lt continuous_const (hc 0)).mem_nhds ht.1
  have hsum : ∀ᶠ u in nhds t, u 0 + u 1 < s :=
    (isOpen_lt ((hc 0).add (hc 1)) continuous_const).mem_nhds
      (by simpa only [Set.mem_setOf_eq, ht.2.1, add_zero] using ht.2.2)
  filter_upwards [hleft, hsum] with u hu hv
  exact ⟨fun h => h.2.1, fun h => ⟨hu, h, hv⟩⟩

/-- Translations between two points of the bottom edge preserve which side enters
the actual triangle in sufficiently small neighborhoods. -/
theorem standardTriangleEdge_same_direction_nhds (s : ℝ) (t θ : Euclidean 2)
    (ht : t ∈ standardTriangleEdge s) (htθ : t + θ ∈ standardTriangleEdge s) :
    ∀ᶠ u in nhds t, u + θ ∈ standardTriangle s ↔ u ∈ standardTriangle s := by
  have hnormal := standardTriangleEdge_translation_normal_zero s t θ ht htθ
  have hshift : Tendsto (fun u : Euclidean 2 => u + θ) (nhds t) (nhds (t + θ)) :=
    (continuous_id.add continuous_const).continuousAt
  filter_upwards [standardTriangleEdge_local_halfplane s t ht,
    hshift.eventually (standardTriangleEdge_local_halfplane s (t + θ) htθ)] with u hu hv
  rw [hu, hv]
  simp only [PiLp.add_apply, hnormal, add_zero]

/-- Along any approaching sequence, every surviving translated bottom-edge point
crosses in the same direction. -/
theorem standardTriangleEdge_same_direction (s : ℝ) (t θ : Euclidean 2)
    (ht : t ∈ standardTriangleEdge s) (htθ : t + θ ∈ standardTriangleEdge s)
    (ts : ℕ → Euclidean 2) (hts : Tendsto ts atTop (nhds t)) :
    ∀ᶠ j in atTop, ts j + θ ∈ standardTriangle s ↔ ts j ∈ standardTriangle s :=
  hts.eventually (standardTriangleEdge_same_direction_nhds s t θ ht htθ)

/-- A finite intersection of strict supporting halfspaces in actual Euclidean space. -/
def strictHalfspaceIntersection {d : ℕ} {ι : Type*}
    (normal : ι → Euclidean d) (offset : ι → ℝ) : Set (Euclidean d) :=
  {x | ∀ i, offset i < inner (𝕜 := ℝ) x (normal i)}

/-- At a point with exactly one active supporting constraint, membership in the
polyhedron is locally determined by that constraint's inward normal. -/
theorem strictHalfspaceIntersection_local_halfspace {d : ℕ} {ι : Type*} [Fintype ι]
    (normal : ι → Euclidean d) (offset : ι → ℝ) (j : ι) (t : Euclidean d)
    (hstrict : ∀ i, i ≠ j → offset i < inner (𝕜 := ℝ) t (normal i)) :
    ∀ᶠ u in nhds t, u ∈ strictHalfspaceIntersection normal offset ↔
      offset j < inner (𝕜 := ℝ) u (normal j) := by
  have hother : ∀ i, ∀ᶠ u in nhds t,
      i ≠ j → offset i < inner (𝕜 := ℝ) u (normal i) := by
    intro i
    by_cases hij : i = j
    · exact Eventually.of_forall (fun _ h => (h hij).elim)
    · have hi : ∀ᶠ u in nhds t, offset i < inner (𝕜 := ℝ) u (normal i) :=
        (isOpen_lt continuous_const (by fun_prop)).mem_nhds (hstrict i hij)
      exact hi.mono (fun _ h _ => h)
  filter_upwards [eventually_all.mpr hother] with u hu
  constructor
  · exact fun h => h j
  · intro h i
    by_cases hij : i = j
    · simpa only [hij] using h
    · exact hu i hij

/-- Two points in the relative interior of the same supporting face have identical
local crossing direction, with their tangential translation explicitly retained. -/
theorem strictHalfspaceIntersection_same_direction {d : ℕ} {ι : Type*} [Fintype ι]
    (normal : ι → Euclidean d) (offset : ι → ℝ) (j : ι) (t θ : Euclidean d)
    (hactive : inner (𝕜 := ℝ) t (normal j) = offset j)
    (hactiveθ : inner (𝕜 := ℝ) (t + θ) (normal j) = offset j)
    (hstrict : ∀ i, i ≠ j → offset i < inner (𝕜 := ℝ) t (normal i))
    (hstrictθ : ∀ i, i ≠ j → offset i < inner (𝕜 := ℝ) (t + θ) (normal i)) :
    ∀ᶠ u in nhds t, u + θ ∈ strictHalfspaceIntersection normal offset ↔
      u ∈ strictHalfspaceIntersection normal offset := by
  have hn : inner (𝕜 := ℝ) θ (normal j) = 0 := by
    rw [inner_add_left, hactive] at hactiveθ
    linarith
  have hshift : Tendsto (fun u : Euclidean d => u + θ) (nhds t) (nhds (t + θ)) :=
    (continuous_id.add continuous_const).continuousAt
  filter_upwards [strictHalfspaceIntersection_local_halfspace normal offset j t hstrict,
    hshift.eventually (strictHalfspaceIntersection_local_halfspace
      normal offset j (t + θ) hstrictθ)] with u hu hv
  rw [hu, hv, inner_add_left, hn, add_zero]

end RieszEuclidean
