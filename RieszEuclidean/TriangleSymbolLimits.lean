import RieszEuclidean.TriangleBoundary
import RieszEuclidean.BoundarySymbols

noncomputable section
open MeasureTheory Filter Topology
namespace RieszEuclidean

/-- The full surviving bottom-edge jump, retaining tangential translations. -/
def standardTriangleJump (s : ℝ) (t : Euclidean 2) : Set (Euclidean 2) :=
  {θ | t + θ ∈ standardTriangleEdge s}

/-- The full edge jump is a measurable frequency set. -/
theorem standardTriangleJump_measurableSet (s : ℝ) (hs : 0 < s) (t : Euclidean 2) :
    MeasurableSet (standardTriangleJump s t) := by
  have he : MeasurableSet (standardTriangleEdge s) := by
    rw [standardTriangleEdge_eq_openSegment s hs]
    exact measurableSet_openEdge _ _ (standardHorizontalPoint_ne_zero s hs).symm
  exact he.preimage (measurable_const.add measurable_id)

/-- The invariant zero frequency always belongs to the edge jump. -/
theorem zero_mem_standardTriangleJump (s : ℝ) (t : Euclidean 2)
    (ht : t ∈ standardTriangleEdge s) : 0 ∈ standardTriangleJump s t := by
  simpa only [standardTriangleJump, Set.mem_setOf_eq, add_zero] using ht

/-- Every retained jump frequency is tangential to the chosen bottom edge. -/
theorem standardTriangleJump_normal_zero (s : ℝ) (t : Euclidean 2)
    (ht : t ∈ standardTriangleEdge s) {θ : Euclidean 2}
    (hθ : θ ∈ standardTriangleJump s t) : θ 1 = 0 :=
  standardTriangleEdge_translation_normal_zero s t θ ht hθ

/-- Jump frequencies lie outside the original open-domain symbol. -/
theorem standardTriangleJump_not_mem (s : ℝ) (t : Euclidean 2)
    {θ : Euclidean 2} (hθ : θ ∈ standardTriangleJump s t) :
    t + θ ∉ standardTriangle s := by
  intro h
  have he : (t + θ) 1 = 0 := hθ.2.1
  exact (ne_of_gt h.2.1) he

/-- Arbitrary interior approaches eventually turn on each retained jump frequency. -/
theorem standardTriangleJump_interior_eventually (s : ℝ) (t θ : Euclidean 2)
    (ht : t ∈ standardTriangleEdge s) (hθ : θ ∈ standardTriangleJump s t)
    {ts : ℕ → Euclidean 2} (hts : Tendsto ts atTop (nhds t))
    (hin : ∀ n, ts n ∈ standardTriangle s) :
    ∀ᶠ n in atTop, cutoffSymbol (standardTriangle s) (ts n) θ = 1 := by
  filter_upwards [standardTriangleEdge_same_direction s t θ ht hθ ts hts] with n hn
  exact Set.indicator_of_mem (hn.mpr (hin n)) _

/-- Arbitrary strict exterior approaches eventually turn off each retained frequency. -/
theorem standardTriangleJump_exterior_eventually (s : ℝ) (t θ : Euclidean 2)
    (ht : t ∈ standardTriangleEdge s) (hθ : θ ∈ standardTriangleJump s t)
    {ts : ℕ → Euclidean 2} (hts : Tendsto ts atTop (nhds t))
    (hout : ∀ n, ts n ∉ closure (standardTriangle s)) :
    ∀ᶠ n in atTop, cutoffSymbol (standardTriangle s) (ts n) θ = 0 := by
  filter_upwards [standardTriangleEdge_same_direction s t θ ht hθ ts hts] with n hn
  exact Set.indicator_of_not_mem (fun h => hout n (subset_closure (hn.mp h))) _

/-- At a clean bottom point the interior symbol gains the entire edge jump. -/
theorem standardTriangle_cutoffSymbol_interior_ae_tendsto (s : ℝ)
    (t : Euclidean 2) (ht : t ∈ standardTriangleEdge s)
    (σ : Measure (Euclidean 2))
    (hclean : σ {θ | t + θ ∈ frontier (standardTriangle s) \ standardTriangleEdge s} = 0)
    {ts : ℕ → Euclidean 2} (hts : Tendsto ts atTop (nhds t))
    (hin : ∀ n, ts n ∈ standardTriangle s) :
    ∀ᵐ θ ∂σ, Tendsto (fun n => cutoffSymbol (standardTriangle s) (ts n) θ) atTop
      (nhds (cutoffSymbol (standardTriangle s) t θ +
        (standardTriangleJump s t).indicator (fun _ => (1 : ℂ)) θ)) := by
  have hae : ∀ᵐ θ ∂σ,
      t + θ ∉ frontier (standardTriangle s) \ standardTriangleEdge s :=
    compl_mem_ae_iff.mpr hclean
  filter_upwards [hae] with θ hθ
  by_cases hj : θ ∈ standardTriangleJump s t
  · have hn := standardTriangleJump_not_mem s t hj
    simpa only [cutoffSymbol, Set.indicator_of_not_mem hn, Set.indicator_of_mem hj,
      zero_add] using
      tendsto_const_nhds.congr' ((standardTriangleJump_interior_eventually s t θ ht hj hts hin).mono (fun _ h => h.symm))
  · have hoff : t + θ ∉ frontier (standardTriangle s) := fun h => hθ ⟨h, hj⟩
    simpa only [Set.indicator_of_not_mem hj, add_zero] using
      tendsto_cutoffSymbol_off_frontier hts hoff

/-- At the same clean point the exterior symbol keeps the original open-domain value. -/
theorem standardTriangle_cutoffSymbol_exterior_ae_tendsto (s : ℝ)
    (t : Euclidean 2) (ht : t ∈ standardTriangleEdge s)
    (σ : Measure (Euclidean 2))
    (hclean : σ {θ | t + θ ∈ frontier (standardTriangle s) \ standardTriangleEdge s} = 0)
    {ts : ℕ → Euclidean 2} (hts : Tendsto ts atTop (nhds t))
    (hout : ∀ n, ts n ∉ closure (standardTriangle s)) :
    ∀ᵐ θ ∂σ, Tendsto (fun n => cutoffSymbol (standardTriangle s) (ts n) θ) atTop
      (nhds (cutoffSymbol (standardTriangle s) t θ)) := by
  have hae : ∀ᵐ θ ∂σ,
      t + θ ∉ frontier (standardTriangle s) \ standardTriangleEdge s :=
    compl_mem_ae_iff.mpr hclean
  filter_upwards [hae] with θ hθ
  by_cases hj : θ ∈ standardTriangleJump s t
  · have hn := standardTriangleJump_not_mem s t hj
    simpa only [cutoffSymbol, Set.indicator_of_not_mem hn] using
      tendsto_const_nhds.congr' ((standardTriangleJump_exterior_eventually s t θ ht hj hts hout).mono (fun _ h => h.symm))
  · exact tendsto_cutoffSymbol_off_frontier hts (fun h => hθ ⟨h, hj⟩)

/-- The jump is the whole translated open edge interval on the tangent line. -/
theorem standardTriangleJump_eq_tangent_interval (s : ℝ) (t : Euclidean 2)
    (ht : t ∈ standardTriangleEdge s) :
    standardTriangleJump s t =
      {θ : Euclidean 2 | θ 1 = 0 ∧ -(t 0) < θ 0 ∧ θ 0 < s - t 0} := by
  ext θ
  change (0 < t 0 + θ 0 ∧ t 1 + θ 1 = 0 ∧ t 0 + θ 0 < s) ↔ _
  rw [ht.2.1, zero_add]
  constructor
  · rintro ⟨h₀, h₁, h₂⟩
    exact ⟨h₁, by linarith, by linarith⟩
  · rintro ⟨h₁, h₀, h₂⟩
    exact ⟨by linarith, h₁, by linarith⟩

/-- Every ambient conull set supplies both boundary approaches at one point clean
for the entire control measure, with the actual shifted-indicator limits. -/
theorem exists_standardTriangle_boundary_symbol_limits (s : ℝ) (hs : 0 < s)
    (σ : Measure (Euclidean 2)) [SFinite σ]
    {G : Set (Euclidean 2)} (hG : volume Gᶜ = 0) :
    ∃ t ∈ standardTriangleEdge s,
      σ {θ | t + θ ∈ frontier (standardTriangle s) \ standardTriangleEdge s} = 0 ∧
      (∃ ts : ℕ → Euclidean 2,
        (∀ n, ts n ∈ G ∩ standardTriangle s) ∧ Tendsto ts atTop (nhds t) ∧
        ∀ᵐ θ ∂σ, Tendsto (fun n => cutoffSymbol (standardTriangle s) (ts n) θ) atTop
          (nhds (cutoffSymbol (standardTriangle s) t θ +
            (standardTriangleJump s t).indicator (fun _ => (1 : ℂ)) θ))) ∧
      (∃ ts : ℕ → Euclidean 2,
        (∀ n, ts n ∈ G ∩ (closure (standardTriangle s))ᶜ) ∧ Tendsto ts atTop (nhds t) ∧
        ∀ᵐ θ ∂σ, Tendsto (fun n => cutoffSymbol (standardTriangle s) (ts n) θ) atTop
          (nhds (cutoffSymbol (standardTriangle s) t θ))) := by
  obtain ⟨t, ht, hc⟩ := exists_clean_standardTriangle_edge_point s hs σ
  obtain ⟨⟨tin, hin, htin⟩, ⟨tout, hout, htout⟩⟩ :=
    exists_conull_sequences_standardTriangle_two_sides s hs hG t ht
  exact ⟨t, ht, hc,
    ⟨tin, hin, htin, standardTriangle_cutoffSymbol_interior_ae_tendsto s t ht σ hc htin
      (fun n => (hin n).2)⟩,
    ⟨tout, hout, htout, standardTriangle_cutoffSymbol_exterior_ae_tendsto s t ht σ hc htout
      (fun n => (hout n).2)⟩⟩

end RieszEuclidean
