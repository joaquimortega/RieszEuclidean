import RieszEuclidean.HausdorffMatching
open Filter TopologicalSpace Metric
namespace RieszEuclidean
/-- Hausdorff limits on nested windows are compatible with inclusion. -/
theorem compactRestriction_limit_mono {d : ℕ} {K L : Set (Euclidean d)}
    (hKL : K ⊆ L) {Γ : ℕ → Set (Euclidean d)} (hΓ : ∀ n, IsClosed (Γ n))
    {C : Closeds K} {D : Closeds L}
    (hC : Tendsto (fun n => compactRestriction K (Γ n) (hΓ n)) atTop (nhds C))
    (hD : Tendsto (fun n => compactRestriction L (Γ n) (hΓ n)) atTop (nhds D))
    (x : K) (hx : x ∈ C) : (⟨x, hKL x.property⟩ : L) ∈ D := by
  apply D.isClosed.closure_subset
  rw [Metric.mem_closure_iff]
  intro ε hε
  have hc := hausdorff_eventually_matching hC (half_pos hε)
  have hd := hausdorff_eventually_matching hD (half_pos hε)
  obtain ⟨n, hcn, hdn⟩ := (hc.and hd).exists
  obtain ⟨a, ha, hxa⟩ := hcn.2 x hx
  let aL : L := ⟨a, hKL a.property⟩
  have haL : aL ∈ compactRestriction L (Γ n) (hΓ n) := ha
  obtain ⟨b, hb, hab⟩ := hdn.1 aL haL
  refine ⟨b, hb, ?_⟩
  have ht := dist_triangle (⟨x, hKL x.property⟩ : L) aL b
  have hxa' : dist (⟨x, hKL x.property⟩ : L) aL < ε / 2 := hxa
  linarith
/-- A limit point inside a window is detected by the limit on that window. -/
theorem compactRestriction_limit_interior {d : ℕ} {K L : Set (Euclidean d)}
    {Γ : ℕ → Set (Euclidean d)} (hΓ : ∀ n, IsClosed (Γ n))
    {C : Closeds K} {D : Closeds L}
    (hC : Tendsto (fun n => compactRestriction K (Γ n) (hΓ n)) atTop (nhds C))
    (hD : Tendsto (fun n => compactRestriction L (Γ n) (hΓ n)) atTop (nhds D))
    (x : L) (hx : x ∈ D) (hxK : (x : Euclidean d) ∈ K)
    {r : ℝ} (hr : 0 < r) (hball : Metric.ball (x : Euclidean d) r ⊆ K) :
    (⟨x, hxK⟩ : K) ∈ C := by
  apply C.isClosed.closure_subset
  rw [Metric.mem_closure_iff]
  intro ε hε
  have hη : 0 < min r (ε / 2) := lt_min hr (half_pos hε)
  have hc := hausdorff_eventually_matching hC (half_pos hε)
  have hd := hausdorff_eventually_matching hD hη
  obtain ⟨n, hcn, hdn⟩ := (hc.and hd).exists
  obtain ⟨a, ha, hxa⟩ := hdn.2 x hx
  have har : dist (a : Euclidean d) x < r := by
    rw [dist_comm]
    exact hxa.trans_le (min_le_left _ _)
  let aK : K := ⟨a, hball har⟩
  have haK : aK ∈ compactRestriction K (Γ n) (hΓ n) := ha
  obtain ⟨b, hb, hab⟩ := hcn.1 aK haK
  refine ⟨b, hb, ?_⟩
  have ht := dist_triangle (⟨x, hxK⟩ : K) aK b
  have hxa' : dist (⟨x, hxK⟩ : K) aK < ε / 2 :=
    hxa.trans_le (min_le_right _ _)
  linarith
end RieszEuclidean
