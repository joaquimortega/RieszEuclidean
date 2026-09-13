import RieszEuclidean.ConfigurationTopology
open Set Topology
namespace RieszEuclidean.SeparatedConfiguration
/-- The real translation orbit of a configuration. -/
def orbit {d : ℕ} {δ : ℝ} (Γ : SeparatedConfiguration d δ) : Set (SeparatedConfiguration d δ) :=
  Set.range (fun z : Euclidean d => translate z Γ)
/-- The compact hull used to construct stationary measures. -/
def hull {d : ℕ} {δ : ℝ} (Γ : SeparatedConfiguration d δ) : Set (SeparatedConfiguration d δ) :=
  closure (orbit Γ)
/-- A configuration belongs to its own orbit closure. -/
theorem mem_hull {d : ℕ} {δ : ℝ} (Γ : SeparatedConfiguration d δ) : Γ ∈ hull Γ := by
  apply subset_closure
  exact ⟨0, translate_zero Γ⟩
/-- The translation hull is compact for positive separation. -/
theorem isCompact_hull {d : ℕ} {δ : ℝ} (hδ : 0 < δ) (Γ : SeparatedConfiguration d δ) :
    IsCompact (hull Γ) := by
  letI := compactSpace (d := d) hδ
  exact isClosed_closure.isCompact
/-- Each real translation maps the hull into itself. -/
theorem translate_mem_hull {d : ℕ} {δ : ℝ} (hδ : 0 < δ)
    (Γ : SeparatedConfiguration d δ) (z : Euclidean d)
    {Δ : SeparatedConfiguration d δ} (hΔ : Δ ∈ hull Γ) : translate z Δ ∈ hull Γ := by
  have hc : Continuous (translate z : SeparatedConfiguration d δ → SeparatedConfiguration d δ) :=
    (continuous_translate hδ).comp (continuous_const.prodMk continuous_id)
  have hm : MapsTo (translate z) (orbit Γ) (orbit Γ) := by
    rintro _ ⟨y, rfl⟩
    exact ⟨z + y, (translate_add z y Γ).symm⟩
  exact hm.closure hc hΔ
/-- Restrict a real translation to the compact orbit closure. -/
def hullTranslate {d : ℕ} {δ : ℝ} (hδ : 0 < δ)
    (Γ : SeparatedConfiguration d δ) (z : Euclidean d) : hull Γ → hull Γ :=
  fun Δ => ⟨translate z Δ, translate_mem_hull hδ Γ z Δ.property⟩
/-- The restricted action remains jointly continuous. -/
theorem continuous_hullTranslate {d : ℕ} {δ : ℝ} (hδ : 0 < δ)
    (Γ : SeparatedConfiguration d δ) :
    Continuous (fun p : Euclidean d × hull Γ => hullTranslate hδ Γ p.1 p.2) := by
  apply Continuous.subtype_mk
  exact (continuous_translate hδ).comp
    (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
end RieszEuclidean.SeparatedConfiguration
