import RieszEuclidean.DistanceProfile
import RieszEuclidean.MovingTranslations
import Mathlib.Topology.Metrizable.Real
import Mathlib.Topology.Metrizable.Urysohn
open Filter TopologicalSpace Metric EMetric Set Topology
open scoped ENNReal
namespace RieszEuclidean
/-- Closed Euclidean configurations with a fixed separation bound. -/
structure SeparatedConfiguration (d : ℕ) (δ : ℝ) where
  /-- The underlying set of Euclidean points. -/
  carrier : Set (Euclidean d)
  /-- The configuration contains all of its finite limit points. -/
  isClosed : IsClosed carrier
  /-- Distinct points are at least the specified distance apart. -/
  separated : Separated δ carrier
namespace SeparatedConfiguration
/-- The empty configuration is allowed for every separation bound. -/
instance {d : ℕ} {δ : ℝ} : Nonempty (SeparatedConfiguration d δ) :=
  ⟨⟨∅, isClosed_empty, by simp [Separated]⟩⟩
/-- Configurations are equal when their underlying sets are equal. -/
@[ext] theorem ext {d : ℕ} {δ : ℝ} {Γ Δ : SeparatedConfiguration d δ}
    (h : Γ.carrier = Δ.carrier) : Γ = Δ := by
  cases Γ
  cases Δ
  cases h
  rfl
/-- Countably many distance probes determine a closed configuration. -/
noncomputable def profile {d : ℕ} {δ : ℝ} (Γ : SeparatedConfiguration d δ) : ℕ → ℝ≥0∞ :=
  fun n => infEdist (denseSeq (Euclidean d) n) Γ.carrier
/-- Equality of all distance probes implies equality of configurations. -/
theorem profile_injective {d : ℕ} {δ : ℝ} :
    Function.Injective (profile (d := d) (δ := δ)) := by
  intro Γ Δ h
  have he : (fun x => infEdist x Γ.carrier) = fun x => infEdist x Δ.carrier := by
    apply Continuous.ext_on (denseRange_denseSeq (Euclidean d)) continuous_infEdist continuous_infEdist
    rintro x ⟨n, rfl⟩
    exact congrFun h n
  have hc : Γ.carrier = Δ.carrier := by
    ext x
    rw [mem_iff_infEdist_zero_of_closed Γ.isClosed, mem_iff_infEdist_zero_of_closed Δ.isClosed]
    rw [congrFun he x]
  cases Γ
  cases Δ
  cases hc
  rfl
/-- The topology is induced by extended-distance probes on a dense sequence. -/
instance {d : ℕ} {δ : ℝ} : TopologicalSpace (SeparatedConfiguration d δ) :=
  TopologicalSpace.induced profile inferInstance
/-- The distance profile is a topological embedding. -/
theorem profile_isEmbedding {d : ℕ} {δ : ℝ} :
    IsEmbedding (profile (d := d) (δ := δ)) := profile_injective.isEmbedding_induced
/-- This countable probe topology is metrizable. -/
instance {d : ℕ} {δ : ℝ} : MetrizableSpace (SeparatedConfiguration d δ) :=
  profile_isEmbedding.metrizableSpace
/-- Beurling weak convergence implies convergence in the configuration topology. -/
theorem tendsto_of_weaklyConverges {d : ℕ} {δ : ℝ}
    {Γ : ℕ → SeparatedConfiguration d δ} {Γ₀ : SeparatedConfiguration d δ}
    (h : WeaklyConverges (fun n => (Γ n).carrier) Γ₀.carrier) :
    Tendsto Γ atTop (nhds Γ₀) := by
  apply profile_isEmbedding.tendsto_nhds_iff.mpr
  apply tendsto_pi_nhds.mpr
  intro n
  exact h.tendsto_infEdist (denseSeq (Euclidean d) n)
/-- Positive separation makes the configuration space sequentially compact. -/
theorem seqCompactSpace {d : ℕ} {δ : ℝ} (hδ : 0 < δ) :
    SeqCompactSpace (SeparatedConfiguration d δ) := by
  refine ⟨?_⟩
  intro Γ _
  obtain ⟨Γ₀, hs, φ, hφ, hw⟩ := separated_weak_subsequence hδ
    (fun n => (Γ n).carrier) (fun n => (Γ n).separated)
  exact ⟨⟨Γ₀, hs.isClosed hδ, hs⟩, Set.mem_univ _, φ, hφ, tendsto_of_weaklyConverges hw⟩
/-- With positive separation the configuration topology is compact. -/
theorem compactSpace {d : ℕ} {δ : ℝ} (hδ : 0 < δ) :
    CompactSpace (SeparatedConfiguration d δ) := by
  letI := metrizableSpaceMetric (SeparatedConfiguration d δ)
  exact UniformSpace.compactSpace_iff_seqCompactSpace.mpr (seqCompactSpace hδ)
/-- Convergence in the distance-probe topology is exactly Beurling weak convergence. -/
theorem weaklyConverges_of_tendsto {d : ℕ} {δ : ℝ} (hδ : 0 < δ)
    {Γ : ℕ → SeparatedConfiguration d δ} {Γ₀ : SeparatedConfiguration d δ}
    (h : Tendsto Γ atTop (nhds Γ₀)) :
    WeaklyConverges (fun n => (Γ n).carrier) Γ₀.carrier := by
  intro R hR ε hε
  by_contra hbad
  simp only [not_exists, not_forall, _root_.not_imp, exists_prop] at hbad
  obtain ⟨φ, hφ, hbadφ⟩ := extraction_of_frequently_atTop (frequently_atTop.mpr hbad)
  obtain ⟨S, hs, ψ, hψ, hw⟩ := separated_weak_subsequence hδ
    (fun n => (Γ (φ n)).carrier) (fun n => (Γ (φ n)).separated)
  let Δ : SeparatedConfiguration d δ := ⟨S, hs.isClosed hδ, hs⟩
  have ht : Tendsto (fun n => Γ (φ (ψ n))) atTop (nhds Δ) := tendsto_of_weaklyConverges hw
  have ht' : Tendsto (fun n => Γ (φ (ψ n))) atTop (nhds Γ₀) :=
    h.comp (hφ.comp hψ).tendsto_atTop
  have he : Δ = Γ₀ := tendsto_nhds_unique ht ht'
  change WeaklyConverges (fun n => (Γ (φ (ψ n))).carrier) Δ.carrier at hw
  rw [he] at hw
  obtain ⟨N, hN⟩ := hw R hR ε hε
  exact hbadφ (ψ N) (hN N le_rfl)
/-- Translate a separated closed configuration by a real Euclidean vector. -/
def translate {d : ℕ} {δ : ℝ} (z : Euclidean d) (Γ : SeparatedConfiguration d δ) :
    SeparatedConfiguration d δ where
  carrier := RieszEuclidean.translate z Γ.carrier
  isClosed := Γ.isClosed.preimage (continuous_id.add continuous_const)
  separated := Γ.separated.translate z
/-- Real translations act jointly continuously on the configuration space. -/
theorem continuous_translate {d : ℕ} {δ : ℝ} (hδ : 0 < δ) :
    Continuous (fun p : Euclidean d × SeparatedConfiguration d δ => translate p.1 p.2) := by
  apply SeqContinuous.continuous
  intro p p₀ hp
  apply tendsto_of_weaklyConverges
  have hc := weaklyConverges_of_tendsto hδ ((continuous_snd.tendsto p₀).comp hp)
  exact hc.moving_translate ((continuous_fst.tendsto p₀).comp hp)
/-- The chosen topology has precisely the paper's sequential convergence. -/
theorem tendsto_iff_weaklyConverges {d : ℕ} {δ : ℝ} (hδ : 0 < δ)
    {Γ : ℕ → SeparatedConfiguration d δ} {Γ₀ : SeparatedConfiguration d δ} :
    Tendsto Γ atTop (nhds Γ₀) ↔ WeaklyConverges (fun n => (Γ n).carrier) Γ₀.carrier :=
  ⟨weaklyConverges_of_tendsto hδ, tendsto_of_weaklyConverges⟩
/-- Zero translation fixes each configuration. -/
@[simp] theorem translate_zero {d : ℕ} {δ : ℝ} (Γ : SeparatedConfiguration d δ) :
    translate 0 Γ = Γ := ext (RieszEuclidean.translate_zero Γ.carrier)
/-- Successive real translations agree with translation by their sum. -/
@[simp] theorem translate_add {d : ℕ} {δ : ℝ} (y z : Euclidean d)
    (Γ : SeparatedConfiguration d δ) : translate y (translate z Γ) = translate (y + z) Γ :=
  ext (RieszEuclidean.translate_add y z Γ.carrier)
end SeparatedConfiguration
end RieszEuclidean
