import RieszEuclidean.Basic
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Group.Measure

/-!
# Almost every translation avoids a null exceptional set

Tonelli's theorem and translation invariance give the measurable conull set of
parameters used for the spectral cutoffs. No spectral-measure existence result
is needed; the input measure may be any s-finite Borel measure.
-/

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace RieszEuclidean

/-- The mass of a translated exceptional set in frequency space. -/
def translatedExceptionalMass {d : ℕ} (σ : Measure (Euclidean d))
    (E : Set (Euclidean d)) (t : Euclidean d) : ℝ≥0∞ :=
  σ {θ | t + θ ∈ E}

/-- The parameters whose translated exceptional set has zero spectral mass. -/
def goodParameters {d : ℕ} (σ : Measure (Euclidean d))
    (E : Set (Euclidean d)) : Set (Euclidean d) :=
  {t | translatedExceptionalMass σ E t = 0}

/-- Section masses are measurable for any measurable exceptional set. -/
theorem measurable_translatedExceptionalMass {d : ℕ} (σ : Measure (Euclidean d))
    [SFinite σ] {E : Set (Euclidean d)} (hE : MeasurableSet E) :
    Measurable (translatedExceptionalMass σ E) := by
  exact measurable_measure_prodMk_left (hE.preimage (measurable_fst.add measurable_snd))

/-- Almost every translate of a Lebesgue-null set has zero mass for a fixed s-finite measure. -/
theorem translatedExceptionalMass_ae_zero {d : ℕ} (σ : Measure (Euclidean d))
    [SFinite σ] {E : Set (Euclidean d)} (hE : MeasurableSet E) (hnull : volume E = 0) :
    ∀ᵐ t ∂volume, translatedExceptionalMass σ E t = 0 := by
  have h : ∀ᵐ θ ∂σ, ∀ᵐ t ∂volume, t + θ ∉ E := by
    exact Filter.Eventually.of_forall fun θ => by
      rw [ae_iff]
      simp only [not_not]
      change volume ((fun t => t + θ) ⁻¹' E) = 0
      rw [measure_preimage_add_right, hnull]
  have hh := (Measure.ae_ae_comm (μ := volume) (ν := σ)
    (hE.preimage (measurable_fst.add measurable_snd)).compl).mpr h
  filter_upwards [hh] with t ht
  simpa only [ae_iff, not_not] using ht

/-- The good-parameter set is measurable. -/
theorem measurableSet_goodParameters {d : ℕ} (σ : Measure (Euclidean d))
    [SFinite σ] {E : Set (Euclidean d)} (hE : MeasurableSet E) :
    MeasurableSet (goodParameters σ E) :=
  (measurable_translatedExceptionalMass σ hE) (measurableSet_singleton 0)

/-- The complement of the good-parameter set is Lebesgue-null. -/
theorem volume_compl_goodParameters {d : ℕ} (σ : Measure (Euclidean d))
    [SFinite σ] {E : Set (Euclidean d)} (hE : MeasurableSet E) (hnull : volume E = 0) :
    volume (goodParameters σ E)ᶜ = 0 := by
  exact (ae_iff.mp (translatedExceptionalMass_ae_zero σ hE hnull))

/-- The good parameters for a domain with null boundary form a measurable conull set.
The section is written as a preimage, so its sign is exactly `∂Ω - t`. -/
theorem frontier_goodParameters {d : ℕ} (σ : Measure (Euclidean d))
    [SFinite σ] {Ω : Set (Euclidean d)} (hΩ : volume (frontier Ω) = 0) :
    MeasurableSet (goodParameters σ (frontier Ω)) ∧
      volume (goodParameters σ (frontier Ω))ᶜ = 0 :=
  ⟨measurableSet_goodParameters σ isClosed_frontier.measurableSet,
    volume_compl_goodParameters σ isClosed_frontier.measurableSet hΩ⟩

/-- On the good set, the translated boundary has zero control mass. -/
theorem mem_goodParameters_frontier {d : ℕ} (σ : Measure (Euclidean d))
    (Ω : Set (Euclidean d)) (t : Euclidean d) :
    t ∈ goodParameters σ (frontier Ω) ↔ σ {θ | t + θ ∈ frontier Ω} = 0 :=
  Iff.rfl

end RieszEuclidean
