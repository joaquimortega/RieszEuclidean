import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Topology.Bases
import Mathlib.Topology.Sequences

open Filter Topology

namespace RieszEuclidean

/-- A separable complex Hilbert space with a unit vector has a sequence of unit vectors
whose scalar multiples sequentially approximate every vector. -/
theorem exists_unit_sequence_scalar_approximants
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [TopologicalSpace.SeparableSpace H] (u : H) (hu : ‖u‖ = 1) :
    ∃ h : ℕ → H, (∀ n, ‖h n‖ = 1) ∧
      ∀ f : H, ∃ g : ℕ → H,
        (∀ n, ∃ c : ℂ, ∃ j : ℕ, g n = c • h j) ∧
        Tendsto g atTop (𝓝 f) := by
  classical
  obtain ⟨v, hv⟩ := TopologicalSpace.exists_dense_seq H
  let h : ℕ → H := fun n => if v n = 0 then u else (‖v n‖⁻¹ : ℂ) • v n
  have hh : ∀ n, ‖h n‖ = 1 := by
    intro n
    dsimp [h]
    split_ifs with hn
    · exact hu
    · rw [norm_smul]
      simp [norm_ne_zero_iff.mpr hn, abs_of_nonneg (norm_nonneg (v n))]
  refine ⟨h, hh, ?_⟩
  intro f
  obtain ⟨g, hg, hgf⟩ := mem_closure_iff_seq_limit.mp (hv f)
  refine ⟨g, ?_, hgf⟩
  intro n
  obtain ⟨j, hj⟩ := hg n
  refine ⟨(‖v j‖ : ℂ), j, ?_⟩
  rw [← hj]
  dsimp [h]
  split_ifs with hj0
  · simp [hj0]
  · change v j = (‖v j‖ : ℂ) • ((‖v j‖ : ℂ)⁻¹ • v j)
    rw [smul_smul]
    have hn : (‖v j‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr hj0
    simp [hn]

end RieszEuclidean
