import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Topology.UniformSpace.Cauchy

open Filter Topology

namespace RieszEuclidean

variable {ι H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- A pointwise limit of uniformly bounded linear operators is a bounded linear operator. -/
theorem exists_clm_of_strong_limit {l : Filter ι} [NeBot l]
    (A : ι → H →L[ℂ] H) (F : H → H) {M : ℝ} (hM : 0 ≤ M)
    (hA : ∀ i, ‖A i‖ ≤ M) (hF : ∀ f, Tendsto (fun i => A i f) l (𝓝 (F f))) :
    ∃ B : H →L[ℂ] H, (∀ f, B f = F f) ∧ ‖B‖ ≤ M := by
  have hbound : ∀ f, ‖F f‖ ≤ M * ‖f‖ := by
    intro f
    exact le_of_tendsto (hF f).norm (Filter.Eventually.of_forall fun i =>
      (A i).le_of_opNorm_le (hA i) f)
  let L : H →ₗ[ℂ] H :=
    { toFun := F
      map_add' := fun f g => tendsto_nhds_unique (hF (f + g))
        (by simpa only [map_add] using (hF f).add (hF g))
      map_smul' := fun c f => tendsto_nhds_unique (hF (c • f))
        (by simpa only [map_smul, RingHom.id_apply] using (hF f).const_smul c) }
  let B := L.mkContinuous M hbound
  exact ⟨B, fun _ => rfl, B.opNorm_le_bound hM hbound⟩

/-- Pointwise Cauchy uniformly bounded operators admit a bounded strong limit. -/
theorem exists_clm_of_pointwise_cauchy [CompleteSpace H]
    {l : Filter ι} [NeBot l] (A : ι → H →L[ℂ] H) {M : ℝ} (hM : 0 ≤ M)
    (hA : ∀ i, ‖A i‖ ≤ M) (hC : ∀ f, Cauchy (l.map (fun i => A i f))) :
    ∃ B : H →L[ℂ] H, ‖B‖ ≤ M ∧ ∀ f, Tendsto (fun i => A i f) l (𝓝 (B f)) := by
  classical
  choose F hF using fun f => cauchy_map_iff_exists_tendsto.mp (hC f)
  obtain ⟨B, hB, hBn⟩ := exists_clm_of_strong_limit A F hM hA hF
  exact ⟨B, hBn, fun f => (hB f).symm ▸ hF f⟩

/-- Uniformly bounded operators send convergent moving vectors to the expected strong limit. -/
theorem strong_limit_apply_tendsto {l : Filter ι}
    (A : ι → H →L[ℂ] H) (B : H →L[ℂ] H) {M : ℝ}
    (hA : ∀ i, ‖A i‖ ≤ M) (hB : ∀ f, Tendsto (fun i => A i f) l (𝓝 (B f)))
    {v : ι → H} {f : H} (hv : Tendsto v l (𝓝 f)) :
    Tendsto (fun i => A i (v i)) l (𝓝 (B f)) := by
  have hz : Tendsto (fun i => A i (v i - f)) l (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero (fun _ => norm_nonneg _) (fun i =>
      (A i).le_of_opNorm_le (hA i) (v i - f))
    simpa using ((hv.sub (tendsto_const_nhds (x := f))).norm.const_mul M)
  simpa only [map_sub, sub_add_cancel, zero_add] using hz.add (hB f)

/-- Products pass to strong limits when the first factors are uniformly bounded. -/
theorem strong_limit_comp {l : Filter ι}
    (A C : ι → H →L[ℂ] H) (B D : H →L[ℂ] H) {M : ℝ}
    (hA : ∀ i, ‖A i‖ ≤ M) (hB : ∀ f, Tendsto (fun i => A i f) l (𝓝 (B f)))
    (hD : ∀ f, Tendsto (fun i => C i f) l (𝓝 (D f))) (f : H) :
    Tendsto (fun i => (A i).comp (C i) f) l (𝓝 (B.comp D f)) :=
  strong_limit_apply_tendsto A B hA hB (hD f)

/-- An asymptotically idempotent uniformly bounded family has an idempotent strong limit. -/
theorem strong_limit_idempotent {l : Filter ι} [NeBot l]
    (A : ι → H →L[ℂ] H) (B : H →L[ℂ] H) {M : ℝ}
    (hA : ∀ i, ‖A i‖ ≤ M) (hB : ∀ f, Tendsto (fun i => A i f) l (𝓝 (B f)))
    (hidem : ∀ f, Tendsto (fun i => ‖A i (A i f) - A i f‖) l (𝓝 0)) :
    B.comp B = B := by
  ext f
  have ht := (strong_limit_comp A A B B hA hB hB f).sub (hB f)
  have hz := tendsto_zero_iff_norm_tendsto_zero.mpr (hidem f)
  exact sub_eq_zero.mp (tendsto_nhds_unique ht hz)

/-- Self-adjointness passes to pointwise limits through the inner product. -/
theorem strong_limit_isSelfAdjoint [CompleteSpace H]
    {l : Filter ι} [NeBot l] (A : ι → H →L[ℂ] H) (B : H →L[ℂ] H)
    (hA : ∀ i, IsSelfAdjoint (A i))
    (hB : ∀ f, Tendsto (fun i => A i f) l (𝓝 (B f))) : IsSelfAdjoint B := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  intro f g
  apply tendsto_nhds_unique ((hB f).inner (𝕜 := ℂ) tendsto_const_nhds)
  have ht := (tendsto_const_nhds (x := f)).inner (𝕜 := ℂ) (hB g)
  exact ht.congr' (Filter.Eventually.of_forall fun i => (hA i).isSymmetric f g |>.symm)

/-- The pointwise Cauchy cutoff construction yields a self-adjoint idempotent contraction. -/
theorem exists_projection_of_cauchy_contractions [CompleteSpace H]
    {l : Filter ι} [NeBot l] (A : ι → H →L[ℂ] H)
    (hA : ∀ i, ‖A i‖ ≤ 1) (hself : ∀ i, IsSelfAdjoint (A i))
    (hC : ∀ f, Cauchy (l.map (fun i => A i f)))
    (hidem : ∀ f, Tendsto (fun i => ‖A i (A i f) - A i f‖) l (𝓝 0)) :
    ∃ B : H →L[ℂ] H, ‖B‖ ≤ 1 ∧ IsSelfAdjoint B ∧ B.comp B = B ∧
      ∀ f, Tendsto (fun i => A i f) l (𝓝 (B f)) := by
  obtain ⟨B, hBn, hB⟩ := exists_clm_of_pointwise_cauchy A zero_le_one hA hC
  exact ⟨B, hBn, strong_limit_isSelfAdjoint A B hself hB,
    strong_limit_idempotent A B hA hB hidem, hB⟩

end RieszEuclidean
