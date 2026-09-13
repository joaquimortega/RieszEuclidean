import RieszEuclidean.PolygonSymbolLimits
import RieszEuclidean.BoundaryJumpLimits

noncomputable section
open MeasureTheory Filter Topology
namespace RieszEuclidean

variable {ι : Type*} [Fintype ι]

/-- Actual polygon cutoffs have orthogonal strong limits with the complete edge jump. -/
theorem exists_polygonFace_cutoff_limits {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (normal : ι → Euclidean 2) (offset : ι → ℝ) (j : ι) (hn : normal j ≠ 0) {G : Set (Euclidean 2)} (hG : volume Gᶜ = 0)
    {t₀ : Euclidean 2} (hx : t₀ ∈ strictSupportingFace normal offset j)
    (σ : H → Measure (Euclidean 2)) (hfinite : ∀ f, IsFiniteMeasure (σ f))
    (hclean : ∀ f, σ f {θ | t₀ + θ ∈ frontier (strictHalfspaceIntersection normal offset) \ strictSupportingFace normal offset j} = 0)
    (P : G → H →L[ℂ] H)
    (hP : ∀ t, ‖P t‖ ≤ 1 ∧ IsSelfAdjoint (P t) ∧ (P t).comp (P t) = P t)
    (hnorm : ∀ t f, ‖P t f‖ ^ 2 = ∫ θ, ‖cutoffSymbol (strictHalfspaceIntersection normal offset) t θ‖ ^ 2 ∂σ f)
    (hdiff : ∀ a b f, ‖P a f - P b f‖ ^ 2 =
      ∫ θ, ‖cutoffSymbol (strictHalfspaceIntersection normal offset) a θ - cutoffSymbol (strictHalfspaceIntersection normal offset) b θ‖ ^ 2 ∂σ f) :
    ∃ (tm tp : ℕ → G) (Rm Rp : H →L[ℂ] H),
      (∀ n, (tm n : Euclidean 2) ∉ closure (strictHalfspaceIntersection normal offset) ∧ (tp n : Euclidean 2) ∈ (strictHalfspaceIntersection normal offset)) ∧
      Tendsto (fun n => (tm n : Euclidean 2)) atTop (𝓝 t₀) ∧
      Tendsto (fun n => (tp n : Euclidean 2)) atTop (𝓝 t₀) ∧
      (‖Rm‖ ≤ 1 ∧ IsSelfAdjoint Rm ∧ Rm.comp Rm = Rm) ∧
      (‖Rp‖ ≤ 1 ∧ IsSelfAdjoint Rp ∧ Rp.comp Rp = Rp) ∧
      (∀ f, Tendsto (fun n => P (tm n) f) atTop (𝓝 (Rm f))) ∧
      (∀ f, Tendsto (fun n => P (tp n) f) atTop (𝓝 (Rp f))) ∧
      (∀ f, ‖Rm f‖ ^ 2 = ∫ θ, ‖cutoffSymbol (strictHalfspaceIntersection normal offset) t₀ θ‖ ^ 2 ∂σ f) ∧
      (∀ f, ‖Rp f‖ ^ 2 = ∫ θ, ‖boundaryJumpSymbol (strictHalfspaceIntersection normal offset) t₀ (supportingFaceJump normal offset j t₀) θ‖ ^ 2 ∂σ f) := by
  obtain ⟨⟨tp', hp', htp⟩, ⟨tm', hm', htm⟩⟩ :=
    exists_conull_sequences_strictSupportingFace_two_sides normal offset j hG t₀ hx hn
  let tp : ℕ → G := fun n => ⟨tp' n, (hp' n).1⟩
  let tm : ℕ → G := fun n => ⟨tm' n, (hm' n).1⟩
  have ha (t : ℕ → G) (f : H) (n : ℕ) :
      AEStronglyMeasurable (cutoffSymbol (strictHalfspaceIntersection normal offset) (t n)) (σ f) :=
    (measurable_cutoffSymbol (strictHalfspaceIntersection_isOpen normal offset).measurableSet (t n)).aestronglyMeasurable
  have hb (t : ℕ → G) (f : H) (n : ℕ) :
      ∀ᵐ θ ∂σ f, ‖cutoffSymbol (strictHalfspaceIntersection normal offset) (t n) θ‖ ≤ 1 :=
    Filter.Eventually.of_forall (norm_cutoffSymbol_le_one (strictHalfspaceIntersection normal offset) (t n))
  obtain ⟨Rm, hRm, hRms, hRmi, hRmt, hRmn⟩ :=
    exists_projection_of_spectral_symbol_limit (l := atTop) (fun n => P (tm n))
      (fun n => (hP (tm n)).1) (fun n => (hP (tm n)).2.1)
      (fun n => (hP (tm n)).2.2) σ hfinite
      (fun n => cutoffSymbol (strictHalfspaceIntersection normal offset) (tm n)) (cutoffSymbol (strictHalfspaceIntersection normal offset) t₀) (ha tm) (hb tm)
      (fun f => polygonFace_cutoffSymbol_exterior_ae_tendsto normal offset j t₀ hx (σ f) (hclean f) htm
        (fun n => (hm' n).2))
      (fun f i j => hdiff (tm i) (tm j) f) (fun f n => hnorm (tm n) f)
  obtain ⟨Rp, hRp, hRps, hRpi, hRpt, hRpn⟩ :=
    exists_projection_of_spectral_symbol_limit (l := atTop) (fun n => P (tp n))
      (fun n => (hP (tp n)).1) (fun n => (hP (tp n)).2.1)
      (fun n => (hP (tp n)).2.2) σ hfinite
      (fun n => cutoffSymbol (strictHalfspaceIntersection normal offset) (tp n)) (boundaryJumpSymbol (strictHalfspaceIntersection normal offset) t₀ (supportingFaceJump normal offset j t₀)) (ha tp) (hb tp)
      (fun f => polygonFace_cutoffSymbol_interior_ae_tendsto normal offset j t₀ hx (σ f) (hclean f) htp
        (fun n => (hp' n).2))
      (fun f i j => hdiff (tp i) (tp j) f) (fun f n => hnorm (tp n) f)
  exact ⟨tm, tp, Rm, Rp, fun n => ⟨(hm' n).2, (hp' n).2⟩, htm, htp,
    ⟨hRm, hRms, hRmi⟩, ⟨hRp, hRps, hRpi⟩, hRmt, hRpt, hRmn, hRpn⟩

/-- The complete polygon edge jump obstructs a common subunit gap to a continuous
orthogonal comparison family at a point clean for all the given spectral measures. -/
theorem polygonFace_clean_cutoffs_comparison_obstruction {H : Type}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (normal : ι → Euclidean 2) (offset : ι → ℝ) (j : ι) (hn : normal j ≠ 0) {G : Set (Euclidean 2)} (hG : volume Gᶜ = 0)
    {t₀ : Euclidean 2} (hx : t₀ ∈ strictSupportingFace normal offset j)
    (σ : H → Measure (Euclidean 2)) (hfinite : ∀ f, IsFiniteMeasure (σ f))
    (hclean : ∀ f, σ f {θ | t₀ + θ ∈ frontier (strictHalfspaceIntersection normal offset) \ strictSupportingFace normal offset j} = 0)
    (P : G → H →L[ℂ] H)
    (hP : ∀ t, ‖P t‖ ≤ 1 ∧ IsSelfAdjoint (P t) ∧ (P t).comp (P t) = P t)
    (hnorm : ∀ t f, ‖P t f‖ ^ 2 = ∫ θ, ‖cutoffSymbol (strictHalfspaceIntersection normal offset) t θ‖ ^ 2 ∂σ f)
    (hdiff : ∀ a b f, ‖P a f - P b f‖ ^ 2 =
      ∫ θ, ‖cutoffSymbol (strictHalfspaceIntersection normal offset) a θ - cutoffSymbol (strictHalfspaceIntersection normal offset) b θ‖ ^ 2 ∂σ f)
    (u : H) (hu : ‖u‖ = 1) (hσu : σ u = Measure.dirac 0)
    (M : Euclidean 2 → H →L[ℂ] H) (hM : ContinuousAt M t₀)
    (hMs : IsSelfAdjoint (M t₀)) (hMi : (M t₀).comp (M t₀) = M t₀)
    {γ : ℝ} (hγ : γ < 1) (hgap : ∀ t : G, ‖P t - M t‖ ≤ γ) : False := by
  obtain ⟨tm, tp, Rm, Rp, _, htm, htp, hRm, hRp, hRmt, hRpt, hRmn, hRpn⟩ :=
    exists_polygonFace_cutoff_limits normal offset j hn hG hx σ hfinite hclean P hP hnorm hdiff
  obtain ⟨_, _, hstrict⟩ := boundary_jump_cutoff_ranges_strict
    (strictHalfspaceIntersection_isOpen normal offset).measurableSet t₀ (supportingFaceJump_measurableSet normal offset j t₀)
    (fun _ h => supportingFaceJump_not_mem normal offset j t₀ h) (zero_mem_supportingFaceJump normal offset j t₀ hx)
    σ hfinite Rm Rp hRm.2.1 hRp.2.1 hRm.2.2 hRp.2.2 hRmn hRpn u hu hσu
  let Rminus : OrthProjection H := ⟨Rm, hRm.2.2, hRm.2.1.isSymmetric⟩
  let Rplus : OrthProjection H := ⟨Rp, hRp.2.2, hRp.2.1.isSymmetric⟩
  let Q : OrthProjection H := ⟨M t₀, hMi, hMs.isSymmetric⟩
  exact OrthProjection.moving_comparison_obstruction
    (fun n => P (tm n)) (fun n => P (tp n))
    (fun n => M (tm n)) (fun n => M (tp n)) Rminus Rplus Q γ hγ
    hRmt hRpt (hM.tendsto.comp htm) (hM.tendsto.comp htp)
    (fun n => hgap (tm n)) (fun n => hgap (tp n)) hstrict

/-- The actual polygon geometry excludes a uniform subunit gap for spectral cutoffs
with the stated norm and difference identities and a common control measure.
Constructing those analytic identities from an exponential Riesz basis is separate. -/
theorem unpairedSupportingFace_cutoffs_continuous_comparison_obstruction {H : Type}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (normal : ι → Euclidean 2) (offset : ι → ℝ) (j : ι) (hn : normal j ≠ 0)
    (hface : (strictSupportingFace normal offset j).Nonempty)
    (hparallel : ∀ i, i ≠ j → ∀ r : ℝ, normal i ≠ r • normal j) {G : Set (Euclidean 2)} (hG : volume Gᶜ = 0)
    (σ : H → Measure (Euclidean 2)) (hfinite : ∀ f, IsFiniteMeasure (σ f))
    (μ : Measure (Euclidean 2)) [SFinite μ] (hdom : ∀ f, σ f ≪ μ)
    (P : G → H →L[ℂ] H)
    (hP : ∀ t, ‖P t‖ ≤ 1 ∧ IsSelfAdjoint (P t) ∧ (P t).comp (P t) = P t)
    (hnorm : ∀ t f, ‖P t f‖ ^ 2 = ∫ θ, ‖cutoffSymbol (strictHalfspaceIntersection normal offset) t θ‖ ^ 2 ∂σ f)
    (hdiff : ∀ a b f, ‖P a f - P b f‖ ^ 2 =
      ∫ θ, ‖cutoffSymbol (strictHalfspaceIntersection normal offset) a θ - cutoffSymbol (strictHalfspaceIntersection normal offset) b θ‖ ^ 2 ∂σ f)
    (u : H) (hu : ‖u‖ = 1) (hσu : σ u = Measure.dirac 0)
    (M : Euclidean 2 → H →L[ℂ] H) (hM : Continuous M)
    (hMs : ∀ t, IsSelfAdjoint (M t)) (hMi : ∀ t, (M t).comp (M t) = M t)
    {γ : ℝ} (hγ : γ < 1) (hgap : ∀ t : G, ‖P t - M t‖ ≤ γ) : False := by
  obtain ⟨t₀, ht₀, hclean⟩ := exists_clean_unpairedSupportingFace_point normal offset j hn hface hparallel μ
  exact polygonFace_clean_cutoffs_comparison_obstruction normal offset j hn hG ht₀ σ hfinite
    (fun f => hdom f hclean) P hP hnorm hdiff u hu hσu
    M hM.continuousAt (hMs t₀) (hMi t₀) hγ hgap

end RieszEuclidean
