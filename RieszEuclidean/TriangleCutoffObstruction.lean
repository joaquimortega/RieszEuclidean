import RieszEuclidean.TriangleSymbolLimits
import RieszEuclidean.BoundaryJumpLimits

noncomputable section
open MeasureTheory Filter Topology
namespace RieszEuclidean

/-- Actual triangle cutoffs have orthogonal strong limits with the complete edge jump. -/
theorem exists_standardTriangle_cutoff_limits {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (s : ℝ) (hs : 0 < s) {G : Set (Euclidean 2)} (hG : volume Gᶜ = 0)
    {t₀ : Euclidean 2} (hx : t₀ ∈ standardTriangleEdge s)
    (σ : H → Measure (Euclidean 2)) (hfinite : ∀ f, IsFiniteMeasure (σ f))
    (hclean : ∀ f, σ f {θ | t₀ + θ ∈ frontier (standardTriangle s) \ standardTriangleEdge s} = 0)
    (P : G → H →L[ℂ] H)
    (hP : ∀ t, ‖P t‖ ≤ 1 ∧ IsSelfAdjoint (P t) ∧ (P t).comp (P t) = P t)
    (hnorm : ∀ t f, ‖P t f‖ ^ 2 = ∫ θ, ‖cutoffSymbol (standardTriangle s) t θ‖ ^ 2 ∂σ f)
    (hdiff : ∀ a b f, ‖P a f - P b f‖ ^ 2 =
      ∫ θ, ‖cutoffSymbol (standardTriangle s) a θ - cutoffSymbol (standardTriangle s) b θ‖ ^ 2 ∂σ f) :
    ∃ (tm tp : ℕ → G) (Rm Rp : H →L[ℂ] H),
      (∀ n, (tm n : Euclidean 2) ∉ closure (standardTriangle s) ∧ (tp n : Euclidean 2) ∈ (standardTriangle s)) ∧
      Tendsto (fun n => (tm n : Euclidean 2)) atTop (𝓝 t₀) ∧
      Tendsto (fun n => (tp n : Euclidean 2)) atTop (𝓝 t₀) ∧
      (‖Rm‖ ≤ 1 ∧ IsSelfAdjoint Rm ∧ Rm.comp Rm = Rm) ∧
      (‖Rp‖ ≤ 1 ∧ IsSelfAdjoint Rp ∧ Rp.comp Rp = Rp) ∧
      (∀ f, Tendsto (fun n => P (tm n) f) atTop (𝓝 (Rm f))) ∧
      (∀ f, Tendsto (fun n => P (tp n) f) atTop (𝓝 (Rp f))) ∧
      (∀ f, ‖Rm f‖ ^ 2 = ∫ θ, ‖cutoffSymbol (standardTriangle s) t₀ θ‖ ^ 2 ∂σ f) ∧
      (∀ f, ‖Rp f‖ ^ 2 = ∫ θ, ‖boundaryJumpSymbol (standardTriangle s) t₀ (standardTriangleJump s t₀) θ‖ ^ 2 ∂σ f) := by
  obtain ⟨⟨tp', hp', htp⟩, ⟨tm', hm', htm⟩⟩ :=
    exists_conull_sequences_standardTriangle_two_sides s hs hG t₀ hx
  let tp : ℕ → G := fun n => ⟨tp' n, (hp' n).1⟩
  let tm : ℕ → G := fun n => ⟨tm' n, (hm' n).1⟩
  have ha (t : ℕ → G) (f : H) (n : ℕ) :
      AEStronglyMeasurable (cutoffSymbol (standardTriangle s) (t n)) (σ f) :=
    (measurable_cutoffSymbol (standardTriangle_isOpen s).measurableSet (t n)).aestronglyMeasurable
  have hb (t : ℕ → G) (f : H) (n : ℕ) :
      ∀ᵐ θ ∂σ f, ‖cutoffSymbol (standardTriangle s) (t n) θ‖ ≤ 1 :=
    Filter.Eventually.of_forall (norm_cutoffSymbol_le_one (standardTriangle s) (t n))
  obtain ⟨Rm, hRm, hRms, hRmi, hRmt, hRmn⟩ :=
    exists_projection_of_spectral_symbol_limit (l := atTop) (fun n => P (tm n))
      (fun n => (hP (tm n)).1) (fun n => (hP (tm n)).2.1)
      (fun n => (hP (tm n)).2.2) σ hfinite
      (fun n => cutoffSymbol (standardTriangle s) (tm n)) (cutoffSymbol (standardTriangle s) t₀) (ha tm) (hb tm)
      (fun f => standardTriangle_cutoffSymbol_exterior_ae_tendsto s t₀ hx (σ f) (hclean f) htm
        (fun n => (hm' n).2))
      (fun f i j => hdiff (tm i) (tm j) f) (fun f n => hnorm (tm n) f)
  obtain ⟨Rp, hRp, hRps, hRpi, hRpt, hRpn⟩ :=
    exists_projection_of_spectral_symbol_limit (l := atTop) (fun n => P (tp n))
      (fun n => (hP (tp n)).1) (fun n => (hP (tp n)).2.1)
      (fun n => (hP (tp n)).2.2) σ hfinite
      (fun n => cutoffSymbol (standardTriangle s) (tp n)) (boundaryJumpSymbol (standardTriangle s) t₀ (standardTriangleJump s t₀)) (ha tp) (hb tp)
      (fun f => standardTriangle_cutoffSymbol_interior_ae_tendsto s t₀ hx (σ f) (hclean f) htp
        (fun n => (hp' n).2))
      (fun f i j => hdiff (tp i) (tp j) f) (fun f n => hnorm (tp n) f)
  exact ⟨tm, tp, Rm, Rp, fun n => ⟨(hm' n).2, (hp' n).2⟩, htm, htp,
    ⟨hRm, hRms, hRmi⟩, ⟨hRp, hRps, hRpi⟩, hRmt, hRpt, hRmn, hRpn⟩

/-- The complete triangle edge jump obstructs a common subunit gap to a continuous
orthogonal comparison family at a point clean for all the given spectral measures. -/
theorem standardTriangle_clean_cutoffs_comparison_obstruction {H : Type}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (s : ℝ) (hs : 0 < s) {G : Set (Euclidean 2)} (hG : volume Gᶜ = 0)
    {t₀ : Euclidean 2} (hx : t₀ ∈ standardTriangleEdge s)
    (σ : H → Measure (Euclidean 2)) (hfinite : ∀ f, IsFiniteMeasure (σ f))
    (hclean : ∀ f, σ f {θ | t₀ + θ ∈ frontier (standardTriangle s) \ standardTriangleEdge s} = 0)
    (P : G → H →L[ℂ] H)
    (hP : ∀ t, ‖P t‖ ≤ 1 ∧ IsSelfAdjoint (P t) ∧ (P t).comp (P t) = P t)
    (hnorm : ∀ t f, ‖P t f‖ ^ 2 = ∫ θ, ‖cutoffSymbol (standardTriangle s) t θ‖ ^ 2 ∂σ f)
    (hdiff : ∀ a b f, ‖P a f - P b f‖ ^ 2 =
      ∫ θ, ‖cutoffSymbol (standardTriangle s) a θ - cutoffSymbol (standardTriangle s) b θ‖ ^ 2 ∂σ f)
    (u : H) (hu : ‖u‖ = 1) (hσu : σ u = Measure.dirac 0)
    (M : Euclidean 2 → H →L[ℂ] H) (hM : ContinuousAt M t₀)
    (hMs : IsSelfAdjoint (M t₀)) (hMi : (M t₀).comp (M t₀) = M t₀)
    {γ : ℝ} (hγ : γ < 1) (hgap : ∀ t : G, ‖P t - M t‖ ≤ γ) : False := by
  obtain ⟨tm, tp, Rm, Rp, _, htm, htp, hRm, hRp, hRmt, hRpt, hRmn, hRpn⟩ :=
    exists_standardTriangle_cutoff_limits s hs hG hx σ hfinite hclean P hP hnorm hdiff
  obtain ⟨_, _, hstrict⟩ := boundary_jump_cutoff_ranges_strict
    (standardTriangle_isOpen s).measurableSet t₀ (standardTriangleJump_measurableSet s hs t₀)
    (fun _ h => standardTriangleJump_not_mem s t₀ h) (zero_mem_standardTriangleJump s t₀ hx)
    σ hfinite Rm Rp hRm.2.1 hRp.2.1 hRm.2.2 hRp.2.2 hRmn hRpn u hu hσu
  let Rminus : OrthProjection H := ⟨Rm, hRm.2.2, hRm.2.1.isSymmetric⟩
  let Rplus : OrthProjection H := ⟨Rp, hRp.2.2, hRp.2.1.isSymmetric⟩
  let Q : OrthProjection H := ⟨M t₀, hMi, hMs.isSymmetric⟩
  exact OrthProjection.moving_comparison_obstruction
    (fun n => P (tm n)) (fun n => P (tp n))
    (fun n => M (tm n)) (fun n => M (tp n)) Rminus Rplus Q γ hγ
    hRmt hRpt (hM.tendsto.comp htm) (hM.tendsto.comp htp)
    (fun n => hgap (tm n)) (fun n => hgap (tp n)) hstrict

/-- The actual triangle geometry excludes a uniform subunit gap for spectral cutoffs
with the stated norm and difference identities and a common control measure.
Constructing those analytic identities from an exponential Riesz basis is separate. -/
theorem standardTriangle_cutoffs_continuous_comparison_obstruction {H : Type}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (s : ℝ) (hs : 0 < s) {G : Set (Euclidean 2)} (hG : volume Gᶜ = 0)
    (σ : H → Measure (Euclidean 2)) (hfinite : ∀ f, IsFiniteMeasure (σ f))
    (μ : Measure (Euclidean 2)) [SFinite μ] (hdom : ∀ f, σ f ≪ μ)
    (P : G → H →L[ℂ] H)
    (hP : ∀ t, ‖P t‖ ≤ 1 ∧ IsSelfAdjoint (P t) ∧ (P t).comp (P t) = P t)
    (hnorm : ∀ t f, ‖P t f‖ ^ 2 = ∫ θ, ‖cutoffSymbol (standardTriangle s) t θ‖ ^ 2 ∂σ f)
    (hdiff : ∀ a b f, ‖P a f - P b f‖ ^ 2 =
      ∫ θ, ‖cutoffSymbol (standardTriangle s) a θ - cutoffSymbol (standardTriangle s) b θ‖ ^ 2 ∂σ f)
    (u : H) (hu : ‖u‖ = 1) (hσu : σ u = Measure.dirac 0)
    (M : Euclidean 2 → H →L[ℂ] H) (hM : Continuous M)
    (hMs : ∀ t, IsSelfAdjoint (M t)) (hMi : ∀ t, (M t).comp (M t) = M t)
    {γ : ℝ} (hγ : γ < 1) (hgap : ∀ t : G, ‖P t - M t‖ ≤ γ) : False := by
  obtain ⟨t₀, ht₀, hclean⟩ := exists_clean_standardTriangle_edge_point s hs μ
  exact standardTriangle_clean_cutoffs_comparison_obstruction s hs hG ht₀ σ hfinite
    (fun f => hdom f hclean) P hP hnorm hdiff u hu hσu
    M hM.continuousAt (hMs t₀) (hMi t₀) hγ hgap

end RieszEuclidean
