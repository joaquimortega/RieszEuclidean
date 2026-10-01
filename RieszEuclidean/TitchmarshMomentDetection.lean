import Mathlib.Topology.ContinuousMap.StoneWeierstrass
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

noncomputable section

open MeasureTheory

namespace RieszEuclidean

private def continuousMulRightCLM {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (h : C(X, ℂ)) : C(X, ℂ) →L[ℝ] C(X, ℂ) := by
  let L : C(X, ℂ) →ₗ[ℝ] C(X, ℂ) := {
    toFun := fun f => f * h
    map_add' := by intro f g; ext x; simp [add_mul]
    map_smul' := by intro c f; ext x; simp [smul_eq_mul, mul_assoc, mul_left_comm, mul_comm]
  }
  have hL : ∀ f, ‖L f‖ ≤ ‖h‖ * ‖f‖ := by
    intro f
    change ‖f * h‖ ≤ ‖h‖ * ‖f‖
    calc
      ‖f * h‖ ≤ ‖f‖ * ‖h‖ := norm_mul_le _ _
      _ = ‖h‖ * ‖f‖ := mul_comm _ _
  exact L.mkContinuous ‖h‖ hL

/-- Vanishing of the moment functional on a dense star subalgebra's closure forces a continuous
function to vanish. The proof tests against `star h` and uses positivity of the integral of
`‖h‖²` on any nonempty open set. -/
theorem continuous_moment_detection_of_vanishing_on_closure
    {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    [CompactSpace X] [T2Space X]
    (μ : Measure X) [IsFiniteMeasure μ] [Measure.IsOpenPosMeasure μ]
    (A : StarSubalgebra ℂ C(X, ℂ))
    (hA : A.topologicalClosure = ⊤)
    (h : C(X, ℂ))
    (hmom : ∀ p ∈ A.topologicalClosure, ∫ x, p x * h x ∂μ = 0) :
    h = 0 := by
  classical
  have hstar : star h ∈ A.topologicalClosure := by rw [hA]; trivial
  have hzero : ∫ x, star (h x) * h x ∂μ = 0 := by
    apply hmom (star h)
    exact hstar
  by_contra hne
  have hx : ∃ x, h x ≠ 0 := by
    by_contra h'
    push_neg at h'
    apply hne
    ext x
    exact h' x
  obtain ⟨x, hx⟩ := hx
  have hcont : Continuous (fun x : X => ‖h x‖ ^ 2) :=
    h.continuous.norm.pow 2
  have hint : Integrable (fun x : X => ‖h x‖ ^ 2) μ := by
    simpa only [IntegrableOn, Measure.restrict_univ] using
      hcont.continuousOn.integrableOn_compact isCompact_univ
  have hxn : ‖h x‖ ^ 2 ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr hx)
  have hpos : 0 < ∫ x, ‖h x‖ ^ 2 ∂μ :=
    integral_pos_of_integrable_nonneg_nonzero hcont hint (fun _ => sq_nonneg _) hxn
  have hfun : (fun x : X => star (h x) * h x) = fun x => (↑(‖h x‖ ^ 2) : ℂ) := by
    funext x
    simp [Complex.conj_mul']
  rw [hfun, integral_complex_ofReal] at hzero
  have hI : (∫ x, ‖h x‖ ^ 2 ∂μ) = 0 := by
    have := congrArg Complex.re hzero
    simpa using this
  exact (ne_of_gt hpos) hI

/-- Multivariate polynomial moments detect a continuous function on a compact Euclidean set,
provided the measure has full topological support. -/
theorem compact_euclidean_polynomial_moment_detection
    {d : ℕ} {K : Set (EuclideanSpace ℝ (Fin d))}
    [CompactSpace K]
    [MeasurableSpace K] [BorelSpace K]
    (μ : Measure K) [IsFiniteMeasure μ] [Measure.IsOpenPosMeasure μ]
    (h : C(K, ℂ))
    (hmom : ∀ p : MvPolynomial (Fin d) ℂ,
      ∫ x, MvPolynomial.eval (fun i => ((x : EuclideanSpace ℝ (Fin d)) i : ℂ)) p * h x ∂μ = 0) :
    h = 0 := by
  classical
  let coord : Fin d → C(K, ℂ) := fun i =>
    ⟨fun x => ((x : EuclideanSpace ℝ (Fin d)) i : ℂ),
      Complex.continuous_ofReal.comp ((continuous_apply i).comp continuous_subtype_val)⟩
  let evalHom : MvPolynomial (Fin d) ℂ →ₐ[ℂ] C(K, ℂ) := MvPolynomial.aeval coord
  have heval (p : MvPolynomial (Fin d) ℂ) (x : K) :
      evalHom p x = MvPolynomial.eval (fun i => ((x : EuclideanSpace ℝ (Fin d)) i : ℂ)) p := by
    induction p using MvPolynomial.induction_on with
    | C a => simp [evalHom, coord, MvPolynomial.aeval_def]
    | add p q hp hq =>
        change evalHom (p + q) x = _
        rw [map_add, ContinuousMap.add_apply, hp, hq, MvPolynomial.eval_add]
    | mul_X p i hp =>
        change evalHom (p * MvPolynomial.X i) x = _
        rw [map_mul, ContinuousMap.mul_apply, hp]
        have hXi : evalHom (MvPolynomial.X i) x = ((x : EuclideanSpace ℝ (Fin d)) i : ℂ) := by
          simp [evalHom, coord]
        rw [hXi, MvPolynomial.eval_mul, MvPolynomial.eval_X]
  let R := evalHom.range
  have hsep : R.SeparatesPoints := by
    intro x y hxy
    obtain ⟨i, hi⟩ : ∃ i : Fin d,
        (x : EuclideanSpace ℝ (Fin d)) i ≠ (y : EuclideanSpace ℝ (Fin d)) i := by
      by_contra hnot
      have heq : ∀ i : Fin d, (x : EuclideanSpace ℝ (Fin d)) i =
          (y : EuclideanSpace ℝ (Fin d)) i := by
        intro i
        by_contra hneq
        exact hnot ⟨i, hneq⟩
      exact hxy (Subtype.ext (funext heq))
    refine ⟨_, ⟨evalHom (MvPolynomial.X i), ?_, rfl⟩, ?_⟩
    · exact ⟨MvPolynomial.X i, rfl⟩
    simpa [evalHom, coord] using hi
  have hstarEval (p : MvPolynomial (Fin d) ℂ) :
      star (evalHom p) = evalHom (MvPolynomial.map (starRingEnd ℂ) p) := by
    ext x
    change star (evalHom p x) = evalHom (MvPolynomial.map (starRingEnd ℂ) p) x
    rw [heval, heval]
    induction p using MvPolynomial.induction_on' with
    | monomial s a =>
        simp only [MvPolynomial.map_monomial, MvPolynomial.eval_monomial]
        have hprod : star (s.prod fun n e => ((x : EuclideanSpace ℝ (Fin d)) n : ℂ) ^ e) =
            s.prod fun n e => ((x : EuclideanSpace ℝ (Fin d)) n : ℂ) ^ e := by
          simp [Finsupp.prod, Complex.conj_ofReal]
        rw [star_mul, hprod]
        rw [starRingEnd_apply]
        exact mul_comm _ _
    | add p q hp hq => simp [hp, hq]
  let A : StarSubalgebra ℂ C(K, ℂ) := ⟨R, by
    rintro f ⟨p, rfl⟩
    exact ⟨MvPolynomial.map (starRingEnd ℂ) p, (hstarEval p).symm⟩⟩
  have hA : A.topologicalClosure = ⊤ :=
    ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints A hsep
  let mult := continuousMulRightCLM h
  let T : C(K, ℂ) →L[ℝ] ℂ :=
    (MeasureTheory.L1.integralCLM (μ := μ)).comp
      ((ContinuousMap.toLp 1 μ ℝ).comp mult)
  have hT_apply (f : C(K, ℂ)) : T f = ∫ x, f x * h x ∂μ := by
    change MeasureTheory.L1.integralCLM
      (ContinuousMap.toLp 1 μ ℝ ((mult) f)) = _
    change MeasureTheory.L1.integralCLM
      (ContinuousMap.toLp 1 μ ℝ (f * h)) = _
    rw [← MeasureTheory.L1.integral_eq, MeasureTheory.L1.integral_eq_integral]
    exact integral_congr_ae
      (ContinuousMap.coeFn_toLp (p := 1) (μ := μ) (𝕜 := ℝ) (f * h))
  have hclosed : IsClosed {f : C(K, ℂ) | T f = 0} :=
    isClosed_singleton.preimage T.continuous
  have hvanish : ∀ f ∈ (A : Set C(K, ℂ)), T f = 0 := by
    rintro f ⟨p, rfl⟩
    rw [hT_apply]
    calc
      (∫ x, evalHom p x * h x ∂μ) =
          ∫ x, MvPolynomial.eval (fun i => ((x : EuclideanSpace ℝ (Fin d)) i : ℂ)) p * h x ∂μ := by
        apply integral_congr_ae
        filter_upwards with x
        rw [heval]
      _ = 0 := hmom p
  have hvanishClosure : ∀ f ∈ A.topologicalClosure, T f = 0 := by
    intro f hf
    exact hclosed.closure_subset_iff.mpr hvanish hf
  have hstar : star h ∈ A.topologicalClosure := by rw [hA]; trivial
  have hzero : ∫ x, star (h x) * h x ∂μ = 0 := by
    calc
      (∫ x, star (h x) * h x ∂μ) = T (star h) := (hT_apply (star h)).symm
      _ = 0 := hvanishClosure (star h) hstar
  have hpoint : ∀ x : K, h x = 0 := by
    intro x
    by_cases hx : h x = 0
    · exact hx
    · have hx' : h x ≠ 0 := hx
      have hcont : Continuous (fun x : K => ‖h x‖ ^ 2) := h.continuous.norm.pow 2
      have hint : Integrable (fun x : K => ‖h x‖ ^ 2) μ := by
        simpa only [IntegrableOn, Measure.restrict_univ] using
          hcont.continuousOn.integrableOn_compact isCompact_univ
      have hxn : ‖h x‖ ^ 2 ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr hx')
      have hpos : 0 < ∫ x, ‖h x‖ ^ 2 ∂μ :=
        integral_pos_of_integrable_nonneg_nonzero hcont hint (fun _ => sq_nonneg _) hxn
      have hfun : (fun x : K => star (h x) * h x) = fun x => (↑(‖h x‖ ^ 2) : ℂ) := by
        funext x
        simp [Complex.conj_mul']
      rw [hfun, integral_complex_ofReal] at hzero
      have hI : (∫ x, ‖h x‖ ^ 2 ∂μ) = 0 := by
        have := congrArg Complex.re hzero
        simpa using this
      exact False.elim ((ne_of_gt hpos) hI)
  ext x
  exact hpoint x

/-- A continuous compactly supported Euclidean function is detected by all of its polynomial
moments with respect to Lebesgue measure. -/
theorem euclidean_compactSupport_polynomial_moment_detection
    {d : ℕ} (h : EuclideanSpace ℝ (Fin d) → ℂ) (hcont : Continuous h)
    (hcompact : HasCompactSupport h)
    (hmom : ∀ p : MvPolynomial (Fin d) ℂ,
      ∫ x, MvPolynomial.eval (fun i => ((x : EuclideanSpace ℝ (Fin d)) i : ℂ)) p * h x = 0) :
    h = 0 := by
  classical
  let K : Set (EuclideanSpace ℝ (Fin d)) := tsupport h
  have hKcompact : IsCompact K := by
    change IsCompact (tsupport h)
    exact hcompact
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hKcompact
  letI : MeasureSpace K := MeasureTheory.Measure.Subtype.measureSpace
  have hKmeas : MeasurableSet K := hKcompact.measurableSet
  letI : IsFiniteMeasure (volume : Measure K) := by
    refine ⟨?_⟩
    rw [MeasureTheory.Measure.Subtype.volume_univ hKmeas.nullMeasurableSet]
    exact hKcompact.measure_lt_top
  let S : Set K := Subtype.val ⁻¹' Function.support h
  have hImage : (Subtype.val '' S) = Function.support h := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨⟨x, subset_tsupport h hx⟩, hx, rfl⟩
  have hDense : Dense S := by
    rw [dense_iff_closure_eq]
    ext x
    rw [closure_subtype, hImage]
    simp [K, tsupport]
  letI : Measure.IsOpenPosMeasure (volume : Measure K) := by
    constructor
    intro U hU hUne
    obtain ⟨V, hVopen, hV⟩ := isOpen_induced_iff.mp hU
    obtain ⟨x, hx⟩ := hUne
    obtain ⟨y, hyS, hyV⟩ := hDense.exists_mem_open
      (hVopen.preimage continuous_subtype_val) ⟨x, hV ▸ hx⟩
    have hySupport : y.1 ∈ Function.support h := hyS
    let W : Set (EuclideanSpace ℝ (Fin d)) := V ∩ Function.support h
    have hSupportOpen : IsOpen (Function.support h) := by
      change IsOpen (h ⁻¹' ({0}ᶜ : Set ℂ))
      exact hcont.isOpen_preimage _ isClosed_singleton.isOpen_compl
    have hWopen : IsOpen W := hVopen.inter hSupportOpen
    have hWne : W.Nonempty := ⟨y.1, hyV, hySupport⟩
    have hWsub : W ⊆ Subtype.val '' U := by
      intro z hz
      refine ⟨⟨z, subset_tsupport h hz.2⟩, ?_, rfl⟩
      rw [← hV]
      exact hz.1
    have hUmeasure : (volume : Measure K) U = volume (Subtype.val '' U) := by
      rw [MeasureTheory.Measure.Subtype.volume_def]
      exact comap_subtype_coe_apply hKmeas volume U
    have hWpos : 0 < volume W := hWopen.measure_pos volume hWne
    rw [hUmeasure]
    exact (ne_of_gt (lt_of_lt_of_le hWpos (measure_mono hWsub)))
  have hMomentOnK (p : MvPolynomial (Fin d) ℂ) :
      ∫ x : K, MvPolynomial.eval (fun i => ((x.1 : EuclideanSpace ℝ (Fin d)) i : ℂ)) p * h x.1
        ∂(volume : Measure K) = 0 := by
    let F : EuclideanSpace ℝ (Fin d) → ℂ := fun x =>
      MvPolynomial.eval (fun i => (x i : ℂ)) p * h x
    have hMap : (volume : Measure K).map (Subtype.val : K → EuclideanSpace ℝ (Fin d)) =
        volume.restrict K := MeasurableSet.map_coe_volume hKmeas
    have hFullRestr : ∫ x, F x = ∫ x in K, F x := by
      rw [← integral_indicator hKmeas]
      apply integral_congr_ae
      filter_upwards with x
      by_cases hx : x ∈ K
      · simp [hx, F]
      · have hx0 : h x = 0 := by
          by_contra hn
          exact hx (subset_tsupport h (by simpa [Function.mem_support] using hn))
        simp [hx, hx0, F]
    calc
      _ = ∫ x, F x ∂(volume.restrict K) := by
        symm
        rw [← hMap]
        exact (MeasurableEmbedding.subtype_coe hKmeas).integral_map F
      _ = ∫ x in K, F x := rfl
      _ = ∫ x, F x := hFullRestr.symm
      _ = 0 := hmom p
  let hK : C(K, ℂ) := ⟨fun x => h x.1, hcont.comp continuous_subtype_val⟩
  have hhK : hK = 0 :=
    compact_euclidean_polynomial_moment_detection (μ := volume) hK hMomentOnK
  ext x
  by_cases hx : h x = 0
  · exact hx
  · have hxK : x ∈ K := subset_tsupport h (by simpa [Function.mem_support] using hx)
    have hzero := congrArg (fun q : C(K, ℂ) => q ⟨x, hxK⟩) hhK
    exact (hx (by simpa [hK] using hzero)).elim

end RieszEuclidean
