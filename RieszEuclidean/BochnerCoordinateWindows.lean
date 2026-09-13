import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Inner

noncomputable section
open MeasureTheory
namespace RieszEuclidean
variable {α ι H : Type*} [MeasurableSpace α] {μ : Measure α}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Parseval in the nonnegative real form needed for integration. -/
theorem hilbertBasis_hasSum_sq (e : HilbertBasis ι ℂ H) (v : H) :
    HasSum (fun i => ‖inner (𝕜 := ℂ) (e i) v‖ ^ 2) (‖v‖ ^ 2) := by
  have h := (e.hasSum_inner_mul_inner v v).mapL Complex.reCLM
  convert h using 1
  · funext i
    change ‖inner (𝕜 := ℂ) (e i) v‖ ^ 2 =
      (inner (𝕜 := ℂ) v (e i) * inner (𝕜 := ℂ) (e i) v).re
    rw [← inner_conj_symm v (e i), RCLike.conj_mul]
    simp [← Complex.ofReal_pow]
  · simp [inner_self_eq_norm_sq_to_K, ← Complex.ofReal_pow]

/-- Scalar coordinates preserve inner products after summation. -/
theorem hilbertBasis_hasSum_inner (e : HilbertBasis ι ℂ H) (v w : H) :
    HasSum (fun i => inner (𝕜 := ℂ) (inner (𝕜 := ℂ) (e i) v)
      (inner (𝕜 := ℂ) (e i) w)) (inner (𝕜 := ℂ) v w) := by
  simpa only [RCLike.inner_apply, inner_conj_symm, mul_comm] using
    e.hasSum_inner_mul_inner v w

/-- Integrated Parseval for a countable Hilbert basis. -/
theorem hilbertBasis_hasSum_integral_sq [Countable ι] (e : HilbertBasis ι ℂ H)
    (v : α → H) (hv : AEStronglyMeasurable v μ)
    (hvi : Integrable (fun x => ‖v x‖ ^ 2) μ) :
    HasSum (fun i => ∫ x, ‖inner (𝕜 := ℂ) (e i) (v x)‖ ^ 2 ∂μ)
      (∫ x, ‖v x‖ ^ 2 ∂μ) := by
  apply hasSum_integral_of_dominated_convergence
    (fun i x => ‖inner (𝕜 := ℂ) (e i) (v x)‖ ^ 2)
  · exact fun i => (hv.const_inner).norm.pow 2
  · exact fun i => Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  · exact Filter.Eventually.of_forall fun x => (hilbertBasis_hasSum_sq e (v x)).summable
  · simpa only [(hilbertBasis_hasSum_sq e _).tsum_eq] using hvi
  · exact Filter.Eventually.of_forall fun x => hilbertBasis_hasSum_sq e (v x)

/-- The scalar coordinate pair is bounded by the sum of its two coordinate energies. -/
theorem hilbertBasis_coordinate_inner_bound (e : HilbertBasis ι ℂ H)
    (v w : H) (i : ι) :
    ‖inner (𝕜 := ℂ) (inner (𝕜 := ℂ) (e i) v) (inner (𝕜 := ℂ) (e i) w)‖ ≤
      ‖inner (𝕜 := ℂ) (e i) v‖ ^ 2 + ‖inner (𝕜 := ℂ) (e i) w‖ ^ 2 := by
  refine (norm_inner_le_norm _ _).trans ?_
  nlinarith [sq_nonneg (‖inner (𝕜 := ℂ) (e i) v‖ - ‖inner (𝕜 := ℂ) (e i) w‖)]

/-- Integrated inner-product Parseval, with both inputs controlled in square mean. -/
theorem hilbertBasis_hasSum_integral_inner [Countable ι] (e : HilbertBasis ι ℂ H)
    (v w : α → H) (hv : AEStronglyMeasurable v μ) (hw : AEStronglyMeasurable w μ)
    (hvi : Integrable (fun x => ‖v x‖ ^ 2) μ)
    (hwi : Integrable (fun x => ‖w x‖ ^ 2) μ) :
    HasSum (fun i => ∫ x, inner (𝕜 := ℂ) (inner (𝕜 := ℂ) (e i) (v x))
      (inner (𝕜 := ℂ) (e i) (w x)) ∂μ) (∫ x, inner (𝕜 := ℂ) (v x) (w x) ∂μ) := by
  apply hasSum_integral_of_dominated_convergence
    (fun i x => ‖inner (𝕜 := ℂ) (e i) (v x)‖ ^ 2 +
      ‖inner (𝕜 := ℂ) (e i) (w x)‖ ^ 2)
  · exact fun i => hv.const_inner.inner hw.const_inner
  · exact fun i => Filter.Eventually.of_forall fun x => hilbertBasis_coordinate_inner_bound e _ _ i
  · exact Filter.Eventually.of_forall fun x =>
      (hilbertBasis_hasSum_sq e (v x)).summable.add (hilbertBasis_hasSum_sq e (w x)).summable
  · have he : (fun x => ∑' i, (‖inner (𝕜 := ℂ) (e i) (v x)‖ ^ 2 +
        ‖inner (𝕜 := ℂ) (e i) (w x)‖ ^ 2)) = fun x => ‖v x‖ ^ 2 + ‖w x‖ ^ 2 := by
      funext x
      exact ((hilbertBasis_hasSum_sq e (v x)).add (hilbertBasis_hasSum_sq e (w x))).tsum_eq
    rw [he]
    exact hvi.add hwi
  · exact Filter.Eventually.of_forall fun x => hilbertBasis_hasSum_inner e (v x) (w x)

/-- Absolute integrals of all coordinate pairings form a summable series. -/
theorem hilbertBasis_summable_integral_norm_inner [Countable ι] (e : HilbertBasis ι ℂ H)
    (v w : α → H) (hv : AEStronglyMeasurable v μ) (hw : AEStronglyMeasurable w μ)
    (hvi : Integrable (fun x => ‖v x‖ ^ 2) μ)
    (hwi : Integrable (fun x => ‖w x‖ ^ 2) μ) :
    Summable (fun i => ∫ x, ‖inner (𝕜 := ℂ) (inner (𝕜 := ℂ) (e i) (v x))
      (inner (𝕜 := ℂ) (e i) (w x))‖ ∂μ) := by
  apply HasSum.summable (a := ∫ x, ∑' i, ‖inner (𝕜 := ℂ)
    (inner (𝕜 := ℂ) (e i) (v x)) (inner (𝕜 := ℂ) (e i) (w x))‖ ∂μ)
  apply hasSum_integral_of_dominated_convergence
    (fun i x => ‖inner (𝕜 := ℂ) (e i) (v x)‖ ^ 2 +
      ‖inner (𝕜 := ℂ) (e i) (w x)‖ ^ 2)
  · exact fun i => (hv.const_inner.inner hw.const_inner).norm
  · exact fun i => Filter.Eventually.of_forall fun x => by
      simpa only [norm_norm] using hilbertBasis_coordinate_inner_bound e (v x) (w x) i
  · exact Filter.Eventually.of_forall fun x =>
      (hilbertBasis_hasSum_sq e (v x)).summable.add (hilbertBasis_hasSum_sq e (w x)).summable
  · have he : (fun x => ∑' i, (‖inner (𝕜 := ℂ) (e i) (v x)‖ ^ 2 +
        ‖inner (𝕜 := ℂ) (e i) (w x)‖ ^ 2)) = fun x => ‖v x‖ ^ 2 + ‖w x‖ ^ 2 := by
      funext x
      exact ((hilbertBasis_hasSum_sq e (v x)).add (hilbertBasis_hasSum_sq e (w x))).tsum_eq
    rw [he]
    exact hvi.add hwi
  · exact Filter.Eventually.of_forall fun x =>
      (summable_norm_iff.mpr (hilbertBasis_hasSum_inner e (v x) (w x)).summable).hasSum

/-- Every individual coordinate square is integrable under a square-integrable bound. -/
theorem hilbertBasis_integrable_coordinate_sq (e : HilbertBasis ι ℂ H)
    (v : α → H) (hv : AEStronglyMeasurable v μ)
    (hvi : Integrable (fun x => ‖v x‖ ^ 2) μ) (i : ι) :
    Integrable (fun x => ‖inner (𝕜 := ℂ) (e i) (v x)‖ ^ 2) μ := by
  apply hvi.mono' (hv.const_inner.norm.pow 2)
  exact Filter.Eventually.of_forall fun x => by
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    rw [← (hilbertBasis_hasSum_sq e (v x)).tsum_eq]
    exact (hilbertBasis_hasSum_sq e (v x)).summable.le_tsum i (fun j _ => sq_nonneg _)

/-- Every coordinate pairing is integrable for two square-integrable inputs. -/
theorem hilbertBasis_integrable_coordinate_inner (e : HilbertBasis ι ℂ H)
    (v w : α → H) (hv : AEStronglyMeasurable v μ) (hw : AEStronglyMeasurable w μ)
    (hvi : Integrable (fun x => ‖v x‖ ^ 2) μ)
    (hwi : Integrable (fun x => ‖w x‖ ^ 2) μ) (i : ι) :
    Integrable (fun x => inner (𝕜 := ℂ) (inner (𝕜 := ℂ) (e i) (v x))
      (inner (𝕜 := ℂ) (e i) (w x))) μ := by
  apply ((hilbertBasis_integrable_coordinate_sq e v hv hvi i).add
    (hilbertBasis_integrable_coordinate_sq e w hw hwi i)).mono'
    (hv.const_inner.inner hw.const_inner)
  exact Filter.Eventually.of_forall fun x => hilbertBasis_coordinate_inner_bound e _ _ i

/-- A Hilbert basis in a separable space has countably many indices. -/
theorem hilbertBasis_countable [TopologicalSpace.SeparableSpace H]
    (e : HilbertBasis ι ℂ H) : Countable ι := by
  have hd : Pairwise (fun i j => Disjoint (Metric.ball (e i) (1 / 2 : ℝ))
      (Metric.ball (e j) (1 / 2 : ℝ))) := by
    intro i j hij
    apply Metric.ball_disjoint_ball
    have hh : ‖e i - e j‖ ^ 2 = 2 := by
      rw [norm_sub_sq (𝕜 := ℂ), e.orthonormal.norm_eq_one, e.orthonormal.norm_eq_one,
        e.orthonormal.inner_eq_zero hij]
      norm_num
    rw [dist_eq_norm]
    nlinarith [norm_nonneg (e i - e j)]
  exact hd.countable_of_isOpen_disjoint (fun _ => Metric.isOpen_ball)
    (fun i => Metric.nonempty_ball.mpr (by norm_num))

/-- A separable complete complex Hilbert space admits a countable Hilbert basis. -/
theorem exists_countable_hilbertBasis [CompleteSpace H] [TopologicalSpace.SeparableSpace H] :
    ∃ (s : Set H), Countable s ∧ Nonempty (HilbertBasis s ℂ H) := by
  obtain ⟨s, e, _⟩ := exists_hilbertBasis ℂ H
  exact ⟨s, hilbertBasis_countable e, ⟨e⟩⟩
end RieszEuclidean
