import RieszEuclidean.TitchmarshFunctionAlgebra
import RieszEuclidean.TitchmarshBootstrap
import RieszEuclidean.TitchmarshFunctionHalf
import RieszEuclidean.TitchmarshFunctionTranslations
import RieszEuclidean.TitchmarshMomentDetection
import Mathlib.Algebra.MvPolynomial.Basic

/-! Endpoint consequences for the actual convolution of compactly supported functions. -/

noncomputable section

open MeasureTheory
open Filter Topology
open scoped Convolution CompactlySupported

namespace RieszEuclidean.TitchmarshFunctionAlgebra

open RieszEuclidean.TitchmarshBootstrap
open HalfspaceFunctions

variable {d : ℕ}

private def coordinateFunctional (i : Fin d) : Euclidean d →L[ℝ] ℝ :=
  PiLp.proj 2 (fun _ : Fin d => ℝ) i

private theorem coordinateFunctional_apply (i : Fin d) (x : Euclidean d) :
    coordinateFunctional i x = x i := rfl

private theorem coordinate_continuous (i : Fin d) :
    Continuous (fun x : Euclidean d => ((x i : ℝ) : ℂ)) :=
  Complex.continuous_ofReal.comp (continuous_apply i)

private theorem polynomialEval_continuous (p : MvPolynomial (Fin d) ℂ) :
    Continuous (fun x : Euclidean d =>
      MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ)) p) := by
  induction p using MvPolynomial.induction_on with
  | C c => simpa using continuous_const
  | add p q hp hq =>
      simpa only [MvPolynomial.eval_add] using hp.add hq
  | mul_X p i hp =>
      have hXi : Continuous (fun x : Euclidean d => ((x i : ℝ) : ℂ)) :=
        coordinate_continuous i
      simpa only [MvPolynomial.eval_mul, MvPolynomial.eval_X] using hp.mul hXi

/-- Apply a complex polynomial in the coordinate multipliers to a halfspace
function. -/
private def polynomialMultiplier (ℓ : Euclidean d →L[ℝ] ℝ)
    (p : MvPolynomial (Fin d) ℂ) (g : HalfspaceFunctions d ℓ) :
    HalfspaceFunctions d ℓ := by
  let q : Euclidean d → ℂ := fun x =>
    MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ)) p * g.val x
  have hq : Continuous q := polynomialEval_continuous p |>.mul g.val.continuous
  have hs : HasCompactSupport q := by
    dsimp [q]
    exact g.val.hasCompactSupport.mul_left
  refine ⟨⟨⟨q, hq⟩, hs⟩, ?_⟩
  intro x hx
  simp [q, g.property x hx]

private theorem coe_polynomialMultiplier (ℓ : Euclidean d →L[ℝ] ℝ)
    (p : MvPolynomial (Fin d) ℂ) (g : HalfspaceFunctions d ℓ) (x : Euclidean d) :
    (polynomialMultiplier ℓ p g).val x =
      MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ)) p * g.val x := rfl

private theorem polynomialMultiplier_C (ℓ : Euclidean d →L[ℝ] ℝ)
    (c : ℂ) (g : HalfspaceFunctions d ℓ) :
    polynomialMultiplier ℓ (MvPolynomial.C c) g = c • g := by
  apply Subtype.ext
  apply CompactlySupportedContinuousMap.ext
  intro x
  simp [polynomialMultiplier, MvPolynomial.eval_C, smul_eq_mul]

private theorem polynomialMultiplier_add (ℓ : Euclidean d →L[ℝ] ℝ)
    (p q : MvPolynomial (Fin d) ℂ) (g : HalfspaceFunctions d ℓ) :
    polynomialMultiplier ℓ (p + q) g =
      polynomialMultiplier ℓ p g + polynomialMultiplier ℓ q g := by
  apply Subtype.ext
  apply CompactlySupportedContinuousMap.ext
  intro x
  simp [polynomialMultiplier, MvPolynomial.eval_add, add_mul]

private theorem polynomialMultiplier_mul_X (ℓ : Euclidean d →L[ℝ] ℝ)
    (p : MvPolynomial (Fin d) ℂ) (i : Fin d) (g : HalfspaceFunctions d ℓ) :
    polynomialMultiplier ℓ (p * MvPolynomial.X i) g =
      HalfspaceFunctions.Mcoordinate d (coordinateFunctional i)
        (polynomialMultiplier ℓ p g) := by
  apply Subtype.ext
  apply CompactlySupportedContinuousMap.ext
  intro x
  simp [polynomialMultiplier, HalfspaceFunctions.Mcoordinate,
    coordinateFunctional, coordinateMultiplier, MvPolynomial.eval_mul,
    MvPolynomial.eval_X, mul_assoc, mul_left_comm, mul_comm]

private theorem polynomialMultiplier_preserves_vanishing
    (ℓ : Euclidean d →L[ℝ] ℝ) {f g : HalfspaceFunctions d ℓ} {T : ℝ}
    (hT : 0 ≤ T) (hfg : HalfspaceFunctions.V d (f * g) T)
    (p : MvPolynomial (Fin d) ℂ) :
    HalfspaceFunctions.V d (f * polynomialMultiplier ℓ p g) T := by
  let A := HalfspaceFunctions d ℓ
  let V := HalfspaceFunctions.V d (ℓ := ℓ)
  let D : Fin d → Data A := fun i =>
    HalfspaceFunctions.provedBootstrapData d ℓ
      (coordinateFunctional i)
  induction p using MvPolynomial.induction_on with
  | C c =>
      have hs : V (c • (f * g)) T := by
        intro x hx
        have hzero := hfg x hx
        simp only [coe_mul] at hzero
        simp [hzero]
      have hmul : f * polynomialMultiplier ℓ (MvPolynomial.C c) g =
          c • (f * g) := by
        rw [polynomialMultiplier_C]
        apply Subtype.ext
        apply CompactlySupportedContinuousMap.ext
        intro x
        change (convolution d f.val (c • g.val) : Euclidean d → ℂ) x =
          c • (convolution d f.val g.val : Euclidean d → ℂ) x
        rw [coe_convolution, coe_convolution]
        simp only [Pi.smul_apply, smul_eq_mul]
        rw [← integral_const_mul]
        apply integral_congr_ae
        filter_upwards with y
        change f.val y * (c * g.val (x - y)) = c * (f.val y * g.val (x - y))
        ring
      rw [hmul]
      exact hs
  | add p q hp hq =>
      rw [polynomialMultiplier_add]
      simpa only [mul_add] using HalfspaceFunctions.V_add d hp hq
  | mul_X p i hp =>
      rw [polynomialMultiplier_mul_X]
      exact (D i).multiplier_stability f (polynomialMultiplier ℓ p g) hT hp

/-- If two functions are supported in the positive halfspace and their
convolution vanishes below `T`, every pointwise product across a sublevel sum
also vanishes. -/
theorem halfspace_convolution_pointwise_zero
    (ℓ : Euclidean d →L[ℝ] ℝ) {f g : Function d}
    (hf : ∀ x, ℓ x < 0 → f x = 0)
    (hg : ∀ x, ℓ x < 0 → g x = 0)
    {T : ℝ} (hT : 0 ≤ T)
    (hconv : ∀ x, ℓ x < T →
      (convolution d f g : Euclidean d → ℂ) x = 0) :
    ∀ x, ℓ x < T → ∀ y, f y * g (x - y) = 0 := by
  let f' : HalfspaceFunctions d ℓ := ⟨f, hf⟩
  let g' : HalfspaceFunctions d ℓ := ⟨g, hg⟩
  intro x hx y
  let H : Euclidean d → ℂ := fun z => f (x - z) * g z
  have hHcont : Continuous H := by
    dsimp [H]
    exact f.continuous.comp (continuous_const.sub continuous_id) |>.mul g.continuous
  have hHcompact : HasCompactSupport H := by
    dsimp [H]
    exact g.hasCompactSupport.mul_left
  have hmom : ∀ p : MvPolynomial (Fin d) ℂ,
      ∫ z, MvPolynomial.eval (fun i => ((z i : ℝ) : ℂ)) p * H z = 0 := by
    intro p
    have hpoly := polynomialMultiplier_preserves_vanishing ℓ (f := f') (g := g') hT
      (by
        intro q hq
        simpa [f', g', HalfspaceFunctions.coe_mul, coe_convolution] using hconv q hq) p
    have hvan : (f' * polynomialMultiplier ℓ p g').val x = 0 := hpoly x hx
    have hconv' : (convolution d f (polynomialMultiplier ℓ p g').val :
        Euclidean d → ℂ) x = 0 := by
      simpa [f', g', HalfspaceFunctions.coe_mul] using hvan
    have hcomm : convolution d f (polynomialMultiplier ℓ p g').val =
        convolution d (polynomialMultiplier ℓ p g').val f :=
      convolution_comm d f (polynomialMultiplier ℓ p g').val
    have hconv'' : (convolution d (polynomialMultiplier ℓ p g').val f :
        Euclidean d → ℂ) x = 0 := by
      rw [← hcomm]
      exact hconv'
    rw [coe_convolution] at hconv''
    calc
      (∫ z, MvPolynomial.eval (fun i => ((z i : ℝ) : ℂ)) p * H z) =
          ∫ z, (polynomialMultiplier ℓ p g').val z * f (x - z) := by
        apply integral_congr_ae
        filter_upwards with z
        rw [coe_polynomialMultiplier]
        dsimp [H]
        ring
      _ = 0 := hconv''
  have hzero := RieszEuclidean.euclidean_compactSupport_polynomial_moment_detection
    H hHcont hHcompact hmom
  have hpoint := congrFun hzero (x - y)
  simpa [H, sub_sub_cancel] using hpoint

/-- The support endpoint of the actual convolution is the sum of the factor
endpoints, expressed pointwise along any continuous real linear functional. -/
theorem convolution_halfspace_endpoint {f g : Euclidean d → ℂ}
    (hf : Continuous f) (hg : Continuous g)
    (hfc : HasCompactSupport f) (hgc : HasCompactSupport g)
    (ℓ : Euclidean d →L[ℝ] ℝ) {T : ℝ}
    (hvan : ∀ z, ℓ z < T →
      (f ⋆[ContinuousLinearMap.mul ℂ ℂ, volume] g) z = 0) :
    ∀ x y, f x ≠ 0 → g y ≠ 0 → T ≤ ℓ (x + y) := by
  intro x y hfx hgy
  have hfne : f ≠ 0 := by
    intro hz
    apply hfx
    simp [hz]
  have hgne : g ≠ 0 := by
    intro hz
    apply hgy
    simp [hz]
  obtain ⟨a, ha, hamin⟩ :=
    RieszEuclidean.CompleteMinimal.exists_minimum_on_tsupport hfc hfne ℓ
  obtain ⟨b, hb, hbmin⟩ :=
    RieszEuclidean.CompleteMinimal.exists_minimum_on_tsupport hgc hgne ℓ
  let f₀ := RieszEuclidean.CompleteMinimal.titchmarshTranslate f (-a)
  let g₀ := RieszEuclidean.CompleteMinimal.titchmarshTranslate g (-b)
  have hf₀cont : Continuous f₀ :=
    RieszEuclidean.CompleteMinimal.continuous_titchmarshTranslate hf (-a)
  have hg₀cont : Continuous g₀ :=
    RieszEuclidean.CompleteMinimal.continuous_titchmarshTranslate hg (-b)
  have hf₀compact : HasCompactSupport f₀ :=
    RieszEuclidean.CompleteMinimal.hasCompactSupport_titchmarshTranslate hfc (-a)
  have hg₀compact : HasCompactSupport g₀ :=
    RieszEuclidean.CompleteMinimal.hasCompactSupport_titchmarshTranslate hgc (-b)
  have hf₀supp : ∀ z, ℓ z < 0 → f₀ z = 0 := by
    intro z hz
    by_cases hzero : f₀ z = 0
    · exact hzero
    · have hnonzero := hamin (z + a) (by
        apply subset_tsupport
        simpa [f₀, RieszEuclidean.CompleteMinimal.titchmarshTranslate] using hzero)
      have heq : ℓ (z + a) = ℓ z + ℓ a := by simp
      rw [heq] at hnonzero
      linarith
  have hg₀supp : ∀ z, ℓ z < 0 → g₀ z = 0 := by
    intro z hz
    by_cases hzero : g₀ z = 0
    · exact hzero
    · have hnonzero := hbmin (z + b) (by
        apply subset_tsupport
        simpa [g₀, RieszEuclidean.CompleteMinimal.titchmarshTranslate] using hzero)
      have heq : ℓ (z + b) = ℓ z + ℓ b := by simp
      rw [heq] at hnonzero
      linarith
  let T₀ := T - ℓ a - ℓ b
  have hT₀_nonpos : T₀ ≤ 0 := by
    by_cases hT₀ : 0 < T₀
    · have hT₀_nonneg : 0 ≤ T₀ := le_of_lt hT₀
      have hvan₀ : ∀ z, ℓ z < T₀ →
          (f₀ ⋆[ContinuousLinearMap.mul ℂ ℂ, volume] g₀) z = 0 := by
        intro z hz
        rw [RieszEuclidean.CompleteMinimal.convolution_titchmarshTranslate]
        apply hvan
        have heq : ℓ (z - ((-a) + (-b))) = ℓ z + ℓ a + ℓ b := by
          simp [map_add, sub_eq_add_neg]
          ring
        rw [heq]
        dsimp [T₀] at hz
        linarith
      have hpoint := halfspace_convolution_pointwise_zero (d := d)
        (ℓ := ℓ) (f := ⟨⟨f₀, hf₀cont⟩, hf₀compact⟩)
        (g := ⟨⟨g₀, hg₀cont⟩, hg₀compact⟩)
        hf₀supp hg₀supp
        (T := T₀) hT₀_nonneg (by
          intro z hz
          simpa [coe_convolution] using hvan₀ z hz)
      have hnear_f : ∃ u, f₀ u ≠ 0 ∧ ℓ u < T₀ / 2 := by
        have hmem : a ∈ closure (Function.support f) := ha
        have hnhds : {q : Euclidean d | ℓ (q - a) < T₀ / 2} ∈ 𝓝 a := by
          apply (isOpen_lt (ℓ.continuous.comp (continuous_id.sub continuous_const))
            continuous_const).mem_nhds
          simpa using half_pos hT₀
        obtain ⟨q, hq, hqsupp⟩ := (mem_closure_iff_nhds.mp hmem) _ hnhds
        refine ⟨q - a, ?_, ?_⟩
        · simpa [f₀, RieszEuclidean.CompleteMinimal.titchmarshTranslate,
            sub_eq_add_neg, add_assoc] using hqsupp
        · simpa using hq
      have hnear_g : ∃ u, g₀ u ≠ 0 ∧ ℓ u < T₀ / 2 := by
        have hmem : b ∈ closure (Function.support g) := hb
        have hnhds : {q : Euclidean d | ℓ (q - b) < T₀ / 2} ∈ 𝓝 b := by
          apply (isOpen_lt (ℓ.continuous.comp (continuous_id.sub continuous_const))
            continuous_const).mem_nhds
          simpa using half_pos hT₀
        obtain ⟨q, hq, hqsupp⟩ := (mem_closure_iff_nhds.mp hmem) _ hnhds
        refine ⟨q - b, ?_, ?_⟩
        · simpa [g₀, RieszEuclidean.CompleteMinimal.titchmarshTranslate,
            sub_eq_add_neg, add_assoc] using hqsupp
        · simpa using hq
      obtain ⟨u, hu, hlu⟩ := hnear_f
      obtain ⟨w, hw, hlw⟩ := hnear_g
      have hprod := hpoint (u + w) (by simpa using add_lt_add hlu hlw) u
      have hprod' : f₀ u * g₀ w = 0 := by
        simpa [sub_eq_add_neg, add_assoc] using hprod
      exact False.elim ((mul_ne_zero hu hw) hprod')
    · exact le_of_not_gt hT₀
  have haminx := hamin x (subset_tsupport f hfx)
  have hbminy := hbmin y (subset_tsupport g hgy)
  have hsum_min : ℓ a + ℓ b ≤ ℓ (x + y) := by
    have hxadd : ℓ (x + y) = ℓ x + ℓ y := by simp
    rw [hxadd]
    linarith
  dsimp [T₀] at hT₀_nonpos
  linarith

end RieszEuclidean.TitchmarshFunctionAlgebra
