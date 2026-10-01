import Mathlib.Analysis.Convolution
import Mathlib.Topology.ContinuousMap.CompactlySupported
import RieszEuclidean.Basic
import RieszEuclidean.TitchmarshBootstrap
import RieszEuclidean.TitchmarshFunctionHalf

/-!
# Compactly supported functions with convolution multiplication

This file sets up the concrete convolution algebra used by the algebraic
Titchmarsh bootstrap. The multiplication is Lebesgue convolution, rather than
pointwise multiplication.
-/

noncomputable section

set_option maxHeartbeats 600000

open MeasureTheory
open scoped CompactlySupported Convolution

namespace RieszEuclidean.TitchmarshFunctionAlgebra

variable (d : ℕ)

private theorem volume_neg_map :
    Measure.map Neg.neg (volume : Measure (RieszEuclidean.Euclidean d)) = volume := by
  exact (LinearIsometryEquiv.measurePreserving
    (LinearIsometryEquiv.neg ℝ : RieszEuclidean.Euclidean d ≃ₗᵢ[ℝ]
      RieszEuclidean.Euclidean d)).map_eq

local instance : (volume : Measure (RieszEuclidean.Euclidean d)).IsNegInvariant :=
  ⟨by rw [Measure.neg_def]; exact volume_neg_map d⟩

/-- Compactly supported continuous complex functions on Euclidean space, with
the multiplication intended to be convolution. -/
abbrev Function := C_c(RieszEuclidean.Euclidean d, ℂ)

local notation "𝒞" => Function d

/-- The actual Lebesgue convolution of two compactly supported continuous
functions. -/
def convolution (f g : 𝒞) : 𝒞 := by
  let h : RieszEuclidean.Euclidean d → ℂ :=
    MeasureTheory.convolution (f : RieszEuclidean.Euclidean d → ℂ)
      (g : RieszEuclidean.Euclidean d → ℂ) (ContinuousLinearMap.mul ℂ ℂ) volume
  have hc : Continuous h := by
    apply HasCompactSupport.continuous_convolution_right (L := ContinuousLinearMap.mul ℂ ℂ)
    · exact g.hasCompactSupport
    · exact (f.continuous.locallyIntegrable)
    · exact g.continuous
  have hs : HasCompactSupport h :=
    HasCompactSupport.convolution (L := ContinuousLinearMap.mul ℂ ℂ)
      f.hasCompactSupport g.hasCompactSupport
  exact ⟨⟨h, hc⟩, hs⟩

@[simp]
theorem coe_convolution (f g : 𝒞) (x : RieszEuclidean.Euclidean d) :
    (convolution d f g : RieszEuclidean.Euclidean d → ℂ) x =
      ∫ y, f y * g (x - y) ∂volume := by
  rfl

private theorem convolution_exists (f g : 𝒞) :
    MeasureTheory.ConvolutionExists (f : RieszEuclidean.Euclidean d → ℂ)
      (g : RieszEuclidean.Euclidean d → ℂ) (ContinuousLinearMap.mul ℂ ℂ) volume := by
  exact f.hasCompactSupport.convolutionExists_left (ContinuousLinearMap.mul ℂ ℂ)
    f.continuous g.continuous.locallyIntegrable

theorem convolution_add_left (f g h : 𝒞) :
    convolution d (f + g) h = convolution d f h + convolution d g h := by
  apply CompactlySupportedContinuousMap.ext
  intro x
  change (MeasureTheory.convolution (f + g) h (ContinuousLinearMap.mul ℂ ℂ) volume) x = _
  exact congrFun ((convolution_exists d f h).add_distrib (convolution_exists d g h)) x

theorem convolution_add_right (f g h : 𝒞) :
    convolution d f (g + h) = convolution d f g + convolution d f h := by
  apply CompactlySupportedContinuousMap.ext
  intro x
  change (MeasureTheory.convolution f (g + h) (ContinuousLinearMap.mul ℂ ℂ) volume) x = _
  exact congrFun ((convolution_exists d f g).distrib_add (convolution_exists d f h)) x

theorem convolution_comm (f g : 𝒞) : convolution d f g = convolution d g f := by
  apply CompactlySupportedContinuousMap.ext
  intro x
  have hflip := MeasureTheory.convolution_flip (L := ContinuousLinearMap.mul ℂ ℂ)
    (μ := volume) (f := (f : RieszEuclidean.Euclidean d → ℂ))
    (g := (g : RieszEuclidean.Euclidean d → ℂ))
  have hmul : (ContinuousLinearMap.mul ℂ ℂ).flip = ContinuousLinearMap.mul ℂ ℂ := by
    ext
    simp [ContinuousLinearMap.mul_apply, mul_comm]
  change (MeasureTheory.convolution f g (ContinuousLinearMap.mul ℂ ℂ) volume) x = _
  rw [hmul] at hflip
  exact (congrFun hflip x).symm

theorem convolution_assoc (f g h : 𝒞) :
    convolution d (convolution d f g) h = convolution d f (convolution d g h) := by
  apply CompactlySupportedContinuousMap.ext
  intro x
  let nf : RieszEuclidean.Euclidean d → ℝ := fun y => ‖f y‖
  let ng : RieszEuclidean.Euclidean d → ℝ := fun y => ‖g y‖
  let nh : RieszEuclidean.Euclidean d → ℝ := fun y => ‖h y‖
  let q : RieszEuclidean.Euclidean d → ℝ :=
    MeasureTheory.convolution ng nh (ContinuousLinearMap.mul ℝ ℝ) volume
  have hqcont : Continuous q := by
    dsimp [q]
    apply HasCompactSupport.continuous_convolution_right
    · exact h.hasCompactSupport.norm
    · exact (g.continuous.norm.locallyIntegrable)
    · exact h.continuous.norm
  have hfg : ∀ᵐ y : RieszEuclidean.Euclidean d ∂volume,
      MeasureTheory.ConvolutionExistsAt f g y (ContinuousLinearMap.mul ℂ ℂ) volume :=
    Filter.Eventually.of_forall fun y => (convolution_exists d f g) y
  have hgnh : ∀ᵐ y : RieszEuclidean.Euclidean d ∂volume,
      MeasureTheory.ConvolutionExistsAt ng nh y (ContinuousLinearMap.mul ℝ ℝ) volume := by
    exact MeasureTheory.Integrable.ae_convolution_exists
      (L := ContinuousLinearMap.mul ℝ ℝ)
      (g.continuous.norm.integrable_of_hasCompactSupport g.hasCompactSupport.norm)
      (h.continuous.norm.integrable_of_hasCompactSupport h.hasCompactSupport.norm)
  have hfgq : MeasureTheory.ConvolutionExistsAt nf q x
      (ContinuousLinearMap.mul ℝ ℝ) volume := by
    apply HasCompactSupport.convolutionExistsAt
    · exact f.hasCompactSupport.norm.mul_right
    · exact f.continuous.norm.locallyIntegrable
    · exact hqcont
  exact MeasureTheory.convolution_assoc (L := ContinuousLinearMap.mul ℂ ℂ)
    (L₂ := ContinuousLinearMap.mul ℂ ℂ) (L₃ := ContinuousLinearMap.mul ℂ ℂ)
    (L₄ := ContinuousLinearMap.mul ℂ ℂ)
    (fun a b c => by simp [ContinuousLinearMap.mul_apply, mul_assoc])
    f.continuous.aestronglyMeasurable g.continuous.aestronglyMeasurable
    h.continuous.aestronglyMeasurable hfg hgnh hfgq

@[simp]
theorem convolution_zero_left (f : 𝒞) : convolution d (0 : 𝒞) f = 0 := by
  apply CompactlySupportedContinuousMap.ext
  intro x
  simp [coe_convolution]

@[simp]
theorem convolution_zero_right (f : 𝒞) : convolution d f (0 : 𝒞) = 0 := by
  apply CompactlySupportedContinuousMap.ext
  intro x
  simp [coe_convolution]

/-- Multiplication by a real linear coordinate, regarded as a complex-valued
function. -/
def coordinateMultiplier (ℓ : RieszEuclidean.Euclidean d →L[ℝ] ℝ) (f : 𝒞) : 𝒞 := by
  let m : RieszEuclidean.Euclidean d → ℂ := fun x => (ℓ x : ℂ) * f x
  have hm : Continuous m := by
    dsimp [m]
    fun_prop
  have hs : HasCompactSupport m := by
    dsimp [m]
    exact f.hasCompactSupport.mul_left
  exact ⟨⟨m, hm⟩, hs⟩

@[simp]
theorem coe_coordinateMultiplier (ℓ : RieszEuclidean.Euclidean d →L[ℝ] ℝ)
    (f : 𝒞) (x : RieszEuclidean.Euclidean d) :
    (coordinateMultiplier d ℓ f : RieszEuclidean.Euclidean d → ℂ) x =
      (ℓ x : ℂ) * f x := rfl

/-- Multiplication by a linear coordinate is a derivation for convolution. -/
theorem coordinateMultiplier_convolution
    (ℓ : RieszEuclidean.Euclidean d →L[ℝ] ℝ) (f g : 𝒞) :
    coordinateMultiplier d ℓ (convolution d f g) =
    convolution d (coordinateMultiplier d ℓ f) g +
        convolution d f (coordinateMultiplier d ℓ g) := by
  apply CompactlySupportedContinuousMap.ext
  intro x
  change (ℓ x : ℂ) * (∫ y, f y * g (x - y) ∂volume) =
    (∫ y, (ℓ y : ℂ) * f y * g (x - y) ∂volume) +
      (∫ y, f y * ((ℓ (x - y) : ℂ) * g (x - y)) ∂volume)
  have hi₂ : Integrable (fun y : RieszEuclidean.Euclidean d =>
      (ℓ y : ℂ) * f y * g (x - y)) := by
    let q : RieszEuclidean.Euclidean d → ℂ := fun y => (ℓ y : ℂ) * g (x - y)
    have hcont : Continuous q :=
      (Complex.continuous_ofReal.comp ℓ.continuous).mul
        (g.continuous.comp (continuous_const.sub continuous_id))
    have heq : (fun y : RieszEuclidean.Euclidean d =>
        (ℓ y : ℂ) * f y * g (x - y)) = fun y => f y * q y := by
      funext y
      dsimp [q]
      ring
    rw [heq]
    exact Continuous.integrable_of_hasCompactSupport (f.continuous.mul hcont)
      (f.hasCompactSupport.mul_right)
  have hi₃ : Integrable (fun y : RieszEuclidean.Euclidean d =>
      f y * ((ℓ (x - y) : ℂ) * g (x - y))) := by
    exact Continuous.integrable_of_hasCompactSupport
      (f.continuous.mul ((Complex.continuous_ofReal.comp ℓ.continuous).comp
        (continuous_const.sub continuous_id) |>.mul
        (g.continuous.comp (continuous_const.sub continuous_id))))
      (f.hasCompactSupport.mul_right)
  rw [← integral_const_mul, ← integral_add hi₂ hi₃]
  apply integral_congr_ae
  filter_upwards with y
  have hℓ : ℓ x = ℓ y + ℓ (x - y) := by simp
  rw [hℓ]
  push_cast
  ring

/-- Functions supported in the closed positive halfspace for a chosen
continuous real coordinate. -/
def halfspace (ℓ : RieszEuclidean.Euclidean d →L[ℝ] ℝ) : Submodule ℂ 𝒞 where
  carrier := {f | ∀ x, ℓ x < 0 → f x = 0}
  zero_mem' := by simp
  add_mem' := by
    intro f g hf hg x hx
    simp [hf x hx, hg x hx]
  smul_mem' := by
    intro c f hf x hx
    simp [hf x hx]

/-- Compactly supported continuous functions whose support lies in a fixed
closed halfspace. -/
abbrev HalfspaceFunctions (ℓ : RieszEuclidean.Euclidean d →L[ℝ] ℝ) :=
  (halfspace d ℓ : Submodule ℂ 𝒞)

namespace HalfspaceFunctions

variable {ℓ : RieszEuclidean.Euclidean d →L[ℝ] ℝ}

/-- Vanishing of a halfspace-supported function below any level. -/
def V (f : HalfspaceFunctions d ℓ) (t : ℝ) : Prop :=
  ∀ x, ℓ x < t → f.val x = 0

theorem V_zero (t : ℝ) : V d (ℓ := ℓ) (0 : HalfspaceFunctions d ℓ) t := by
  intro x hx
  simp

theorem V_base (f : HalfspaceFunctions d ℓ) : V d f 0 := f.property

theorem V_mono {f : HalfspaceFunctions d ℓ} {s t : ℝ}
    (hf : V d f t) (hst : s ≤ t) : V d f s := by
  intro x hx
  exact hf x (hx.trans_le hst)

theorem V_closed {f : HalfspaceFunctions d ℓ} {t : ℝ}
    (hf : ∀ s < t, V d f s) : V d f t := by
  intro x hx
  obtain ⟨s, hxs, hst⟩ := exists_between hx
  exact hf s hst x hxs

theorem V_add {f g : HalfspaceFunctions d ℓ} {t : ℝ}
    (hf : V d f t) (hg : V d g t) : V d (f + g) t := by
  intro x hx
  simp [hf x hx, hg x hx]

theorem V_neg {f : HalfspaceFunctions d ℓ} {t : ℝ}
    (hf : V d f t) : V d (-f) t := by
  intro x hx
  simp [hf x hx]

theorem convolution_mem_halfspace (f g : HalfspaceFunctions d ℓ) :
    convolution d f.val g.val ∈ HalfspaceFunctions d ℓ := by
  intro x hx
  rw [coe_convolution]
  apply integral_eq_zero_of_ae
  filter_upwards with y
  by_cases hy : ℓ y < 0
  · simp [f.property y hy]
  · by_cases hxy : ℓ (x - y) < 0
    · simp [g.property (x - y) hxy]
    · have hsum : ℓ x = ℓ y + ℓ (x - y) := by simp
      linarith [hsum, hx]

instance : Mul (HalfspaceFunctions d ℓ) where
  mul f g := ⟨convolution d f.val g.val, convolution_mem_halfspace d f g⟩

@[simp]
theorem coe_mul (f g : HalfspaceFunctions d ℓ) :
    (f * g).val = convolution d f.val g.val := rfl

instance : NonUnitalNonAssocRing (HalfspaceFunctions d ℓ) where
  left_distrib f g h := by
    apply Subtype.ext
    change convolution d f.val (g.val + h.val) =
      convolution d f.val g.val + convolution d f.val h.val
    exact convolution_add_right d f.val g.val h.val
  right_distrib f g h := by
    apply Subtype.ext
    change convolution d (f.val + g.val) h.val =
      convolution d f.val h.val + convolution d g.val h.val
    exact convolution_add_left d f.val g.val h.val
  zero_mul f := by
    apply Subtype.ext
    change convolution d (0 : 𝒞) f.val = 0
    exact convolution_zero_left d f.val
  mul_zero f := by
    apply Subtype.ext
    change convolution d f.val (0 : 𝒞) = 0
    exact convolution_zero_right d f.val

instance : NonUnitalRing (HalfspaceFunctions d ℓ) where
  toNonUnitalNonAssocRing := inferInstance
  mul_assoc f g h := by
    apply Subtype.ext
    change convolution d (convolution d f.val g.val) h.val =
      convolution d f.val (convolution d g.val h.val)
    exact convolution_assoc d f.val g.val h.val

instance : NonUnitalCommRing (HalfspaceFunctions d ℓ) :=
  NonUnitalCommRing.mk (fun f g => by
    apply Subtype.ext
    change convolution d f.val g.val = convolution d g.val f.val
    exact convolution_comm d f.val g.val)

/-- Convolution retains a lower support bound equal to the sum of the two
factor bounds. -/
theorem V_convolution {f g : HalfspaceFunctions d ℓ} {s t : ℝ}
    (hf : V d f s) (hg : V d g t) :
    V d (f * g) (s + t) := by
  intro x hx
  rw [coe_mul, coe_convolution]
  apply integral_eq_zero_of_ae
  filter_upwards with y
  by_cases hys : ℓ y < s
  · simp [hf y hys]
  · by_cases hyt : ℓ (x - y) < t
    · simp [hg (x - y) hyt]
    · have hxy : ℓ x = ℓ y + ℓ (x - y) := by simp
      linarith [hxy, hx]

/-- The coordinate multiplier, as an endomorphism of the halfspace function
space. -/
def M (f : HalfspaceFunctions d ℓ) : HalfspaceFunctions d ℓ :=
  ⟨coordinateMultiplier d ℓ f.val, by
    intro x hx
    simp [f.property x hx]⟩

@[simp]
theorem coe_M (f : HalfspaceFunctions d ℓ) :
    (M d f : 𝒞) = coordinateMultiplier d ℓ f.val := rfl

/-- The coordinate multiplier is a derivation for the halfspace convolution
product. -/
theorem M_mul (f g : HalfspaceFunctions d ℓ) :
    M d (f * g) = M d f * g + f * M d g := by
  apply Subtype.ext
  change coordinateMultiplier d ℓ (convolution d f.val g.val) =
    convolution d (coordinateMultiplier d ℓ f.val) g.val +
      convolution d f.val (coordinateMultiplier d ℓ g.val)
  exact coordinateMultiplier_convolution d ℓ f.val g.val

theorem V_coordinateMultiplier {f : HalfspaceFunctions d ℓ} {t : ℝ}
    (hf : V d f t) : V d (M d f) t := by
  intro x hx
  simp [M, coordinateMultiplier, hf x hx]

/-- The coordinate multiplier by any real linear functional. The multiplier
coordinate is independent of the halfspace defining the function space. -/
def Mcoordinate (m : RieszEuclidean.Euclidean d →L[ℝ] ℝ)
    (f : HalfspaceFunctions d ℓ) : HalfspaceFunctions d ℓ :=
  ⟨coordinateMultiplier d m f.val, by
    intro x hx
    simp [f.property x hx]⟩

@[simp]
theorem coe_Mcoordinate (m : RieszEuclidean.Euclidean d →L[ℝ] ℝ)
    (f : HalfspaceFunctions d ℓ) :
    (Mcoordinate d m f : 𝒞) = coordinateMultiplier d m f.val := rfl

theorem Mcoordinate_mul (m : RieszEuclidean.Euclidean d →L[ℝ] ℝ)
    (f g : HalfspaceFunctions d ℓ) :
    Mcoordinate d m (f * g) = Mcoordinate d m f * g + f * Mcoordinate d m g := by
  apply Subtype.ext
  change coordinateMultiplier d m (convolution d f.val g.val) =
    convolution d (coordinateMultiplier d m f.val) g.val +
      convolution d f.val (coordinateMultiplier d m g.val)
  exact coordinateMultiplier_convolution d m f.val g.val

theorem V_Mcoordinate {m : RieszEuclidean.Euclidean d →L[ℝ] ℝ}
    {f : HalfspaceFunctions d ℓ} {t : ℝ} (hf : V d f t) :
    V d (Mcoordinate d m f) t := by
  intro x hx
  simp [Mcoordinate, coordinateMultiplier, hf x hx]

/-- The concrete bootstrap data for the halfspace algebra. The self-convolution
half lemma is the sole analytic input left to the algebraic bootstrap. -/
def bootstrapData (ℓ m : RieszEuclidean.Euclidean d →L[ℝ] ℝ)
    (half : ∀ {f : HalfspaceFunctions d ℓ} {t : ℝ}, 0 ≤ t →
      V d (f * f) (2 * t) → V d f t) :
    RieszEuclidean.TitchmarshBootstrap.Data (HalfspaceFunctions d ℓ) where
  M := Mcoordinate d m
  V := V d
  V_zero := V_base d
  V_mono := fun hf hst => V_mono d hf hst
  V_closed := fun hf => V_closed d hf
  V_add := fun hf hg => V_add d hf hg
  V_neg := fun hf => V_neg d hf
  V_mul := fun hf hg => V_convolution d hf hg
  V_M := fun hf => V_Mcoordinate d hf
  M_mul := Mcoordinate_mul d m
  half := half

/-- Bootstrap data using the proved self-convolution halfspace theorem. -/
def provedBootstrapData (ℓ m : RieszEuclidean.Euclidean d →L[ℝ] ℝ) :
    RieszEuclidean.TitchmarshBootstrap.Data (HalfspaceFunctions d ℓ) :=
  bootstrapData d ℓ m (by
    intro f t ht hsq
    exact RieszEuclidean.CompleteMinimal.self_convolution_halfspace_linear
      f.val.continuous f.val.hasCompactSupport ℓ t (by
        intro x hx
        have hzero := hsq x hx
        change (MeasureTheory.convolution f.val f.val
          (ContinuousLinearMap.mul ℂ ℂ) volume) x = 0
        simpa [coe_mul, coe_convolution, convolution] using hzero))

end HalfspaceFunctions

end RieszEuclidean.TitchmarshFunctionAlgebra
