import RieszEuclidean.CompleteMinimalAnalyticAssembly
import RieszEuclidean.CompleteMinimalPolynomialGrowth
import RieszEuclidean.CompleteMinimalPolynomialDimension
import Mathlib.LinearAlgebra.Dimension.Finrank

noncomputable section
open MeasureTheory Set

namespace RieszEuclidean.CompleteMinimal

/-- A continuous Fourier multiplier nonzero at the origin embeds every bounded
polynomial space injectively into actual functions. -/
theorem polynomialFourierMap_injective {d : ℕ} (degree : ℕ)
    (M : ComplexEuclidean d → ℂ) (hM : Continuous M) (hM0 : M 0 ≠ 0) :
    Function.Injective (polynomialFourierMap degree M) := by
  have hemb : Continuous (realToComplex : Euclidean d → ComplexEuclidean d) :=
    (PiLp.continuous_equiv_symm 2 _).comp (continuous_pi fun j => by
      change Continuous (fun x : Euclidean d => (x j : ℂ)); fun_prop)
  have hopen : IsOpen {x : Euclidean d | M (realToComplex x) ≠ 0} :=
    isOpen_ne.preimage (hM.comp hemb)
  have hzero : (0 : Euclidean d) ∈ {x | M (realToComplex x) ≠ 0} := by
    simpa [realToComplex] using hM0
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hopen 0 hzero
  intro p q hpq
  have hpoly : p.val - q.val = 0 := by
    apply polynomial_eq_zero_of_real_ball _ r hr
    intro x hx
    let v : Euclidean d := (WithLp.equiv 2 _).symm x
    have hnormsq : ‖v‖ ^ 2 = ∑ i, x i ^ 2 := by
      simp [PiLp.norm_sq_eq_of_L2, v, Real.norm_eq_abs]
    have hv : v ∈ Metric.ball 0 r := by
      rw [Metric.mem_ball, dist_zero_right]
      exact (sq_lt_sq₀ (norm_nonneg v) hr.le).mp (hnormsq ▸ hx)
    have hne := hball hv
    have heq := congrFun hpq (realToComplex v)
    have heval : polynomialEvaluation v p.val = polynomialEvaluation v q.val := by
      exact mul_left_cancel₀ hne heq
    simpa [polynomialEvaluation_apply, v, realToComplex_apply] using
      sub_eq_zero.mpr heval
  exact Subtype.ext (sub_eq_zero.mp hpoly)

namespace SphereAnalyticInputs

variable {d : ℕ} {Ω : Set (Euclidean d)} {hΩ : MeasurableSet Ω}
    {hfinite : volume Ω ≠ ⊤} {radius : ℕ → ℝ} {core : Set (Euclidean d)}

/-- Exact tail-annihilator membership for the actual domain L² interpolation space. -/
theorem mem_spaces_iff_tail_orthogonal
    (I : SphereAnalyticInputs Ω hΩ hfinite radius core) (hbounded : Bornology.IsBounded Ω)
    (N : ℕ) (f : DomainL2 Ω) :
    f ∈ I.spaces hbounded N ↔
      ∀ x ∈ laterSpheres radius N, inner (𝕜 := ℂ) f (exponentialL2 Ω hfinite x) = 0 := by
  constructor
  · rintro ⟨p, hp⟩ x ⟨j, hj, hx⟩
    have hF : domainEntireFourier Ω hΩ f (realToComplex x) = 0 := by
      change (domainEntireFourierLinear Ω hΩ hbounded) f (realToComplex x) = 0
      rw [← congrFun hp (realToComplex x)]
      change I.multiplier N (realToComplex x) * _ = 0
      rw [I.zero N j hj x hx, zero_mul]
    apply (inner_eq_zero_symm (𝕜 := ℂ)).mpr
    exact (domainEntireFourier_real_inner hΩ hfinite f x) ▸ hF
  · intro hf
    obtain ⟨p, hp⟩ := I.tail N f hf
    exact ⟨p, funext (fun z => (hp z).symm)⟩

/-- The actual finite interpolation spaces are nested. -/
theorem spaces_mono (I : SphereAnalyticInputs Ω hΩ hfinite radius core)
    (hbounded : Bornology.IsBounded Ω) : Monotone (I.spaces hbounded) := by
  intro N K hNK f hf
  apply (I.mem_spaces_iff_tail_orthogonal hbounded K f).mpr
  intro x hx
  apply (I.mem_spaces_iff_tail_orthogonal hbounded N f).mp hf x
  obtain ⟨j, hj, hxnorm⟩ := hx
  exact ⟨j, lt_of_le_of_lt hNK hj, hxnorm⟩

/-- The actual entire Fourier map on a stage space, with its prescribed range. -/
def spaceFourierMap (I : SphereAnalyticInputs Ω hΩ hfinite radius core)
    (hbounded : Bornology.IsBounded Ω) (N : ℕ) :
    I.spaces hbounded N →ₗ[ℂ] LinearMap.range (polynomialFourierMap (2 * N) (I.multiplier N)) :=
  ((domainEntireFourierLinear Ω hΩ hbounded).comp (I.spaces hbounded N).subtype).codRestrict
    _ (fun f => f.property)

/-- Synthesis and actual Fourier injectivity make the stage Fourier map bijective. -/
theorem spaceFourierMap_bijective (I : SphereAnalyticInputs Ω hΩ hfinite radius core)
    (hbounded : Bornology.IsBounded Ω) (N : ℕ) :
    Function.Bijective (I.spaceFourierMap hbounded N) := by
  constructor
  · intro f g hfg
    apply Subtype.ext
    apply domainEntireFourier_injective hΩ hbounded
    exact congrArg Subtype.val hfg
  · rintro ⟨F, p, hp⟩
    obtain ⟨f, _hs, hf⟩ := I.synthesize N p
    have hmem : f ∈ I.spaces hbounded N := ⟨p, hf.symm⟩
    refine ⟨⟨f, hmem⟩, Subtype.ext ?_⟩
    exact hf.trans hp

/-- The source polynomial parametrization is a genuine linear equivalence with
actual domain L² vectors, whenever the multiplier is continuous and nonzero at zero. -/
def polynomialEquivSpace (I : SphereAnalyticInputs Ω hΩ hfinite radius core)
    (hbounded : Bornology.IsBounded Ω) (N : ℕ)
    (hM : Continuous (I.multiplier N)) (hM0 : I.multiplier N 0 ≠ 0) :
    MvPolynomial.restrictTotalDegree (Fin d) ℂ (2 * N) ≃ₗ[ℂ] I.spaces hbounded N :=
  (LinearEquiv.ofInjective (polynomialFourierMap (2 * N) (I.multiplier N))
    (polynomialFourierMap_injective (2 * N) (I.multiplier N) hM hM0)).trans
    (LinearEquiv.ofBijective (I.spaceFourierMap hbounded N)
      (I.spaceFourierMap_bijective hbounded N)).symm

/-- The linear equivalence has the actual multiplier-polynomial Fourier formula. -/
theorem polynomialEquivSpace_fourier
    (I : SphereAnalyticInputs Ω hΩ hfinite radius core)
    (hbounded : Bornology.IsBounded Ω) (N : ℕ)
    (hM : Continuous (I.multiplier N)) (hM0 : I.multiplier N 0 ≠ 0)
    (p : MvPolynomial.restrictTotalDegree (Fin d) ℂ (2 * N)) :
    domainEntireFourier Ω hΩ (I.polynomialEquivSpace hbounded N hM hM0 p).val =
      polynomialFourierMap (2 * N) (I.multiplier N) p := by
  exact congrArg Subtype.val
    ((LinearEquiv.ofBijective (I.spaceFourierMap hbounded N)
      (I.spaceFourierMap_bijective hbounded N)).apply_symm_apply
        (LinearEquiv.ofInjective (polynomialFourierMap (2 * N) (I.multiplier N))
          (polynomialFourierMap_injective (2 * N) (I.multiplier N) hM hM0) p))

end SphereAnalyticInputs

/-- The actual normalized interpolation subspace at level `N`. -/
def normalizedInterpolationSpace (n : ℕ)
    (Ω : Set (Euclidean (n + 1))) (hΩ : MeasurableSet Ω)
    (hbounded : Bornology.IsBounded Ω) (N : ℕ) : Submodule ℂ (DomainL2 Ω) :=
  polynomialFourierSpace Ω hΩ hbounded (2 * N) (sphereKernelMultiplier n (ballZeroRadius n) N)

section Normalized

variable (n : ℕ) (hTL : TitchmarshLions (n + 1))
    (Ω : Set (Euclidean (n + 1))) (hΩ : MeasurableSet Ω)
    (hbounded : Bornology.IsBounded Ω) (hconvex : Convex ℝ Ω)
    (hJ : IsJohnEllipsoid (closure Ω) (Metric.closedBall (0 : Euclidean (n + 1)) 1))
    (hB : Metric.ball (0 : Euclidean (n + 1)) 1 ⊆ Ω)

include hTL hconvex hJ hB

/-- The actual normalized interpolation spaces are nested. -/
theorem normalizedInterpolationSpace_mono :
    Monotone (normalizedInterpolationSpace n Ω hΩ hbounded) :=
  (sphereAnalyticInputs n hTL Ω hΩ hbounded hbounded.measure_lt_top.ne hconvex hJ hB).spaces_mono
    hbounded

/-- Every actual interpolation-space vector is supported in the closed unit ball. -/
theorem normalizedInterpolationSpace_supported (N : ℕ) (f : DomainL2 Ω)
    (hf : f ∈ normalizedInterpolationSpace n Ω hΩ hbounded N) :
    SupportedOn Ω f (Metric.closedBall 0 1) :=
  (sphereAnalyticInputs n hTL Ω hΩ hbounded hbounded.measure_lt_top.ne hconvex hJ hB).supported
    hbounded hf

/-- Exact membership is orthogonality to all frequency spheres past the cutoff. -/
theorem normalizedInterpolationSpace_iff_tail_orthogonal (N : ℕ) (f : DomainL2 Ω) :
    f ∈ normalizedInterpolationSpace n Ω hΩ hbounded N ↔
      ∀ x ∈ laterSpheres (ballZeroRadius n) N,
        inner (𝕜 := ℂ) f (exponentialL2 Ω hbounded.measure_lt_top.ne x) = 0 :=
  (sphereAnalyticInputs n hTL Ω hΩ hbounded hbounded.measure_lt_top.ne hconvex hJ hB).mem_spaces_iff_tail_orthogonal
    hbounded N f

/-- The actual normalized polynomial parametrization is a linear equivalence. -/
def normalizedPolynomialEquivSpace (N : ℕ) :
    MvPolynomial.restrictTotalDegree (Fin (n + 1)) ℂ (2 * N) ≃ₗ[ℂ]
      normalizedInterpolationSpace n Ω hΩ hbounded N := by
  let I := sphereAnalyticInputs n hTL Ω hΩ hbounded hbounded.measure_lt_top.ne hconvex hJ hB
  apply I.polynomialEquivSpace hbounded N
  · change Continuous (sphereKernelMultiplier n (ballZeroRadius n) N)
    exact (sphereKernelMultiplier_differentiable n (ballZeroRadius n) N
      (fun _ hj _ => ballZeroRadius_resolvent_normalization n hj)).continuous
  · have hr : 0 ≤ ballZeroRadius n N := by
      simpa only [ballZeroRadius_zero] using (ballZeroRadius_strictMono n).monotone (Nat.zero_le N)
    have h := I.nonzero N (0 : Euclidean (n + 1)) (by simpa using hr)
    simpa [realToComplex] using h

include hTL Ω hΩ hbounded hconvex hJ hB in
/-- The actual Fourier multiplier is nonzero throughout all radii up to its cutoff. -/
theorem normalizedInterpolationMultiplier_nonzero (N : ℕ) (x : Euclidean (n + 1))
    (hx : ‖x‖ ≤ ballZeroRadius n N) :
    sphereKernelMultiplier n (ballZeroRadius n) N (realToComplex x) ≠ 0 :=
  (sphereAnalyticInputs n hTL Ω hΩ hbounded hbounded.measure_lt_top.ne hconvex hJ hB).nonzero N x hx

include hTL Ω hΩ hbounded hconvex hJ hB in
/-- The actual Fourier multiplier vanishes on every later frequency sphere. -/
theorem normalizedInterpolationMultiplier_zero (N j : ℕ) (hj : N < j)
    (x : Euclidean (n + 1)) (hx : ‖x‖ = ballZeroRadius n j) :
    sphereKernelMultiplier n (ballZeroRadius n) N (realToComplex x) = 0 :=
  (sphereAnalyticInputs n hTL Ω hΩ hbounded hbounded.measure_lt_top.ne hconvex hJ hB).zero N j hj x hx

/-- The exact finite dimension in the source membership lemma. -/
theorem normalizedInterpolationSpace_finrank (N : ℕ) :
    Module.finrank ℂ (normalizedInterpolationSpace n Ω hΩ hbounded N) =
      Nat.choose (2 * N + (n + 1)) (n + 1) := by
  rw [← (normalizedPolynomialEquivSpace n hTL Ω hΩ hbounded hconvex hJ hB N).finrank_eq]
  exact finrank_restrictTotalDegree (n + 1) (2 * N)

/-- The complete source interpolation-space clauses: nesting, exact dimension,
unit-ball support, and the precise tail-annihilator characterization, for the
actual normalized spaces with no analytic package premises. -/
theorem normalized_interpolation_spaces :
    Monotone (normalizedInterpolationSpace n Ω hΩ hbounded) ∧
    ∀ N : ℕ,
      Module.finrank ℂ (normalizedInterpolationSpace n Ω hΩ hbounded N) =
        Nat.choose (2 * N + (n + 1)) (n + 1) ∧
      (∀ f : DomainL2 Ω,
        f ∈ normalizedInterpolationSpace n Ω hΩ hbounded N →
          SupportedOn Ω f (Metric.closedBall 0 1)) ∧
      (∀ f : DomainL2 Ω,
        f ∈ normalizedInterpolationSpace n Ω hΩ hbounded N ↔
          ∀ x ∈ laterSpheres (ballZeroRadius n) N,
            inner (𝕜 := ℂ) f (exponentialL2 Ω hbounded.measure_lt_top.ne x) = 0) :=
  ⟨normalizedInterpolationSpace_mono n hTL Ω hΩ hbounded hconvex hJ hB,
    fun N => ⟨normalizedInterpolationSpace_finrank n hTL Ω hΩ hbounded hconvex hJ hB N,
      normalizedInterpolationSpace_supported n hTL Ω hΩ hbounded hconvex hJ hB N,
      normalizedInterpolationSpace_iff_tail_orthogonal n hTL Ω hΩ hbounded hconvex hJ hB N⟩⟩

end Normalized

end RieszEuclidean.CompleteMinimal
