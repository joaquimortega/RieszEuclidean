import RieszEuclidean.CompleteMinimalAvailable
import RieszEuclidean.CompleteMinimalExtension
import RieszEuclidean.CompleteMinimalSelection
import Mathlib.Analysis.NormedSpace.Real
import Mathlib.MeasureTheory.Measure.SeparableMeasure

noncomputable section

open MeasureTheory
open Classical
open Filter Topology

namespace RieszEuclidean.CompleteMinimal

/-- The origin sphere and the positive-radius frequency spheres. -/
def sphereFrequencies {d : ℕ} (radius : ℕ → ℝ) : Set (Euclidean d) :=
  {x | ∃ j, ‖x‖ = radius j}

/-- Frequency spheres whose indices lie strictly beyond a given cutoff. -/
def laterSpheres {d : ℕ} (radius : ℕ → ℝ) (n : ℕ) : Set (Euclidean d) :=
  {x | ∃ j, n < j ∧ ‖x‖ = radius j}

/-- The frequency spheres with indices between two cutoffs. -/
def sphereInterval {d : ℕ} (radius : ℕ → ℝ) (n N : ℕ) : Set (Euclidean d) :=
  {x | ∃ j, n < j ∧ j ≤ N ∧ ‖x‖ = radius j}

/-- The unique radius index of a frequency on one of the prescribed spheres. -/
def sphereLevel {d : ℕ} (radius : ℕ → ℝ) (x : Euclidean d) : ℕ :=
  if h : ∃ j, ‖x‖ = radius j then Classical.choose h else 0

/-- A point on a strictly indexed sphere has that sphere's level. -/
theorem sphereLevel_of_norm {d : ℕ} {radius : ℕ → ℝ} (hstrict : StrictMono radius)
    {x : Euclidean d} {j : ℕ} (hx : ‖x‖ = radius j) : sphereLevel radius x = j := by
  unfold sphereLevel
  rw [dif_pos ⟨j, hx⟩]
  exact hstrict.injective ((Classical.choose_spec (show ∃ k, ‖x‖ = radius k from ⟨j, hx⟩)).symm.trans hx)

/-- Recover the norm from the sphere level of a frequency. -/
theorem sphereLevel_norm {d : ℕ} {radius : ℕ → ℝ} {x : Euclidean d}
    (hx : x ∈ sphereFrequencies radius) : ‖x‖ = radius (sphereLevel radius x) := by
  change ∃ j, ‖x‖ = radius j at hx
  unfold sphereLevel
  rw [dif_pos hx]
  exact Classical.choose_spec hx

/-- Successive sphere divisions reduce a joint annihilator to the old interpolation space. -/
theorem polynomial_eq_zero_of_interpolation_and_sphereInterval {d n k : ℕ}
    (hd : 1 ≤ d) (radius : ℕ → ℝ) (hpositive : ∀ j, 0 < j → 0 < radius j)
    (hstrict : StrictMono radius) (A : Finset (Euclidean d))
    (hA : ∀ x ∈ A, ‖x‖ ≤ radius n)
    (hsampling : Function.Injective (boundedSampling (2 * n) (fun x : ↥A => x.val)))
    (p : MvPolynomial.restrictTotalDegree (Fin d) ℂ (2 * (n + k)))
    (hzero : ∀ x ∈ (A : Set (Euclidean d)) ∪ sphereInterval radius n (n + k),
      polynomialEvaluation x p.val = 0) : p = 0 := by
  induction k with
  | zero =>
    apply hsampling
    ext x
    simpa using hzero x.val (Or.inl x.property)
  | succ k ih =>
    obtain ⟨q, hpq, hqdegree⟩ := exists_spherePolynomial_quotient_of_norm hd
      (radius (n + (k + 1))) (hpositive _ (by omega)) p.val
      (fun x hx => hzero x (Or.inr ⟨n + (k + 1), by omega, le_rfl, hx⟩))
    have hqbound : q.totalDegree ≤ 2 * (n + k) := by
      have hpdegree := (MvPolynomial.mem_restrictTotalDegree _ _ _).mp p.property
      omega
    let q' : MvPolynomial.restrictTotalDegree (Fin d) ℂ (2 * (n + k)) :=
      ⟨q, (MvPolynomial.mem_restrictTotalDegree _ _ _).mpr hqbound⟩
    have hqzero : q' = 0 := by
      apply ih q'
      intro x hx
      have hnorm : ‖x‖ < radius (n + (k + 1)) := by
        rcases hx with hx | ⟨j, _hj, hj, hx⟩
        · exact (hA x hx).trans_lt (hstrict (by omega))
        · rw [hx]
          exact hstrict (by omega)
      have hpzero : polynomialEvaluation x p.val = 0 := by
        apply hzero x
        rcases hx with hx | ⟨j, hjn, hjN, hx⟩
        · exact Or.inl hx
        · exact Or.inr ⟨j, hjn, by omega, hx⟩
      rw [hpq, polynomialEvaluation_apply, map_mul] at hpzero
      have hfactor : polynomialEvaluation x (spherePolynomial d (radius (n + (k + 1)))) ≠ 0 := by
        intro he
        exact hnorm.ne ((polynomialEvaluation_spherePolynomial_eq_zero_iff x _
          (hpositive _ (by omega)).le).mp he)
      exact (mul_eq_zero.mp hpzero).resolve_left hfactor
    apply Subtype.ext
    have hq : q = 0 := congrArg Subtype.val hqzero
    simpa [hq] using hpq

/-- Finite polynomial interpolation data; the sampling invariant is retained
through every selection stage. -/
structure PolynomialSphereStage (d : ℕ) (radius : ℕ → ℝ) where
  /-- The finite interpolation set retained at this stage. -/
  points : Finset (Euclidean d)
  /-- The greatest sphere index included at this stage. -/
  cutoff : ℕ
  spheres : ∀ x ∈ points, x ∈ sphereFrequencies radius
  bounded : ∀ x ∈ points, sphereLevel radius x ≤ cutoff
  sampling : Function.Bijective (boundedSampling (2 * cutoff) (fun x : ↥points => x.val))

/-- Enlarge a polynomial stage while retaining any finite set of prescribed later
points. The additional basis points lie only on later spheres. -/
theorem extend_polynomialSphereStage {d : ℕ} (hd : 1 ≤ d)
    (radius : ℕ → ℝ) (hpositive : ∀ j, 0 < j → 0 < radius j) (hstrict : StrictMono radius)
    (A : PolynomialSphereStage d radius) (B : Finset (Euclidean d))
    (hB : (B : Set (Euclidean d)) ⊆ (A.points : Set (Euclidean d)) ∪ laterSpheres radius A.cutoff) :
    ∃ C : PolynomialSphereStage d radius, A.points ∪ B ⊆ C.points ∧
      A.cutoff < C.cutoff ∧
      ∀ x ∈ C.points, x ∉ A.points → A.cutoff < sphereLevel radius x := by
  classical
  let prescribed := A.points ∪ B
  let N := max (max A.cutoff (B.sup (sphereLevel radius))) prescribed.card + 1
  have hnN : A.cutoff < N := by
    dsimp [N]
    omega
  have hBN : ∀ x ∈ B, sphereLevel radius x ≤ N := by
    intro x hx
    have hle := Finset.le_sup (f := sphereLevel radius) hx
    dsimp [N]
    omega
  have hprescribed : (prescribed : Set (Euclidean d)) ⊆
      (A.points : Set (Euclidean d)) ∪ sphereInterval radius A.cutoff N := by
    intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · exact Or.inl hx
    · have hxB := hx
      rcases hB hx with hx | ⟨j, hj, hx⟩
      · exact Or.inl hx
      · exact Or.inr ⟨j, hj, by simpa [sphereLevel_of_norm hstrict hx] using hBN x hxB, hx⟩
  have hind : LinearIndependent ℂ
      (fun x : ↥prescribed => boundedPolynomialEvaluation (2 * N) x.val) := by
    apply boundedPolynomialEvaluation_finset_linearIndependent
    dsimp [N]
    omega
  have hspan : Submodule.span ℂ (boundedPolynomialEvaluation (2 * N) ''
      ((prescribed : Set (Euclidean d)) ∪ sphereInterval radius A.cutoff N)) = ⊤ := by
    apply boundedPolynomialEvaluation_span_eq_top
    intro p hp
    have hnorm : ∀ x ∈ A.points, ‖x‖ ≤ radius A.cutoff := by
      intro x hx
      rw [sphereLevel_norm (A.spheres x hx)]
      exact hstrict.monotone (A.bounded x hx)
    have hN : N = A.cutoff + (N - A.cutoff) := by omega
    let p' : MvPolynomial.restrictTotalDegree (Fin d) ℂ
        (2 * (A.cutoff + (N - A.cutoff))) :=
      ⟨p.val, by rw [← hN]; exact p.property⟩
    have hz : p' = 0 := by
      apply polynomial_eq_zero_of_interpolation_and_sphereInterval hd radius hpositive hstrict
        A.points hnorm A.sampling.1 (k := N - A.cutoff) p'
      intro x hx
      apply hp x
      rcases hx with hx | hx
      · exact Or.inl (Finset.mem_union_left B hx)
      · exact Or.inr (by simpa [← hN] using hx)
    apply Subtype.ext
    have hzval : p'.val = 0 := congrArg Subtype.val hz
    exact hzval
  obtain ⟨t, hpt, ht, _hcard, hsampling⟩ := exists_bounded_interpolation_extension_with_card
    prescribed (sphereInterval radius A.cutoff N) hind hspan
  have ht' : (t : Set (Euclidean d)) ⊆
      (A.points : Set (Euclidean d)) ∪ sphereInterval radius A.cutoff N :=
    ht.trans (Set.union_subset hprescribed Set.subset_union_right)
  have htsphere : ∀ x ∈ t, x ∈ sphereFrequencies radius := by
    intro x hx
    rcases ht' hx with hx | ⟨j, _hj, _hjN, hx⟩
    · exact A.spheres x hx
    · exact ⟨j, hx⟩
  have htlevel : ∀ x ∈ t, sphereLevel radius x ≤ N := by
    intro x hx
    rcases ht' hx with hx | ⟨j, _hj, hjN, hx⟩
    · exact (A.bounded x hx).trans hnN.le
    · simpa [sphereLevel_of_norm hstrict hx] using hjN
  refine ⟨⟨t, N, htsphere, htlevel, hsampling⟩, hpt, hnN, ?_⟩
  intro x hx hnot
  obtain ⟨j, hj, _hjN, hxnorm⟩ := (ht' hx).resolve_left hnot
  simpa [sphereLevel_of_norm hstrict hxnorm] using hj

/-- Multiplication by a fixed Fourier factor, on actual bounded-degree polynomials. -/
def polynomialFourierMap {d : ℕ} (degree : ℕ) (multiplier : ComplexEuclidean d → ℂ) :
    MvPolynomial.restrictTotalDegree (Fin d) ℂ degree →ₗ[ℂ] (ComplexEuclidean d → ℂ) where
  toFun p := fun z => multiplier z * MvPolynomial.eval (fun i => z i) p.val
  map_add' p q := by ext z; simp [mul_add]
  map_smul' c p := by ext z; simp [mul_left_comm, mul_comm]

/-- The actual domain L² subspace whose Fourier transforms have the prescribed
multiplier-polynomial form. -/
def polynomialFourierSpace {d : ℕ} (Ω : Set (Euclidean d)) (hΩ : MeasurableSet Ω)
    (hbounded : Bornology.IsBounded Ω) (degree : ℕ) (multiplier : ComplexEuclidean d → ℂ) :
    Submodule ℂ (DomainL2 Ω) :=
  (LinearMap.range (polynomialFourierMap degree multiplier)).comap
    (domainEntireFourierLinear Ω hΩ hbounded)

/-- The remaining analytic inputs are stated on actual Fourier transforms and
physical L² support. The geometric finite-extension and selection conclusions
are not assumed. -/
structure SphereAnalyticInputs {d : ℕ} (Ω : Set (Euclidean d)) (hΩ : MeasurableSet Ω)
    (hfinite : volume Ω ≠ ⊤) (radius : ℕ → ℝ) (core : Set (Euclidean d)) where
  /-- The analytic multiplier defining the polynomial Fourier space at each level. -/
  multiplier : ℕ → ComplexEuclidean d → ℂ
  synthesize : ∀ N (p : MvPolynomial.restrictTotalDegree (Fin d) ℂ (2 * N)),
    ∃ f : DomainL2 Ω, SupportedOn Ω f core ∧
      domainEntireFourier Ω hΩ f = polynomialFourierMap (2 * N) (multiplier N) p
  tail : ∀ N, TailPolynomialRepresentation Ω hΩ hfinite (laterSpheres radius N)
    (2 * N) (multiplier N)
  nonzero : ∀ N x, ‖x‖ ≤ radius N → multiplier N (realToComplex x) ≠ 0
  zero : ∀ N j, N < j → ∀ x : Euclidean d, ‖x‖ = radius j →
    multiplier N (realToComplex x) = 0

namespace SphereAnalyticInputs

variable {d : ℕ} {Ω : Set (Euclidean d)} {hΩ : MeasurableSet Ω}
    {hfinite : volume Ω ≠ ⊤} {radius : ℕ → ℝ} {core : Set (Euclidean d)}

/-- The stage's actual domain L² Fourier-polynomial subspace. -/
def spaces (I : SphereAnalyticInputs Ω hΩ hfinite radius core)
    (hbounded : Bornology.IsBounded Ω) (N : ℕ) : Submodule ℂ (DomainL2 Ω) :=
  polynomialFourierSpace Ω hΩ hbounded (2 * N) (I.multiplier N)

/-- Fourier injectivity transfers synthesis support to every vector in the stage space. -/
theorem supported (I : SphereAnalyticInputs Ω hΩ hfinite radius core)
    (hbounded : Bornology.IsBounded Ω) {N : ℕ} {f : DomainL2 Ω}
    (hf : f ∈ I.spaces hbounded N) : SupportedOn Ω f core := by
  obtain ⟨p, hp⟩ := hf
  obtain ⟨g, hg, hgp⟩ := I.synthesize N p
  have hfg : f = g := domainEntireFourier_injective hΩ hbounded (hp.symm.trans hgp.symm)
  exact hfg ▸ hg

/-- Every vector in a stage space is orthogonal to every later frequency sphere. -/
theorem vanish (I : SphereAnalyticInputs Ω hΩ hfinite radius core)
    (hbounded : Bornology.IsBounded Ω) {N : ℕ} {f : DomainL2 Ω}
    (hf : f ∈ I.spaces hbounded N) {x : Euclidean d} (hx : N < sphereLevel radius x) :
    inner (𝕜 := ℂ) f (exponentialL2 Ω hfinite x) = 0 := by
  obtain ⟨p, hp⟩ := hf
  have hxsphere : x ∈ sphereFrequencies radius := by
    by_contra hn
    change ¬ ∃ j, ‖x‖ = radius j at hn
    have hlevel : sphereLevel radius x = 0 := by
      unfold sphereLevel
      rw [dif_neg hn]
    omega
  have hft : domainEntireFourier Ω hΩ f (realToComplex x) = 0 := by
    change polynomialFourierMap (2 * N) (I.multiplier N) p =
      domainEntireFourier Ω hΩ f at hp
    rw [← congrFun hp (realToComplex x)]
    change I.multiplier N (realToComplex x) * _ = 0
    rw [I.zero N (sphereLevel radius x) hx x (sphereLevel_norm hxsphere), zero_mul]
  apply (inner_eq_zero_symm (𝕜 := ℂ)).mpr
  exact (domainEntireFourier_real_inner hΩ hfinite f x) ▸ hft

/-- A polynomial interpolation stage supplies genuine supported exponential
interpolants, through the analytic synthesis input. -/
def toFiniteStage (I : SphereAnalyticInputs Ω hΩ hfinite radius core)
    (hbounded : Bornology.IsBounded Ω) (hstrict : StrictMono radius)
    (A : PolynomialSphereStage d radius) :
    FiniteStage (exponentialL2 Ω hfinite) (sphereLevel radius) (I.spaces hbounded) where
  points := A.points
  cutoff := A.cutoff
  bounded := A.bounded
  interpolate := by
    intro x hx
    let values : ↥A.points → ℂ := fun y =>
      (if x = y.val then 1 else 0) / I.multiplier A.cutoff (realToComplex y.val)
    obtain ⟨p, hp⟩ := A.sampling.2 values
    obtain ⟨f, _hsupport, hfp⟩ := I.synthesize A.cutoff p
    refine ⟨f, ⟨p, hfp.symm⟩, ?_⟩
    intro y hy
    have hnorm : ‖y‖ ≤ radius A.cutoff := by
      rw [sphereLevel_norm (A.spheres y hy)]
      exact hstrict.monotone (A.bounded y hy)
    have hv : polynomialEvaluation y p.val = values ⟨y, hy⟩ := congrFun hp ⟨y, hy⟩
    have hft : domainEntireFourier Ω hΩ f (realToComplex y) = if x = y then 1 else 0 := by
      rw [hfp]
      change I.multiplier A.cutoff (realToComplex y) * polynomialEvaluation y p.val = _
      rw [hv]
      dsimp [values]
      field_simp [I.nonzero A.cutoff y hnorm]
    rw [← inner_conj_symm, ← domainEntireFourier_real_inner hΩ hfinite, hft]
    split_ifs <;> simp

/-- The concrete finite-step construction: available-frequency density supplies
the approximation points, and sphere basis extension retains them. -/
theorem extend_stage (I : SphereAnalyticInputs Ω hΩ hfinite radius core)
    (hbounded : Bornology.IsBounded Ω) (hd : 1 ≤ d)
    (hpositive : ∀ j, 0 < j → 0 < radius j) (hstrict : StrictMono radius)
    (A : PolynomialSphereStage d radius) (targets : Finset (DomainL2 Ω))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ B : PolynomialSphereStage d radius, A.points ⊆ B.points ∧
      A.cutoff < B.cutoff ∧
      (∀ x ∈ B.points, x ∉ A.points → A.cutoff < sphereLevel radius x) ∧
      ∀ f ∈ targets, ∃ v ∈ Submodule.span ℂ
        (exponentialL2 Ω hfinite '' (B.points : Set (Euclidean d))), dist f v < ε := by
  have hnonzero : ∀ x ∈ A.points, I.multiplier A.cutoff (realToComplex x) ≠ 0 := by
    intro x hx
    apply I.nonzero
    rw [sphereLevel_norm (A.spheres x hx)]
    exact hstrict.monotone (A.bounded x hx)
  obtain ⟨prescribed, hp, happ⟩ := available_exponentials_approximate_finite_targets
    Ω hΩ hbounded hfinite A.points (laterSpheres radius A.cutoff) (I.multiplier A.cutoff)
    (I.tail A.cutoff) A.sampling hnonzero targets ε hε
  obtain ⟨B, hAB, hcutoff, hfresh⟩ :=
    extend_polynomialSphereStage hd radius hpositive hstrict A prescribed hp
  refine ⟨B, Finset.subset_union_left.trans hAB, hcutoff, hfresh, ?_⟩
  intro f hf
  obtain ⟨v, hv, hdist⟩ := happ f hf
  refine ⟨v, Submodule.span_mono (Set.image_mono ?_) hv, hdist⟩
  exact Finset.coe_subset.mpr (Finset.subset_union_right.trans hAB)

/-- The degree-zero initial stage lies on the radius-zero sphere at the origin. -/
theorem exists_initial_polynomialSphereStage (d : ℕ)
    (radius : ℕ → ℝ) (hzero : radius 0 = 0) (hstrict : StrictMono radius) :
    ∃ A : PolynomialSphereStage d radius, A.cutoff = 0 := by
  let x : Euclidean d := 0
  have hx : ‖x‖ = radius 0 := by rw [hzero]; exact norm_zero
  have hspan : Submodule.span ℂ (boundedPolynomialEvaluation 0 '' {y : Euclidean d | ‖y‖ = radius 0}) = ⊤ := by
    apply boundedPolynomialEvaluation_span_eq_top
    intro p hp
    have hdegree : p.val.totalDegree = 0 := Nat.eq_zero_of_le_zero
      ((MvPolynomial.mem_restrictTotalDegree _ _ _).mp p.property)
    have hconstant := MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp hdegree
    have heval := hp x hx
    rw [boundedPolynomialEvaluation_apply, polynomialEvaluation_apply, hconstant,
      MvPolynomial.eval_C] at heval
    apply Subtype.ext
    rw [hconstant, heval, map_zero]
    rfl
  have hind : LinearIndependent ℂ
      (fun x : ↥(∅ : Finset (Euclidean d)) => boundedPolynomialEvaluation 0 x.val) := by
    apply boundedPolynomialEvaluation_finset_linearIndependent
    simp
  obtain ⟨t, _hst, ht, _hcard, hsampling⟩ := exists_bounded_interpolation_extension_with_card
    (∅ : Finset (Euclidean d)) {y | ‖y‖ = radius 0} hind (by simpa using hspan)
  have htsphere : ∀ y ∈ t, y ∈ sphereFrequencies radius := by
    intro y hy
    exact ⟨0, (ht hy).resolve_left (by simp)⟩
  have htlevel : ∀ y ∈ t, sphereLevel radius y ≤ 0 := by
    intro y hy
    have hynorm := (ht hy).resolve_left (by simp)
    exact (sphereLevel_of_norm hstrict hynorm).le
  exact ⟨⟨t, 0, htsphere, htlevel, hsampling⟩, rfl⟩

/-- Run the finite extension recursion while preserving its polynomial sampling
invariant, then expose the resulting genuine Hilbert-space selection stages. -/
theorem exists_polynomial_selectionStages
    (I : SphereAnalyticInputs Ω hΩ hfinite radius core)
    (hbounded : Bornology.IsBounded Ω) (hd : 1 ≤ d)
    (hpositive : ∀ j, 0 < j → 0 < radius j) (hstrict : StrictMono radius)
    (initial : PolynomialSphereStage d radius) (targets : ℕ → DomainL2 Ω) :
    ∃ S : SelectionStages (exponentialL2 Ω hfinite) (sphereLevel radius)
        (I.spaces hbounded) targets,
      ∀ n x, x ∈ (S.stage n).points → x ∈ sphereFrequencies radius := by
  let next : ℕ → PolynomialSphereStage d radius → PolynomialSphereStage d radius := fun n A =>
    Classical.choose (I.extend_stage hbounded hd hpositive hstrict A
      ((Finset.range (n + 1)).image targets) (1 / (n + 1 : ℝ)) (by positivity))
  have next_spec (n : ℕ) (A : PolynomialSphereStage d radius) :
      A.points ⊆ (next n A).points ∧ A.cutoff < (next n A).cutoff ∧
      (∀ x ∈ (next n A).points, x ∉ A.points → A.cutoff < sphereLevel radius x) ∧
      ∀ j ≤ n, ∃ v ∈ Submodule.span ℂ
        (exponentialL2 Ω hfinite '' ((next n A).points : Set (Euclidean d))),
        dist (targets j) v < 1 / (n + 1 : ℝ) := by
    obtain ⟨hsub, hcut, hfresh, happ⟩ := Classical.choose_spec
      (I.extend_stage hbounded hd hpositive hstrict A
        ((Finset.range (n + 1)).image targets) (1 / (n + 1 : ℝ)) (by positivity))
    refine ⟨hsub, hcut, hfresh, ?_⟩
    intro j hj
    exact happ (targets j) (Finset.mem_image.mpr
      ⟨j, Finset.mem_range.mpr (by omega), rfl⟩)
  let stages : ℕ → PolynomialSphereStage d radius := fun n => Nat.rec initial next n
  refine ⟨{ stage := fun n => I.toFiniteStage hbounded hstrict (stages n)
            nested := fun n => (next_spec n (stages n)).1
            increasing := fun n => (next_spec n (stages n)).2.1
            fresh := fun n => (next_spec n (stages n)).2.2.1
            approximate := fun n => (next_spec n (stages n)).2.2.2 }, ?_⟩
  intro n x hx
  exact (stages n).spheres x hx

end SphereAnalyticInputs

/-- Diverging radii bound the sphere index in each neighborhood. -/
theorem sphereLevel_locally_bounded {d : ℕ} (radius : ℕ → ℝ)
    (hstrict : StrictMono radius) (hescape : Tendsto radius atTop atTop) :
    ∀ x : Euclidean d, ∃ U ∈ nhds x, ∃ N : ℕ, ∀ y ∈ U, sphereLevel radius y ≤ N := by
  intro x
  obtain ⟨N, hN⟩ := ((tendsto_atTop.1 hescape) (‖x‖ + 1)).exists
  refine ⟨Metric.ball x 1, Metric.ball_mem_nhds x zero_lt_one, N, ?_⟩
  intro y hy
  by_cases hsphere : y ∈ sphereFrequencies radius
  · have hnorm := (norm_lt_of_mem_ball hy).trans_le hN
    rw [sphereLevel_norm hsphere] at hnorm
    exact le_of_not_gt (fun h => (not_lt_of_ge (hstrict h).le) hnorm)
  · change ¬ ∃ j, ‖y‖ = radius j at hsphere
    unfold sphereLevel
    rw [dif_neg hsphere]
    exact Nat.zero_le N

/-- Conditional assembly of the actual complete and minimal exponential system.
Only the explicit sphere-multiplier analytic inputs remain to be discharged. -/
theorem complete_minimal_exponentials_of_sphere_analytic_inputs {d : ℕ}
    (hd : 1 ≤ d) (Ω : Set (Euclidean d)) (hΩ : MeasurableSet Ω)
    (hbounded : Bornology.IsBounded Ω) (hfinite : volume Ω ≠ ⊤)
    (radius : ℕ → ℝ) (hzero : radius 0 = 0)
    (hpositive : ∀ j, 0 < j → 0 < radius j) (hstrict : StrictMono radius)
    (hescape : Tendsto radius atTop atTop) (core : Set (Euclidean d))
    (I : SphereAnalyticInputs Ω hΩ hfinite radius core) :
    ∃ Λ : Set (Euclidean d), Λ ⊆ sphereFrequencies radius ∧
      IsCompleteExponential Ω hfinite Λ ∧ IsMinimalExponential Ω hfinite Λ ∧
      (∀ x, ∃ U ∈ nhds x, (Λ ∩ U).Finite) ∧
      ∃ g : Λ → DomainL2 Ω,
        IsBiorthogonal (exponentialFamily Ω hfinite Λ) g ∧
        ∀ ξ, SupportedOn Ω (g ξ) core := by
  letI : IsFiniteMeasure (volume.restrict Ω) := ⟨by simpa using hfinite.lt_top⟩
  letI : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by norm_num⟩
  obtain ⟨targets, htargets⟩ := TopologicalSpace.exists_dense_seq (DomainL2 Ω)
  obtain ⟨initial, _hcutoff⟩ := SphereAnalyticInputs.exists_initial_polynomialSphereStage
    d radius hzero hstrict
  obtain ⟨S, hspheres⟩ := I.exists_polynomial_selectionStages hbounded hd hpositive hstrict
    initial targets
  have hvanish : ∀ N f, f ∈ I.spaces hbounded N → ∀ x, N < sphereLevel radius x →
      inner (𝕜 := ℂ) f (exponentialL2 Ω hfinite x) = 0 :=
    fun _ _ hf _ hx => I.vanish hbounded hf hx
  obtain ⟨g, hg, hbiorthogonal⟩ := S.exists_biorthogonal hvanish
  have hbi : IsBiorthogonal (exponentialFamily Ω hfinite S.selected) g := by
    intro x y
    by_cases hxy : x = y
    · simpa only [exponentialFamily, if_pos hxy] using hbiorthogonal x y
    · simpa only [exponentialFamily, if_neg hxy] using hbiorthogonal x y
  refine ⟨S.selected, ?_, ?_, hbi.isMinimal,
    S.locally_finite (sphereLevel_locally_bounded radius hstrict hescape), g, hbi, ?_⟩
  · intro x hx
    obtain ⟨n, hn⟩ := hx
    exact hspheres n x hn
  · have hrange : Set.range (exponentialFamily Ω hfinite S.selected) =
        exponentialL2 Ω hfinite '' S.selected := by
      ext f
      simp [exponentialFamily]
    change (Submodule.span ℂ (Set.range (exponentialFamily Ω hfinite S.selected))).topologicalClosure = ⊤
    rw [hrange]
    exact S.complete htargets
  · intro ξ
    obtain ⟨N, hN⟩ := hg ξ
    exact I.supported hbounded hN

end RieszEuclidean.CompleteMinimal
