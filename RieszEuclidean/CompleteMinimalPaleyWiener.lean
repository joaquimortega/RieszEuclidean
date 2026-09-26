import RieszEuclidean.CompleteMinimalEntireFourier
import RieszEuclidean.CompleteMinimalDistributions
import RieszEuclidean.CompleteMinimalConvolutionSupport
import RieszEuclidean.CompleteMinimalQuotientType
import Mathlib.Analysis.Complex.PhragmenLindelof
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
The Paley–Wiener–Schwartz support direction for entire functions of finite exponential
type with polynomial real-axis growth. The proof uses Phragmén–Lindelöf growth reduction,
Gaussian regularization, actual contour shifts, and convergence on Schwartz tests.
-/

noncomputable section
open MeasureTheory Filter Topology Set Complex
open scoped BigOperators ComplexOrder NNReal

namespace RieszEuclidean.CompleteMinimal

/-- A bound on the real axis controls a function of exponential type throughout
the upper half-plane. The coefficient in the global type estimate disappears. -/
theorem exponential_type_upper_half_plane_bound {f : ℂ → ℂ} {A C R : ℝ}
    (hf : DiffContOnCl ℂ f {z : ℂ | 0 < z.im}) (hR : 0 ≤ R)
    (htype : ∀ z : ℂ, 0 ≤ z.im → ‖f z‖ ≤ A * Real.exp (R * ‖z‖))
    (hreal : ∀ t : ℝ, ‖f t‖ ≤ C) {z : ℂ} (hz : 0 ≤ z.im) :
    ‖f z‖ ≤ C * Real.exp (R * z.im) := by
  let g : ℂ → ℂ := fun w => Complex.exp ((R : ℂ) * Complex.I * w) * f w
  have hg : DiffContOnCl ℂ g {z : ℂ | 0 < z.im} := by
    simpa only [g, smul_eq_mul] using
      ((differentiable_id.const_mul ((R : ℂ) * Complex.I)).cexp.diffContOnCl.smul hf)
  have hgnorm (w : ℂ) : ‖g w‖ = Real.exp (-R * w.im) * ‖f w‖ := by
    simp [g, norm_mul, Complex.norm_exp, Complex.mul_re, Complex.mul_im]
  have hgreal (t : ℝ) : ‖g t‖ ≤ C := by
    simpa only [hgnorm, Complex.ofReal_im, mul_zero, Real.exp_zero, one_mul] using hreal t
  have hgtype (w : ℂ) (hw : 0 ≤ w.im) :
      ‖g w‖ ≤ A * Real.exp (R * ‖w‖) := by
    rw [hgnorm]
    have hexp : Real.exp (-R * w.im) ≤ 1 := by
      rw [← Real.exp_zero]
      apply Real.exp_le_exp.mpr
      exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hR) hw
    exact (mul_le_mul_of_nonneg_right hexp (norm_nonneg _)).trans
      (by simpa only [one_mul] using htype w hw)
  have hgimag (t : ℝ) (ht : 0 ≤ t) : ‖g (t * Complex.I)‖ ≤ A := by
    rw [hgnorm]
    have him : ((t : ℂ) * Complex.I).im = t := by simp
    rw [him]
    calc
      Real.exp (-R * t) * ‖f (t * Complex.I)‖ ≤
          Real.exp (-R * t) * (A * Real.exp (R * t)) :=
        mul_le_mul_of_nonneg_left
          (by simpa [him, abs_of_nonneg ht] using
            (htype (t * Complex.I) (by simpa using ht)))
          (Real.exp_pos _).le
      _ = A := by rw [← mul_assoc, mul_comm _ A, mul_assoc, ← Real.exp_add]; simp
  have hquadI : ∀ w : ℂ, 0 ≤ w.re → 0 ≤ w.im → ‖g w‖ ≤ max C A := by
    intro w hwre hwim
    apply PhragmenLindelof.quadrant_I
      (hg.mono (fun w hw => hw.2)) ?_
      (fun t _ => (hgreal t).trans (le_max_left _ _))
      (fun t ht => (hgimag t ht).trans (le_max_right _ _)) hwre hwim
    refine ⟨1, by norm_num, R, Asymptotics.IsBigO.of_bound A ?_⟩
    apply Filter.Eventually.filter_mono (f₂ := 𝓟 (Ioi 0 ×ℂ Ioi 0)) inf_le_right
    rw [Filter.eventually_principal]
    intro w hw
    simpa only [Real.rpow_one, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using
      hgtype w hw.2.le
  have hquadII : ∀ w : ℂ, w.re ≤ 0 → 0 ≤ w.im → ‖g w‖ ≤ max C A := by
    intro w hwre hwim
    apply PhragmenLindelof.quadrant_II
      (hg.mono (fun w hw => hw.2)) ?_
      (fun t _ => (hgreal t).trans (le_max_left _ _))
      (fun t ht => (hgimag t ht).trans (le_max_right _ _)) hwre hwim
    refine ⟨1, by norm_num, R, Asymptotics.IsBigO.of_bound A ?_⟩
    apply Filter.Eventually.filter_mono (f₂ := 𝓟 (Iio 0 ×ℂ Ioi 0)) inf_le_right
    rw [Filter.eventually_principal]
    intro w hw
    simpa only [Real.rpow_one, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using
      hgtype w hw.2.le
  have hgbound (w : ℂ) (hw : 0 ≤ w.im) : ‖g w‖ ≤ max C A := by
    rcases le_total 0 w.re with h | h
    · exact hquadI w h hw
    · exact hquadII w h hw
  let h : ℂ → ℂ := fun w => g (w * Complex.I)
  have hd : DiffContOnCl ℂ h {w : ℂ | 0 < w.re} := by
    apply hg.comp (differentiable_id.mul_const Complex.I).diffContOnCl
    intro w hw
    simpa only [Set.mem_setOf_eq, id_eq, Complex.mul_I_im] using hw
  have hbound (w : ℂ) (hw : 0 ≤ w.re) : ‖h w‖ ≤ max C A := by
    apply hgbound
    simpa only [Complex.mul_I_im] using hw
  have hsmall : ∀ w : ℂ, 0 ≤ w.re → ‖h w‖ ≤ C := by
    intro w hw
    apply PhragmenLindelof.right_half_plane_of_bounded_on_real hd ?_ ?_ ?_ hw
    · refine ⟨0, by norm_num, 0, Asymptotics.IsBigO.of_bound (max C A) ?_⟩
      apply Filter.Eventually.filter_mono (f₂ := 𝓟 {w : ℂ | 0 < w.re}) inf_le_right
      rw [Filter.eventually_principal]
      intro v hv
      simpa using hbound v hv.le
    · refine ⟨max C A, ?_⟩
      change ∀ᶠ t : ℝ in atTop, ‖h t‖ ≤ max C A
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
      exact hbound t (by simpa using ht)
    · intro t
      simpa [h, mul_assoc] using hgreal (-t)
  have hgC : ‖g z‖ ≤ C := by
    have hrot : (z * -Complex.I) * Complex.I = z := by simp [mul_assoc]
    have hpos : 0 ≤ (z * -Complex.I).re := by simpa using hz
    simpa only [h, hrot] using hsmall (z * -Complex.I) hpos
  rw [hgnorm] at hgC
  calc
    ‖f z‖ = Real.exp (R * z.im) * (Real.exp (-R * z.im) * ‖f z‖) := by
      rw [← mul_assoc, ← Real.exp_add]
      simp
    _ ≤ Real.exp (R * z.im) * C :=
      mul_le_mul_of_nonneg_left hgC (Real.exp_pos _).le
    _ = _ := mul_comm _ _

/-- Entire functions of finite exponential type bounded on the real axis obey
the standard bound depending only on the imaginary part. -/
theorem exponential_type_imaginary_bound {f : ℂ → ℂ} {A C R : ℝ}
    (hf : Differentiable ℂ f) (hR : 0 ≤ R)
    (htype : ∀ z : ℂ, ‖f z‖ ≤ A * Real.exp (R * ‖z‖))
    (hreal : ∀ t : ℝ, ‖f t‖ ≤ C) (z : ℂ) :
    ‖f z‖ ≤ C * Real.exp (R * |z.im|) := by
  rcases le_total 0 z.im with hz | hz
  · simpa only [abs_of_nonneg hz] using exponential_type_upper_half_plane_bound
      hf.diffContOnCl hR (fun w _ => htype w) hreal hz
  · have hn : 0 ≤ (-z).im := by simpa using hz
    have hfn : Differentiable ℂ (fun w => f (-w)) := hf.comp differentiable_neg
    have hb := exponential_type_upper_half_plane_bound hfn.diffContOnCl hR
      (fun w _ => by simpa only [norm_neg] using htype (-w))
      (fun t => by simpa using hreal (-t)) hn
    simpa only [neg_neg, Complex.neg_im, abs_of_nonpos hz] using hb

theorem imaginary_shift_norm_ge {z : ℂ} {b : ℝ} (hz : 0 ≤ z.im) :
    b ≤ ‖z + (b : ℂ) * Complex.I‖ := by
  calc
    b ≤ z.im + b := by linarith
    _ = (z + (b : ℂ) * Complex.I).im := by simp
    _ ≤ ‖z + (b : ℂ) * Complex.I‖ := Complex.im_le_norm _

/-- Polynomial real-axis growth is upgraded to the usual polynomial times
imaginary exponential estimate. The shift parameter permits uniform use on
affine real lines whose origins vary. -/
theorem polynomial_exponential_type_upper_bound {f : ℂ → ℂ} {A C R b : ℝ} {N : ℕ}
    (hf : DiffContOnCl ℂ f {z : ℂ | 0 < z.im}) (hC : 0 ≤ C) (hR : 0 ≤ R)
    (hb : 1 ≤ b)
    (htype : ∀ z : ℂ, 0 ≤ z.im → ‖f z‖ ≤ A * Real.exp (R * ‖z‖))
    (hreal : ∀ t : ℝ, ‖f t‖ ≤ C * (b + |t|) ^ N)
    {z : ℂ} (hz : 0 ≤ z.im) :
    ‖f z‖ ≤ C * 2 ^ N * (b + ‖z‖) ^ N * Real.exp (R * z.im) := by
  let p : ℂ → ℂ := fun w => (w + (b : ℂ) * Complex.I) ^ N
  let g : ℂ → ℂ := fun w => f w / p w
  have hbpos : 0 < b := lt_of_lt_of_le zero_lt_one hb
  have hp : DiffContOnCl ℂ p {z : ℂ | 0 < z.im} :=
    ((differentiable_id.add_const ((b : ℂ) * Complex.I)).pow N).diffContOnCl
  have hpne (w : ℂ) (hw : 0 ≤ w.im) : p w ≠ 0 := by
    apply pow_ne_zero
    intro hzero
    have heq := congrArg Complex.im hzero
    simp only [Complex.add_im, Complex.mul_I_im, Complex.ofReal_re, Complex.zero_im] at heq
    linarith
  have hg : DiffContOnCl ℂ g {z : ℂ | 0 < z.im} := by
    have hi : DiffContOnCl ℂ (fun w => (p w)⁻¹) {z : ℂ | 0 < z.im} :=
      hp.inv (fun w hw => hpne w (by simpa only [Complex.closure_setOf_lt_im,
        Set.mem_setOf_eq] using hw))
    simpa only [g, div_eq_mul_inv, smul_eq_mul] using hf.smul hi
  have hpnorm (w : ℂ) : ‖p w‖ = ‖w + (b : ℂ) * Complex.I‖ ^ N := by
    simp only [p, norm_pow]
  have hplower (w : ℂ) (hw : 0 ≤ w.im) : 1 ≤ ‖p w‖ := by
    rw [hpnorm]
    exact one_le_pow₀ (hb.trans (imaginary_shift_norm_ge hw))
  have hgtype (w : ℂ) (hw : 0 ≤ w.im) :
      ‖g w‖ ≤ A * Real.exp (R * ‖w‖) := by
    calc
      ‖g w‖ = ‖f w‖ / ‖p w‖ := norm_div _ _
      _ ≤ ‖f w‖ := div_le_self (norm_nonneg _) (hplower w hw)
      _ ≤ _ := htype w hw
  have hgreal (t : ℝ) : ‖g t‖ ≤ C * 2 ^ N := by
    have htN : |t| ≤ ‖(t : ℂ) + (b : ℂ) * Complex.I‖ := by
      simpa using Complex.abs_re_le_norm ((t : ℂ) + (b : ℂ) * Complex.I)
    have hbN : b ≤ ‖(t : ℂ) + (b : ℂ) * Complex.I‖ := imaginary_shift_norm_ge (by simp)
    have hsum : b + |t| ≤ 2 * ‖(t : ℂ) + (b : ℂ) * Complex.I‖ := by linarith
    have hnum : ‖f t‖ ≤ C * (2 * ‖(t : ℂ) + (b : ℂ) * Complex.I‖) ^ N := by
      apply (hreal t).trans
      gcongr
    have hpzero : ‖p t‖ ≠ 0 := norm_ne_zero_iff.mpr (hpne t (by simp))
    calc
      ‖g t‖ = ‖f t‖ / ‖p t‖ := norm_div _ _
      _ ≤ (C * (2 * ‖(t : ℂ) + (b : ℂ) * Complex.I‖) ^ N) / ‖p t‖ :=
        div_le_div_of_nonneg_right hnum (norm_nonneg _)
      _ = (C * 2 ^ N * ‖p t‖) / ‖p t‖ := by rw [mul_pow, hpnorm]; ring
      _ = C * 2 ^ N := mul_div_cancel_right₀ _ hpzero
  have hgBound := exponential_type_upper_half_plane_bound hg hR hgtype hgreal hz
  have hpupper : ‖p z‖ ≤ (b + ‖z‖) ^ N := by
    rw [hpnorm]
    have hn : ‖z + (b : ℂ) * Complex.I‖ ≤ b + ‖z‖ := by
      calc
        _ ≤ ‖z‖ + ‖(b : ℂ) * Complex.I‖ := norm_add_le _ _
        _ = b + ‖z‖ := by simp [norm_mul, abs_of_nonneg hbpos.le, add_comm]
    gcongr
  have hpzero : ‖p z‖ ≠ 0 := norm_ne_zero_iff.mpr (hpne z hz)
  calc
    ‖f z‖ = (‖f z‖ / ‖p z‖) * ‖p z‖ := (div_mul_cancel₀ _ hpzero).symm
    _ = ‖g z‖ * ‖p z‖ := by rw [show ‖g z‖ = ‖f z‖ / ‖p z‖ from norm_div _ _]
    _ ≤ (C * 2 ^ N * Real.exp (R * z.im)) * (b + ‖z‖) ^ N :=
      mul_le_mul hgBound hpupper (norm_nonneg _) (by positivity)
    _ = _ := by ring

theorem polynomial_exponential_type_imaginary_bound {f : ℂ → ℂ} {A C R b : ℝ} {N : ℕ}
    (hf : Differentiable ℂ f) (hC : 0 ≤ C) (hR : 0 ≤ R) (hb : 1 ≤ b)
    (htype : ∀ z : ℂ, ‖f z‖ ≤ A * Real.exp (R * ‖z‖))
    (hreal : ∀ t : ℝ, ‖f t‖ ≤ C * (b + |t|) ^ N) (z : ℂ) :
    ‖f z‖ ≤ C * 2 ^ N * (b + ‖z‖) ^ N * Real.exp (R * |z.im|) := by
  rcases le_total 0 z.im with hz | hz
  · simpa only [abs_of_nonneg hz] using polynomial_exponential_type_upper_bound
      hf.diffContOnCl hC hR hb (fun w _ => htype w) hreal hz
  · have hn : 0 ≤ (-z).im := by simpa using hz
    have hfn : Differentiable ℂ (fun w => f (-w)) := hf.comp differentiable_neg
    have hbound := polynomial_exponential_type_upper_bound hfn.diffContOnCl hC hR hb
      (fun w _ => by simpa only [norm_neg] using htype (-w))
      (fun t => by simpa only [Complex.ofReal_neg, abs_neg] using hreal (-t)) hn
    simpa only [neg_neg, Complex.neg_im, norm_neg, abs_of_nonpos hz] using hbound

@[simp] theorem realToComplex_add {d : ℕ} (x y : Euclidean d) :
    realToComplex (x + y) = realToComplex x + realToComplex y := by
  ext j
  simp

@[simp] theorem realToComplex_real_smul {d : ℕ} (t : ℝ) (x : Euclidean d) :
    realToComplex (t • x) = (t : ℂ) • realToComplex x := by
  ext j
  simp [smul_eq_mul]

/-- The one-variable principle applied uniformly to affine real lines gives
the multivariate polynomial times imaginary exponential bound. -/
theorem multivariate_polynomial_imaginary_bound {d N : ℕ}
    {F : ComplexEuclidean d → ℂ} {A C R : ℝ}
    (hF : Differentiable ℂ F) (hA : 0 ≤ A) (hC : 0 ≤ C) (hR : 0 ≤ R)
    (htype : ∀ z, ‖F z‖ ≤ A * Real.exp (R * ‖z‖))
    (hreal : ∀ x : Euclidean d, ‖F (realToComplex x)‖ ≤ C * (1 + ‖x‖) ^ N)
    (x y : Euclidean d) :
    ‖F (realToComplex x + Complex.I • realToComplex y)‖ ≤
      C * 2 ^ N * (1 + ‖x‖ + ‖y‖) ^ N * Real.exp (R * ‖y‖) := by
  by_cases hy : y = 0
  · simpa only [hy, norm_zero, add_zero, mul_zero, Real.exp_zero, mul_one,
      realToComplex, PiLp.zero_apply, Complex.ofReal_zero, smul_zero,
      show (WithLp.equiv 2 (Fin d → ℂ)).symm (fun _ => 0) = (0 : ComplexEuclidean d) from rfl]
      using (hreal x).trans (by
        have hpow : (1 : ℝ) ≤ 2 ^ N := one_le_pow₀ (by norm_num)
        calc
          C * (1 + ‖x‖) ^ N ≤ (C * (1 + ‖x‖) ^ N) * 2 ^ N :=
            le_mul_of_one_le_right (by positivity) hpow
          _ = C * 2 ^ N * (1 + ‖x‖) ^ N := by ring)
  let u : Euclidean d := (‖y‖⁻¹ : ℝ) • y
  have hynorm : ‖y‖ ≠ 0 := norm_ne_zero_iff.mpr hy
  have hunorm : ‖u‖ = 1 := by
    simp [u, norm_smul, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg y)), hynorm]
  let f : ℂ → ℂ := fun w => F (realToComplex x + w • realToComplex u)
  have hf : Differentiable ℂ f :=
    hF.comp ((differentiable_const (realToComplex x)).add
      (differentiable_id.smul_const (realToComplex u)))
  have hfType (w : ℂ) : ‖f w‖ ≤ (A * Real.exp (R * ‖x‖)) * Real.exp (R * ‖w‖) := by
    have hline : ‖realToComplex x + w • realToComplex u‖ ≤ ‖x‖ + ‖w‖ := by
      calc
        _ ≤ ‖realToComplex x‖ + ‖w • realToComplex u‖ := norm_add_le _ _
        _ = _ := by rw [norm_smul w (realToComplex u), realToComplex_norm,
          realToComplex_norm, hunorm, mul_one]
    calc
      ‖f w‖ ≤ A * Real.exp (R * ‖realToComplex x + w • realToComplex u‖) := htype _
      _ ≤ A * Real.exp (R * (‖x‖ + ‖w‖)) := by gcongr
      _ = _ := by rw [mul_add, Real.exp_add]; ring
  have hfReal (t : ℝ) : ‖f t‖ ≤ C * ((1 + ‖x‖) + |t|) ^ N := by
    have hline : ‖x + t • u‖ ≤ ‖x‖ + |t| := by
      calc
        _ ≤ ‖x‖ + ‖t • u‖ := norm_add_le _ _
        _ = _ := by rw [norm_smul, Real.norm_eq_abs, hunorm, mul_one]
    have heq : realToComplex (x + t • u) = realToComplex x + (t : ℂ) • realToComplex u := by simp
    calc
      ‖f t‖ = ‖F (realToComplex (x + t • u))‖ := by rw [heq]
      _ ≤ C * (1 + ‖x + t • u‖) ^ N := hreal _
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ hC
        apply pow_le_pow_left₀ (by positivity)
        linarith
  have hBound := polynomial_exponential_type_imaginary_bound hf hC hR
    (le_add_of_nonneg_right (norm_nonneg x)) hfType hfReal ((‖y‖ : ℂ) * Complex.I)
  have hwNorm : ‖(‖y‖ : ℂ) * Complex.I‖ = ‖y‖ := by simp [norm_mul]
  have hwIm : |((‖y‖ : ℂ) * Complex.I).im| = ‖y‖ := by simp
  have heq : ((‖y‖ : ℂ) * Complex.I) • realToComplex u =
      Complex.I • realToComplex y := by
    rw [show realToComplex u = (‖y‖⁻¹ : ℂ) • realToComplex y by
      simp only [u, realToComplex_real_smul, Complex.ofReal_inv]]
    rw [smul_smul]
    congr 1
    have hne : (‖y‖ : ℂ) ≠ 0 := by exact_mod_cast hynorm
    field_simp
  simpa only [f, heq, hwNorm, hwIm, add_assoc] using hBound

/-- The real coordinates of a complex Euclidean vector. -/
def complexRealPart {d : ℕ} (z : ComplexEuclidean d) : Euclidean d :=
  (WithLp.equiv 2 (Fin d → ℝ)).symm (fun j => (z j).re)

/-- The imaginary coordinates of a complex Euclidean vector. -/
def complexImagPart {d : ℕ} (z : ComplexEuclidean d) : Euclidean d :=
  (WithLp.equiv 2 (Fin d → ℝ)).symm (fun j => (z j).im)

@[simp] theorem complexRealPart_apply {d : ℕ} (z : ComplexEuclidean d) (j : Fin d) :
    complexRealPart z j = (z j).re := rfl

@[simp] theorem complexImagPart_apply {d : ℕ} (z : ComplexEuclidean d) (j : Fin d) :
    complexImagPart z j = (z j).im := rfl

theorem complexRealPart_norm_le {d : ℕ} (z : ComplexEuclidean d) :
    ‖complexRealPart z‖ ≤ ‖z‖ := by
  have hs : ‖complexRealPart z‖ ^ 2 ≤ ‖z‖ ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2]
    apply Finset.sum_le_sum
    intro j _
    apply pow_le_pow_left₀ (norm_nonneg _)
    simpa only [complexRealPart_apply, Real.norm_eq_abs] using Complex.abs_re_le_norm (z j)
  nlinarith [norm_nonneg (complexRealPart z), norm_nonneg z]

theorem complexImagPart_norm_le {d : ℕ} (z : ComplexEuclidean d) :
    ‖complexImagPart z‖ ≤ ‖z‖ := by
  have hs : ‖complexImagPart z‖ ^ 2 ≤ ‖z‖ ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2]
    apply Finset.sum_le_sum
    intro j _
    apply pow_le_pow_left₀ (norm_nonneg _)
    simpa only [complexImagPart_apply, Real.norm_eq_abs] using Complex.abs_im_le_norm (z j)
  nlinarith [norm_nonneg (complexImagPart z), norm_nonneg z]

theorem complex_real_imag_decomposition {d : ℕ} (z : ComplexEuclidean d) :
    realToComplex (complexRealPart z) + Complex.I • realToComplex (complexImagPart z) = z := by
  ext j
  change ((z j).re : ℂ) + Complex.I * ((z j).im : ℂ) = z j
  rw [mul_comm]
  exact Complex.re_add_im (z j)

/-- Finite total exponential type and polynomial real-axis growth imply the
standard Paley–Wiener growth estimate in all complex dimensions. -/
theorem standard_paley_wiener_growth {d N : ℕ}
    {F : ComplexEuclidean d → ℂ} {A C R : ℝ}
    (hF : Differentiable ℂ F) (hA : 0 ≤ A) (hC : 0 ≤ C) (hR : 0 ≤ R)
    (htype : ∀ z, ‖F z‖ ≤ A * Real.exp (R * ‖z‖))
    (hreal : ∀ x : Euclidean d, ‖F (realToComplex x)‖ ≤ C * (1 + ‖x‖) ^ N)
    (z : ComplexEuclidean d) :
    ‖F z‖ ≤ C * 4 ^ N * (1 + ‖z‖) ^ N * Real.exp (R * ‖complexImagPart z‖) := by
  have hbound := multivariate_polynomial_imaginary_bound hF hA hC hR htype hreal
    (complexRealPart z) (complexImagPart z)
  rw [complex_real_imag_decomposition] at hbound
  have hs : 1 + ‖complexRealPart z‖ + ‖complexImagPart z‖ ≤ 2 * (1 + ‖z‖) := by
    linarith [complexRealPart_norm_le z, complexImagPart_norm_le z]
  calc
    ‖F z‖ ≤ C * 2 ^ N * (1 + ‖complexRealPart z‖ + ‖complexImagPart z‖) ^ N *
        Real.exp (R * ‖complexImagPart z‖) := hbound
    _ ≤ C * 2 ^ N * (2 * (1 + ‖z‖)) ^ N *
        Real.exp (R * ‖complexImagPart z‖) := by
      apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact pow_le_pow_left₀ (by positivity) hs N
    _ = _ := by
      rw [mul_pow]
      have hp : (2 : ℝ) ^ N * 2 ^ N = 4 ^ N := by rw [← mul_pow]; norm_num
      calc
        _ = C * ((2 : ℝ) ^ N * 2 ^ N) * (1 + ‖z‖) ^ N *
            Real.exp (R * ‖complexImagPart z‖) := by ring
        _ = _ := by rw [hp]

/-- A quantitative bound for the vertical edges used when shifting a real
Fourier integral into a horizontal complex contour. -/
theorem vertical_contour_norm_le {f : ℂ → ℂ} {C T : ℝ} (hT : 0 ≤ T)
    (hdecay : ∀ x : ℝ, ∀ y ∈ Set.Icc 0 T,
      ‖f ((x : ℂ) + (y : ℂ) * Complex.I)‖ ≤ C / (1 + x ^ 2)) (x : ℝ) :
    ‖∫ y : ℝ in (0 : ℝ)..T, f ((x : ℂ) + (y : ℂ) * Complex.I)‖ ≤
      C / (1 + x ^ 2) * T := by
  have hbound := intervalIntegral.norm_integral_le_of_norm_le_const
    (f := fun y : ℝ => f ((x : ℂ) + (y : ℂ) * Complex.I))
    (a := 0) (b := T) (C := C / (1 + x ^ 2)) (by
      intro y hy
      rw [Set.uIoc_of_le hT] at hy
      exact hdecay x y ⟨hy.1.le, hy.2⟩)
  simpa only [sub_zero, abs_of_nonneg hT] using hbound

/-- Entire integrands with uniform quadratic decay on a closed horizontal
strip have the same integral on its two boundary lines. -/
theorem horizontal_contour_shift {f : ℂ → ℂ} {C T : ℝ}
    (hf : Differentiable ℂ f) (hT : 0 ≤ T)
    (hdecay : ∀ x : ℝ, ∀ y ∈ Set.Icc 0 T,
      ‖f ((x : ℂ) + (y : ℂ) * Complex.I)‖ ≤ C / (1 + x ^ 2)) :
    (∫ x : ℝ, f x) = ∫ x : ℝ, f ((x : ℂ) + (T : ℂ) * Complex.I) := by
  have hInt (y : ℝ) (hy : y ∈ Set.Icc 0 T) :
      Integrable (fun x : ℝ => f ((x : ℂ) + (y : ℂ) * Complex.I)) := by
    apply (integrable_inv_one_add_sq.const_mul C).mono'
      (hf.continuous.comp (Complex.continuous_ofReal.add continuous_const)).aestronglyMeasurable
    filter_upwards with x
    simpa only [div_eq_mul_inv] using hdecay x y hy
  have hInt0 : Integrable (fun x : ℝ => f x) := by
    simpa using hInt 0 ⟨le_rfl, hT⟩
  have hIntT := hInt T ⟨hT, le_rfl⟩
  let V : ℝ → ℂ := fun x => ∫ y : ℝ in (0 : ℝ)..T, f ((x : ℂ) + (y : ℂ) * Complex.I)
  have hVnorm (x : ℝ) : ‖V x‖ ≤ C / (1 + x ^ 2) * T :=
    vertical_contour_norm_le hT hdecay x
  have hdecaylim : Tendsto (fun x : ℝ => C / (1 + x ^ 2) * T) atTop (𝓝 0) := by
    have hpow : Tendsto (fun x : ℝ => x ^ 2) atTop atTop := tendsto_pow_atTop (by norm_num)
    have hden : Tendsto (fun x : ℝ => 1 + x ^ 2) atTop atTop :=
      tendsto_atTop_mono (fun x => le_add_of_nonneg_left (by norm_num)) hpow
    have hinv := (tendsto_const_nhds : Tendsto (fun _ : ℝ => C) atTop (𝓝 C)).div_atTop hden
    simpa only [zero_mul] using hinv.mul_const T
  have hVlim : Tendsto V atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    exact squeeze_zero (fun x => norm_nonneg _) hVnorm hdecaylim
  have hVneglim : Tendsto (fun x : ℝ => V (-x)) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    apply squeeze_zero (fun x => norm_nonneg _) _ hdecaylim
    intro x
    simpa only [neg_sq] using hVnorm (-x)
  have hrect (m : ℝ) :
      (∫ x : ℝ in -m..m, f x) -
        (∫ x : ℝ in -m..m, f ((x : ℂ) + (T : ℂ) * Complex.I)) =
      Complex.I * V (-m) - Complex.I * V m := by
    have hboundary := Complex.integral_boundary_rect_eq_zero_of_differentiableOn f
      ((-m : ℝ) : ℂ) ((m : ℂ) + (T : ℂ) * Complex.I) hf.differentiableOn
    simp only [Complex.ofReal_re, Complex.ofReal_im, Complex.add_re, Complex.add_im,
      Complex.mul_I_re, Complex.mul_I_im, neg_zero, add_zero, zero_add, zero_mul,
      smul_eq_mul, Complex.ofReal_zero, V] at hboundary
    dsimp [V]
    linear_combination hboundary
  have hleft := (intervalIntegral_tendsto_integral hInt0 tendsto_neg_atTop_atBot
    (tendsto_id : Tendsto (fun m : ℝ => m) atTop atTop)).sub
      (intervalIntegral_tendsto_integral hIntT tendsto_neg_atTop_atBot
        (tendsto_id : Tendsto (fun m : ℝ => m) atTop atTop))
  have hright := (hVneglim.const_mul Complex.I).sub (hVlim.const_mul Complex.I)
  have heq : (∫ x : ℝ, f x) - (∫ x : ℝ, f ((x : ℂ) + (T : ℂ) * Complex.I)) = 0 := by
    apply tendsto_nhds_unique hleft
    simpa only [mul_zero, sub_zero] using hright.congr (fun m => (hrect m).symm)
  exact sub_eq_zero.mp heq

/-- Gaussian damping on the real frequency space, parametrized by a nonnegative width. -/
def gaussianFrequencyDamping {d : ℕ} (ε : ℝ≥0) (x : Euclidean d) : ℂ :=
  (Real.exp (-(ε : ℝ) * ‖x‖ ^ 2) : ℂ)

/-- Damping never increases the absolute value of a real-frequency integrand. -/
theorem gaussianFrequencyDamping_norm_le_one {d : ℕ} (ε : ℝ≥0) (x : Euclidean d) :
    ‖gaussianFrequencyDamping ε x‖ ≤ 1 := by
  simp only [gaussianFrequencyDamping, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]
  rw [← Real.exp_zero]
  apply Real.exp_le_exp.mpr
  exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ε.coe_nonneg) (sq_nonneg _)

/-- The damping is continuous in the frequency variable. -/
theorem gaussianFrequencyDamping_continuous {d : ℕ} (ε : ℝ≥0) :
    Continuous (gaussianFrequencyDamping (d := d) ε) := by
  unfold gaussianFrequencyDamping
  fun_prop

/-- A damped polynomially bounded function retains its original polynomial bound. -/
theorem gaussian_damped_polynomial_bound {d N : ℕ} {f : Euclidean d → ℂ} {C : ℝ}
    (hf : ∀ x, ‖f x‖ ≤ C * (1 + ‖x‖) ^ N) (ε : ℝ≥0) (x : Euclidean d) :
    ‖f x * gaussianFrequencyDamping ε x‖ ≤ C * (1 + ‖x‖) ^ N := by
  rw [norm_mul]
  exact (mul_le_of_le_one_right (norm_nonneg _) (gaussianFrequencyDamping_norm_le_one ε x)).trans
    (hf x)

/-- Gaussian regularization as an actual continuous functional on Schwartz space. -/
def gaussianRegularizedDistribution {d N : ℕ} (f : Euclidean d → ℂ) {C : ℝ}
    (hC : 0 ≤ C) (hf : ∀ x, ‖f x‖ ≤ C * (1 + ‖x‖) ^ N)
    (hm : AEStronglyMeasurable f volume) (ε : ℝ≥0) : TemperedDistribution d :=
  polynomialDistribution (fun x => f x * gaussianFrequencyDamping ε x) hC
    (gaussian_damped_polynomial_bound hf ε)
    (hm.mul (gaussianFrequencyDamping_continuous ε).aestronglyMeasurable)

/-- Removing Gaussian damping recovers the polynomial distribution on every test. -/
theorem gaussianRegularizedDistribution_tendsto {d N : ℕ} {f : Euclidean d → ℂ} {C : ℝ}
    (hC : 0 ≤ C) (hf : ∀ x, ‖f x‖ ≤ C * (1 + ‖x‖) ^ N)
    (hm : AEStronglyMeasurable f volume) (φ : SchwartzMap (Euclidean d) ℂ) :
    Tendsto (fun ε : ℝ≥0 => gaussianRegularizedDistribution f hC hf hm ε φ) (𝓝 0)
      (𝓝 (polynomialDistribution f hC hf hm φ)) := by
  change Tendsto (fun ε : ℝ≥0 => ∫ x, (f x * gaussianFrequencyDamping ε x) * φ x)
    (𝓝 0) (𝓝 (∫ x, f x * φ x))
  apply tendsto_integral_filter_of_dominated_convergence (fun x => ‖f x * φ x‖)
  · exact Eventually.of_forall fun ε =>
      (hm.mul (gaussianFrequencyDamping_continuous ε).aestronglyMeasurable).mul
        φ.continuous.aestronglyMeasurable
  · exact Eventually.of_forall fun ε => Eventually.of_forall fun x => by
      rw [norm_mul, norm_mul, norm_mul]
      calc
        (‖f x‖ * ‖gaussianFrequencyDamping ε x‖) * ‖φ x‖ ≤ ‖f x‖ * ‖φ x‖ :=
          mul_le_mul_of_nonneg_right
            (mul_le_of_le_one_right (norm_nonneg _) (gaussianFrequencyDamping_norm_le_one ε x))
            (norm_nonneg _)
        _ = _ := rfl
  · exact (polynomial_schwartz_integrable hC hf hm φ).norm
  · exact Eventually.of_forall fun x => by
      have hcont : Continuous (fun ε : ℝ≥0 => (f x * gaussianFrequencyDamping ε x) * φ x) := by
        unfold gaussianFrequencyDamping
        fun_prop
      simpa [gaussianFrequencyDamping] using hcont.tendsto 0

/-- The inverse transforms of the Gaussian regularizations converge on every
Schwartz test to the inverse transform of the polynomial distribution. -/
theorem inverseGaussianRegularizedDistribution_tendsto {d N : ℕ}
    {f : Euclidean d → ℂ} {C : ℝ}
    (hC : 0 ≤ C) (hf : ∀ x, ‖f x‖ ≤ C * (1 + ‖x‖) ^ N)
    (hm : AEStronglyMeasurable f volume) (φ : SchwartzMap (Euclidean d) ℂ) :
    Tendsto (fun ε : ℝ≥0 =>
      distributionInverseFourier (gaussianRegularizedDistribution f hC hf hm ε) φ) (𝓝 0)
      (𝓝 (distributionInverseFourier (polynomialDistribution f hC hf hm) φ)) := by
  simpa only [distributionInverseFourier_apply] using
    gaussianRegularizedDistribution_tendsto hC hf hm ((SchwartzMap.fourierTransformCLE ℂ).symm φ)

/-- The holomorphic quadratic form used to extend real Gaussian damping. -/
def gaussianQuadratic {d : ℕ} (z : ComplexEuclidean d) : ℂ := ∑ j, z j ^ 2

/-- The real coordinate sum of squares equals the Euclidean squared norm. -/
theorem real_coordinate_square_sum {d : ℕ} (x : Euclidean d) :
    (∑ j, x j ^ 2) = ‖x‖ ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2]
  simp only [Real.norm_eq_abs, sq_abs]

/-- The quadratic form gains precisely the negative squared imaginary norm on a shift. -/
theorem gaussianQuadratic_shift_re {d : ℕ} (x y : Euclidean d) :
    (gaussianQuadratic (realToComplex x + Complex.I • realToComplex y)).re =
      ‖x‖ ^ 2 - ‖y‖ ^ 2 := by
  simp only [gaussianQuadratic, Complex.re_sum, PiLp.add_apply, PiLp.smul_apply,
    realToComplex_apply, smul_eq_mul, pow_two, Complex.mul_re, Complex.add_re,
    Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
    Complex.ofReal_re, Complex.ofReal_im]
  simp only [zero_mul, mul_zero, zero_sub, zero_add, one_mul, add_zero, neg_zero]
  rw [Finset.sum_sub_distrib]
  simp only [← pow_two, real_coordinate_square_sum]

/-- Holomorphic Gaussian damping in the complex frequency space. -/
def complexGaussianDamping {d : ℕ} (ε : ℝ) (z : ComplexEuclidean d) : ℂ :=
  Complex.exp (-(ε : ℂ) * gaussianQuadratic z)

/-- Exact growth of Gaussian damping under an imaginary contour shift. -/
theorem complexGaussianDamping_shift_norm {d : ℕ} (ε : ℝ) (x y : Euclidean d) :
    ‖complexGaussianDamping ε (realToComplex x + Complex.I • realToComplex y)‖ =
      Real.exp (-ε * ‖x‖ ^ 2 + ε * ‖y‖ ^ 2) := by
  rw [complexGaussianDamping, Complex.norm_exp]
  simp only [Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.ofReal_re,
    Complex.ofReal_im, neg_zero, zero_mul, sub_zero, gaussianQuadratic_shift_re]
  congr 1
  ring

/-- The inverse Fourier kernel at complex frequencies. -/
def complexInverseFourierKernel {d : ℕ} (p : Euclidean d) (z : ComplexEuclidean d) : ℂ :=
  Complex.exp (-fourierPhaseCLM p z)

/-- The physical frequency supplies exponential decay along a positive imaginary shift. -/
theorem complexInverseFourierKernel_shift_norm {d : ℕ} (p x y : Euclidean d) :
    ‖complexInverseFourierKernel p (realToComplex x + Complex.I • realToComplex y)‖ =
      Real.exp (-2 * Real.pi * inner (𝕜 := ℝ) p y) := by
  rw [complexInverseFourierKernel, Complex.norm_exp, map_add, map_smul]
  simp only [fourierPhaseCLM, ContinuousLinearMap.smul_apply, smul_eq_mul,
    complexPairingCLM_apply, complexPairing_realToComplex]
  simp only [Complex.neg_re, Complex.add_re, Complex.mul_re, Complex.mul_im,
    Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.neg_im]
  congr 1
  norm_num

/-- A polynomial times a Gaussian is bounded by a slower Gaussian, with an explicit constant. -/
theorem polynomial_gaussian_bound (N : ℕ) {ε r : ℝ} (hε : 0 < ε) (hr : 0 ≤ r) :
    (1 + r) ^ N * Real.exp (-ε * r ^ 2) ≤
      ((2 + 2 / ε) ^ N * (N.factorial : ℝ) * Real.exp 1) *
        Real.exp (-(ε / 2) * r ^ 2) := by
  have ht : 0 ≤ 1 + (ε / 2) * r ^ 2 := by positivity
  have hscalar : 1 + r ≤ (2 + 2 / ε) * (1 + (ε / 2) * r ^ 2) := by
    have hinv : 0 < 2 / ε := div_pos (by norm_num) hε
    have hprod : (2 + 2 / ε) * (1 + (ε / 2) * r ^ 2) =
        2 + 2 / ε + (ε + 1) * r ^ 2 := by field_simp; ring
    rw [hprod]
    nlinarith [sq_nonneg (r - 1 / 2), mul_nonneg hε.le (sq_nonneg r)]
  have hfactorial : 0 < (N.factorial : ℝ) := by exact_mod_cast N.factorial_pos
  have hpow := (div_le_iff₀ hfactorial).mp
    (Real.pow_div_factorial_le_exp (1 + (ε / 2) * r ^ 2) ht N)
  calc
    (1 + r) ^ N * Real.exp (-ε * r ^ 2) ≤
        ((2 + 2 / ε) * (1 + (ε / 2) * r ^ 2)) ^ N * Real.exp (-ε * r ^ 2) :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hscalar N)
        (Real.exp_nonneg _)
    _ = (2 + 2 / ε) ^ N * (1 + (ε / 2) * r ^ 2) ^ N *
        Real.exp (-ε * r ^ 2) := by rw [mul_pow]
    _ ≤ (2 + 2 / ε) ^ N *
        (Real.exp (1 + (ε / 2) * r ^ 2) * (N.factorial : ℝ)) *
          Real.exp (-ε * r ^ 2) := by gcongr
    _ = _ := by
      have hexp : Real.exp (1 + (ε / 2) * r ^ 2) * Real.exp (-ε * r ^ 2) =
          Real.exp 1 * Real.exp (-(ε / 2) * r ^ 2) := by
        rw [← Real.exp_add, ← Real.exp_add]
        congr 1
        ring
      calc
        _ = (2 + 2 / ε) ^ N * (N.factorial : ℝ) *
            (Real.exp (1 + (ε / 2) * r ^ 2) * Real.exp (-ε * r ^ 2)) := by ring
        _ = _ := by rw [hexp]; ring

/-- Polynomial Gaussian weights are integrable in any real Euclidean dimension. -/
theorem polynomial_gaussian_integrable {d : ℕ} (N : ℕ) {ε : ℝ} (hε : 0 < ε) :
    Integrable (fun x : Euclidean d => (1 + ‖x‖) ^ N * Real.exp (-ε * ‖x‖ ^ 2)) := by
  have hg : Integrable (fun x : Euclidean d => Real.exp (-(ε / 2) * ‖x‖ ^ 2)) := by
    have hc := GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (V := Euclidean d)
      (b := (ε / 2 : ℝ)) (by simpa using (half_pos hε)) (0 : ℂ) (0 : Euclidean d)
    simpa only [zero_mul, add_zero, ← Complex.ofReal_mul, ← Complex.ofReal_neg,
      ← Complex.ofReal_pow, ← Complex.ofReal_exp, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using hc.norm
  apply (hg.const_mul ((2 + 2 / ε) ^ N * (N.factorial : ℝ) * Real.exp 1)).mono'
    ((by fun_prop : Continuous (fun x : Euclidean d =>
      (1 + ‖x‖) ^ N * Real.exp (-ε * ‖x‖ ^ 2))).aestronglyMeasurable)
  exact Eventually.of_forall fun x => by
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact polynomial_gaussian_bound N hε (norm_nonneg x)

/-- Gaussian damping makes every measurable polynomially bounded function integrable. -/
theorem gaussian_damped_polynomial_integrable {d N : ℕ} {f : Euclidean d → ℂ} {C : ℝ}
    (hf : ∀ x, ‖f x‖ ≤ C * (1 + ‖x‖) ^ N)
    (hm : AEStronglyMeasurable f volume) {ε : ℝ≥0} (hε : 0 < ε) :
    Integrable (fun x => f x * gaussianFrequencyDamping ε x) := by
  apply ((polynomial_gaussian_integrable (d := d) N (show 0 < (ε : ℝ) from hε)).const_mul C).mono'
    (hm.mul (gaussianFrequencyDamping_continuous ε).aestronglyMeasurable)
  exact Eventually.of_forall fun x => by
    change ‖f x * gaussianFrequencyDamping ε x‖ ≤
      C * ((1 + ‖x‖) ^ N * Real.exp (-(ε : ℝ) * ‖x‖ ^ 2))
    simp only [norm_mul, gaussianFrequencyDamping, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_right (hf x) (Real.exp_nonneg _)

/-- The inverse Fourier kernel has modulus one on real frequencies. -/
theorem complexInverseFourierKernel_real_norm {d : ℕ} (p x : Euclidean d) :
    ‖complexInverseFourierKernel p (realToComplex x)‖ = 1 := by
  have hzero : realToComplex (0 : Euclidean d) = 0 := by ext j; simp
  simpa only [hzero, smul_zero, add_zero, inner_zero_right, mul_zero, Real.exp_zero]
    using complexInverseFourierKernel_shift_norm p x (0 : Euclidean d)

/-- The entire function, damping, and inverse kernel form an actual integrable real-frequency
integrand, whenever the entire function has polynomial growth on the real axis. -/
theorem gaussian_inverse_integrand_integrable {d N : ℕ} {F : ComplexEuclidean d → ℂ} {C : ℝ}
    (hF : Continuous F)
    (hreal : ∀ x, ‖F (realToComplex x)‖ ≤ C * (1 + ‖x‖) ^ N)
    {ε : ℝ≥0} (hε : 0 < ε) (p : Euclidean d) :
    Integrable (fun x => (F (realToComplex x) * gaussianFrequencyDamping ε x) *
      complexInverseFourierKernel p (realToComplex x)) := by
  have hemb : Continuous (realToComplex : Euclidean d → ComplexEuclidean d) := by
    exact (PiLp.continuous_equiv_symm 2 _).comp (continuous_pi fun j => by
      change Continuous (fun x : Euclidean d => (x j : ℂ))
      fun_prop)
  apply (gaussian_damped_polynomial_integrable hreal
    (hF.comp hemb).aestronglyMeasurable hε).mono
  · apply Continuous.aestronglyMeasurable
    apply ((hF.comp hemb).mul (gaussianFrequencyDamping_continuous ε)).mul
    unfold complexInverseFourierKernel
    exact (fourierPhaseCLM p |>.continuous.comp hemb).neg.cexp
  · exact Eventually.of_forall fun x => by
      rw [norm_mul, complexInverseFourierKernel_real_norm, mul_one]

/-- Contour-shift estimate for the Gaussian regularized inverse Fourier integrand. -/
theorem gaussian_inverse_shift_norm_le {d N : ℕ} {F : ComplexEuclidean d → ℂ}
    {A C R : ℝ} (hF : Differentiable ℂ F) (hA : 0 ≤ A) (hC : 0 ≤ C) (hR : 0 ≤ R)
    (htype : ∀ z, ‖F z‖ ≤ A * Real.exp (R * ‖z‖))
    (hreal : ∀ x, ‖F (realToComplex x)‖ ≤ C * (1 + ‖x‖) ^ N)
    (ε : ℝ) (p x y : Euclidean d) :
    ‖(F (realToComplex x + Complex.I • realToComplex y) *
        complexGaussianDamping ε (realToComplex x + Complex.I • realToComplex y)) *
      complexInverseFourierKernel p (realToComplex x + Complex.I • realToComplex y)‖ ≤
      C * 2 ^ N * (1 + ‖x‖ + ‖y‖) ^ N *
        Real.exp (-ε * ‖x‖ ^ 2 + ε * ‖y‖ ^ 2 + R * ‖y‖ -
          2 * Real.pi * inner (𝕜 := ℝ) p y) := by
  rw [norm_mul, norm_mul, complexGaussianDamping_shift_norm,
    complexInverseFourierKernel_shift_norm]
  calc
    _ ≤ (C * 2 ^ N * (1 + ‖x‖ + ‖y‖) ^ N * Real.exp (R * ‖y‖)) *
        Real.exp (-ε * ‖x‖ ^ 2 + ε * ‖y‖ ^ 2) *
          Real.exp (-2 * Real.pi * inner (𝕜 := ℝ) p y) := by
      gcongr
      exact multivariate_polynomial_imaginary_bound hF hA hC hR htype hreal x y
    _ = _ := by
      have hexp : Real.exp (R * ‖y‖) * Real.exp (-ε * ‖x‖ ^ 2 + ε * ‖y‖ ^ 2) *
          Real.exp (-2 * Real.pi * inner (𝕜 := ℝ) p y) =
          Real.exp (-ε * ‖x‖ ^ 2 + ε * ‖y‖ ^ 2 + R * ‖y‖ -
            2 * Real.pi * inner (𝕜 := ℝ) p y) := by
        rw [← Real.exp_add, ← Real.exp_add]
        congr 1
        ring
      rw [mul_assoc, mul_assoc, ← mul_assoc (Real.exp (R * ‖y‖)), hexp]

/-- The real-frequency inverse kernel has the conventional positive Fourier sign. -/
theorem complexInverseFourierKernel_real {d : ℕ} (p x : Euclidean d) :
    complexInverseFourierKernel p (realToComplex x) =
      Complex.exp (((2 * Real.pi * inner (𝕜 := ℝ) x p : ℝ) : ℂ) * Complex.I) := by
  unfold complexInverseFourierKernel fourierPhaseCLM
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul, complexPairingCLM_apply,
    complexPairing_realToComplex, Complex.ofReal_mul, Complex.ofReal_ofNat,
    real_inner_comm p x]
  congr 1
  ring

/-- An integral representation of the inverse Fourier transform with the complex kernel. -/
theorem inverseFourier_kernel_integral {d : ℕ} (f : Euclidean d → ℂ) (p : Euclidean d) :
    Real.fourierIntegralInv f p =
      ∫ x, f x * complexInverseFourierKernel p (realToComplex x) := by
  rw [Real.fourierIntegralInv_eq']
  simp only [complexInverseFourierKernel_real, smul_eq_mul, mul_comm]

/-- Fourier inversion can be moved between the two factors of an integrable pairing. -/
theorem integral_inverseFourier_mul {d : ℕ} {f g : Euclidean d → ℂ}
    (hf : Integrable f) (hg : Integrable g) :
    (∫ p, Real.fourierIntegralInv f p * g p) =
      ∫ x, f x * Real.fourierIntegralInv g x := by
  have hflip : (-innerₗ (Euclidean d)).flip = -innerₗ (Euclidean d) := by
    ext x y
    change -inner (𝕜 := ℝ) y x = -inner (𝕜 := ℝ) x y
    rw [real_inner_comm]
  simpa only [Real.fourierIntegralInv, hflip, smul_eq_mul] using
    VectorFourier.integral_fourierIntegral_smul_eq_flip (L := -innerₗ (Euclidean d))
      Real.continuous_fourierChar continuous_inner.neg hf hg

/-- The inverse Gaussian-regularized distribution is represented by its genuine inverse
Fourier integral when evaluated against any Schwartz test. -/
theorem inverseGaussianRegularizedDistribution_apply {d N : ℕ}
    {f : Euclidean d → ℂ} {C : ℝ} (hC : 0 ≤ C)
    (hf : ∀ x, ‖f x‖ ≤ C * (1 + ‖x‖) ^ N) (hm : AEStronglyMeasurable f volume)
    {ε : ℝ≥0} (hε : 0 < ε) (φ : SchwartzMap (Euclidean d) ℂ) :
    distributionInverseFourier (gaussianRegularizedDistribution f hC hf hm ε) φ =
      ∫ p, Real.fourierIntegralInv (fun x => f x * gaussianFrequencyDamping ε x) p * φ p := by
  rw [distributionInverseFourier_apply]
  change (∫ x, (f x * gaussianFrequencyDamping ε x) *
    ((SchwartzMap.fourierTransformCLE ℂ).symm φ) x) = _
  simp only [SchwartzMap.fourierTransformCLE_symm_apply]
  exact (integral_inverseFourier_mul (gaussian_damped_polynomial_integrable hf hm hε)
    φ.integrable).symm

/-- Imaginary contour shifts also hold in the negative direction. -/
theorem horizontal_contour_shift_nonpositive {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    {T C : ℝ} (hT : T ≤ 0)
    (hdecay : ∀ x y : ℝ, y ∈ Icc T 0 → ‖f ((x : ℂ) + (y : ℂ) * Complex.I)‖ ≤
      C / (1 + x ^ 2)) :
    (∫ x : ℝ, f x) = ∫ x : ℝ, f ((x : ℂ) + (T : ℂ) * Complex.I) := by
  let g : ℂ → ℂ := fun z => f (-z)
  have hg : Differentiable ℂ g := hf.comp differentiable_id.neg
  have hbound : ∀ x y : ℝ, y ∈ Icc 0 (-T) → ‖g ((x : ℂ) + (y : ℂ) * Complex.I)‖ ≤
      C / (1 + x ^ 2) := by
    intro x y hy
    have heq : -((x : ℂ) + (y : ℂ) * Complex.I) =
        ((-x : ℝ) : ℂ) + ((-y : ℝ) : ℂ) * Complex.I := by push_cast; ring
    simpa only [g, heq, neg_sq] using hdecay (-x) (-y) ⟨by linarith [hy.2], by linarith [hy.1]⟩
  have h := horizontal_contour_shift hg (neg_nonneg.mpr hT) hbound
  have heq (x : ℝ) : g ((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I) =
      f (((-x : ℝ) : ℂ) + (T : ℂ) * Complex.I) := by
    unfold g
    congr 1
    push_cast
    ring
  simp only [heq] at h
  have hleft : (∫ x : ℝ, g x) = ∫ x : ℝ, f x := by
    simpa only [g, Complex.ofReal_neg] using integral_neg_eq_self (fun x : ℝ => f x) volume
  have hright : (∫ x : ℝ, f (((-x : ℝ) : ℂ) + (T : ℂ) * Complex.I)) =
      ∫ x : ℝ, f ((x : ℂ) + (T : ℂ) * Complex.I) :=
    integral_neg_eq_self (fun x : ℝ => f ((x : ℂ) + (T : ℂ) * Complex.I)) volume
  rwa [hleft, hright] at h

/-- A single contour shift in either imaginary direction, under uniform strip decay. -/
theorem horizontal_contour_shift_any {f : ℂ → ℂ} (hf : Differentiable ℂ f) (T C : ℝ)
    (hdecay : ∀ x y : ℝ, y ∈ uIcc 0 T → ‖f ((x : ℂ) + (y : ℂ) * Complex.I)‖ ≤
      C / (1 + x ^ 2)) :
    (∫ x : ℝ, f x) = ∫ x : ℝ, f ((x : ℂ) + (T : ℂ) * Complex.I) := by
  rcases le_total 0 T with hT | hT
  · exact horizontal_contour_shift hf hT (by simpa only [uIcc_of_le hT] using hdecay)
  · exact horizontal_contour_shift_nonpositive hf hT
      (by simpa only [uIcc_of_ge hT] using hdecay)

/-- Exponential suppression dominates every fixed inverse power of the damping width. -/
theorem gaussian_suppression_tendsto (M : ℕ) {a : ℝ} (ha : 0 < a) :
    Tendsto (fun ε : ℝ => (ε⁻¹) ^ M * Real.exp (-a / ε)) (𝓝[>] 0) (𝓝 0) := by
  simpa only [Function.comp_def, Real.rpow_natCast, div_eq_mul_inv] using
    (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (M : ℝ) a ha).comp
      (tendsto_inv_nhdsGT_zero : Tendsto (fun ε : ℝ => ε⁻¹) (𝓝[>] 0) atTop)

/-- The radial imaginary shift optimizes the Gaussian localization exponent. -/
theorem gaussian_radial_shift_exponent {d : ℕ} (p : Euclidean d) {ε R : ℝ}
    (hε : 0 < ε) (hp : 0 < ‖p‖) (hδ : 0 ≤ 2 * Real.pi * ‖p‖ - R) :
    let y := ((2 * Real.pi * ‖p‖ - R) / (2 * ε) / ‖p‖) • p
    ε * ‖y‖ ^ 2 + R * ‖y‖ - 2 * Real.pi * inner (𝕜 := ℝ) p y =
      -(2 * Real.pi * ‖p‖ - R) ^ 2 / (4 * ε) := by
  dsimp only
  have ht : 0 ≤ (2 * Real.pi * ‖p‖ - R) / (2 * ε) / ‖p‖ :=
    div_nonneg (div_nonneg hδ (by positivity)) hp.le
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht, inner_smul_right,
    real_inner_self_eq_norm_sq]
  field_simp
  ring

/-- A one-dimensional contour shift can be integrated over arbitrary remaining coordinates. -/
theorem parameterized_contour_shift {X : Type*} [MeasurableSpace X] (μ : Measure X)
    [SigmaFinite μ] (f : X → ℂ → ℂ) (T : ℝ)
    (hf : ∀ x, Differentiable ℂ (f x))
    (hdecay : ∀ x, ∃ C : ℝ, ∀ s t : ℝ, t ∈ uIcc 0 T →
      ‖f x ((s : ℂ) + (t : ℂ) * Complex.I)‖ ≤ C / (1 + s ^ 2))
    (h0 : Integrable (fun p : X × ℝ => f p.1 p.2) (μ.prod volume))
    (hT : Integrable (fun p : X × ℝ => f p.1 ((p.2 : ℂ) + (T : ℂ) * Complex.I))
      (μ.prod volume)) :
    (∫ p : X × ℝ, f p.1 p.2 ∂μ.prod volume) =
      ∫ p : X × ℝ, f p.1 ((p.2 : ℂ) + (T : ℂ) * Complex.I) ∂μ.prod volume := by
  rw [integral_prod _ h0, integral_prod _ hT]
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by
    obtain ⟨C, hC⟩ := hdecay x
    exact horizontal_contour_shift_any (hf x) T C hC

/-- Fubini transports a contour shift through any chosen coordinate of a finite-dimensional
real frequency integral. -/
theorem fin_coordinate_contour_shift {n : ℕ} (j : Fin (n + 1))
    (f : (Fin n → ℝ) → ℂ → ℂ) (T : ℝ)
    (hf : ∀ v, Differentiable ℂ (f v))
    (hdecay : ∀ v, ∃ C : ℝ, ∀ s t : ℝ, t ∈ uIcc 0 T →
      ‖f v ((s : ℂ) + (t : ℂ) * Complex.I)‖ ≤ C / (1 + s ^ 2))
    (h0 : Integrable (fun x : Fin (n + 1) → ℝ => f (fun k => x (j.succAbove k)) (x j)))
    (hT : Integrable (fun x : Fin (n + 1) → ℝ =>
      f (fun k => x (j.succAbove k)) ((x j : ℂ) + (T : ℂ) * Complex.I))) :
    (∫ x : Fin (n + 1) → ℝ, f (fun k => x (j.succAbove k)) (x j)) =
      ∫ x : Fin (n + 1) → ℝ,
        f (fun k => x (j.succAbove k)) ((x j : ℂ) + (T : ℂ) * Complex.I) := by
  let e := (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) j).symm
  have he : MeasurePreserving e :=
    (volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) j).symm
  have h0p : Integrable (fun p : ℝ × (Fin n → ℝ) => f p.2 p.1) := by
    simpa only [e, Function.comp_def, MeasurableEquiv.piFinSuccAbove_symm_apply,
      Fin.insertNthEquiv, Equiv.coe_fn_mk, Fin.insertNth_apply_same,
      Fin.insertNth_apply_succAbove] using
      (he.integrable_comp_emb e.measurableEmbedding).mpr h0
  have hTp : Integrable (fun p : ℝ × (Fin n → ℝ) =>
      f p.2 ((p.1 : ℂ) + (T : ℂ) * Complex.I)) := by
    simpa only [e, Function.comp_def, MeasurableEquiv.piFinSuccAbove_symm_apply,
      Fin.insertNthEquiv, Equiv.coe_fn_mk, Fin.insertNth_apply_same,
      Fin.insertNth_apply_succAbove] using
      (he.integrable_comp_emb e.measurableEmbedding).mpr hT
  rw [← he.integral_comp' (fun x : Fin (n + 1) → ℝ =>
    f (fun k => x (j.succAbove k)) (x j)),
    ← he.integral_comp' (fun x : Fin (n + 1) → ℝ =>
      f (fun k => x (j.succAbove k)) ((x j : ℂ) + (T : ℂ) * Complex.I))]
  simp only [e, MeasurableEquiv.piFinSuccAbove_symm_apply,
    Fin.insertNthEquiv, Equiv.coe_fn_mk, Fin.insertNth_apply_same,
    Fin.insertNth_apply_succAbove, Measure.volume_eq_prod]
  rw [integral_prod_symm _ h0p, integral_prod_symm _ hTp]
  apply integral_congr_ae
  exact Eventually.of_forall fun v => by
    obtain ⟨C, hC⟩ := hdecay v
    exact horizontal_contour_shift_any (hf v) T C hC

/-- The shifted inverse integrand separates into an integrable real Gaussian weight and a
factor depending only on the imaginary displacement. -/
theorem gaussian_inverse_shift_norm_le_product {d N : ℕ} {F : ComplexEuclidean d → ℂ}
    {A C R : ℝ} (hF : Differentiable ℂ F) (hA : 0 ≤ A) (hC : 0 ≤ C) (hR : 0 ≤ R)
    (htype : ∀ z, ‖F z‖ ≤ A * Real.exp (R * ‖z‖))
    (hreal : ∀ x, ‖F (realToComplex x)‖ ≤ C * (1 + ‖x‖) ^ N)
    (ε : ℝ) (p x y : Euclidean d) :
    ‖(F (realToComplex x + Complex.I • realToComplex y) *
        complexGaussianDamping ε (realToComplex x + Complex.I • realToComplex y)) *
      complexInverseFourierKernel p (realToComplex x + Complex.I • realToComplex y)‖ ≤
      (C * 2 ^ N * (1 + ‖y‖) ^ N *
        Real.exp (ε * ‖y‖ ^ 2 + R * ‖y‖ - 2 * Real.pi * inner (𝕜 := ℝ) p y)) *
          ((1 + ‖x‖) ^ N * Real.exp (-ε * ‖x‖ ^ 2)) := by
  apply (gaussian_inverse_shift_norm_le hF hA hC hR htype hreal ε p x y).trans
  have hp : (1 + ‖x‖ + ‖y‖) ^ N ≤ ((1 + ‖x‖) * (1 + ‖y‖)) ^ N := by
    apply pow_le_pow_left₀ (by positivity)
    nlinarith [mul_nonneg (norm_nonneg x) (norm_nonneg y)]
  calc
    _ ≤ C * 2 ^ N * ((1 + ‖x‖) * (1 + ‖y‖)) ^ N *
        Real.exp (-ε * ‖x‖ ^ 2 + ε * ‖y‖ ^ 2 + R * ‖y‖ -
          2 * Real.pi * inner (𝕜 := ℝ) p y) := by gcongr
    _ = _ := by
      rw [mul_pow]
      have hexp : Real.exp (-ε * ‖x‖ ^ 2 + ε * ‖y‖ ^ 2 + R * ‖y‖ -
          2 * Real.pi * inner (𝕜 := ℝ) p y) =
          Real.exp (ε * ‖y‖ ^ 2 + R * ‖y‖ - 2 * Real.pi * inner (𝕜 := ℝ) p y) *
            Real.exp (-ε * ‖x‖ ^ 2) := by
        rw [← Real.exp_add]
        congr 1
        ring
      rw [hexp]
      ring

/-- Every imaginary shift of the Gaussian regularized inverse integrand is absolutely integrable. -/
theorem gaussian_inverse_shift_integrable {d N : ℕ} {F : ComplexEuclidean d → ℂ}
    {A C R : ℝ} (hF : Differentiable ℂ F) (hA : 0 ≤ A) (hC : 0 ≤ C) (hR : 0 ≤ R)
    (htype : ∀ z, ‖F z‖ ≤ A * Real.exp (R * ‖z‖))
    (hreal : ∀ x, ‖F (realToComplex x)‖ ≤ C * (1 + ‖x‖) ^ N)
    {ε : ℝ} (hε : 0 < ε) (p y : Euclidean d) :
    Integrable (fun x =>
      (F (realToComplex x + Complex.I • realToComplex y) *
        complexGaussianDamping ε (realToComplex x + Complex.I • realToComplex y)) *
      complexInverseFourierKernel p (realToComplex x + Complex.I • realToComplex y)) := by
  apply ((polynomial_gaussian_integrable (d := d) N hε).const_mul
    (C * 2 ^ N * (1 + ‖y‖) ^ N *
      Real.exp (ε * ‖y‖ ^ 2 + R * ‖y‖ - 2 * Real.pi * inner (𝕜 := ℝ) p y))).mono'
  · have hemb : Continuous (realToComplex : Euclidean d → ComplexEuclidean d) :=
      (PiLp.continuous_equiv_symm 2 _).comp (continuous_pi fun j => by
        change Continuous (fun x : Euclidean d => (x j : ℂ))
        fun_prop)
    have hshift : Continuous (fun x : Euclidean d =>
        realToComplex x + Complex.I • realToComplex y) := hemb.add continuous_const
    apply Continuous.aestronglyMeasurable
    apply ((hF.continuous.comp hshift).mul ?_).mul ?_
    · unfold complexGaussianDamping gaussianQuadratic
      fun_prop
    · unfold complexInverseFourierKernel
      exact ((fourierPhaseCLM p).continuous.comp hshift).neg.cexp
  · exact Eventually.of_forall fun x =>
      gaussian_inverse_shift_norm_le_product hF hA hC hR htype hreal ε p x y

/-- A positive Gaussian dominates a linear exponential, with half its decay rate left over. -/
theorem linear_exponential_gaussian_bound {ε L r : ℝ} (hε : 0 < ε) :
    Real.exp (L * r - ε * r ^ 2) ≤
      Real.exp (L ^ 2 / (2 * ε)) * Real.exp (-(ε / 2) * r ^ 2) := by
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hden : 0 < 2 * ε := by positivity
  have hgoal : 2 * ε * (L * r - ε * r ^ 2) ≤
      2 * ε * (L ^ 2 / (2 * ε) + -(ε / 2) * r ^ 2) := by
    have hcancel : 2 * ε * (L ^ 2 / (2 * ε)) = L ^ 2 := by field_simp
    rw [mul_add, hcancel]
    nlinarith [sq_nonneg (ε * r - L)]
  exact (mul_le_mul_left hden).mp hgoal

/-- A uniform Gaussian bound across a strip supplies the quadratic decay required by the
rectangle-contour argument. -/
theorem gaussian_strip_quadratic_decay {f : ℂ → ℂ} {ε K T : ℝ}
    (hε : 0 < ε) (hK : 0 ≤ K)
    (hbound : ∀ s t : ℝ, t ∈ uIcc 0 T →
      ‖f ((s : ℂ) + (t : ℂ) * Complex.I)‖ ≤ K * Real.exp (-ε * s ^ 2)) :
    ∃ C : ℝ, ∀ s t : ℝ, t ∈ uIcc 0 T →
      ‖f ((s : ℂ) + (t : ℂ) * Complex.I)‖ ≤ C / (1 + s ^ 2) := by
  let B : ℝ := (2 + 2 / ε) ^ 2 * ((2 : ℕ).factorial : ℝ) * Real.exp 1
  refine ⟨K * B, fun s t ht => ?_⟩
  apply (hbound s t ht).trans
  apply (le_div_iff₀ (by positivity : 0 < 1 + s ^ 2)).mpr
  have hpoly := polynomial_gaussian_bound 2 hε (abs_nonneg s)
  have hexp : Real.exp (-(ε / 2) * |s| ^ 2) ≤ 1 := by
    rw [← Real.exp_zero]
    apply Real.exp_le_exp.mpr
    exact mul_nonpos_of_nonpos_of_nonneg (by linarith) (sq_nonneg _)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hp : (1 + s ^ 2) * Real.exp (-ε * s ^ 2) ≤ B := by
    calc
      _ ≤ (1 + |s|) ^ 2 * Real.exp (-ε * |s| ^ 2) := by
        rw [sq_abs]
        gcongr
        nlinarith [abs_nonneg s, sq_abs s]
      _ ≤ B * Real.exp (-(ε / 2) * |s| ^ 2) := hpoly
      _ ≤ B := mul_le_of_le_one_right hB hexp
  nlinarith [mul_le_mul_of_nonneg_left hp hK]

/-- The holomorphic integrand whose real integral regularizes the inverse Fourier transform. -/
def gaussianInverseEntireIntegrand {d : ℕ} (F : ComplexEuclidean d → ℂ)
    (ε : ℝ) (p : Euclidean d) (z : ComplexEuclidean d) : ℂ :=
  (F z * complexGaussianDamping ε z) * complexInverseFourierKernel p z

/-- Gaussian regularization preserves complex differentiability. -/
theorem gaussianInverseEntireIntegrand_differentiable {d : ℕ} {F : ComplexEuclidean d → ℂ}
    (hF : Differentiable ℂ F) (ε : ℝ) (p : Euclidean d) :
    Differentiable ℂ (gaussianInverseEntireIntegrand F ε p) := by
  have hquad : Differentiable ℂ (gaussianQuadratic (d := d)) := by
    unfold gaussianQuadratic
    have hp (j : Fin d) : Differentiable ℂ (fun z : ComplexEuclidean d => z j ^ 2) := by
      have hproj : Differentiable ℂ (fun z : ComplexEuclidean d => z j) :=
        (PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin d => ℂ) j).differentiable
      exact hproj.pow 2
    exact Differentiable.sum (u := Finset.univ) (fun j _ => hp j)
  have hgauss : Differentiable ℂ (complexGaussianDamping (d := d) ε) :=
    (hquad.const_mul (-(ε : ℂ))).cexp
  exact (hF.mul hgauss).mul ((fourierPhaseCLM p).differentiable.neg.cexp)

/-- Total exponential type gives uniform Gaussian decay on each coordinate strip. -/
theorem gaussian_inverse_slice_bound {d : ℕ} {F : ComplexEuclidean d → ℂ}
    {A R ε b M s : ℝ} (hA : 0 ≤ A) (hR : 0 ≤ R) (hε : 0 < ε)
    (htype : ∀ z, ‖F z‖ ≤ A * Real.exp (R * ‖z‖)) (p x y : Euclidean d)
    (hx : ‖x‖ ≤ |s| + b) (hxsq : s ^ 2 ≤ ‖x‖ ^ 2) (hy : ‖y‖ ≤ M) :
    ‖gaussianInverseEntireIntegrand F ε p (realToComplex x + Complex.I • realToComplex y)‖ ≤
      (A * Real.exp (R * (b + M) + ε * M ^ 2 + 2 * Real.pi * ‖p‖ * M + R ^ 2 / (2 * ε))) *
        Real.exp (-(ε / 2) * s ^ 2) := by
  have hn : ‖realToComplex x + Complex.I • realToComplex y‖ ≤ |s| + b + M := by
    calc
      _ ≤ ‖realToComplex x‖ + ‖Complex.I • realToComplex y‖ := norm_add_le _ _
      _ = ‖x‖ + ‖y‖ := by simp [norm_smul]
      _ ≤ _ := add_le_add hx hy
  have hFnorm : ‖F (realToComplex x + Complex.I • realToComplex y)‖ ≤
      A * Real.exp (R * (|s| + b + M)) :=
    (htype _).trans (mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hn hR)) hA)
  have hgauss : Real.exp (-ε * ‖x‖ ^ 2 + ε * ‖y‖ ^ 2) ≤
      Real.exp (-ε * s ^ 2 + ε * M ^ 2) := by
    apply Real.exp_le_exp.mpr
    have hy2 := pow_le_pow_left₀ (norm_nonneg y) hy 2
    nlinarith [mul_le_mul_of_nonneg_left hxsq hε.le,
      mul_le_mul_of_nonneg_left hy2 hε.le]
  have hinner : -inner (𝕜 := ℝ) p y ≤ ‖p‖ * M := by
    exact ((neg_le_abs _).trans (abs_real_inner_le_norm p y)).trans
      (mul_le_mul_of_nonneg_left hy (norm_nonneg p))
  have hkernel : Real.exp (-2 * Real.pi * inner (𝕜 := ℝ) p y) ≤
      Real.exp (2 * Real.pi * ‖p‖ * M) := by
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_left hinner (show 0 ≤ 2 * Real.pi by positivity)]
  unfold gaussianInverseEntireIntegrand
  rw [norm_mul, norm_mul, complexGaussianDamping_shift_norm,
    complexInverseFourierKernel_shift_norm]
  calc
    _ ≤ (A * Real.exp (R * (|s| + b + M))) *
        Real.exp (-ε * s ^ 2 + ε * M ^ 2) * Real.exp (2 * Real.pi * ‖p‖ * M) := by gcongr
    _ = (A * Real.exp (R * (b + M) + ε * M ^ 2 + 2 * Real.pi * ‖p‖ * M)) *
        Real.exp (R * |s| - ε * |s| ^ 2) := by
      rw [sq_abs]
      have hexp : Real.exp (R * (|s| + b + M)) * Real.exp (-ε * s ^ 2 + ε * M ^ 2) *
          Real.exp (2 * Real.pi * ‖p‖ * M) =
          Real.exp (R * (b + M) + ε * M ^ 2 + 2 * Real.pi * ‖p‖ * M) *
            Real.exp (R * |s| - ε * s ^ 2) := by
        rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
        congr 1
        ring
      rw [mul_assoc, mul_assoc, ← mul_assoc (Real.exp (R * (|s| + b + M))), hexp, mul_assoc]
      ring
    _ ≤ (A * Real.exp (R * (b + M) + ε * M ^ 2 + 2 * Real.pi * ‖p‖ * M)) *
        (Real.exp (R ^ 2 / (2 * ε)) * Real.exp (-(ε / 2) * |s| ^ 2)) := by
      gcongr
      exact linear_exponential_gaussian_bound hε
    _ = _ := by
      rw [sq_abs, ← mul_assoc, mul_assoc A, ← Real.exp_add]

/-- A complex affine line varying a single frequency coordinate. -/
def coordinateContourPoint {d : ℕ} (j : Fin d) (x y : Euclidean d) (z : ℂ) :
    ComplexEuclidean d :=
  realToComplex x + Complex.I • realToComplex y + z • EuclideanSpace.single j (1 : ℂ)

/-- Real and imaginary parts of a coordinate line are real coordinate displacements. -/
theorem coordinateContourPoint_real_imag {d : ℕ} (j : Fin d) (x y : Euclidean d) (s t : ℝ) :
    coordinateContourPoint j x y ((s : ℂ) + (t : ℂ) * Complex.I) =
      realToComplex (x + EuclideanSpace.single j s) +
        Complex.I • realToComplex (y + EuclideanSpace.single j t) := by
  ext k
  simp only [coordinateContourPoint, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul,
    realToComplex_apply, EuclideanSpace.single_apply, Complex.ofReal_add]
  split_ifs <;> simp
  ring

/-- The coordinate affine line is complex differentiable. -/
theorem coordinateContourPoint_differentiable {d : ℕ} (j : Fin d) (x y : Euclidean d) :
    Differentiable ℂ (coordinateContourPoint j x y) := by
  have hid : Differentiable ℂ (fun z : ℂ => z) := differentiable_id
  have hc : Differentiable ℂ (fun _ : ℂ => realToComplex x + Complex.I • realToComplex y) :=
    differentiable_const _
  exact hc.add (hid.smul_const (EuclideanSpace.single j (1 : ℂ)))

/-- The actual regularized inverse integrand satisfies the uniform coordinate-strip decay
required by the Cauchy rectangle theorem. -/
theorem gaussian_inverse_coordinate_strip_decay {d : ℕ} {F : ComplexEuclidean d → ℂ}
    {A R ε : ℝ} (hA : 0 ≤ A) (hR : 0 ≤ R) (hε : 0 < ε)
    (htype : ∀ z, ‖F z‖ ≤ A * Real.exp (R * ‖z‖)) (p : Euclidean d)
    (j : Fin d) (x y : Euclidean d) (hx : x j = 0) (T : ℝ) :
    ∃ C : ℝ, ∀ s t : ℝ, t ∈ uIcc 0 T →
      ‖gaussianInverseEntireIntegrand F ε p (coordinateContourPoint j x y
        ((s : ℂ) + (t : ℂ) * Complex.I))‖ ≤ C / (1 + s ^ 2) := by
  let M := ‖y‖ + |T|
  let K := A * Real.exp (R * (‖x‖ + M) + ε * M ^ 2 + 2 * Real.pi * ‖p‖ * M + R ^ 2 / (2 * ε))
  apply gaussian_strip_quadratic_decay
    (f := fun z => gaussianInverseEntireIntegrand F ε p (coordinateContourPoint j x y z))
    (K := K) (show 0 < ε / 2 by positivity) (show 0 ≤ K by positivity)
  intro s t ht
  rw [coordinateContourPoint_real_imag]
  have hxs : ‖x + EuclideanSpace.single j s‖ ≤ |s| + ‖x‖ := by
    simpa only [EuclideanSpace.norm_single, Real.norm_eq_abs, add_comm] using
      norm_add_le x (EuclideanSpace.single j s)
  have hsq : s ^ 2 ≤ ‖x + EuclideanSpace.single j s‖ ^ 2 := by
    have hn := PiLp.norm_apply_le (x + EuclideanSpace.single j s) j
    simp only [PiLp.add_apply, EuclideanSpace.single_apply, if_pos rfl, hx, zero_add,
      Real.norm_eq_abs] at hn
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg s) hn 2
  have hyt : ‖y + EuclideanSpace.single j t‖ ≤ M := by
    have habs : |t| ≤ |T| := by simpa only [sub_zero] using abs_sub_left_of_mem_uIcc ht
    calc
      _ ≤ ‖y‖ + ‖EuclideanSpace.single j t‖ := norm_add_le _ _
      _ = ‖y‖ + |t| := by simp [Real.norm_eq_abs]
      _ ≤ M := add_le_add_left habs _
  exact gaussian_inverse_slice_bound hA hR hε htype p
    (x + EuclideanSpace.single j s) (y + EuclideanSpace.single j t) hxs hsq hyt

/-- Insert the zero coordinate needed to parameterize a coordinate contour. -/
def coordinateZeroInsert {n : ℕ} (j : Fin (n + 1)) (v : Fin n → ℝ) : Euclidean (n + 1) :=
  (WithLp.equiv 2 (Fin (n + 1) → ℝ)).symm (j.insertNth 0 v)

@[simp] theorem coordinateZeroInsert_same {n : ℕ} (j : Fin (n + 1)) (v : Fin n → ℝ) :
    coordinateZeroInsert j v j = 0 := by simp [coordinateZeroInsert]

@[simp] theorem coordinateZeroInsert_succAbove {n : ℕ} (j : Fin (n + 1))
    (v : Fin n → ℝ) (k : Fin n) :
    coordinateZeroInsert j v (j.succAbove k) = v k := by simp [coordinateZeroInsert]

/-- Reconstruct the full real frequency vector from its contour coordinate and remaining coordinates. -/
theorem coordinateContourPoint_reconstruct {n : ℕ} (j : Fin (n + 1))
    (x : Fin (n + 1) → ℝ) (y : Euclidean (n + 1)) (T : ℝ) :
    coordinateContourPoint j (coordinateZeroInsert j (fun k => x (j.succAbove k))) y
        ((x j : ℂ) + (T : ℂ) * Complex.I) =
      realToComplex ((WithLp.equiv 2 (Fin (n + 1) → ℝ)).symm x) +
        Complex.I • realToComplex (y + EuclideanSpace.single j T) := by
  rw [coordinateContourPoint_real_imag]
  congr 1
  apply congrArg realToComplex
  apply PiLp.ext
  exact j.forall_iff_succAbove.mpr ⟨by simp, fun k => by
    simp only [PiLp.add_apply, coordinateZeroInsert_succAbove, EuclideanSpace.single_apply,
      Fin.succAbove_ne, if_false, add_zero, WithLp.equiv_symm_pi_apply]⟩

/-- The Gaussian regularized inverse integral can be shifted through one actual frequency
coordinate, with all integrability and strip-decay hypotheses discharged. -/
theorem gaussian_inverse_coordinate_shift {n N : ℕ} {F : ComplexEuclidean (n + 1) → ℂ}
    {A C R ε : ℝ} (hF : Differentiable ℂ F) (hA : 0 ≤ A) (hC : 0 ≤ C) (hR : 0 ≤ R)
    (htype : ∀ z, ‖F z‖ ≤ A * Real.exp (R * ‖z‖))
    (hreal : ∀ x, ‖F (realToComplex x)‖ ≤ C * (1 + ‖x‖) ^ N)
    (hε : 0 < ε) (p y : Euclidean (n + 1)) (j : Fin (n + 1)) (T : ℝ) :
    (∫ x, gaussianInverseEntireIntegrand F ε p (realToComplex x + Complex.I • realToComplex y)) =
      ∫ x, gaussianInverseEntireIntegrand F ε p
        (realToComplex x + Complex.I • realToComplex (y + EuclideanSpace.single j T)) := by
  let e := EuclideanSpace.measurableEquiv (Fin (n + 1))
  have he := (EuclideanSpace.volume_preserving_measurableEquiv (Fin (n + 1))).symm
  let f : (Fin n → ℝ) → ℂ → ℂ := fun v z =>
    gaussianInverseEntireIntegrand F ε p (coordinateContourPoint j (coordinateZeroInsert j v) y z)
  have hslice (v : Fin n → ℝ) : Differentiable ℂ (f v) :=
    (gaussianInverseEntireIntegrand_differentiable hF ε p).comp
      (coordinateContourPoint_differentiable j (coordinateZeroInsert j v) y)
  have hstrip (v : Fin n → ℝ) : ∃ B : ℝ, ∀ s t : ℝ, t ∈ uIcc 0 T →
      ‖f v ((s : ℂ) + (t : ℂ) * Complex.I)‖ ≤ B / (1 + s ^ 2) :=
    gaussian_inverse_coordinate_strip_decay hA hR hε htype p j (coordinateZeroInsert j v) y
      (coordinateZeroInsert_same j v) T
  have hpoint (x : Fin (n + 1) → ℝ) (t : ℝ) :
      f (fun k => x (j.succAbove k)) ((x j : ℂ) + (t : ℂ) * Complex.I) =
        gaussianInverseEntireIntegrand F ε p
          (realToComplex (e.symm x) + Complex.I • realToComplex (y + EuclideanSpace.single j t)) := by
    dsimp only [f]
    rw [coordinateContourPoint_reconstruct]
    rfl
  have hzero : EuclideanSpace.single j (0 : ℝ) = 0 := by ext k; simp [EuclideanSpace.single_apply]
  have hpoint0 (x : Fin (n + 1) → ℝ) :
      f (fun k => x (j.succAbove k)) (x j) =
        gaussianInverseEntireIntegrand F ε p (realToComplex (e.symm x) + Complex.I • realToComplex y) := by
    simpa only [Complex.ofReal_zero, zero_mul, add_zero, hzero] using hpoint x 0
  have hInt (v : Euclidean (n + 1)) : Integrable (fun x : Fin (n + 1) → ℝ =>
      gaussianInverseEntireIntegrand F ε p (realToComplex (e.symm x) + Complex.I • realToComplex v)) := by
    exact (he.integrable_comp_emb e.symm.measurableEmbedding).mpr
      (gaussian_inverse_shift_integrable hF hA hC hR htype hreal hε p v)
  have h0 : Integrable (fun x : Fin (n + 1) → ℝ => f (fun k => x (j.succAbove k)) (x j)) := by
    simp only [hpoint0]
    exact hInt y
  have hT : Integrable (fun x : Fin (n + 1) → ℝ =>
      f (fun k => x (j.succAbove k)) ((x j : ℂ) + (T : ℂ) * Complex.I)) := by
    simp only [hpoint]
    exact hInt (y + EuclideanSpace.single j T)
  have hshift := fin_coordinate_contour_shift j f T hslice hstrip h0 hT
  simp only [hpoint0, hpoint] at hshift
  have htransport (v : Euclidean (n + 1)) :
      (∫ x : Fin (n + 1) → ℝ, gaussianInverseEntireIntegrand F ε p
        (realToComplex (e.symm x) + Complex.I • realToComplex v)) =
      ∫ x : Euclidean (n + 1), gaussianInverseEntireIntegrand F ε p
        (realToComplex x + Complex.I • realToComplex v) := by
    simpa only [e] using he.integral_comp' (fun x : Euclidean (n + 1) =>
      gaussianInverseEntireIntegrand F ε p (realToComplex x + Complex.I • realToComplex v))
  rwa [htransport y, htransport (y + EuclideanSpace.single j T)] at hshift

/-- Iterating actual coordinate shifts gives a contour shift by an arbitrary imaginary
Euclidean vector for the Gaussian regularized inverse Fourier integral. -/
theorem gaussian_inverse_contour_shift {d N : ℕ} {F : ComplexEuclidean d → ℂ}
    {A C R ε : ℝ} (hF : Differentiable ℂ F) (hA : 0 ≤ A) (hC : 0 ≤ C) (hR : 0 ≤ R)
    (htype : ∀ z, ‖F z‖ ≤ A * Real.exp (R * ‖z‖))
    (hreal : ∀ x, ‖F (realToComplex x)‖ ≤ C * (1 + ‖x‖) ^ N)
    (hε : 0 < ε) (p y : Euclidean d) :
    (∫ x, gaussianInverseEntireIntegrand F ε p (realToComplex x)) =
      ∫ x, gaussianInverseEntireIntegrand F ε p (realToComplex x + Complex.I • realToComplex y) := by
  let J : Euclidean d → ℂ := fun v => ∫ x, gaussianInverseEntireIntegrand F ε p
    (realToComplex x + Complex.I • realToComplex v)
  have hstep (v : Euclidean d) (j : Fin d) : J v = J (v + EuclideanSpace.single j (y j)) := by
    cases d with
    | zero => exact Fin.elim0 j
    | succ n => exact gaussian_inverse_coordinate_shift hF hA hC hR htype hreal hε p v j (y j)
  have hsum (S : Finset (Fin d)) : J 0 = J (∑ j ∈ S, EuclideanSpace.single j (y j)) := by
    induction S using Finset.induction_on with
    | empty => simp
    | @insert j S hj ih =>
      rw [Finset.sum_insert hj]
      simpa only [add_comm] using ih.trans (hstep (∑ k ∈ S, EuclideanSpace.single k (y k)) j)
  have hy : (∑ j : Fin d, EuclideanSpace.single j (y j)) = y := by
    ext k
    change (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin d => ℝ) k)
      (∑ j : Fin d, EuclideanSpace.single j (y j)) = y k
    rw [map_sum]
    simp [EuclideanSpace.single_apply]
  have hzero : realToComplex (0 : Euclidean d) = 0 := by ext j; simp
  simpa only [hy, J, hzero, smul_zero, add_zero] using hsum Finset.univ

/-- The holomorphic Gaussian extends the real damping factor exactly. -/
theorem complexGaussianDamping_real {d : ℕ} (ε : ℝ≥0) (x : Euclidean d) :
    complexGaussianDamping ε (realToComplex x) = gaussianFrequencyDamping ε x := by
  have hquad : gaussianQuadratic (realToComplex x) = (‖x‖ ^ 2 : ℝ) := by
    simp only [gaussianQuadratic, realToComplex_apply, ← Complex.ofReal_pow,
      ← Complex.ofReal_sum, real_coordinate_square_sum]
  rw [complexGaussianDamping, hquad, gaussianFrequencyDamping]
  norm_cast

/-- The regularized inverse Fourier transform equals any of its imaginary-shifted
Gaussian integrals. -/
theorem gaussian_inverseFourier_eq_shifted_integral {d N : ℕ} {F : ComplexEuclidean d → ℂ}
    {A C R : ℝ} (hF : Differentiable ℂ F) (hA : 0 ≤ A) (hC : 0 ≤ C) (hR : 0 ≤ R)
    (htype : ∀ z, ‖F z‖ ≤ A * Real.exp (R * ‖z‖))
    (hreal : ∀ x, ‖F (realToComplex x)‖ ≤ C * (1 + ‖x‖) ^ N)
    {ε : ℝ≥0} (hε : 0 < ε) (p y : Euclidean d) :
    Real.fourierIntegralInv (fun x => F (realToComplex x) * gaussianFrequencyDamping ε x) p =
      ∫ x, gaussianInverseEntireIntegrand F ε p (realToComplex x + Complex.I • realToComplex y) := by
  rw [inverseFourier_kernel_integral]
  simp_rw [← complexGaussianDamping_real]
  exact gaussian_inverse_contour_shift hF hA hC hR htype hreal hε p y

/-- An explicit bound on the total polynomial Gaussian mass. -/
theorem polynomial_gaussian_integral_le {d : ℕ} (N : ℕ) {ε : ℝ} (hε : 0 < ε) :
    (∫ x : Euclidean d, (1 + ‖x‖) ^ N * Real.exp (-ε * ‖x‖ ^ 2)) ≤
      ((2 + 2 / ε) ^ N * (N.factorial : ℝ) * Real.exp 1) *
        (2 * Real.pi / ε) ^ ((d : ℝ) / 2) := by
  have hg : Integrable (fun x : Euclidean d => Real.exp (-(ε / 2) * ‖x‖ ^ 2)) := by
    simpa only [pow_zero, one_mul] using polynomial_gaussian_integrable (d := d) 0 (half_pos hε)
  have hbound := integral_mono (polynomial_gaussian_integrable (d := d) N hε)
    (hg.const_mul ((2 + 2 / ε) ^ N * (N.factorial : ℝ) * Real.exp 1))
    (fun x => polynomial_gaussian_bound N hε (norm_nonneg x))
  rw [integral_const_mul, GaussianFourier.integral_rexp_neg_mul_sq_norm (half_pos hε)] at hbound
  simpa only [finrank_euclideanSpace_fin, show Real.pi / (ε / 2) = 2 * Real.pi / ε by ring] using hbound

/-- For small damping widths, the polynomial Gaussian mass is bounded by a fixed inverse
integer power of the width. -/
theorem polynomial_gaussian_integral_le_inverse_power {d : ℕ} (N : ℕ) {ε : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1) :
    (∫ x : Euclidean d, (1 + ‖x‖) ^ N * Real.exp (-ε * ‖x‖ ^ 2)) ≤
      (4 ^ N * (N.factorial : ℝ) * Real.exp 1 * (2 * Real.pi) ^ d) * (ε⁻¹) ^ (N + d) := by
  apply (polynomial_gaussian_integral_le (d := d) N hε).trans
  have hK : 2 + 2 / ε ≤ 4 * ε⁻¹ := by
    have h : 2 + 2 / ε ≤ 4 / ε := by
      apply (le_div_iff₀ hε).mpr
      have heq : (2 + 2 / ε) * ε = 2 * ε + 2 := by field_simp
      rw [heq]
      linarith
    simpa only [div_eq_mul_inv] using h
  have hbase : 1 ≤ 2 * Real.pi / ε := by
    apply (le_div_iff₀ hε).mpr
    nlinarith [Real.two_le_pi]
  have hGauss : (2 * Real.pi / ε) ^ ((d : ℝ) / 2) ≤ (2 * Real.pi / ε) ^ d := by
    simpa only [Real.rpow_natCast] using Real.rpow_le_rpow_of_exponent_le hbase
      (show (d : ℝ) / 2 ≤ (d : ℝ) by linarith)
  calc
    _ ≤ ((4 * ε⁻¹) ^ N * (N.factorial : ℝ) * Real.exp 1) * (2 * Real.pi / ε) ^ d := by
      gcongr
    _ = _ := by rw [mul_pow, div_eq_mul_inv, mul_pow, pow_add]; ring

/-- Norm bound for a Gaussian inverse transform after any imaginary contour shift. -/
theorem gaussian_inverseFourier_shift_bound {d N : ℕ} {F : ComplexEuclidean d → ℂ}
    {A C R : ℝ} (hF : Differentiable ℂ F) (hA : 0 ≤ A) (hC : 0 ≤ C) (hR : 0 ≤ R)
    (htype : ∀ z, ‖F z‖ ≤ A * Real.exp (R * ‖z‖))
    (hreal : ∀ x, ‖F (realToComplex x)‖ ≤ C * (1 + ‖x‖) ^ N)
    {ε : ℝ≥0} (hε : 0 < ε) (p y : Euclidean d) :
    ‖Real.fourierIntegralInv (fun x => F (realToComplex x) * gaussianFrequencyDamping ε x) p‖ ≤
      (C * 2 ^ N * (1 + ‖y‖) ^ N *
        Real.exp ((ε : ℝ) * ‖y‖ ^ 2 + R * ‖y‖ - 2 * Real.pi * inner (𝕜 := ℝ) p y)) *
          (∫ x : Euclidean d, (1 + ‖x‖) ^ N * Real.exp (-(ε : ℝ) * ‖x‖ ^ 2)) := by
  rw [gaussian_inverseFourier_eq_shifted_integral hF hA hC hR htype hreal hε p y]
  have hweight := (polynomial_gaussian_integrable (d := d) N (show 0 < (ε : ℝ) from hε)).const_mul
    (C * 2 ^ N * (1 + ‖y‖) ^ N *
      Real.exp ((ε : ℝ) * ‖y‖ ^ 2 + R * ‖y‖ - 2 * Real.pi * inner (𝕜 := ℝ) p y))
  have hbound := norm_integral_le_of_norm_le hweight (Eventually.of_forall fun x =>
    gaussian_inverse_shift_norm_le_product hF hA hC hR htype hreal ε p x y)
  rwa [integral_const_mul] at hbound

/-- Norm of the imaginary vector optimizing Gaussian localization. -/
theorem gaussian_radial_shift_norm {d : ℕ} (p : Euclidean d) {ε R : ℝ}
    (hε : 0 < ε) (hp : 0 < ‖p‖) (hδ : 0 ≤ 2 * Real.pi * ‖p‖ - R) :
    ‖((2 * Real.pi * ‖p‖ - R) / (2 * ε) / ‖p‖) • p‖ =
      (2 * Real.pi * ‖p‖ - R) / (2 * ε) := by
  have ht : 0 ≤ (2 * Real.pi * ‖p‖ - R) / (2 * ε) / ‖p‖ := by positivity
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht, div_mul_cancel₀ _ hp.ne']

/-- The regularized inverse Fourier transform is exponentially small uniformly on each
bounded set separated from the Paley–Wiener support ball. -/
theorem gaussian_inverseFourier_uniform_localization_bound {d N : ℕ}
    {F : ComplexEuclidean d → ℂ} {A C R L a : ℝ}
    (hF : Differentiable ℂ F) (hA : 0 ≤ A) (hC : 0 ≤ C) (hR : 0 ≤ R) (hL : 0 ≤ L) (ha : 0 < a)
    (htype : ∀ z, ‖F z‖ ≤ A * Real.exp (R * ‖z‖))
    (hreal : ∀ x, ‖F (realToComplex x)‖ ≤ C * (1 + ‖x‖) ^ N)
    {ε : ℝ≥0} (hε : 0 < ε) (hε1 : (ε : ℝ) ≤ 1) (p : Euclidean d)
    (hpL : ‖p‖ ≤ L) (hgap : a ≤ 2 * Real.pi * ‖p‖ - R) :
    ‖Real.fourierIntegralInv (fun x => F (realToComplex x) * gaussianFrequencyDamping ε x) p‖ ≤
      (C * 2 ^ N * (1 + Real.pi * L) ^ N *
        (4 ^ N * (N.factorial : ℝ) * Real.exp 1 * (2 * Real.pi) ^ d)) *
          ((ε : ℝ)⁻¹) ^ (2 * N + d) * Real.exp (-(a ^ 2 / 4) / (ε : ℝ)) := by
  have hεr : 0 < (ε : ℝ) := hε
  have hδ : 0 ≤ 2 * Real.pi * ‖p‖ - R := ha.le.trans hgap
  have hp : 0 < ‖p‖ := by nlinarith [Real.pi_pos]
  let δ := 2 * Real.pi * ‖p‖ - R
  let y := (δ / (2 * (ε : ℝ)) / ‖p‖) • p
  have hynorm : ‖y‖ = δ / (2 * (ε : ℝ)) := gaussian_radial_shift_norm p hεr hp hδ
  have hexponent : (ε : ℝ) * ‖y‖ ^ 2 + R * ‖y‖ - 2 * Real.pi * inner (𝕜 := ℝ) p y =
      -δ ^ 2 / (4 * (ε : ℝ)) := gaussian_radial_shift_exponent p hεr hp hδ
  have hybound : 1 + ‖y‖ ≤ (1 + Real.pi * L) * (ε : ℝ)⁻¹ := by
    rw [hynorm]
    apply (mul_le_mul_right hεr).mp
    have heq : (1 + δ / (2 * (ε : ℝ))) * (ε : ℝ) = (ε : ℝ) + δ / 2 := by field_simp; ring
    rw [heq, mul_assoc, inv_mul_cancel₀ hεr.ne', mul_one]
    dsimp [δ]
    nlinarith [mul_le_mul_of_nonneg_left hpL Real.pi_pos.le]
  have hgap2 : a ^ 2 ≤ δ ^ 2 := pow_le_pow_left₀ ha.le hgap 2
  have hexp : Real.exp (-δ ^ 2 / (4 * (ε : ℝ))) ≤ Real.exp (-(a ^ 2 / 4) / (ε : ℝ)) := by
    apply Real.exp_le_exp.mpr
    have heq : -(a ^ 2 / 4) / (ε : ℝ) = -a ^ 2 / (4 * (ε : ℝ)) := by ring
    rw [heq]
    exact div_le_div_of_nonneg_right (neg_le_neg hgap2) (by positivity)
  have hbound := gaussian_inverseFourier_shift_bound hF hA hC hR htype hreal hε p y
  rw [hexponent] at hbound
  apply hbound.trans
  have hmass := polynomial_gaussian_integral_le_inverse_power (d := d) N hεr hε1
  have hpoly : (1 + ‖y‖) ^ N ≤ ((1 + Real.pi * L) * (ε : ℝ)⁻¹) ^ N :=
    pow_le_pow_left₀ (by positivity) hybound N
  have hlead : C * 2 ^ N * (1 + ‖y‖) ^ N * Real.exp (-δ ^ 2 / (4 * (ε : ℝ))) ≤
      C * 2 ^ N * ((1 + Real.pi * L) * (ε : ℝ)⁻¹) ^ N *
        Real.exp (-(a ^ 2 / 4) / (ε : ℝ)) :=
    mul_le_mul (mul_le_mul_of_nonneg_left hpoly (by positivity)) hexp
      (Real.exp_nonneg _) (by positivity)
  have hmass0 : 0 ≤ ∫ x : Euclidean d, (1 + ‖x‖) ^ N * Real.exp (-(ε : ℝ) * ‖x‖ ^ 2) :=
    integral_nonneg fun x => by positivity
  calc
    _ ≤ (C * 2 ^ N * ((1 + Real.pi * L) * (ε : ℝ)⁻¹) ^ N *
        Real.exp (-(a ^ 2 / 4) / (ε : ℝ))) *
        ((4 ^ N * (N.factorial : ℝ) * Real.exp 1 * (2 * Real.pi) ^ d) *
          ((ε : ℝ)⁻¹) ^ (N + d)) :=
      mul_le_mul hlead hmass hmass0 (by positivity)
    _ = _ := by
      rw [mul_pow, show 2 * N + d = N + (N + d) by omega, pow_add]
      ring

/-- The Paley–Wiener–Schwartz support direction: an entire function of finite total
exponential type and polynomial real-axis growth is the Fourier transform of an actual
tempered distribution supported in the corresponding Euclidean ball. -/
theorem paleyWiener_inverse_polynomialDistribution_supported {d N : ℕ}
    {F : ComplexEuclidean d → ℂ} {A C R : ℝ}
    (hF : Differentiable ℂ F) (hA : 0 ≤ A) (hC : 0 ≤ C) (hR : 0 ≤ R)
    (htype : ∀ z, ‖F z‖ ≤ A * Real.exp (R * ‖z‖))
    (hreal : ∀ x, ‖F (realToComplex x)‖ ≤ C * (1 + ‖x‖) ^ N)
    (hm : AEStronglyMeasurable (fun x => F (realToComplex x)) volume) :
    DistributionSupportedIn
      (distributionInverseFourier (polynomialDistribution (fun x => F (realToComplex x)) hC hreal hm))
      (Metric.closedBall (0 : Euclidean d) (R / (2 * Real.pi))) := by
  intro φ hφ hdisj
  change IsCompact (tsupport (φ : Euclidean d → ℂ)) at hφ
  have hgap (p : Euclidean d) (hp : p ∈ tsupport (φ : Euclidean d → ℂ)) :
      0 < 2 * Real.pi * ‖p‖ - R := by
    have hout : p ∉ Metric.closedBall (0 : Euclidean d) (R / (2 * Real.pi)) :=
      fun h => Set.disjoint_left.mp hdisj hp h
    have hn : R / (2 * Real.pi) < ‖p‖ := by
      simpa only [Metric.mem_closedBall, dist_zero_right, not_le] using hout
    have h := (div_lt_iff₀ (show 0 < 2 * Real.pi by positivity)).mp hn
    linarith
  obtain ⟨a, ha, hgapUniform⟩ := hφ.exists_forall_le'
    (by fun_prop : ContinuousOn (fun p : Euclidean d => 2 * Real.pi * ‖p‖ - R)
      (tsupport (φ : Euclidean d → ℂ))) hgap
  obtain ⟨L, hL, hnorm⟩ := hφ.isBounded.exists_pos_norm_le
  let B : ℝ := C * 2 ^ N * (1 + Real.pi * L) ^ N *
    (4 ^ N * (N.factorial : ℝ) * Real.exp 1 * (2 * Real.pi) ^ d)
  let J : ℝ := ∫ p : Euclidean d, ‖φ p‖
  let u : ℝ≥0 → TemperedDistribution d := fun ε =>
    distributionInverseFourier
      (gaussianRegularizedDistribution (fun x => F (realToComplex x)) hC hreal hm ε)
  have hpair (ε : ℝ≥0) (hε : 0 < ε) (hε1 : (ε : ℝ) ≤ 1) :
      ‖u ε φ‖ ≤ B * ((ε : ℝ)⁻¹) ^ (2 * N + d) * Real.exp (-(a ^ 2 / 4) / (ε : ℝ)) * J := by
    dsimp only [u]
    rw [inverseGaussianRegularizedDistribution_apply hC hreal hm hε]
    have hb := norm_integral_le_of_norm_le
      (μ := (volume : Measure (Euclidean d)))
      (f := fun p : Euclidean d =>
        Real.fourierIntegralInv (fun x => F (realToComplex x) * gaussianFrequencyDamping ε x) p * φ p)
      (φ.integrable.norm.const_mul
        (B * ((ε : ℝ)⁻¹) ^ (2 * N + d) * Real.exp (-(a ^ 2 / 4) / (ε : ℝ))))
      (Eventually.of_forall fun p => by
        rw [norm_mul]
        by_cases hp : φ p = 0
        · simp only [hp, norm_zero, mul_zero, le_refl]
        · have hpK : p ∈ tsupport (φ : Euclidean d → ℂ) := subset_tsupport _ hp
          exact mul_le_mul_of_nonneg_right
            (gaussian_inverseFourier_uniform_localization_bound hF hA hC hR hL.le ha
              htype hreal hε hε1 p (hnorm p hpK) (hgapUniform p hpK)) (norm_nonneg _))
    rwa [integral_const_mul] at hb
  have hnn : Tendsto (fun ε : ℝ => ε.toNNReal) (𝓝[>] 0) (𝓝 (0 : ℝ≥0)) := by
    simpa only [Real.toNNReal_zero] using
      (continuous_real_toNNReal.tendsto (0 : ℝ)).mono_left inf_le_left
  have hlimit := (inverseGaussianRegularizedDistribution_tendsto hC hreal hm φ).comp hnn
  have hzero : Tendsto (fun ε : ℝ => u ε.toNNReal φ) (𝓝[>] 0) (𝓝 0) := by
    apply squeeze_zero_norm'
    · filter_upwards [self_mem_nhdsWithin,
        (eventually_le_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono inf_le_left] with ε hε hε1
      have hεnn : 0 < ε.toNNReal := Real.toNNReal_pos.mpr hε
      have hεcoe := Real.coe_toNNReal ε hε.le
      simpa only [hεcoe] using hpair ε.toNNReal hεnn (by simpa only [hεcoe] using hε1)
    · have hsup := (gaussian_suppression_tendsto (2 * N + d)
        (show 0 < a ^ 2 / 4 by positivity)).const_mul B
      simpa only [mul_assoc, mul_zero, zero_mul] using hsup.mul_const J
  exact tendsto_nhds_unique hlimit hzero

/-- The finite-type Paley–Wiener–Schwartz existence theorem, in the interface used by
the complete-minimal analytic assembly. Every distribution and Fourier pairing is constructed. -/
theorem paleyWienerSchwartz {d : ℕ} {F : ComplexEuclidean d → ℂ}
    (hF : Differentiable ℂ F) (htype : FiniteExponentialType F)
    (hreal : ∃ N : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ x : Euclidean d, ‖F (realToComplex x)‖ ≤ C * (1 + ‖x‖) ^ N) :
    ∃ u : TemperedDistribution d, CompactlySupportedDistribution u ∧
      ∀ φ : SchwartzMap (Euclidean d) ℂ,
        distributionFourier u φ = ∫ x, F (realToComplex x) * φ x := by
  obtain ⟨A, R, hA, hR, htype⟩ := htype
  obtain ⟨N, C, hC, hreal⟩ := hreal
  have hemb : Continuous (realToComplex : Euclidean d → ComplexEuclidean d) :=
    (PiLp.continuous_equiv_symm 2 _).comp (continuous_pi fun j => by
      change Continuous (fun x : Euclidean d => (x j : ℂ))
      fun_prop)
  have hm : AEStronglyMeasurable (fun x => F (realToComplex x)) volume :=
    (hF.continuous.comp hemb).aestronglyMeasurable
  let u := distributionInverseFourier
    (polynomialDistribution (fun x => F (realToComplex x)) hC hreal hm)
  refine ⟨u, ⟨Metric.closedBall (0 : Euclidean d) (R / (2 * Real.pi)),
    isCompact_closedBall _ _, ?_⟩, ?_⟩
  · exact paleyWiener_inverse_polynomialDistribution_supported hF hA.le hC hR htype hreal hm
  · intro φ
    simp only [u, distributionFourier_inverseFourier, polynomialDistribution_apply]

end RieszEuclidean.CompleteMinimal
