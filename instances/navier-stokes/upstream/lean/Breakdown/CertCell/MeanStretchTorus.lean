import Breakdown.Cert.CoerciveStretchTorus

open MeasureTheory

noncomputable section

namespace Breakdown

namespace CertCell

namespace Bridge

namespace Internal.MeanStretch

open Coercive Coercive.Internal.ModeRotation Coercive.StretchTorusInternal

def waveArg (β : ℤ × ℤ) (τ φ : ℝ) : ℝ := 2 * Real.pi * β.1 * τ + β.2 * φ

def phase (β : ℤ × ℤ) (τ φ : ℝ) : ℂ := Complex.exp ((waveArg β τ φ : ℂ) * Complex.I)

def torusMode (ξ : ℤ × ℤ) (f : ℝ → ℝ → ℝ) : ℂ := modeAverage ξ (fun τ φ (_ : Unit) => f τ φ) ()

theorem expFactor_eq (ξ : ℤ × ℤ) (τ φ : ℝ) :
    expFactor ξ τ φ = Complex.exp (-((waveArg ξ τ φ : ℂ) * Complex.I)) := rfl

theorem norm_phase (β : ℤ × ℤ) (τ φ : ℝ) : ‖phase β τ φ‖ = 1 := by
  unfold phase
  rw [Complex.norm_exp_ofReal_mul_I]

theorem continuous_phase (β : ℤ × ℤ) : Continuous (fun p : ℝ × ℝ => phase β p.1 p.2) := by
  unfold phase waveArg
  fun_prop

theorem waveArg_sub (ξ β : ℤ × ℤ) (τ φ : ℝ) : waveArg (ξ - β) τ φ = waveArg ξ τ φ - waveArg β τ φ := by
  simp only [waveArg, Prod.fst_sub, Prod.snd_sub, Int.cast_sub]
  ring

theorem waveArg_add (ξ β : ℤ × ℤ) (τ φ : ℝ) : waveArg (ξ + β) τ φ = waveArg ξ τ φ + waveArg β τ φ := by
  simp only [waveArg, Prod.fst_add, Prod.snd_add, Int.cast_add]
  ring

theorem waveArg_neg (ξ : ℤ × ℤ) (τ φ : ℝ) : waveArg (-ξ) τ φ = -waveArg ξ τ φ := by
  simp only [waveArg, Prod.fst_neg, Prod.snd_neg, Int.cast_neg]
  ring

theorem expFactor_mul_phase (ξ β : ℤ × ℤ) (τ φ : ℝ) :
    expFactor ξ τ φ * phase β τ φ = expFactor (ξ - β) τ φ := by
  rw [expFactor_eq, expFactor_eq, phase, ← Complex.exp_add, waveArg_sub]
  congr 1
  push_cast
  ring

theorem expFactor_mul_expFactor (ξ β : ℤ × ℤ) (τ φ : ℝ) :
    expFactor ξ τ φ * expFactor β τ φ = expFactor (ξ + β) τ φ := by
  rw [expFactor_eq, expFactor_eq, expFactor_eq, ← Complex.exp_add, waveArg_add]
  congr 1
  push_cast
  ring

theorem conj_expFactor (ξ : ℤ × ℤ) (τ φ : ℝ) :
    (starRingEnd ℂ) (expFactor ξ τ φ) = expFactor (-ξ) τ φ := by
  rw [expFactor_eq, expFactor_eq, ← Complex.exp_conj, waveArg_neg]
  congr 1
  simp only [map_neg, map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

theorem integrable_expFactor_mul (ξ : ℤ × ℤ) {g : ℝ × ℝ → ℝ} (hg : Integrable g boxMeasure) :
    Integrable (fun p : ℝ × ℝ => expFactor ξ p.1 p.2 * ((g p : ℝ) : ℂ)) boxMeasure := by
  refine hg.norm.mono' ((continuous_expFactor ξ).aestronglyMeasurable.mul
    (Complex.continuous_ofReal.comp_aestronglyMeasurable hg.1)) ?_
  refine Filter.Eventually.of_forall fun p => ?_
  simp only [norm_mul, norm_expFactor, one_mul, Complex.norm_real, le_refl]

theorem integrable_phase_mul (β : ℤ × ℤ) {g : ℝ × ℝ → ℝ} (hg : Integrable g boxMeasure) :
    Integrable (fun p : ℝ × ℝ => phase β p.1 p.2 * ((g p : ℝ) : ℂ)) boxMeasure := by
  refine hg.norm.mono' ((continuous_phase β).aestronglyMeasurable.mul
    (Complex.continuous_ofReal.comp_aestronglyMeasurable hg.1)) ?_
  refine Filter.Eventually.of_forall fun p => ?_
  simp only [norm_mul, norm_phase, one_mul, Complex.norm_real, le_refl]

theorem torusMode_eq_box (ξ : ℤ × ℤ) (f : ℝ → ℝ → ℝ)
    (hf : Integrable (fun p : ℝ × ℝ => f p.1 p.2) boxMeasure) :
    torusMode ξ f = (1 / (2 * Real.pi) : ℂ) * ∫ p, expFactor ξ p.1 p.2 * ((f p.1 p.2 : ℝ) : ℂ) ∂boxMeasure := by
  unfold torusMode
  rw [modeAverage_eq, iter_eq_prod (fun τ φ => expFactor ξ τ φ * ((f τ φ : ℝ) : ℂ))
    (integrable_expFactor_mul ξ hf)]

theorem torusMode_neg (ξ : ℤ × ℤ) (f : ℝ → ℝ → ℝ)
    (hf : Integrable (fun p : ℝ × ℝ => f p.1 p.2) boxMeasure) :
    torusMode (-ξ) f = (starRingEnd ℂ) (torusMode ξ f) := by
  rw [torusMode_eq_box _ f hf, torusMode_eq_box _ f hf, map_mul, ← integral_conj]
  congr 1
  · simp only [map_div₀, map_one, map_mul, Complex.conj_ofReal, map_ofNat]
  · congr 1
    funext p
    rw [map_mul, Complex.conj_ofReal, conj_expFactor]

theorem ofReal_cos_eq (x : ℝ) :
    ((Real.cos x : ℝ) : ℂ) = (Complex.exp ((x : ℂ) * Complex.I) + Complex.exp (-((x : ℂ) * Complex.I))) / 2 := by
  rw [Complex.ofReal_cos, Complex.cos, neg_mul]

theorem ofReal_sin_eq (x : ℝ) :
    ((Real.sin x : ℝ) : ℂ) =
      (Complex.exp (-((x : ℂ) * Complex.I)) - Complex.exp ((x : ℂ) * Complex.I)) * Complex.I / 2 := by
  rw [Complex.ofReal_sin, Complex.sin, neg_mul]

theorem integrable_mul_trig (f : ℝ × ℝ → ℝ) (hf : Integrable f boxMeasure) (c : ℝ → ℝ) (hc : Continuous c)
    (hb : ∀ x, |c x| ≤ 1) (β : ℤ × ℤ) :
    Integrable (fun p : ℝ × ℝ => f p * c (waveArg β p.1 p.2)) boxMeasure := by
  have hw : Continuous (fun p : ℝ × ℝ => waveArg β p.1 p.2) := by
    unfold waveArg
    fun_prop
  refine hf.norm.mono' (hf.1.mul (hc.comp hw).aestronglyMeasurable) ?_
  refine Filter.Eventually.of_forall fun p => ?_
  rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
  exact mul_le_of_le_one_right (abs_nonneg _) (hb _)

theorem torusMode_mul_cos (ξ β : ℤ × ℤ) (f : ℝ → ℝ → ℝ)
    (hf : Integrable (fun p : ℝ × ℝ => f p.1 p.2) boxMeasure) :
    torusMode ξ (fun τ φ => f τ φ * Real.cos (waveArg β τ φ))
      = (torusMode (ξ - β) f + torusMode (ξ + β) f) / 2 := by
  have hfc := integrable_mul_trig (fun p => f p.1 p.2) hf Real.cos Real.continuous_cos Real.abs_cos_le_one β
  rw [torusMode_eq_box _ _ hfc, torusMode_eq_box _ f hf, torusMode_eq_box _ f hf, ← mul_add,
    ← integral_add (integrable_expFactor_mul _ hf) (integrable_expFactor_mul _ hf), mul_div_assoc,
    ← integral_div]
  congr 1
  congr 1
  funext p
  rw [Complex.ofReal_mul, ofReal_cos_eq, ← expFactor_mul_phase, ← expFactor_mul_expFactor]
  rw [show Complex.exp (-((waveArg β p.1 p.2 : ℂ) * Complex.I)) = expFactor β p.1 p.2 from rfl]
  unfold phase
  ring

theorem torusMode_mul_sin (ξ β : ℤ × ℤ) (f : ℝ → ℝ → ℝ)
    (hf : Integrable (fun p : ℝ × ℝ => f p.1 p.2) boxMeasure) :
    torusMode ξ (fun τ φ => f τ φ * Real.sin (waveArg β τ φ))
      = (torusMode (ξ + β) f - torusMode (ξ - β) f) * Complex.I / 2 := by
  have hfs := integrable_mul_trig (fun p => f p.1 p.2) hf Real.sin Real.continuous_sin Real.abs_sin_le_one β
  rw [torusMode_eq_box _ _ hfs, torusMode_eq_box _ f hf, torusMode_eq_box _ f hf, ← mul_sub,
    ← integral_sub (integrable_expFactor_mul _ hf) (integrable_expFactor_mul _ hf), mul_assoc, mul_div_assoc,
    ← integral_mul_const, ← integral_div]
  congr 1
  congr 1
  funext p
  rw [Complex.ofReal_mul, ofReal_sin_eq, ← expFactor_mul_phase, ← expFactor_mul_expFactor]
  rw [show Complex.exp (-((waveArg β p.1 p.2 : ℂ) * Complex.I)) = expFactor β p.1 p.2 from rfl]
  unfold phase
  ring

theorem hasSum_normSq_torusMode (hTorus : TorusSquareSumHolds) (f : ℝ → ℝ → ℝ)
    (hf : MemLp (fun p : ℝ × ℝ => f p.1 p.2) 2 boxMeasure) :
    Summable (fun ξ : ℤ × ℤ => ‖torusMode ξ f‖ ^ 2) := by
  have h := (torus_hasSum_mul hTorus hf hf).summable
  refine h.congr fun ξ => ?_
  unfold torusMode
  rw [Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]

theorem summable_norm_pairing (hTorus : TorusSquareSumHolds) (f h : ℝ → ℝ → ℝ)
    (hf : MemLp (fun p : ℝ × ℝ => f p.1 p.2) 2 boxMeasure) (hh : MemLp (fun p : ℝ × ℝ => h p.1 p.2) 2 boxMeasure)
    (β : ℤ × ℤ) :
    Summable (fun ξ : ℤ × ℤ => ‖torusMode ξ f‖ * ‖torusMode (ξ + β) h‖) := by
  have h1 := hasSum_normSq_torusMode hTorus f hf
  have h2 : Summable (fun ξ : ℤ × ℤ => ‖torusMode (ξ + β) h‖ ^ 2) :=
    (Equiv.addRight β).summable_iff.2 (hasSum_normSq_torusMode hTorus h hh)
  refine Summable.of_nonneg_of_le (fun ξ => mul_nonneg (norm_nonneg _) (norm_nonneg _))
    (fun ξ => ?_) ((h1.add h2).div_const 2)
  nlinarith [sq_nonneg (‖torusMode ξ f‖ - ‖torusMode (ξ + β) h‖)]

theorem hasSum_pairing (hTorus : TorusSquareSumHolds) (f h : ℝ → ℝ → ℝ)
    (hf : MemLp (fun p : ℝ × ℝ => f p.1 p.2) 2 boxMeasure) (hh : MemLp (fun p : ℝ × ℝ => h p.1 p.2) 2 boxMeasure)
    (β : ℤ × ℤ) :
    HasSum (fun ξ : ℤ × ℤ => torusMode ξ f * (starRingEnd ℂ) (torusMode (ξ + β) h))
      ((1 / (2 * Real.pi) : ℂ) * ∫ p, phase β p.1 p.2 * ((f p.1 p.2 * h p.1 p.2 : ℝ) : ℂ) ∂boxMeasure) := by
  have hfi : Integrable (fun p : ℝ × ℝ => f p.1 p.2) boxMeasure := hf.integrable one_le_two
  have hhi : Integrable (fun p : ℝ × ℝ => h p.1 p.2) boxMeasure := hh.integrable one_le_two
  set A : ℤ × ℤ → ℂ := fun ξ => torusMode ξ f * (starRingEnd ℂ) (torusMode (ξ + β) h) with hA
  have hAs : Summable A := by
    refine Summable.of_norm ((summable_norm_pairing hTorus f h hf hh β).congr fun ξ => ?_)
    rw [hA, norm_mul, Complex.norm_conj]
  set S := ∑' ξ, A ξ with hS
  have hAS : HasSum A S := hAs.hasSum
  have hB1 : HasSum (fun ξ : ℤ × ℤ => torusMode (ξ - β) f * (starRingEnd ℂ) (torusMode ξ h)) S := by
    rw [← (Equiv.addRight β).hasSum_iff]
    refine hAS.congr_fun fun ξ => ?_
    simp only [Function.comp_apply, Equiv.coe_addRight, add_sub_cancel_right, hA]
  have hB2 : HasSum (fun ξ : ℤ × ℤ => torusMode (ξ + β) f * (starRingEnd ℂ) (torusMode ξ h))
      ((starRingEnd ℂ) S) := by
    have hc : HasSum (fun ξ => (starRingEnd ℂ) (A ξ)) ((starRingEnd ℂ) S) := Complex.hasSum_conj'.2 hAS
    set e : ℤ × ℤ ≃ ℤ × ℤ := (Equiv.neg (ℤ × ℤ)).trans (Equiv.subRight β) with he
    rw [← e.hasSum_iff]
    refine hc.congr_fun fun ξ => ?_
    simp only [Function.comp_apply, he, Equiv.trans_apply, Equiv.neg_apply, Equiv.subRight_apply, hA, map_mul,
      Complex.conj_conj]
    have e1 : -ξ - β + β = -ξ := by abel
    have e2 : -ξ - β = -(ξ + β) := by abel
    rw [e1, e2, torusMode_neg _ f hfi, torusMode_neg _ h hhi, Complex.conj_conj, mul_comm]
  have hw : Continuous (fun p : ℝ × ℝ => waveArg β p.1 p.2) := by
    unfold waveArg
    fun_prop
  have hfc : MemLp (fun p : ℝ × ℝ => f p.1 p.2 * Real.cos (waveArg β p.1 p.2)) 2 boxMeasure := by
    refine hf.of_le (hf.1.mul (Real.continuous_cos.comp hw).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun p => ?_)
    rw [norm_mul, Real.norm_eq_abs (Real.cos _)]
    exact mul_le_of_le_one_right (norm_nonneg _) (Real.abs_cos_le_one _)
  have hfs : MemLp (fun p : ℝ × ℝ => f p.1 p.2 * Real.sin (waveArg β p.1 p.2)) 2 boxMeasure := by
    refine hf.of_le (hf.1.mul (Real.continuous_sin.comp hw).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun p => ?_)
    rw [norm_mul, Real.norm_eq_abs (Real.sin _)]
    exact mul_le_of_le_one_right (norm_nonneg _) (Real.abs_sin_le_one _)
  have Tc := torus_hasSum_mul (f := fun τ φ => f τ φ * Real.cos (waveArg β τ φ)) (h := h) hTorus hfc hh
  have Ts := torus_hasSum_mul (f := fun τ φ => f τ φ * Real.sin (waveArg β τ φ)) (h := h) hTorus hfs hh
  have Hc : HasSum (fun ξ : ℤ × ℤ => (torusMode ξ (fun τ φ => f τ φ * Real.cos (waveArg β τ φ))
      * (starRingEnd ℂ) (torusMode ξ h)).re) (((S + (starRingEnd ℂ) S) / 2).re) := by
    have := Complex.hasSum_re ((hB1.add hB2).div_const 2)
    refine this.congr_fun fun ξ => ?_
    rw [torusMode_mul_cos ξ β f hfi]
    congr 1
    ring
  have Hs : HasSum (fun ξ : ℤ × ℤ => (torusMode ξ (fun τ φ => f τ φ * Real.sin (waveArg β τ φ))
      * (starRingEnd ℂ) (torusMode ξ h)).re) ((((starRingEnd ℂ) S - S) * Complex.I / 2).re) := by
    have := Complex.hasSum_re (((hB2.sub hB1).mul_right Complex.I).div_const 2)
    refine this.congr_fun fun ξ => ?_
    rw [torusMode_mul_sin ξ β f hfi]
    congr 1
    ring
  have ec : S.re = (1 / (2 * Real.pi)) * ∫ p, f p.1 p.2 * Real.cos (waveArg β p.1 p.2) * h p.1 p.2 ∂boxMeasure := by
    have := Hc.unique Tc
    rw [← this]
    simp only [Complex.div_ofNat_re, Complex.add_re, Complex.conj_re]
    ring
  have es : S.im = (1 / (2 * Real.pi)) * ∫ p, f p.1 p.2 * Real.sin (waveArg β p.1 p.2) * h p.1 p.2 ∂boxMeasure := by
    have := Hs.unique Ts
    rw [← this]
    simp only [Complex.div_ofNat_re, Complex.mul_re, Complex.sub_re, Complex.sub_im, Complex.conj_re,
      Complex.conj_im, Complex.I_re, Complex.I_im]
    ring
  have ic : Integrable (fun p : ℝ × ℝ => f p.1 p.2 * Real.cos (waveArg β p.1 p.2) * h p.1 p.2) boxMeasure :=
    hfc.integrable_mul hh
  have is : Integrable (fun p : ℝ × ℝ => f p.1 p.2 * Real.sin (waveArg β p.1 p.2) * h p.1 p.2) boxMeasure :=
    hfs.integrable_mul hh
  have eT : (∫ p, phase β p.1 p.2 * ((f p.1 p.2 * h p.1 p.2 : ℝ) : ℂ) ∂boxMeasure)
      = ((∫ p, f p.1 p.2 * Real.cos (waveArg β p.1 p.2) * h p.1 p.2 ∂boxMeasure : ℝ) : ℂ)
        + ((∫ p, f p.1 p.2 * Real.sin (waveArg β p.1 p.2) * h p.1 p.2 ∂boxMeasure : ℝ) : ℂ) * Complex.I := by
    rw [← integral_complex_ofReal, ← integral_complex_ofReal, ← integral_mul_const,
      ← integral_add ic.ofReal (is.ofReal.mul_const _)]
    congr 1
    funext p
    rw [phase, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    push_cast
    ring
  have hST : S = (1 / (2 * Real.pi) : ℂ) * ∫ p, phase β p.1 p.2 * ((f p.1 p.2 * h p.1 p.2 : ℝ) : ℂ) ∂boxMeasure := by
    rw [eT]
    apply Complex.ext
    · rw [ec]
      simp [Complex.mul_re, Complex.add_re, Complex.ofReal_re]
    · rw [es]
      simp [Complex.mul_im, Complex.add_im]
  rw [← hST]
  exact hAS


theorem expFactor_add_one (β : ℤ × ℤ) (τ φ : ℝ) : expFactor β (τ + 1) φ = expFactor β τ φ := by
  rw [expFactor_eq, expFactor_eq]
  have h : -((waveArg β (τ + 1) φ : ℂ) * Complex.I) =
      -((waveArg β τ φ : ℂ) * Complex.I) + ((-β.1 : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
    simp only [waveArg]
    push_cast
    ring
  rw [h, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

theorem expFactor_time_shift (β : ℤ × ℤ) (τ τ' φ : ℝ) :
    expFactor β τ' φ = Complex.exp (((2 * Real.pi * β.1 * τ : ℝ) : ℂ) * Complex.I) * expFactor β (τ + τ') φ := by
  rw [expFactor_eq, expFactor_eq, ← Complex.exp_add]
  congr 1
  simp only [waveArg]
  push_cast
  ring

theorem shifted_average (β : ℤ × ℤ) (F : ℝ → ℝ → ℂ) (h1 : ∀ τ φ, F (τ + 1) φ = F τ φ)
    (h2 : ∀ τ φ, F τ (φ + 2 * Real.pi) = F τ φ) (τ φ : ℝ) :
    ∫ τ' in (0 : ℝ)..1, ∫ φ' in (0 : ℝ)..(2 * Real.pi), expFactor β τ' φ' * F (τ + τ') (φ' + φ)
      = phase β τ φ * ∫ τ' in (0 : ℝ)..1, ∫ φ' in (0 : ℝ)..(2 * Real.pi), expFactor β τ' φ' * F τ' φ' := by
  set g : ℝ → ℂ := fun t => ∫ φ' in (0 : ℝ)..(2 * Real.pi), expFactor β t φ' * F t φ' with hg
  have hinner : ∀ τ', ∫ φ' in (0 : ℝ)..(2 * Real.pi), expFactor β τ' φ' * F (τ + τ') (φ' + φ)
      = Complex.exp (((β.2 * φ : ℝ) : ℂ) * Complex.I)
        * (Complex.exp (((2 * Real.pi * β.1 * τ : ℝ) : ℂ) * Complex.I) * g (τ' + τ)) := by
    intro τ'
    rw [integral_shift β τ' φ (fun φ' => F (τ + τ') φ') (fun x => h2 _ x)]
    congr 1
    rw [hg, ← intervalIntegral.integral_const_mul]
    congr 1
    funext φ'
    rw [expFactor_time_shift β τ τ' φ', add_comm τ' τ]
    ring
  have hper : Function.Periodic g 1 := by
    intro t
    simp only [hg]
    congr 1
    funext φ'
    rw [expFactor_add_one, h1]
  simp_rw [hinner]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_add_right g τ, zero_add, add_comm 1 τ,
    hper.intervalIntegral_add_eq τ 0, zero_add, ← mul_assoc, phase, ← Complex.exp_add]
  congr 2
  simp only [waveArg]
  push_cast
  ring

end Internal.MeanStretch

end Bridge

end CertCell

end Breakdown
