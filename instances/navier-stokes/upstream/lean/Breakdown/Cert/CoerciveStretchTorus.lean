import Breakdown.Cert.CoerciveModeRotation

open MeasureTheory

noncomputable section

namespace Breakdown

namespace Coercive

namespace StretchTorusInternal

open Internal.ModeRotation

private theorem box_eq :
    (volume.restrict (Set.Icc (0 : ℝ) 1)).prod (volume.restrict (Set.Icc (0 : ℝ) (2 * Real.pi)))
      = boxMeasure := by
  show _ = (volume.restrict (Set.Ioc (0 : ℝ) 1)).prod (volume.restrict (Set.Ioc (0 : ℝ) (2 * Real.pi)))
  rw [Measure.restrict_congr_set (Ioc_ae_eq_Icc (a := (0 : ℝ)) (b := 1)),
    Measure.restrict_congr_set (Ioc_ae_eq_Icc (a := (0 : ℝ)) (b := 2 * Real.pi))]

private theorem hasSum_of_ennreal {a : ℤ × ℤ → ℝ} {c : ℝ} (ha : ∀ ι, 0 ≤ a ι) (hc : 0 ≤ c)
    (h : ∑' ι, ENNReal.ofReal (a ι) = ENNReal.ofReal c) : HasSum a c := by
  have hne : ∑' ι, ENNReal.ofReal (a ι) ≠ ⊤ := by
    rw [h]
    exact ENNReal.ofReal_ne_top
  have hs : Summable a :=
    (ENNReal.summable_toReal hne).congr (fun ι => ENNReal.toReal_ofReal (ha ι))
  have hv : ∑' ι, a ι = c := by
    have e := ENNReal.ofReal_tsum_of_nonneg ha hs
    rw [h] at e
    exact (ENNReal.ofReal_eq_ofReal_iff (tsum_nonneg ha) hc).1 e
  rw [← hv]
  exact hs.hasSum

private theorem hasSum_sq (hTorus : TorusSquareSumHolds) (f : ℝ → ℝ → ℝ)
    (hf : MemLp (fun p : ℝ × ℝ => f p.1 p.2) 2 boxMeasure) :
    HasSum (fun ι : ℤ × ℤ => ‖modeAverage ι (fun τ φ (_ : Unit) => f τ φ) ()‖ ^ 2)
      ((1 / (2 * Real.pi)) * ∫ p, f p.1 p.2 ^ 2 ∂boxMeasure) := by
  have hsq : Integrable (fun p : ℝ × ℝ => f p.1 p.2 ^ 2) boxMeasure := hf.integrable_sq
  have hlin : ∫⁻ p, ENNReal.ofReal (f p.1 p.2 ^ 2) ∂boxMeasure
      = ENNReal.ofReal (∫ p, f p.1 p.2 ^ 2 ∂boxMeasure) :=
    (ofReal_integral_eq_lintegral_ofReal hsq (Filter.Eventually.of_forall fun p => sq_nonneg _)).symm
  have hmeas : AEStronglyMeasurable (fun z : ℝ × ℝ => f z.1 z.2)
      ((volume.restrict (Set.Icc (0 : ℝ) 1)).prod (volume.restrict (Set.Icc (0 : ℝ) (2 * Real.pi)))) := by
    rw [box_eq]
    exact hf.1
  have hae : AEMeasurable (fun z : ℝ × ℝ => ENNReal.ofReal (f z.1 z.2 ^ 2))
      ((volume.restrict (Set.Icc (0 : ℝ) 1)).prod (volume.restrict (Set.Icc (0 : ℝ) (2 * Real.pi)))) :=
    (hmeas.aemeasurable.pow_const 2).ennreal_ofReal
  have hiter : (∫⁻ τ in Set.Icc (0 : ℝ) 1, ∫⁻ φ in Set.Icc (0 : ℝ) (2 * Real.pi), ENNReal.ofReal (f τ φ ^ 2))
      = ∫⁻ p, ENNReal.ofReal (f p.1 p.2 ^ 2) ∂boxMeasure := by
    rw [← box_eq, lintegral_prod _ hae]
  have hT := hTorus f hmeas (by
    rw [hiter, hlin]
    exact ENNReal.ofReal_lt_top)
  rw [hiter, hlin, ← ENNReal.ofReal_mul (by positivity)] at hT
  refine hasSum_of_ennreal (fun ι => sq_nonneg _) ?_ hT
  exact mul_nonneg (by positivity) (integral_nonneg fun p => sq_nonneg _)

private theorem integrable_exp_mul (ι : ℤ × ℤ) {g : ℝ × ℝ → ℝ} (hg : Integrable g boxMeasure) :
    Integrable (fun p : ℝ × ℝ => expFactor ι p.1 p.2 * ((g p : ℝ) : ℂ)) boxMeasure := by
  refine hg.norm.mono' ((continuous_expFactor ι).aestronglyMeasurable.mul
    (Complex.continuous_ofReal.comp_aestronglyMeasurable hg.1)) ?_
  refine Filter.Eventually.of_forall fun p => ?_
  simp only [norm_mul, norm_expFactor, one_mul, Complex.norm_real, le_refl]

private theorem modeAverage_eq_box (ι : ℤ × ℤ) (f : ℝ → ℝ → ℝ)
    (hf : Integrable (fun p : ℝ × ℝ => f p.1 p.2) boxMeasure) :
    modeAverage ι (fun τ φ (_ : Unit) => f τ φ) ()
      = (1 / (2 * Real.pi) : ℂ) * ∫ p, expFactor ι p.1 p.2 * ((f p.1 p.2 : ℝ) : ℂ) ∂boxMeasure := by
  rw [modeAverage_eq, iter_eq_prod (fun τ φ => expFactor ι τ φ * ((f τ φ : ℝ) : ℂ))
    (integrable_exp_mul ι hf)]

private theorem modeAverage_lin (ι : ℤ × ℤ) (ε : ℝ) {f h : ℝ → ℝ → ℝ}
    (hf : Integrable (fun p : ℝ × ℝ => f p.1 p.2) boxMeasure)
    (hh : Integrable (fun p : ℝ × ℝ => h p.1 p.2) boxMeasure) :
    modeAverage ι (fun τ φ (_ : Unit) => f τ φ + ε * h τ φ) ()
      = modeAverage ι (fun τ φ (_ : Unit) => f τ φ) ()
        + (ε : ℂ) * modeAverage ι (fun τ φ (_ : Unit) => h τ φ) () := by
  have e1 := modeAverage_eq_box ι (fun τ φ => f τ φ + ε * h τ φ) (hf.add (hh.const_mul ε))
  rw [e1, modeAverage_eq_box ι f hf, modeAverage_eq_box ι h hh]
  have e : (fun p : ℝ × ℝ => expFactor ι p.1 p.2 * ((f p.1 p.2 + ε * h p.1 p.2 : ℝ) : ℂ))
      = fun p => expFactor ι p.1 p.2 * ((f p.1 p.2 : ℝ) : ℂ)
        + (ε : ℂ) * (expFactor ι p.1 p.2 * ((h p.1 p.2 : ℝ) : ℂ)) := by
    funext p
    push_cast
    ring
  rw [e, integral_add (integrable_exp_mul ι hf) ((integrable_exp_mul ι hh).const_mul _),
    integral_const_mul]
  ring

private theorem re_mul_conj (a b : ℂ) :
    (a * (starRingEnd ℂ) b).re = (‖a + ((1 : ℝ) : ℂ) * b‖ ^ 2 - ‖a + ((-1 : ℝ) : ℂ) * b‖ ^ 2) / 4 := by
  rw [Complex.sq_norm, Complex.sq_norm]
  simp only [Complex.normSq_apply, Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
    Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im]
  ring

theorem torus_hasSum_mul (hTorus : TorusSquareSumHolds) {f h : ℝ → ℝ → ℝ}
    (hf : MemLp (fun p : ℝ × ℝ => f p.1 p.2) 2 boxMeasure)
    (hh : MemLp (fun p : ℝ × ℝ => h p.1 p.2) 2 boxMeasure) :
    HasSum (fun ι : ℤ × ℤ => (modeAverage ι (fun τ φ (_ : Unit) => f τ φ) ()
        * (starRingEnd ℂ) (modeAverage ι (fun τ φ (_ : Unit) => h τ φ) ())).re)
      ((1 / (2 * Real.pi)) * ∫ p, f p.1 p.2 * h p.1 p.2 ∂boxMeasure) := by
  have hfi : Integrable (fun p : ℝ × ℝ => f p.1 p.2) boxMeasure := hf.integrable one_le_two
  have hhi : Integrable (fun p : ℝ × ℝ => h p.1 p.2) boxMeasure := hh.integrable one_le_two
  have key : ∀ ε : ℝ, HasSum (fun ι : ℤ × ℤ => ‖modeAverage ι (fun τ φ (_ : Unit) => f τ φ) ()
        + (ε : ℂ) * modeAverage ι (fun τ φ (_ : Unit) => h τ φ) ()‖ ^ 2)
      ((1 / (2 * Real.pi)) * ∫ p, (f p.1 p.2 + ε * h p.1 p.2) ^ 2 ∂boxMeasure) := by
    intro ε
    have h1 := hasSum_sq hTorus (fun τ φ => f τ φ + ε * h τ φ) (hf.add (hh.const_mul ε))
    have e : ∀ ι : ℤ × ℤ, modeAverage ι (fun τ φ (_ : Unit) => f τ φ + ε * h τ φ) ()
        = modeAverage ι (fun τ φ (_ : Unit) => f τ φ) ()
          + (ε : ℂ) * modeAverage ι (fun τ φ (_ : Unit) => h τ φ) () :=
      fun ι => modeAverage_lin ι ε hfi hhi
    simp only [e] at h1
    exact h1
  have i1 : Integrable (fun p : ℝ × ℝ => (f p.1 p.2 + (1 : ℝ) * h p.1 p.2) ^ 2) boxMeasure :=
    (hf.add (hh.const_mul 1)).integrable_sq
  have i2 : Integrable (fun p : ℝ × ℝ => (f p.1 p.2 + (-1 : ℝ) * h p.1 p.2) ^ 2) boxMeasure :=
    (hf.add (hh.const_mul (-1))).integrable_sq
  have hdiff : ∫ p, (f p.1 p.2 + (1 : ℝ) * h p.1 p.2) ^ 2 ∂boxMeasure
      - ∫ p, (f p.1 p.2 + (-1 : ℝ) * h p.1 p.2) ^ 2 ∂boxMeasure
      = 4 * ∫ p, f p.1 p.2 * h p.1 p.2 ∂boxMeasure := by
    rw [← integral_sub i1 i2, ← integral_const_mul]
    congr 1
    funext p
    ring
  have H := ((key 1).sub (key (-1))).div_const 4
  have hfun : (fun ι : ℤ × ℤ => (modeAverage ι (fun τ φ (_ : Unit) => f τ φ) ()
        * (starRingEnd ℂ) (modeAverage ι (fun τ φ (_ : Unit) => h τ φ) ())).re)
      = fun ι : ℤ × ℤ => (‖modeAverage ι (fun τ φ (_ : Unit) => f τ φ) ()
          + ((1 : ℝ) : ℂ) * modeAverage ι (fun τ φ (_ : Unit) => h τ φ) ()‖ ^ 2
        - ‖modeAverage ι (fun τ φ (_ : Unit) => f τ φ) ()
          + ((-1 : ℝ) : ℂ) * modeAverage ι (fun τ φ (_ : Unit) => h τ φ) ()‖ ^ 2) / 4 :=
    funext fun ι => re_mul_conj _ _
  have hv : (1 / (2 * Real.pi)) * ∫ p, f p.1 p.2 * h p.1 p.2 ∂boxMeasure
      = ((1 / (2 * Real.pi)) * ∫ p, (f p.1 p.2 + (1 : ℝ) * h p.1 p.2) ^ 2 ∂boxMeasure
        - (1 / (2 * Real.pi)) * ∫ p, (f p.1 p.2 + (-1 : ℝ) * h p.1 p.2) ^ 2 ∂boxMeasure) / 4 := by
    rw [← mul_sub, hdiff]
    ring
  rw [hfun, hv]
  exact H

end StretchTorusInternal

end Coercive

end Breakdown
