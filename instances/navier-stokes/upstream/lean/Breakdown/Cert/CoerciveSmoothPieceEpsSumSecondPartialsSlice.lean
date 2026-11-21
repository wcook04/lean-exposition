import Breakdown.Cert.CoerciveSmoothPieceEpsSumSecondPartialsSliceShift

open scoped ContDiff ENNReal
open MeasureTheory

noncomputable section

namespace Breakdown

namespace Coercive

namespace Internal.ModeSlice

private theorem box_eq_restrict :
    Internal.ModeRotation.boxMeasure
      = (volume : Measure (ℝ × ℝ)).restrict (Set.Ioc (0 : ℝ) 1 ×ˢ Set.Ioc (0 : ℝ) (2 * Real.pi)) := by
  show (volume.restrict (Set.Ioc (0 : ℝ) 1)).prod (volume.restrict (Set.Ioc (0 : ℝ) (2 * Real.pi))) = _
  rw [Measure.prod_restrict, Measure.volume_eq_prod]

private theorem box_integrable {E : Type*} [NormedAddCommGroup E] {f : ℝ × ℝ → E} (hf : Continuous f) :
    Integrable f Internal.ModeRotation.boxMeasure := by
  rw [box_eq_restrict]
  exact (hf.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set
    (Set.prod_mono Set.Ioc_subset_Icc_self Set.Ioc_subset_Icc_self)

private theorem box_real_univ : Internal.ModeRotation.boxMeasure.real Set.univ = 2 * Real.pi := by
  rw [measureReal_def, box_eq_restrict, Measure.restrict_apply_univ, Measure.volume_eq_prod]
  rw [Measure.prod_prod, Real.volume_Ioc, Real.volume_Ioc, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by norm_num),
    ENNReal.toReal_ofReal (by linarith [Real.pi_pos])]
  ring

private theorem box_sq_integral_le {G : ℝ × ℝ → ℝ} (hG : Continuous G) :
    (∫ p, G p ∂Internal.ModeRotation.boxMeasure) ^ 2
      ≤ 2 * Real.pi * ∫ p, G p ^ 2 ∂Internal.ModeRotation.boxMeasure := by
  set μ := Internal.ModeRotation.boxMeasure
  have hM : μ.real Set.univ = 2 * Real.pi := box_real_univ
  have hpi : 0 < 2 * Real.pi := by positivity
  set m := (∫ p, G p ∂μ) / (2 * Real.pi)
  have i1 : Integrable G μ := box_integrable hG
  have i2 : Integrable (fun p => G p ^ 2) μ := box_integrable (hG.pow 2)
  have e : ∫ p, (G p - m) ^ 2 ∂μ = ∫ p, G p ^ 2 ∂μ - 2 * m * ∫ p, G p ∂μ + m ^ 2 * (2 * Real.pi) := by
    have pt : (fun p => (G p - m) ^ 2) = fun p => (G p ^ 2 - (2 * m) * G p) + m ^ 2 := by
      funext p; ring
    rw [pt, integral_add (f := fun p => G p ^ 2 - 2 * m * G p) (g := fun _ => m ^ 2) (i2.sub (i1.const_mul _))
      (integrable_const _), integral_sub (f := fun p => G p ^ 2) (g := fun p => 2 * m * G p) i2 (i1.const_mul _),
      integral_const_mul, integral_const, hM, smul_eq_mul]
    ring
  have h0 : 0 ≤ ∫ p, (G p - m) ^ 2 ∂μ := integral_nonneg fun p => sq_nonneg _
  rw [e] at h0
  have hm : m * (2 * Real.pi) = ∫ p, G p ∂μ := by
    simp only [m]; field_simp
  nlinarith [sq_nonneg m]

theorem memLp_modeAverage_dom {β : Type*} (ι : ℤ × ℤ) (b : β) (F : Space → ℝ → ℝ → β → ℝ)
    (hF : Continuous (fun q : Space × ℝ × ℝ => F q.1 q.2.1 q.2.2 b)) (g : ℝ → Space → ℝ)
    (hg : Continuous (fun z : ℝ × Space => g z.1 z.2)) (hgp : IsTimePeriodic g)
    (hg2 : periodLIntegral (fun s x => g s x ^ 2) < ⊤) (σ : ℝ)
    (hdom : ∀ y τ φ, |F y τ φ b| ≤ g (σ + τ) (axialRot φ y)) :
    MemLp (fun y => modeAverage ι (F y) b) 2 volume := by
  have hpi : 0 < 2 * Real.pi := by positivity
  set c : ℝ := 1 / (2 * Real.pi) with hcdef
  have hc0 : 0 < c := by positivity
  have hEc : Continuous (fun p : ℝ × ℝ => Internal.ModeRotation.expFactor ι p.1 p.2) := by
    unfold Internal.ModeRotation.expFactor
    fun_prop
  have hK : Continuous (fun q : Space × ℝ × ℝ =>
      Internal.ModeRotation.expFactor ι q.2.1 q.2.2 * ((F q.1 q.2.1 q.2.2 b : ℝ) : ℂ)) :=
    (hEc.comp continuous_snd).mul (Complex.continuous_ofReal.comp hF)
  have hrot : Continuous (fun q : Space × ℝ × ℝ => axialRot q.2.2 q.1) := by
    unfold axialRot
    fun_prop
  have hGc : Continuous (fun q : Space × ℝ × ℝ => g (σ + q.2.1) (axialRot q.2.2 q.1)) :=
    hg.comp ((continuous_const.add continuous_snd.fst).prodMk hrot)
  have hform : ∀ y, modeAverage ι (F y) b = (c : ℂ) * ∫ p, Internal.ModeRotation.expFactor ι p.1 p.2
      * ((F y p.1 p.2 b : ℝ) : ℂ) ∂Internal.ModeRotation.boxMeasure := by
    intro y
    rw [Internal.ModeRotation.modeAverage_eq, Internal.ModeRotation.iter_eq_prod _
      (box_integrable (hK.comp (continuous_const.prodMk continuous_id)))]
    simp only [hcdef]
    push_cast
    rfl
  have hcont : Continuous (fun y => modeAverage ι (F y) b) := by
    have h1 : Continuous (fun q : Space × ℝ => ∫ φ in (0 : ℝ)..(2 * Real.pi),
        Internal.ModeRotation.expFactor ι q.2 φ * ((F q.1 q.2 φ b : ℝ) : ℂ)) :=
      intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
        (f := fun (q : Space × ℝ) φ => Internal.ModeRotation.expFactor ι q.2 φ * ((F q.1 q.2 φ b : ℝ) : ℂ))
        (hK.comp (continuous_fst.fst.prodMk (continuous_fst.snd.prodMk continuous_snd))) 0 (2 * Real.pi)
    have h2 : Continuous (fun y : Space => ∫ τ in (0 : ℝ)..1, ∫ φ in (0 : ℝ)..(2 * Real.pi),
        Internal.ModeRotation.expFactor ι τ φ * ((F y τ φ b : ℝ) : ℂ)) :=
      intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (f := fun (y : Space) τ => ∫ φ in (0 : ℝ)..(2 * Real.pi),
        Internal.ModeRotation.expFactor ι τ φ * ((F y τ φ b : ℝ) : ℂ)) h1 0 1
    have e : (fun y => modeAverage ι (F y) b) = fun y => (1 / (2 * Real.pi) : ℂ) * ∫ τ in (0 : ℝ)..1,
        ∫ φ in (0 : ℝ)..(2 * Real.pi), Internal.ModeRotation.expFactor ι τ φ * ((F y τ φ b : ℝ) : ℂ) := by
      funext y
      exact Internal.ModeRotation.modeAverage_eq ι (F y) b
    rw [e]
    exact continuous_const.mul h2
  have hpt : ∀ y, ‖modeAverage ι (F y) b‖ ^ 2 ≤ c * ∫ p, g (σ + p.1) (axialRot p.2 y) ^ 2
      ∂Internal.ModeRotation.boxMeasure := by
    intro y
    have hG : Continuous (fun p : ℝ × ℝ => g (σ + p.1) (axialRot p.2 y)) :=
      hGc.comp (continuous_const.prodMk continuous_id)
    have hn : ‖∫ p, Internal.ModeRotation.expFactor ι p.1 p.2 * ((F y p.1 p.2 b : ℝ) : ℂ)
        ∂Internal.ModeRotation.boxMeasure‖ ≤ ∫ p, g (σ + p.1) (axialRot p.2 y) ∂Internal.ModeRotation.boxMeasure := by
      refine norm_integral_le_of_norm_le (box_integrable hG) (ae_of_all _ fun p => ?_)
      rw [norm_mul, Internal.ModeRotation.norm_expFactor, one_mul, Complex.norm_real, Real.norm_eq_abs]
      exact hdom y p.1 p.2
    have hcs := box_sq_integral_le hG
    have hn0 : 0 ≤ ‖∫ p, Internal.ModeRotation.expFactor ι p.1 p.2 * ((F y p.1 p.2 b : ℝ) : ℂ)
        ∂Internal.ModeRotation.boxMeasure‖ := norm_nonneg _
    rw [hform y, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc0, mul_pow]
    have hsq := pow_le_pow_left₀ hn0 hn 2
    have hcpi : c * (2 * Real.pi) = 1 := by simp only [hcdef]; field_simp
    calc c ^ 2 * ‖∫ p, Internal.ModeRotation.expFactor ι p.1 p.2 * ((F y p.1 p.2 b : ℝ) : ℂ)
          ∂Internal.ModeRotation.boxMeasure‖ ^ 2
        ≤ c ^ 2 * (2 * Real.pi * ∫ p, g (σ + p.1) (axialRot p.2 y) ^ 2 ∂Internal.ModeRotation.boxMeasure) :=
          mul_le_mul_of_nonneg_left (hsq.trans hcs) (sq_nonneg c)
      _ = (c * (2 * Real.pi)) * c * ∫ p, g (σ + p.1) (axialRot p.2 y) ^ 2 ∂Internal.ModeRotation.boxMeasure := by ring
      _ = c * ∫ p, g (σ + p.1) (axialRot p.2 y) ^ 2 ∂Internal.ModeRotation.boxMeasure := by rw [hcpi, one_mul]
  have hlin : ∀ y, ENNReal.ofReal (‖modeAverage ι (F y) b‖ ^ 2) ≤ ENNReal.ofReal c *
      ∫⁻ p, ENNReal.ofReal (g (σ + p.1) (axialRot p.2 y) ^ 2) ∂Internal.ModeRotation.boxMeasure := by
    intro y
    have hG2 : Integrable (fun p : ℝ × ℝ => g (σ + p.1) (axialRot p.2 y) ^ 2) Internal.ModeRotation.boxMeasure :=
      box_integrable ((hGc.comp (continuous_const.prodMk continuous_id)).pow 2)
    rw [← ofReal_integral_eq_lintegral_ofReal hG2 (ae_of_all _ fun p => sq_nonneg _),
      ← ENNReal.ofReal_mul hc0.le]
    exact ENNReal.ofReal_le_ofReal (hpt y)
  have hfin : ∫⁻ y, ENNReal.ofReal (‖modeAverage ι (F y) b‖ ^ 2) < ⊤ := by
    refine lt_of_le_of_lt (lintegral_mono hlin) ?_
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_box_rot_shift g hg hgp σ]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hg2)
  have hmeas : AEStronglyMeasurable (fun y => modeAverage ι (F y) b) volume := hcont.aestronglyMeasurable
  refine (memLp_two_iff_integrable_sq_norm hmeas).2 ⟨((continuous_norm.comp hcont).pow 2).aestronglyMeasurable, ?_⟩
  unfold HasFiniteIntegral
  refine lt_of_le_of_lt (le_of_eq (lintegral_congr fun y => ?_)) hfin
  rw [← ofReal_norm_eq_enorm, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]

end Internal.ModeSlice

end Coercive

end Breakdown
