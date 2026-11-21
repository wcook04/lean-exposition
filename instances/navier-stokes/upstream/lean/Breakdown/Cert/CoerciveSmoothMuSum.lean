import Breakdown.Cert.CoerciveSmoothMuMeasure

open scoped ContDiff ENNReal
open MeasureTheory

noncomputable section

namespace Breakdown

namespace Coercive

namespace Internal.MuSmooth

theorem axialRot_smul (φ c : ℝ) (u : Space) : axialRot φ (c • u) = c • axialRot φ u := by
  unfold axialRot
  simp only [PiLp.smul_apply, smul_eq_mul]
  module

def weighted (v : ℝ → Space → Space) (σ : ℝ) (y : Space) : Space := (1 + ‖y‖)⁻¹ • v σ y

theorem modeVel_weighted (v : ℝ → Space → Space) (ι : ℤ × ℤ) (σ : ℝ) (y : Space) (i : Fin 3) :
    modeVel ι (weighted v) σ y i = (((1 + ‖y‖)⁻¹ : ℝ) : ℂ) * modeVel ι v σ y i := by
  have hn : ∀ φ, ‖axialRot φ y‖ = ‖y‖ := fun φ => by
    obtain ⟨R, hR⟩ := axialRotationHolds_proof.1 φ
    rw [← hR, R.norm_map]
  unfold modeVel modeAverage weighted
  simp only [hn, axialRot_smul, PiLp.smul_apply, smul_eq_mul, Complex.ofReal_mul]
  have h : ∀ τ φ : ℝ, Complex.exp (-(((2 * Real.pi * ι.1 * τ + ι.2 * φ : ℝ) : ℂ) * Complex.I))
      * ((((1 + ‖y‖)⁻¹ : ℝ) : ℂ) * ((axialRot (-φ) (v (σ + τ) (axialRot φ y)) i : ℝ) : ℂ))
      = (((1 + ‖y‖)⁻¹ : ℝ) : ℂ) * (Complex.exp (-(((2 * Real.pi * ι.1 * τ + ι.2 * φ : ℝ) : ℂ) * Complex.I))
        * ((axialRot (-φ) (v (σ + τ) (axialRot φ y)) i : ℝ) : ℂ)) := fun τ φ => by ring
  simp only [h, intervalIntegral.integral_const_mul]
  ring

theorem cnormSq_weighted (v : ℝ → Space → Space) (ι : ℤ × ℤ) (σ : ℝ) (y : Space) :
    cnormSq (modeVel ι (weighted v) σ y) = cnormSq (modeVel ι v σ y) / (1 + ‖y‖) ^ 2 := by
  unfold cnormSq
  simp only [modeVel_weighted, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hp : 0 < 1 + ‖y‖ := by positivity
  rw [abs_of_pos (inv_pos.2 hp)]
  field_simp

theorem pairTerm_le {C : Type} (m : ModeWeights C) {B : ℝ}
    (hB : ∀ c y, |m.muW c y| ≤ B ∧ ‖y‖ ^ 2 * |m.muW c y| ≤ B ∧ ‖y‖ * ‖fderiv ℝ (m.muW c) y‖ ≤ B)
    (v Q : ℝ → Space → Space) (ι : ℤ × ℤ) (σ : ℝ) (y : Space) :
    |pairTerm m v Q ι σ y| ≤ 2 * B * cnormSq (modeVel ι (weighted v) σ y) + B * cnormSq (modeVel ι Q σ y) := by
  obtain ⟨h1, h2, -⟩ := hB (m.classOf ι) y
  have hw := ModeL2Internal.abs_re_weighted_le (m.muW (m.classOf ι) y) (modeVel ι v σ y) (modeVel ι Q σ y)
    (t := 1) one_pos
  rw [cnormSq_weighted]
  have hx := cnorm_nonneg (modeVel ι v σ y)
  have hz := cnorm_nonneg (modeVel ι Q σ y)
  have hp : 0 < (1 + ‖y‖) ^ 2 := by positivity
  have hsq : (1 + ‖y‖) ^ 2 ≤ 2 * (1 + ‖y‖ ^ 2) := by nlinarith [sq_nonneg (‖y‖ - 1)]
  have hmu : |m.muW (m.classOf ι) y| * (1 + ‖y‖) ^ 2 ≤ 4 * B := by
    nlinarith [abs_nonneg (m.muW (m.classOf ι) y)]
  have e1 : |m.muW (m.classOf ι) y| * cnormSq (modeVel ι v σ y)
      ≤ 4 * B * (cnormSq (modeVel ι v σ y) / (1 + ‖y‖) ^ 2) := by
    rw [mul_div_assoc', le_div_iff₀ hp]
    nlinarith
  unfold pairTerm
  simp only [one_mul, div_one] at hw
  have hB0 : 0 ≤ B := le_trans (abs_nonneg _) h1
  have hexp : |m.muW (m.classOf ι) y| * ((cnormSq (modeVel ι v σ y) + cnormSq (modeVel ι Q σ y)) / 2)
      = |m.muW (m.classOf ι) y| * cnormSq (modeVel ι v σ y) / 2
        + |m.muW (m.classOf ι) y| * cnormSq (modeVel ι Q σ y) / 2 := by ring
  have hq := mul_le_mul_of_nonneg_right h1 hz
  have hbz := mul_nonneg hB0 hz
  linarith

theorem weighted_square (P : ℝ) (v : ℝ → Space → Space) (hv : IsSmoothPerturbation P v) :
    periodLIntegral (fun σ y => ‖weighted v σ y‖ ^ 2) < ⊤ := by
  have h : (fun σ y => ‖weighted v σ y‖ ^ 2) = fun σ y => ‖v σ y‖ ^ 2 / (1 + ‖y‖) ^ 2 := by
    funext σ y
    unfold weighted
    have hp : 0 < 1 + ‖y‖ := by positivity
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hp), mul_pow, inv_pow]
    field_simp
  rw [h]
  exact hv.weighted_finite

theorem weighted_continuous (v : ℝ → Space → Space) (hv : Continuous (fun z : ℝ × Space => v z.1 z.2)) :
    Continuous (fun z : ℝ × Space => weighted v z.1 z.2) := by
  unfold weighted
  have hp : ∀ z : ℝ × Space, 1 + ‖z.2‖ ≠ 0 := fun z => by positivity
  exact ((continuous_const.add (continuous_norm.comp continuous_snd)).inv₀ hp).smul hv

theorem weighted_periodic (v : ℝ → Space → Space) (hv : IsTimePeriodic v) : IsTimePeriodic (weighted v) := by
  intro σ y
  unfold weighted
  rw [hv σ y]

theorem tsum_mode_lt_top (hPars : ModeSquareSumHolds) (X : ℝ → Space → Space)
    (hm : AEStronglyMeasurable (fun z : ℝ × Space => X z.1 z.2) volume) (hp : IsTimePeriodic X)
    (hs : periodLIntegral (fun σ y => ‖X σ y‖ ^ 2) < ⊤) :
    ∑' ι : ℤ × ℤ, ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ENNReal.ofReal (cnormSq (modeVel ι X σ y)) < ⊤ := by
  rw [← hPars.1 X hm hp hs]
  exact hs

theorem pair_summable_of (hPars : ModeSquareSumHolds) {C : Type} (m : ModeWeights C) (P : ℝ) (b : FlowBounds C)
    (w : Space → ℝ) {w₀ epsSup epsGradSup ratio : ℝ}
    (hm : m.IsAdmissible P b w w₀ epsSup epsGradSup ratio)
    (v : ℝ → Space → Space) (hv : IsSmoothPerturbation P v) (F Q : ℝ → Space → Space)
    (hQ : IsSolenoidalPartOf F Q) :
    Summable (fun ι => pairMode m v Q ι) := by
  obtain ⟨B, hB⟩ := hm.muW_decay
  have hB0 : 0 ≤ B := le_trans (abs_nonneg _) (hB (m.classOf 0) 0).1
  have hvc : Continuous (fun z : ℝ × Space => v z.1 z.2) := hv.smooth.continuous
  have hA := tsum_mode_lt_top hPars (weighted v) (weighted_continuous v hvc).aestronglyMeasurable
    (weighted_periodic v hv.periodic) (weighted_square P v hv)
  have hZ := tsum_mode_lt_top hPars Q hQ.1 hQ.2.1 hQ.2.2.1
  have hcw : ∀ ι, Measurable (fun z : ℝ × Space => ENNReal.ofReal (cnormSq (modeVel ι (weighted v) z.1 z.2))) :=
    fun ι => (continuous_cnormSq_modeVel (weighted_continuous v hvc) ι).measurable.ennreal_ofReal
  set L : ℤ × ℤ → ℝ≥0∞ := fun ι =>
    ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ENNReal.ofReal |pairTerm m v Q ι σ y| with hL
  have hLle : ∀ ι, L ι ≤ ENNReal.ofReal (2 * B) *
      (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ENNReal.ofReal (cnormSq (modeVel ι (weighted v) σ y)))
      + ENNReal.ofReal B * ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ENNReal.ofReal (cnormSq (modeVel ι Q σ y)) := by
    intro ι
    have hpt : ∀ σ y, ENNReal.ofReal |pairTerm m v Q ι σ y|
        ≤ ENNReal.ofReal (2 * B) * ENNReal.ofReal (cnormSq (modeVel ι (weighted v) σ y))
          + ENNReal.ofReal B * ENNReal.ofReal (cnormSq (modeVel ι Q σ y)) := fun σ y => by
      rw [← ENNReal.ofReal_mul (by linarith), ← ENNReal.ofReal_mul hB0,
        ← ENNReal.ofReal_add (mul_nonneg (by linarith) (cnorm_nonneg _)) (mul_nonneg hB0 (cnorm_nonneg _))]
      exact ENNReal.ofReal_le_ofReal (pairTerm_le m hB v Q ι σ y)
    calc L ι ≤ ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y,
          (ENNReal.ofReal (2 * B) * ENNReal.ofReal (cnormSq (modeVel ι (weighted v) σ y))
            + ENNReal.ofReal B * ENNReal.ofReal (cnormSq (modeVel ι Q σ y))) :=
          lintegral_mono fun σ => lintegral_mono fun y => hpt σ y
      _ = _ := by
          have hin : ∀ σ, ∫⁻ y, (ENNReal.ofReal (2 * B) * ENNReal.ofReal (cnormSq (modeVel ι (weighted v) σ y))
              + ENNReal.ofReal B * ENNReal.ofReal (cnormSq (modeVel ι Q σ y)))
              = ENNReal.ofReal (2 * B) * (∫⁻ y, ENNReal.ofReal (cnormSq (modeVel ι (weighted v) σ y)))
                + ENNReal.ofReal B * ∫⁻ y, ENNReal.ofReal (cnormSq (modeVel ι Q σ y)) := fun σ => by
            have hmσ : Measurable (fun y => ENNReal.ofReal (2 * B)
                * ENNReal.ofReal (cnormSq (modeVel ι (weighted v) σ y))) :=
              ((hcw ι).comp measurable_prodMk_left).const_mul _
            rw [lintegral_add_left hmσ,
              lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
          simp_rw [hin]
          have hmo : Measurable (fun σ => ENNReal.ofReal (2 * B)
              * ∫⁻ y, ENNReal.ofReal (cnormSq (modeVel ι (weighted v) σ y))) :=
            ((hcw ι).lintegral_prod_right' (ν := volume)).const_mul _
          rw [lintegral_add_left hmo,
            lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  have hLsum : ∑' ι, L ι ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hLle)
    rw [ENNReal.tsum_add, ENNReal.tsum_mul_left, ENNReal.tsum_mul_left]
    exact ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top hA.ne,
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top hZ.ne⟩
  have hLi : ∀ ι, L ι ≠ ⊤ := fun ι => ne_top_of_le_ne_top hLsum (ENNReal.le_tsum ι)
  refine Summable.of_norm_bounded (g := fun ι => (L ι).toReal) (ENNReal.summable_toReal hLsum) fun ι => ?_
  unfold pairMode
  refine (norm_integral_le_lintegral_norm _).trans (ENNReal.toReal_mono (hLi ι) ?_)
  refine lintegral_mono fun σ => ?_
  refine ENNReal.ofReal_le_of_le_toReal ((norm_integral_le_lintegral_norm _).trans ?_)
  simp only [Real.norm_eq_abs]
  exact le_rfl

end Internal.MuSmooth

end Coercive

end Breakdown
