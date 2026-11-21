import Breakdown.Cert.CoerciveSmoothMuSplit
import Breakdown.Cert.CoerciveSmoothMuWave

open scoped ContDiff ENNReal
open MeasureTheory

noncomputable section

namespace Breakdown

namespace Coercive

namespace Internal.MuSmooth

theorem ofReal_abs_pairMode_le {C : Type} (m : ModeWeights C) (v X : ℝ → Space → Space) (ι : ℤ × ℤ) :
    ENNReal.ofReal |pairMode m v X ι|
      ≤ ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ENNReal.ofReal |pairTerm m v X ι σ y| := by
  unfold pairMode
  rw [← Real.enorm_eq_ofReal_abs]
  refine (enorm_integral_le_lintegral_enorm _).trans (lintegral_mono fun σ => ?_)
  refine (enorm_integral_le_lintegral_enorm _).trans (lintegral_mono fun y => ?_)
  rw [Real.enorm_eq_ofReal_abs]

theorem split_const (e : ℝ → Space → ℝ≥0∞) (he : Measurable (fun p : ℝ × Space => e p.1 p.2))
    (c : ℝ≥0∞) (hc : c ≠ ⊤) (g : ℝ → Space → ℝ≥0∞) :
    ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, (e σ y + c * g σ y)
      = (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, e σ y) + c * ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, g σ y := by
  have hin : ∀ σ, ∫⁻ y, (e σ y + c * g σ y) = (∫⁻ y, e σ y) + c * ∫⁻ y, g σ y := fun σ => by
    have hmσ : Measurable (fun y => e σ y) := he.comp measurable_prodMk_left
    rw [lintegral_add_left hmσ, lintegral_const_mul' _ _ hc]
  simp_rw [hin]
  have hmo : Measurable (fun σ => ∫⁻ y, e σ y) := he.lintegral_prod_right' (ν := volume)
  rw [lintegral_add_left hmo, lintegral_const_mul' _ _ hc]

theorem weighted_product_term (w ca cb η : ℝ) (hη : 0 < η) (hca : 0 ≤ ca) (hcb : 0 ≤ cb) (a b : Fin 3 → ℂ)
    (ha : cnormSq a = ca) (hb : cnormSq b = cb) :
    |(Complex.I * (w : ℂ) * cdot a b).re| ≤ (η / 2) * w ^ 2 * ca + (1 / (2 * η)) * cb := by
  rcases eq_or_ne w 0 with hw | hw
  · subst hw
    simp only [Complex.ofReal_zero, mul_zero, zero_mul, Complex.zero_re, abs_zero]
    positivity
  · have ht : 0 < η * |w| := mul_pos hη (abs_pos.2 hw)
    have h := ModeL2Internal.abs_re_weighted_le w a b ht
    rw [ha, hb] at h
    have hw2 : |w| ^ 2 = w ^ 2 := sq_abs w
    have e : |w| * ((η * |w| * ca + cb / (η * |w|)) / 2) = (η / 2) * w ^ 2 * ca + (1 / (2 * η)) * cb := by
      rw [← hw2]
      field_simp
    linarith

theorem pressure_bound_of (hPars : ModeSquareSumHolds) (hSolenoidal : SolenoidalModeHolds)
    {C : Type} (m : ModeWeights C) (P : ℝ) (b : FlowBounds C)
    (w : Space → ℝ) (W : ℝ → Space → Space) {w₀ epsSup epsGradSup ratio : ℝ}
    (hm : m.IsAdmissible P b w w₀ epsSup epsGradSup ratio) (hb : b.IsValid m W)
    (hW : ContDiff ℝ 2 (fun z : ℝ × Space => W z.1 z.2)) (hWp : IsTimePeriodic W)
    (hWdiv : ∀ σ y, divergenceAt (W σ) y = 0)
    (hWdecay : ∃ D, ∀ σ y, ∀ j ≤ 2, ‖iteratedFDeriv ℝ j (W σ) y‖ ≤ D / (1 + ‖y‖) ^ (j + 1))
    (v : ℝ → Space → Space) (hv : IsSmoothPerturbation P v) (Q : ℝ → Space → Space)
    (hQ : IsSolenoidalPartOf (smoothRight P W v) Q) (Q' : ℝ → Space → Space)
    (hQ' : IsSolenoidalPartOf (fun σ y => fderiv ℝ (W σ) y (v σ y)) Q') (ι : ℤ × ℤ) :
    ENNReal.ofReal (-pairMode m v (fun σ y => (2 : ℝ) • Q' σ y - fderiv ℝ (W σ) y (v σ y)) ι)
      ≤ ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ENNReal.ofReal (pressureLoss m W v ι σ y) := by
  set Y : ℝ → Space → Space := fun σ y => (2 : ℝ) • Q' σ y - fderiv ℝ (W σ) y (v σ y) with hYdef
  set F' : ℝ → Space → Space := fun σ y => fderiv ℝ (W σ) y (v σ y) with hFdef
  obtain ⟨hFm, hFp, hF2, -, -, -, -⟩ := solenoidal_split_smooth hSolenoidal P W hW hWp hWdiv hWdecay v hv Q hQ
  obtain ⟨-, -, -, hrefl⟩ := solenoidal_reflection_modes hPars hSolenoidal F' Q' hFm hFp hF2 hQ'
  have hη := hm.eta_pos (m.classOf ι)
  set η := m.eta (m.classOf ι) with hηdef
  by_cases hz : ∃ x, m.muW (m.classOf ι) x ≠ 0
  swap
  · push Not at hz
    have h0 : pairMode m v Y ι = 0 := by
      unfold pairMode pairTerm
      simp [hz]
    rw [h0, neg_zero, ENNReal.ofReal_zero]
    exact bot_le
  have hind : ModeWeights.ind (∃ x, m.muW (m.classOf ι) x ≠ 0) = 1 := by
    unfold ModeWeights.ind
    rw [if_pos hz]
  obtain ⟨K, hK⟩ := hm.muW_increment (m.classOf ι)
  have hvc : Continuous (fun z : ℝ × Space => v z.1 z.2) := hv.smooth.continuous
  set e : ℝ → Space → ℝ≥0∞ := fun σ y =>
    ENNReal.ofReal ((η / 2) * m.muW (m.classOf ι) y ^ 2 * cnormSq (modeVel ι v σ y)) with hedef
  have he : Measurable (fun p : ℝ × Space => e p.1 p.2) :=
    ((continuous_const.mul (((hK.continuous.comp continuous_snd)).pow 2)).mul
      (continuous_cnormSq_modeVel hvc ι)).measurable.ennreal_ofReal
  have hc : ENNReal.ofReal (1 / (2 * η)) ≠ ⊤ := ENNReal.ofReal_ne_top
  have hηc : 0 ≤ 1 / (2 * η) := by positivity
  have step1 : ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ENNReal.ofReal |pairTerm m v Y ι σ y|
      ≤ ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y,
        (e σ y + ENNReal.ofReal (1 / (2 * η)) * ENNReal.ofReal (cnormSq (modeVel ι Y σ y))) := by
    refine lintegral_mono fun σ => lintegral_mono fun y => ?_
    rw [hedef, ← ENNReal.ofReal_mul hηc, ← ENNReal.ofReal_add
      (mul_nonneg (mul_nonneg (by positivity) (sq_nonneg _)) (cnorm_nonneg _))
      (mul_nonneg hηc (cnorm_nonneg _))]
    exact ENNReal.ofReal_le_ofReal (weighted_product_term _ _ _ η hη (cnorm_nonneg _) (cnorm_nonneg _) _ _ rfl rfl)
  have step2 : ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y,
        (e σ y + ENNReal.ofReal (1 / (2 * η)) * ENNReal.ofReal (cnormSq (modeVel ι Y σ y)))
      = ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y,
        (e σ y + ENNReal.ofReal (1 / (2 * η)) * ENNReal.ofReal (cnormSq (modeVel ι F' σ y))) := by
    rw [split_const e he _ hc, split_const e he _ hc, hrefl ι]
  have step3 : ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y,
        (e σ y + ENNReal.ofReal (1 / (2 * η)) * ENNReal.ofReal (cnormSq (modeVel ι F' σ y)))
      ≤ ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ENNReal.ofReal (pressureLoss m W v ι σ y) := by
    refine lintegral_mono fun σ => lintegral_mono fun y => ?_
    rw [hedef, ← ENNReal.ofReal_mul hηc, ← ENNReal.ofReal_add
      (mul_nonneg (mul_nonneg (by positivity) (sq_nonneg _)) (cnorm_nonneg _))
      (mul_nonneg hηc (cnorm_nonneg _))]
    refine ENNReal.ofReal_le_ofReal ?_
    have hs := stretch_mode_le m P b w W hm hb hW hWp hWdecay v hv ι σ y
    set A := ‖fderiv ℝ (meanField W) y‖ * velAmp v ι σ y
    set S := ∑ α ∈ m.waves, gradAmp (gradField W) α σ y * velAmp v (ι - α) σ y
    have hcf : cnormSq (modeVel ι F' σ y) ≤ 2 * (A ^ 2 + S ^ 2) := by
      have h0 := Real.sqrt_nonneg (cnormSq (modeVel ι F' σ y))
      have h1 : cnormSq (modeVel ι F' σ y) = Real.sqrt (cnormSq (modeVel ι F' σ y)) ^ 2 :=
        (Real.sq_sqrt (cnorm_nonneg _)).symm
      rw [h1]
      nlinarith [sq_nonneg (A - S)]
    have hva : velAmp v ι σ y ^ 2 = cnormSq (modeVel ι v σ y) := Real.sq_sqrt (cnorm_nonneg _)
    have hmu : m.mu ι y ^ 2 = m.muW (m.classOf ι) y ^ 2 := sq_abs _
    unfold pressureLoss
    rw [hind, one_mul, hmu, hva]
    have hA : ‖fderiv ℝ (meanField W) y‖ ^ 2 * cnormSq (modeVel ι v σ y) = A ^ 2 := by
      rw [← hva]
      ring
    rw [hA]
    have hdiv : 1 / (2 * η) * cnormSq (modeVel ι F' σ y) ≤ (A ^ 2 + S ^ 2) / η := by
      rw [div_mul_eq_mul_div, one_mul, div_le_div_iff₀ (by positivity) hη]
      nlinarith
    nlinarith
  calc ENNReal.ofReal (-pairMode m v Y ι) ≤ ENNReal.ofReal |pairMode m v Y ι| :=
        ENNReal.ofReal_le_ofReal (neg_le_abs _)
    _ ≤ _ := ofReal_abs_pairMode_le m v Y ι
    _ ≤ _ := step1
    _ = _ := step2
    _ ≤ _ := step3

end Internal.MuSmooth

end Coercive

end Breakdown
