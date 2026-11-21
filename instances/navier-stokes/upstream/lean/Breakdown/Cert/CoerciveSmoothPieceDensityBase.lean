import Breakdown.Cert.CoerciveNodes
import Breakdown.Cert.CoercivePieceAbsorb
import Breakdown.Cert.CoerciveBase
import Breakdown.Cert.CoerciveRotation

open scoped ContDiff ENNReal
open MeasureTheory

noncomputable section

namespace Breakdown

namespace Coercive

namespace Internal.SmoothPieceDensity

open Internal.PieceAbsorb Internal.FieldModes

def dampVel (v : ℝ → Space → Space) (σ : ℝ) (y : Space) : Space :=
  (Real.sqrt (1 + ‖y‖ ^ 2))⁻¹ • v σ y

theorem modeVel_dampVel (ι : ℤ × ℤ) (v : ℝ → Space → Space) (σ : ℝ) (y : Space) :
    modeVel ι (dampVel v) σ y =
      fun i => (((Real.sqrt (1 + ‖y‖ ^ 2))⁻¹ : ℝ) : ℂ) * modeVel ι v σ y i := by
  funext i
  unfold modeVel dampVel
  rw [← BaseDensityInternal.modeAverage_const_mul]
  congr 1
  funext τ φ j
  rw [RotationInternal.axialRot_norm, RotationInternal.axialRot_map_smul, PiLp.smul_apply, smul_eq_mul]

theorem cnormSq_modeVel_dampVel (ι : ℤ × ℤ) (v : ℝ → Space → Space) (σ : ℝ) (y : Space) :
    cnormSq (modeVel ι (dampVel v) σ y) = cnormSq (modeVel ι v σ y) / (1 + ‖y‖ ^ 2) := by
  rw [modeVel_dampVel]
  have hpos : 0 < 1 + ‖y‖ ^ 2 := by positivity
  unfold cnormSq
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
  rw [← Finset.mul_sum, inv_pow, Real.sq_sqrt hpos.le, div_eq_inv_mul]

theorem norm_dampVel_sq (v : ℝ → Space → Space) (σ : ℝ) (y : Space) :
    ‖dampVel v σ y‖ ^ 2 = ‖v σ y‖ ^ 2 / (1 + ‖y‖ ^ 2) := by
  have hpos : 0 < 1 + ‖y‖ ^ 2 := by positivity
  unfold dampVel
  rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, inv_pow, Real.sq_sqrt hpos.le, div_eq_inv_mul]

theorem tsum_slab_base {f : ℤ × ℤ → ℝ × Space → ℝ≥0∞} (hf : ∀ ι, AEMeasurable (f ι) slabMeasure) :
    ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ∑' ι, f ι (σ, y)
      = ∑' ι, ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, f ι (σ, y) := by
  have h1 := lintegral_prod (μ := volume.restrict (Set.Icc (0 : ℝ) 1)) (ν := (volume : Measure Space))
    (fun z => ∑' ι, f ι z) (AEMeasurable.ennreal_tsum hf)
  rw [← h1, lintegral_tsum hf]
  refine tsum_congr fun ι => ?_
  exact lintegral_prod _ (hf ι)

theorem periodLIntegral_lt_top_of_le_base {f g : ℝ → Space → ℝ} {c : ℝ} (hc : 0 ≤ c)
    (hfg : ∀ σ y, f σ y ≤ c * g σ y) (hg : periodLIntegral g < ⊤) : periodLIntegral f < ⊤ := by
  unfold periodLIntegral at hg ⊢
  calc (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ENNReal.ofReal (f σ y))
      ≤ ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ENNReal.ofReal c * ENNReal.ofReal (g σ y) :=
        lintegral_mono fun σ => lintegral_mono fun y => by
          rw [← ENNReal.ofReal_mul hc]
          exact ENNReal.ofReal_le_ofReal (hfg σ y)
    _ = ENNReal.ofReal c * ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ENNReal.ofReal (g σ y) := by
        simp_rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hg

theorem norm_unitVector_base (i : Fin 3) : ‖unitVector i‖ = 1 := by
  unfold unitVector
  simp

theorem secondDerivSq_le_base (H : Space →L[ℝ] Space →L[ℝ] Space) : secondDerivSq H ≤ 9 * ‖H‖ ^ 2 := by
  unfold secondDerivSq
  have hb : ∀ j l : Fin 3, ‖H (unitVector j) (unitVector l)‖ ^ 2 ≤ ‖H‖ ^ 2 := by
    intro j l
    have h1 : ‖H (unitVector j) (unitVector l)‖ ≤ ‖H‖ := by
      calc ‖H (unitVector j) (unitVector l)‖ ≤ ‖H (unitVector j)‖ * ‖unitVector l‖ := (H (unitVector j)).le_opNorm _
        _ ≤ ‖H‖ * ‖unitVector j‖ * ‖unitVector l‖ := by
            gcongr
            exact H.le_opNorm _
        _ = ‖H‖ := by rw [norm_unitVector_base, norm_unitVector_base, mul_one, mul_one]
    exact pow_le_pow_left₀ (norm_nonneg _) h1 2
  calc ∑ j : Fin 3, ∑ l : Fin 3, ‖H (unitVector j) (unitVector l)‖ ^ 2
      ≤ ∑ j : Fin 3, ∑ l : Fin 3, ‖H‖ ^ 2 := Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun l _ => hb j l
    _ = 9 * ‖H‖ ^ 2 := by simp; ring

theorem matSq_le_base (G : Space →L[ℝ] Space) : matSq G ≤ 3 * ‖G‖ ^ 2 := by
  unfold matSq
  have hb : ∀ i : Fin 3, ‖G (unitVector i)‖ ^ 2 ≤ ‖G‖ ^ 2 := by
    intro i
    have h1 : ‖G (unitVector i)‖ ≤ ‖G‖ := by
      calc ‖G (unitVector i)‖ ≤ ‖G‖ * ‖unitVector i‖ := G.le_opNorm _
        _ = ‖G‖ := by rw [norm_unitVector_base, mul_one]
    exact pow_le_pow_left₀ (norm_nonneg _) h1 2
  calc ∑ i : Fin 3, ‖G (unitVector i)‖ ^ 2 ≤ ∑ i : Fin 3, ‖G‖ ^ 2 := Finset.sum_le_sum fun i _ => hb i
    _ = 3 * ‖G‖ ^ 2 := by simp

theorem base_coef_bound {x2 xc x1 xo x0 cD hD cZ hZ c wv Bd Bz K1 Bw q : ℝ}
    (hcD : |cD| ≤ Bd) (hhD : hD ≤ K1) (hcZ : |cZ| ≤ Bz) (hhZ : hZ ≤ Bz * q) (hc : 0 < c) (hw0 : 0 ≤ wv)
    (hwB : wv ≤ Bw) (hq : 0 ≤ q) (hxc : xc ^ 2 ≤ 729 * x2 ^ 2) (hxo : xo ^ 2 ≤ 243 * x1 ^ 2)
    (hBd : 0 ≤ Bd) (hBz : 0 ≤ Bz) (hK1 : 0 ≤ K1) (hBw : 0 ≤ Bw) :
    -((cD - c) * x2 ^ 2 + (1 - cD) * xc ^ 2 + (1 / 4 - cZ) * xo ^ 2 + (cZ - hD - c * wv) * x1 ^ 2 - hZ * x0 ^ 2)
      ≤ (Bd + c + 729 * (1 + Bd) + 243 * (1 / 4 + Bz) + Bz + K1 + c * Bw + Bz)
          * (x2 ^ 2 + x1 ^ 2 + q * x0 ^ 2) := by
  have a1 := abs_le.1 hcD
  have a2 := abs_le.1 hcZ
  have s2 := sq_nonneg x2
  have sc := sq_nonneg xc
  have s1 := sq_nonneg x1
  have so := sq_nonneg xo
  have s0 := sq_nonneg x0
  have t1 : -(cD - c) * x2 ^ 2 ≤ (Bd + c) * x2 ^ 2 := mul_le_mul_of_nonneg_right (by linarith) s2
  have t2 : -(1 - cD) * xc ^ 2 ≤ 729 * (1 + Bd) * x2 ^ 2 := by
    have := mul_le_mul_of_nonneg_right (show -(1 - cD) ≤ 1 + Bd by linarith) sc
    nlinarith
  have t3 : -(1 / 4 - cZ) * xo ^ 2 ≤ 243 * (1 / 4 + Bz) * x1 ^ 2 := by
    have := mul_le_mul_of_nonneg_right (show -(1 / 4 - cZ) ≤ 1 / 4 + Bz by linarith) so
    nlinarith
  have t4 : -(cZ - hD - c * wv) * x1 ^ 2 ≤ (Bz + K1 + c * Bw) * x1 ^ 2 := by
    have : c * wv ≤ c * Bw := mul_le_mul_of_nonneg_left hwB hc.le
    exact mul_le_mul_of_nonneg_right (by linarith) s1
  have t5 : hZ * x0 ^ 2 ≤ Bz * (q * x0 ^ 2) := by
    have := mul_le_mul_of_nonneg_right hhZ s0
    linarith [mul_assoc Bz q (x0 ^ 2)]
  have hq0 : 0 ≤ q * x0 ^ 2 := mul_nonneg hq s0
  have hcB : 0 ≤ c * Bw := mul_nonneg hc.le hBw
  have k2 : (Bd + c + 729 * (1 + Bd)) * x2 ^ 2
      ≤ (Bd + c + 729 * (1 + Bd) + 243 * (1 / 4 + Bz) + Bz + K1 + c * Bw + Bz) * x2 ^ 2 :=
    mul_le_mul_of_nonneg_right (by linarith) s2
  have k1 : (243 * (1 / 4 + Bz) + (Bz + K1 + c * Bw)) * x1 ^ 2
      ≤ (Bd + c + 729 * (1 + Bd) + 243 * (1 / 4 + Bz) + Bz + K1 + c * Bw + Bz) * x1 ^ 2 :=
    mul_le_mul_of_nonneg_right (by linarith) s1
  have k0 : Bz * (q * x0 ^ 2)
      ≤ (Bd + c + 729 * (1 + Bd) + 243 * (1 / 4 + Bz) + Bz + K1 + c * Bw + Bz) * (q * x0 ^ 2) :=
    mul_le_mul_of_nonneg_right (by linarith) hq0
  have ex : (Bd + c + 729 * (1 + Bd) + 243 * (1 / 4 + Bz) + Bz + K1 + c * Bw + Bz) * (x2 ^ 2 + x1 ^ 2 + q * x0 ^ 2)
      = (Bd + c + 729 * (1 + Bd) + 243 * (1 / 4 + Bz) + Bz + K1 + c * Bw + Bz) * x2 ^ 2
        + (Bd + c + 729 * (1 + Bd) + 243 * (1 / 4 + Bz) + Bz + K1 + c * Bw + Bz) * x1 ^ 2
        + (Bd + c + 729 * (1 + Bd) + 243 * (1 / 4 + Bz) + Bz + K1 + c * Bw + Bz) * (q * x0 ^ 2) := by ring
  rw [ex]
  linarith

section Pieces

variable {C : Type} {nE nM : ℕ} (m : PieceWeights C nE nM) (P : ℝ) (h : HarmonicBounds) (w : Space → ℝ)
  (W v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
  (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space))

theorem secondDerivNorm_convD_bound_base {w₀ epsSup epsGradSup ratio : ℝ}
    (hm : m.IsAdmissible P h w W w₀ epsSup epsGradSup ratio) :
    ∃ K1, 0 ≤ K1 ∧ ∀ c y, ModeWeights.secondDerivNorm (m.convD c) y ≤ K1 := by
  obtain ⟨Bd, hBd⟩ := hm.convD_decay
  have hc : ∀ c, ∃ K, ∀ y, ModeWeights.secondDerivNorm (m.convD c) y ≤ K := by
    intro c
    obtain ⟨K, hK⟩ := (isCompact_closedBall (0 : Space) 1).exists_bound_of_continuousOn
      ((hm.convD_smooth c).continuous_iteratedFDeriv (m := 2) le_rfl).norm.continuousOn
    refine ⟨max K Bd, fun y => ?_⟩
    by_cases hy : ‖y‖ ≤ 1
    · have h1 := hK y (by rw [Metric.mem_closedBall, dist_zero_right]; exact hy)
      rw [norm_norm] at h1
      exact le_max_of_le_left h1
    · rw [not_le] at hy
      have h2 := hBd c y 2 le_rfl
      have hn := norm_nonneg (iteratedFDeriv ℝ 2 (m.convD c) y)
      have : ModeWeights.secondDerivNorm (m.convD c) y ≤ Bd := by
        unfold ModeWeights.secondDerivNorm
        nlinarith [mul_nonneg hn (show (0 : ℝ) ≤ ‖y‖ ^ 2 - 1 by nlinarith)]
      exact le_max_of_le_right this
  choose Kc hKc using hc
  have := hm.finite_classes
  letI := Fintype.ofFinite C
  exact ⟨∑ c, |Kc c|, Finset.sum_nonneg fun c _ => abs_nonneg _, fun c y =>
    (hKc c y).trans ((le_abs_self _).trans (Finset.single_le_sum (f := fun c => |Kc c|)
      (fun c _ => abs_nonneg (Kc c)) (Finset.mem_univ c)))⟩

theorem base_neg_finite_of_mode_sums (hP : ModeSquareSumHolds) {w₀ epsSup epsGradSup ratio : ℝ}
    (hm : m.IsAdmissible P h w W w₀ epsSup epsGradSup ratio)
    (hwb : ∃ B, ∀ y, w y ≤ B) (hv : IsSmoothPerturbation P v) :
    (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ∑' ι, ENNReal.ofReal
      (-modeVals v (gradField v) (secondDerivField v) ι σ y (baseDensity m.convD m.convZ (m.classOf ι) m.c w y))) < ⊤ := by
  obtain ⟨Bd, hBd⟩ := hm.convD_decay
  obtain ⟨Bz, hBz⟩ := hm.convZ_decay
  obtain ⟨Bw, hBw⟩ := hwb
  obtain ⟨K1, hK10, hK1⟩ := secondDerivNorm_convD_bound_base m P h w W hm
  have hBd0 : 0 ≤ Bd := le_trans (by positivity) (hBd (m.classOf 0) 0 0 (by norm_num))
  have hBz0 : 0 ≤ Bz := le_trans (by positivity) (hBz (m.classOf 0) 0 0 (by norm_num))
  have hBw0 : 0 ≤ Bw := le_trans (hm.weight_pos.le.trans (hm.weight_lower 0)) (hBw 0)
  have hcD : ∀ c y, |m.convD c y| ≤ Bd := fun c y => by
    have := hBd c y 0 (by norm_num)
    simpa [norm_iteratedFDeriv_zero, Real.norm_eq_abs] using this
  have hcZ : ∀ c y, |m.convZ c y| ≤ Bz := fun c y => by
    have := hBz c y 0 (by norm_num)
    simpa [norm_iteratedFDeriv_zero, Real.norm_eq_abs] using this
  have hhZ : ∀ c y, ModeWeights.secondDerivNorm (m.convZ c) y ≤ Bz * (1 / (1 + ‖y‖ ^ 2)) := fun c y => by
    have h2 := hBz c y 2 le_rfl
    have hp : 0 < (1 + ‖y‖) ^ 2 := by positivity
    have hq : 0 < 1 + ‖y‖ ^ 2 := by positivity
    have hle : 1 + ‖y‖ ^ 2 ≤ (1 + ‖y‖) ^ 2 := by nlinarith [norm_nonneg y]
    unfold ModeWeights.secondDerivNorm
    have e1 : ‖iteratedFDeriv ℝ 2 (m.convZ c) y‖ ≤ Bz / (1 + ‖y‖) ^ 2 := by
      rw [le_div_iff₀ hp]
      linarith
    calc ‖iteratedFDeriv ℝ 2 (m.convZ c) y‖ ≤ Bz / (1 + ‖y‖) ^ 2 := e1
      _ ≤ Bz / (1 + ‖y‖ ^ 2) := div_le_div_of_nonneg_left hBz0 hq hle
      _ = Bz * (1 / (1 + ‖y‖ ^ 2)) := by ring
  set K := Bd + m.c + 729 * (1 + Bd) + 243 * (1 / 4 + Bz) + Bz + K1 + m.c * Bw + Bz with hKdef
  have hK0 : 0 ≤ K := by
    have := hm.c_pos
    positivity
  have hpt : ∀ ι σ y, -modeVals v (gradField v) (secondDerivField v) ι σ y
      (baseDensity m.convD m.convZ (m.classOf ι) m.c w y)
      ≤ K * (cnormSq (modeSecondDeriv ι (secondDerivField v) σ y) + cnormSq (modeGrad ι (gradField v) σ y)
        + cnormSq (modeVel ι (dampVel v) σ y)) := by
    intro ι σ y
    have e2 := Real.sq_sqrt (cnormSq_nonneg' (modeSecondDeriv ι (secondDerivField v) σ y))
    have ec := Real.sq_sqrt (cnormSq_nonneg' (curlGradOfSecondDeriv (modeSecondDeriv ι (secondDerivField v) σ y)))
    have e1 := Real.sq_sqrt (cnormSq_nonneg' (modeGrad ι (gradField v) σ y))
    have eo := Real.sq_sqrt (cnormSq_nonneg' (curlOfGrad (modeGrad ι (gradField v) σ y)))
    have e0 := Real.sq_sqrt (cnormSq_nonneg' (modeVel ι v σ y))
    have hd := cnormSq_modeVel_dampVel ι v σ y
    have hq : 0 < 1 + ‖y‖ ^ 2 := by positivity
    have key := base_coef_bound (x2 := secondDerivAmp (secondDerivField v) ι σ y) (xc := vortGradAmp (secondDerivField v) ι σ y)
      (x1 := gradAmp (gradField v) ι σ y) (xo := vortAmp (gradField v) ι σ y) (x0 := velAmp v ι σ y)
      (hcD (m.classOf ι) y) (hK1 (m.classOf ι) y) (hcZ (m.classOf ι) y) (hhZ (m.classOf ι) y) hm.c_pos
      (hm.weight_pos.le.trans (hm.weight_lower y)) (hBw y) (by positivity)
      (by
        unfold vortGradAmp secondDerivAmp
        rw [ec, e2]
        exact cnormSq_curlGradOfSecondDeriv_le _)
      (by
        unfold vortAmp gradAmp
        rw [eo, e1]
        exact cnormSq_curlOfGrad_le _) hBd0 hBz0 hK10 hBw0
    unfold modeVals baseDensity
    rw [hd]
    refine le_trans key (le_of_eq ?_)
    unfold secondDerivAmp gradAmp velAmp
    rw [e2, e1, e0, hKdef]
    ring
  have hGc : Continuous (fun z : ℝ × Space => gradField v z.1 z.2) :=
    continuous_fderiv_slice (hv.smooth.of_le (by first | exact_mod_cast (le_top : (2 : ℕ∞) ≤ ⊤) | simp | decide))
  have hHm : Measurable (fun z : ℝ × Space => secondDerivField v z.1 z.2) :=
    measurable_secondDeriv_slice (hv.smooth.of_le (by first | exact_mod_cast (le_top : (2 : ℕ∞) ≤ ⊤) | simp | decide))
  have hvc : Continuous (fun z : ℝ × Space => v z.1 z.2) := hv.smooth.continuous
  have hXm : AEStronglyMeasurable (fun z : ℝ × Space => dampVel v z.1 z.2) volume := by
    have hc : Continuous (fun z : ℝ × Space => (Real.sqrt (1 + ‖z.2‖ ^ 2))⁻¹) := by
      refine Continuous.inv₀ (by fun_prop) fun z => ?_
      exact (Real.sqrt_pos.2 (by positivity)).ne'
    exact hc.aestronglyMeasurable.smul hvc.aestronglyMeasurable
  have mH : ∀ ι, AEMeasurable (fun z : ℝ × Space =>
      ENNReal.ofReal (cnormSq (modeSecondDeriv ι (secondDerivField v) z.1 z.2))) slabMeasure := fun ι =>
    aemeasurable_ofReal_cnormSq (aemeasurable_modeSecondDeriv hHm.aestronglyMeasurable ι)
  have mG : ∀ ι, AEMeasurable (fun z : ℝ × Space =>
      ENNReal.ofReal (cnormSq (modeGrad ι (gradField v) z.1 z.2))) slabMeasure := fun ι =>
    aemeasurable_ofReal_cnormSq (aemeasurable_modeGrad hGc.aestronglyMeasurable ι)
  have mV : ∀ ι, AEMeasurable (fun z : ℝ × Space =>
      ENNReal.ofReal (cnormSq (modeVel ι (dampVel v) z.1 z.2))) slabMeasure := fun ι =>
    aemeasurable_ofReal_cnormSq (aemeasurable_modeVel hXm ι)
  have hvp : ∀ σ, v (σ + 1) = v σ := fun σ => funext (hv.periodic σ)
  have pH : IsTimePeriodic (secondDerivField v) := fun σ y => by simp only [secondDerivField, hvp]
  have pG : IsTimePeriodic (gradField v) := fun σ y => by simp only [gradField, hvp]
  have pV : IsTimePeriodic (dampVel v) := fun σ y => by simp only [dampVel, hvp]
  have fH : periodLIntegral (fun σ y => secondDerivSq (secondDerivField v σ y)) < ⊤ := by
    refine periodLIntegral_lt_top_of_le_base (by norm_num : (0 : ℝ) ≤ 9) (fun σ y => ?_) (hv.derivatives_finite 2 (by norm_num))
    have := secondDerivSq_le_base (secondDerivField v σ y)
    rwa [secondDerivField, ← norm_iteratedFDeriv_one (𝕜 := ℝ), norm_iteratedFDeriv_fderiv] at this
  have fG : periodLIntegral (fun σ y => matSq (gradField v σ y)) < ⊤ := by
    refine periodLIntegral_lt_top_of_le_base (by norm_num : (0 : ℝ) ≤ 3) (fun σ y => ?_) (hv.derivatives_finite 1 le_rfl)
    have := matSq_le_base (gradField v σ y)
    rwa [gradField, ← norm_iteratedFDeriv_one (𝕜 := ℝ)] at this
  have fV : periodLIntegral (fun σ y => ‖dampVel v σ y‖ ^ 2) < ⊤ := by
    refine periodLIntegral_lt_top_of_le_base (by norm_num : (0 : ℝ) ≤ 2) (fun σ y => ?_) hv.weighted_finite
    rw [norm_dampVel_sq]
    have hq : 0 < 1 + ‖y‖ ^ 2 := by positivity
    have hp : 0 < (1 + ‖y‖) ^ 2 := by positivity
    rw [div_le_iff₀ hq, mul_comm, ← mul_assoc, mul_div_assoc']
    rw [le_div_iff₀ hp]
    nlinarith [sq_nonneg ‖v σ y‖, sq_nonneg (‖y‖ - 1), norm_nonneg y, mul_nonneg (sq_nonneg ‖v σ y‖) (sq_nonneg (‖y‖ - 1))]
  have eH := hP.2.2.1 (secondDerivField v) hHm.aestronglyMeasurable pH fH
  have eG := hP.2.1 (gradField v) hGc.aestronglyMeasurable pG fG
  have eV := hP.1 (dampVel v) hXm pV fV
  have sH := tsum_slab_base (f := fun ι z => ENNReal.ofReal (cnormSq (modeSecondDeriv ι (secondDerivField v) z.1 z.2))) mH
  have sG := tsum_slab_base (f := fun ι z => ENNReal.ofReal (cnormSq (modeGrad ι (gradField v) z.1 z.2))) mG
  have sV := tsum_slab_base (f := fun ι z => ENNReal.ofReal (cnormSq (modeVel ι (dampVel v) z.1 z.2))) mV
  have mSG := AEMeasurable.ennreal_tsum mG
  have mSV := AEMeasurable.ennreal_tsum mV
  calc (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ∑' ι, ENNReal.ofReal
        (-modeVals v (gradField v) (secondDerivField v) ι σ y (baseDensity m.convD m.convZ (m.classOf ι) m.c w y)))
      ≤ ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ENNReal.ofReal K *
          ((∑' ι, ENNReal.ofReal (cnormSq (modeSecondDeriv ι (secondDerivField v) σ y)))
            + (∑' ι, ENNReal.ofReal (cnormSq (modeGrad ι (gradField v) σ y)))
            + ∑' ι, ENNReal.ofReal (cnormSq (modeVel ι (dampVel v) σ y))) := by
        refine lintegral_mono fun σ => lintegral_mono fun y => ?_
        rw [← ENNReal.tsum_add, ← ENNReal.tsum_add, ← ENNReal.tsum_mul_left]
        refine ENNReal.tsum_le_tsum fun ι => ?_
        rw [← ENNReal.ofReal_add (cnormSq_nonneg' _) (cnormSq_nonneg' _),
          ← ENNReal.ofReal_add (add_nonneg (cnormSq_nonneg' _) (cnormSq_nonneg' _)) (cnormSq_nonneg' _),
          ← ENNReal.ofReal_mul hK0]
        exact ENNReal.ofReal_le_ofReal (hpt ι σ y)
    _ = ENNReal.ofReal K * ((∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y,
            ∑' ι, ENNReal.ofReal (cnormSq (modeSecondDeriv ι (secondDerivField v) σ y)))
          + (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ∑' ι, ENNReal.ofReal (cnormSq (modeGrad ι (gradField v) σ y)))
          + ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ∑' ι, ENNReal.ofReal (cnormSq (modeVel ι (dampVel v) σ y))) := by
        simp_rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        rw [lintegral_add_iter mSV, lintegral_add_iter mSG]
    _ < ⊤ := by
        refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_
        simp only at sH sG sV
        rw [sH, sG, sV, ← eH, ← eG, ← eV]
        exact ENNReal.add_lt_top.2 ⟨ENNReal.add_lt_top.2 ⟨fH, fG⟩, fV⟩

end Pieces

end Internal.SmoothPieceDensity

end Coercive

end Breakdown
