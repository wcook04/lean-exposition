import Breakdown.Frac.StTorusShell
import Breakdown.Torus.HeatComparisonDensity
import Breakdown.Torus.HeatComparisonFreeDensity

open MeasureTheory Set Real
open scoped ENNReal ContDiff

noncomputable section

namespace Breakdown.Periodic.FracDensity.Internal

open Breakdown.Periodic

theorem factor_pos (α τ : ℝ) (ξ : Space) : 0 < Freq.fracHeatFactor α τ ξ := Real.exp_pos _

theorem factor_le_one (α τ : ℝ) (ξ : Space) : Freq.fracHeatFactor α τ ξ ≤ 1 := by
  unfold Freq.fracHeatFactor
  exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr
    (mul_nonneg (le_max_right τ 0) (Real.rpow_nonneg (by positivity) _)))

theorem sq_sub_one_le_rpow {α : ℝ} (hα : 1 ≤ α) {s : ℝ} (hs : 0 ≤ s) :
    s ^ 2 - 1 ≤ s ^ (2 * α) := by
  rcases le_total 1 s with h | h
  · have h1 : s ^ (2 : ℝ) ≤ s ^ (2 * α) := Real.rpow_le_rpow_of_exponent_le h (by linarith)
    rw [Real.rpow_two] at h1
    linarith
  · have h1 : s ^ 2 ≤ 1 := by nlinarith
    have h2 : 0 ≤ s ^ (2 * α) := Real.rpow_nonneg hs _
    linarith

theorem factor_le_heat {α ε τ : ℝ} (hα : 1 ≤ α) (hε : 0 < ε) (hτ : ε ≤ τ) (ξ : Space) :
    Freq.fracHeatFactor α τ ξ ≤ Real.exp ε * Freq.heatFactor ε ξ := by
  unfold Freq.fracHeatFactor Freq.heatFactor
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hm : ε ≤ max τ 0 := le_max_of_le_left hτ
  rw [max_eq_left hε.le]
  have hs := sq_sub_one_le_rpow hα (by positivity : (0 : ℝ) ≤ 2 * π * ‖ξ‖)
  have hp : 0 ≤ (2 * π * ‖ξ‖) ^ (2 * α) := Real.rpow_nonneg (by positivity) _
  have h1 : ε * (2 * π * ‖ξ‖) ^ (2 * α) ≤ max τ 0 * (2 * π * ‖ξ‖) ^ (2 * α) :=
    mul_le_mul_of_nonneg_right hm hp
  have h2 : ε * ((2 * π * ‖ξ‖) ^ 2 - 1) ≤ ε * (2 * π * ‖ξ‖) ^ (2 * α) :=
    mul_le_mul_of_nonneg_left hs hε.le
  have h3 : (2 * π * ‖ξ‖) ^ 2 = 4 * π ^ 2 * ‖ξ‖ ^ 2 := by ring
  rw [h3] at h2
  nlinarith

theorem factor_decay {α ε τ : ℝ} (hα : 1 ≤ α) (hε : 0 < ε) (hτ : ε ≤ τ) (ξ : Space) :
    Freq.fracHeatFactor α τ ξ * (1 + ‖ξ‖) ^ 6 ≤
      Real.exp ε * (8 * (1 + 3 / (4 * π ^ 2 * ε)) ^ 3) := by
  have h1 := factor_le_heat hα hε hτ ξ
  have h2 := SourceDensity.Internal.heatFactor_decay hε le_rfl ξ
  have h0 : 0 ≤ (1 + ‖ξ‖) ^ 6 := by positivity
  calc Freq.fracHeatFactor α τ ξ * (1 + ‖ξ‖) ^ 6 ≤
        Real.exp ε * Freq.heatFactor ε ξ * (1 + ‖ξ‖) ^ 6 := mul_le_mul_of_nonneg_right h1 h0
    _ = Real.exp ε * (Freq.heatFactor ε ξ * (1 + ‖ξ‖) ^ 6) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le

theorem rpow_sub_le {p a b : ℝ} (hp : 1 ≤ p) (ha : 0 ≤ a) (hab : a ≤ b) :
    b ^ p - a ^ p ≤ p * b ^ (p - 1) * (b - a) := by
  rcases hab.lt_or_eq with h | h
  · have hb : 0 < b := ha.trans_lt h
    have hs : -1 ≤ a / b - 1 := by
      have : 0 ≤ a / b := div_nonneg ha hb.le
      linarith
    have hB := one_add_mul_self_le_rpow_one_add hs hp
    rw [add_sub_cancel, Real.div_rpow ha hb.le] at hB
    have hbp : 0 < b ^ p := Real.rpow_pos_of_pos hb p
    rw [le_div_iff₀ hbp] at hB
    have e : b ^ (p - 1) = b ^ p / b := Real.rpow_sub_one hb.ne' p
    have e2 : (1 + p * (a / b - 1)) * b ^ p = b ^ p - p * b ^ (p - 1) * (b - a) := by
      rw [e]
      field_simp
      ring
    linarith
  · subst h
    simp

theorem abs_rpow_sub_le {p a b M : ℝ} (hp : 1 ≤ p) (ha : 0 ≤ a) (hb : 0 ≤ b) (haM : a ≤ M)
    (hbM : b ≤ M) : |a ^ p - b ^ p| ≤ p * M ^ (p - 1) * |a - b| := by
  have hp0 : 0 ≤ p := by linarith
  rcases le_total a b with h | h
  · have h1 : a ^ p ≤ b ^ p := Real.rpow_le_rpow ha h hp0
    rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
    have h2 := rpow_sub_le hp ha h
    have h3 : b ^ (p - 1) ≤ M ^ (p - 1) := Real.rpow_le_rpow hb hbM (by linarith)
    have h4 : p * b ^ (p - 1) * (b - a) ≤ p * M ^ (p - 1) * (b - a) := by
      apply mul_le_mul_of_nonneg_right _ (by linarith)
      exact mul_le_mul_of_nonneg_left h3 hp0
    linarith
  · have h1 : b ^ p ≤ a ^ p := Real.rpow_le_rpow hb h hp0
    rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
    have h2 := rpow_sub_le hp hb h
    have h3 : a ^ (p - 1) ≤ M ^ (p - 1) := Real.rpow_le_rpow ha haM (by linarith)
    have h4 : p * a ^ (p - 1) * (a - b) ≤ p * M ^ (p - 1) * (a - b) := by
      apply mul_le_mul_of_nonneg_right _ (by linarith)
      exact mul_le_mul_of_nonneg_left h3 hp0
    linarith

def factorDiffConst (α ε R : ℝ) : ℝ := ε⁻¹ * (2 * α * (2 * π * R) ^ (2 * α - 1) * (2 * π))

theorem factor_diff_le {α ε τ R : ℝ} (hα : 1 ≤ α) (hε : 0 < ε) (hτ : τ ≤ ε⁻¹) {ξ ξ' : Space}
    (hξ : ‖ξ‖ ≤ R) (hξ' : ‖ξ'‖ ≤ R) :
    ‖Freq.fracHeatFactor α τ ξ - Freq.fracHeatFactor α τ ξ'‖ ≤ factorDiffConst α ε R * ‖ξ - ξ'‖ := by
  have hm0 : 0 ≤ max τ 0 := le_max_right _ _
  have hm : max τ 0 ≤ ε⁻¹ := max_le hτ (inv_nonneg.mpr hε.le)
  have hR : 0 ≤ R := (norm_nonneg ξ).trans hξ
  have hα0 : 0 < α := by linarith
  rw [Real.norm_eq_abs]
  unfold Freq.fracHeatFactor
  refine (SourceDensity.Internal.exp_neg_sub_le (by positivity) (by positivity)).trans ?_
  rw [← mul_sub, abs_mul, abs_of_nonneg hm0]
  have hpi : (0 : ℝ) < 2 * π := by positivity
  have hd := abs_rpow_sub_le (p := 2 * α) (by linarith) (by positivity : 0 ≤ 2 * π * ‖ξ‖)
    (by positivity : 0 ≤ 2 * π * ‖ξ'‖) (mul_le_mul_of_nonneg_left hξ hpi.le)
    (mul_le_mul_of_nonneg_left hξ' hpi.le)
  have hs : |2 * π * ‖ξ‖ - 2 * π * ‖ξ'‖| ≤ 2 * π * ‖ξ - ξ'‖ := by
    rw [← mul_sub, abs_mul, abs_of_pos hpi]
    exact mul_le_mul_of_nonneg_left (abs_norm_sub_norm_le ξ ξ') hpi.le
  have hK : 0 ≤ 2 * α * (2 * π * R) ^ (2 * α - 1) := by positivity
  unfold factorDiffConst
  calc max τ 0 * |(2 * π * ‖ξ‖) ^ (2 * α) - (2 * π * ‖ξ'‖) ^ (2 * α)| ≤
        ε⁻¹ * (2 * α * (2 * π * R) ^ (2 * α - 1) * (2 * π * ‖ξ - ξ'‖)) :=
        mul_le_mul hm (hd.trans (mul_le_mul_of_nonneg_left hs hK)) (abs_nonneg _)
          (inv_nonneg.mpr hε.le)
    _ = _ := by ring

theorem factorDiffConst_nonneg {α ε R : ℝ} (hα : 1 ≤ α) (hε : 0 < ε) (hR : 0 ≤ R) :
    0 ≤ factorDiffConst α ε R := by
  have hα0 : 0 < α := by linarith
  unfold factorDiffConst
  positivity

end Breakdown.Periodic.FracDensity.Internal

namespace Breakdown.Periodic

open SourceDensity.Internal FracDensity.Internal

theorem fracSourceDensityBounds (α : ℝ) (hα : 1 < α) : FracSourceDensityBounds α := by
  intro b b' ε hε
  set C₀ := (volume (Metric.closedBall (0 : Space) |b'|) ^ (1 / 3 : ℝ)).toReal with hC₀
  set B₀ := Real.exp ε * (8 * (1 + 3 / (4 * π ^ 2 * ε)) ^ 3) with hB₀
  have hC : 0 ≤ C₀ := ENNReal.toReal_nonneg
  have hB : 0 ≤ B₀ := by positivity
  refine ⟨(2 * π + 1) * (2 * C₀ * B₀), ?_⟩
  intro A hA hAn y hy τ hτ ξ
  have hF := freqTrVec_bound A b' hA hAn ξ
  have hP : ‖divFreeVec ξ (freqTrVec (⇑A) ξ)‖ ≤ 2 * C₀ := (divFreeVec_norm_le _ _).trans (by linarith)
  have hh : Freq.fracHeatFactor α τ ξ * (1 + ‖ξ‖) ^ 6 ≤ B₀ := factor_decay hα.le hε hτ.1 ξ
  have h0 := (factor_pos α τ ξ).le
  have hV : ‖fracValueDensity α τ (⇑A) y ξ‖ ≤ Freq.fracHeatFactor α τ ξ * (2 * C₀) := by
    unfold fracValueDensity
    rw [norm_smul, SourceDensity.Internal.norm_expChar, one_mul, norm_smul, Real.norm_of_nonneg h0]
    exact mul_le_mul_of_nonneg_left hP h0
  have hu1 : 1 ≤ 1 + ‖ξ‖ := by linarith [norm_nonneg ξ]
  have hpos : 0 < (1 + ‖ξ‖) ^ 4 := by positivity
  have hpow : (1 + ‖ξ‖) ^ (-4 : ℝ) = ((1 + ‖ξ‖) ^ 4)⁻¹ := by
    rw [Real.rpow_neg (by positivity), show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have h46 : (1 + ‖ξ‖) ^ 4 ≤ (1 + ‖ξ‖) ^ 6 := pow_le_pow_right₀ hu1 (by norm_num)
  have h56 : (1 + ‖ξ‖) ^ 5 ≤ (1 + ‖ξ‖) ^ 6 := pow_le_pow_right₀ hu1 (by norm_num)
  have hX : 0 ≤ 2 * C₀ * B₀ := by positivity
  have hK : 2 * C₀ * B₀ ≤ (2 * π + 1) * (2 * C₀ * B₀) :=
    le_mul_of_one_le_left hX (by linarith [pi_pos])
  have hK' : 2 * π * (2 * C₀ * B₀) ≤ (2 * π + 1) * (2 * C₀ * B₀) := by nlinarith
  rw [hpow, ← div_eq_mul_inv]
  constructor
  · rw [le_div_iff₀ hpos]
    calc ‖fracValueDensity α τ (⇑A) y ξ‖ * (1 + ‖ξ‖) ^ 4 ≤
          Freq.fracHeatFactor α τ ξ * (2 * C₀) * (1 + ‖ξ‖) ^ 6 :=
          mul_le_mul hV h46 (by positivity) (by positivity)
      _ = 2 * C₀ * (Freq.fracHeatFactor α τ ξ * (1 + ‖ξ‖) ^ 6) := by ring
      _ ≤ 2 * C₀ * B₀ := by gcongr
      _ ≤ _ := hK
  · intro j
    rw [le_div_iff₀ hpos]
    unfold fracGradDensity
    rw [norm_smul]
    have hj : ‖(2 * π * Complex.I * ((ξ j : ℝ) : ℂ))‖ ≤ 2 * π * (1 + ‖ξ‖) := by
      rw [norm_two_pi_I_mul]
      have := PiLp.norm_apply_le ξ j
      rw [Real.norm_eq_abs] at this
      gcongr
      linarith
    calc ‖(2 * π * Complex.I * ((ξ j : ℝ) : ℂ))‖ * ‖fracValueDensity α τ (⇑A) y ξ‖ * (1 + ‖ξ‖) ^ 4 ≤
          2 * π * (1 + ‖ξ‖) * (Freq.fracHeatFactor α τ ξ * (2 * C₀)) * (1 + ‖ξ‖) ^ 4 := by gcongr
      _ = 2 * π * (2 * C₀) * (Freq.fracHeatFactor α τ ξ * (1 + ‖ξ‖) ^ 5) := by ring
      _ ≤ 2 * π * (2 * C₀) * (Freq.fracHeatFactor α τ ξ * (1 + ‖ξ‖) ^ 6) := by gcongr
      _ ≤ 2 * π * (2 * C₀) * B₀ := by gcongr
      _ = 2 * π * (2 * C₀ * B₀) := by ring
      _ ≤ _ := hK'

theorem fracSourceDensityIncrement (α : ℝ) (hα : 1 < α) : FracSourceDensityIncrement α := by
  intro b b' ε r R hε hr
  set C₀ := (volume (Metric.closedBall (0 : Space) |b'|) ^ (1 / 3 : ℝ)).toReal with hC₀
  set LF := 2 * π * |b'| * C₀ with hLF
  set Le := 2 * π * |b| with hLe
  set Lh := factorDiffConst α ε R with hLh
  set MP := 2 * C₀ with hMP
  set LP := divFreeSlopeConst r R C₀ LF with hLP
  set LhP := Lh * MP + 1 * LP with hLhP
  set LV := Le * MP + 1 * LhP with hLV
  set Lg := 2 * π * MP + 2 * π * R * LV with hLg
  refine ⟨max LV Lg, ?_⟩
  intro A hA hAn y hy τ hτ ξ ξ' h1 h2 h1' h2'
  have hF := freqTrVec_bound A b' hA hAn ξ
  have hF' := freqTrVec_bound A b' hA hAn ξ'
  have hFL := freqTrVec_slope A b' hA hAn ξ ξ'
  have hPL := divFreeVec_slope hr h1 h2 h1' h2' hF hF' hFL
  have hPn : ‖divFreeVec ξ (freqTrVec (⇑A) ξ)‖ ≤ MP := (divFreeVec_norm_le _ _).trans (by linarith)
  have hh' : ‖Freq.fracHeatFactor α τ ξ'‖ ≤ 1 := by
    rw [Real.norm_of_nonneg (factor_pos _ _ _).le]
    exact FracDensity.Internal.factor_le_one _ _ _
  have hhL := factor_diff_le hα.le hε hτ.2 h2 h2'
  have hhP := smul_slope hh' hPn hhL hPL
  have hhPn : ‖Freq.fracHeatFactor α τ ξ • divFreeVec ξ (freqTrVec (⇑A) ξ)‖ ≤ MP := by
    rw [norm_smul, Real.norm_of_nonneg (factor_pos _ _ _).le]
    exact (mul_le_of_le_one_left (norm_nonneg _) (FracDensity.Internal.factor_le_one _ _ _)).trans hPn
  have he' : ‖expChar y ξ'‖ ≤ 1 := (SourceDensity.Internal.norm_expChar y ξ').le
  have heL := expChar_slope hy ξ ξ'
  have hV : ‖fracValueDensity α τ (⇑A) y ξ - fracValueDensity α τ (⇑A) y ξ'‖ ≤ LV * ‖ξ - ξ'‖ :=
    smul_slope he' hhPn heL hhP
  have hVn : ‖fracValueDensity α τ (⇑A) y ξ‖ ≤ MP := by
    unfold fracValueDensity
    rw [norm_smul, SourceDensity.Internal.norm_expChar, one_mul]
    exact hhPn
  have hd : 0 ≤ ‖ξ - ξ'‖ := norm_nonneg _
  refine ⟨hV.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hd), fun j => ?_⟩
  have hs' : ‖(2 * π * Complex.I * ((ξ' j : ℝ) : ℂ))‖ ≤ 2 * π * R := by
    rw [norm_two_pi_I_mul]
    have := PiLp.norm_apply_le ξ' j
    rw [Real.norm_eq_abs] at this
    gcongr
    linarith
  have hsL : ‖(2 * π * Complex.I * ((ξ j : ℝ) : ℂ)) - (2 * π * Complex.I * ((ξ' j : ℝ) : ℂ))‖ ≤
      2 * π * ‖ξ - ξ'‖ := by
    rw [← mul_sub, ← Complex.ofReal_sub, norm_two_pi_I_mul]
    have := PiLp.norm_apply_le (ξ - ξ') j
    rw [Real.norm_eq_abs, PiLp.sub_apply] at this
    gcongr
  have hg := smul_slope hs' hVn hsL hV
  unfold fracGradDensity
  exact hg.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hd)

end Breakdown.Periodic

namespace Breakdown.Periodic.FracDensity.Internal

open Breakdown.Periodic

theorem norm_free_le (α τ : ℝ) (φ : Space → Space) (y ξ : Space) :
    ‖fracFreeDensity α τ φ y ξ‖ ≤ ‖freqTrVec φ ξ‖ := by
  unfold fracFreeDensity
  rw [norm_smul, norm_smul, FreeDensity.Internal.norm_expChar, one_mul, Real.norm_eq_abs,
    abs_of_pos (factor_pos α τ ξ)]
  have := factor_le_one α τ ξ
  nlinarith [norm_nonneg (freqTrVec φ ξ)]

theorem norm_freeGrad_le (α : ℝ) (j : Fin 3) (τ : ℝ) (φ : Space → Space) (y ξ : Space) :
    ‖fracFreeGradDensity α j τ φ y ξ‖ ≤ 2 * π * ‖ξ‖ * ‖freqTrVec φ ξ‖ := by
  unfold fracFreeGradDensity
  rw [norm_smul, FreeDensity.Internal.norm_coord_factor]
  have h1 := norm_free_le α τ φ y ξ
  have h2 := FreeDensity.Internal.abs_coord_le j ξ
  have h3 : 0 ≤ 2 * π := by positivity
  calc 2 * π * |ξ j| * ‖fracFreeDensity α τ φ y ξ‖ ≤ 2 * π * ‖ξ‖ * ‖freqTrVec φ ξ‖ := by gcongr

theorem norm_factor_smul_le (α τ : ℝ) (ξ : Space) (v : Coef) :
    ‖Freq.fracHeatFactor α τ ξ • v‖ ≤ ‖v‖ := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (factor_pos α τ ξ)]
  have := factor_le_one α τ ξ
  nlinarith [norm_nonneg v]

theorem free_sub {α : ℝ} (hα : 1 ≤ α) (φ : Space → Space) (C LF B ε R τ : ℝ) (hε : 0 < ε)
    (hτ : τ ≤ ε⁻¹) (hC : ∀ ξ, ‖freqTrVec φ ξ‖ ≤ C)
    (hl : ∀ ξ ξ', ‖freqTrVec φ ξ - freqTrVec φ ξ'‖ ≤ LF * ‖ξ - ξ'‖)
    (y ξ ξ' : Space) (hy : ‖y‖ ≤ B) (hξ : ‖ξ‖ ≤ R) (hξ' : ‖ξ'‖ ≤ R) :
    ‖fracFreeDensity α τ φ y ξ - fracFreeDensity α τ φ y ξ'‖ ≤
      (2 * π * B * C + factorDiffConst α ε R * C + LF) * ‖ξ - ξ'‖ := by
  unfold fracFreeDensity
  set e := expChar y ξ
  set e' := expChar y ξ'
  set h := Freq.fracHeatFactor α τ ξ
  set h' := Freq.fracHeatFactor α τ ξ'
  set F := freqTrVec φ ξ
  set F' := freqTrVec φ ξ'
  have hid : e • (h • F) - e' • (h' • F') =
      (e - e') • (h • F) + e' • ((h - h') • F) + e' • (h' • (F - F')) := by
    simp only [sub_smul, smul_sub]; abel
  rw [hid]
  have hd := norm_nonneg (ξ - ξ')
  have t1 : ‖(e - e') • (h • F)‖ ≤ 2 * π * B * C * ‖ξ - ξ'‖ := by
    rw [norm_smul]
    have a1 := FreeDensity.Internal.norm_expChar_sub y ξ ξ'
    have a2 : ‖h • F‖ ≤ C := (norm_factor_smul_le α τ ξ F).trans (hC ξ)
    have a3 := norm_nonneg (h • F)
    have a4 : 0 ≤ 2 * π := by positivity
    calc ‖e - e'‖ * ‖h • F‖ ≤ (2 * π * ‖y‖ * ‖ξ - ξ'‖) * ‖h • F‖ := by gcongr
      _ ≤ (2 * π * B * ‖ξ - ξ'‖) * C := by
        have : 0 ≤ 2 * π * ‖y‖ * ‖ξ - ξ'‖ := by positivity
        have hB : 0 ≤ B := (norm_nonneg y).trans hy
        gcongr
      _ = _ := by ring
  have t2 : ‖e' • ((h - h') • F)‖ ≤ factorDiffConst α ε R * C * ‖ξ - ξ'‖ := by
    rw [norm_smul, FreeDensity.Internal.norm_expChar, one_mul, norm_smul]
    have a1 := factor_diff_le hα hε hτ hξ hξ'
    have a2 := hC ξ
    have hR : 0 ≤ R := (norm_nonneg ξ).trans hξ
    have a3 : 0 ≤ factorDiffConst α ε R * ‖ξ - ξ'‖ :=
      mul_nonneg (factorDiffConst_nonneg hα hε hR) hd
    calc ‖h - h'‖ * ‖F‖ ≤ (factorDiffConst α ε R * ‖ξ - ξ'‖) * C := by
          gcongr
      _ = _ := by ring
  have t3 : ‖e' • (h' • (F - F'))‖ ≤ LF * ‖ξ - ξ'‖ := by
    rw [norm_smul, FreeDensity.Internal.norm_expChar, one_mul]
    exact (norm_factor_smul_le α τ ξ' _).trans (hl ξ ξ')
  calc ‖(e - e') • (h • F) + e' • ((h - h') • F) + e' • (h' • (F - F'))‖
      ≤ ‖(e - e') • (h • F)‖ + ‖e' • ((h - h') • F)‖ + ‖e' • (h' • (F - F'))‖ :=
        norm_add₃_le
    _ ≤ _ := by linarith

theorem freeGrad_sub (α : ℝ) (j : Fin 3) (φ : Space → Space) (C LD R τ : ℝ)
    (y ξ ξ' : Space) (hC : ‖fracFreeDensity α τ φ y ξ‖ ≤ C)
    (hD : ‖fracFreeDensity α τ φ y ξ - fracFreeDensity α τ φ y ξ'‖ ≤ LD * ‖ξ - ξ'‖)
    (hξ' : ‖ξ'‖ ≤ R) :
    ‖fracFreeGradDensity α j τ φ y ξ - fracFreeGradDensity α j τ φ y ξ'‖ ≤
      (2 * π * C + 2 * π * R * LD) * ‖ξ - ξ'‖ := by
  unfold fracFreeGradDensity
  set c := (2 * π * Complex.I * ((ξ j : ℝ) : ℂ))
  set c' := (2 * π * Complex.I * ((ξ' j : ℝ) : ℂ))
  set D := fracFreeDensity α τ φ y ξ
  set D' := fracFreeDensity α τ φ y ξ'
  have hid : c • D - c' • D' = (c - c') • D + c' • (D - D') := by
    simp only [sub_smul, smul_sub]; abel
  rw [hid]
  have hcc : c - c' = 2 * π * Complex.I * (((ξ - ξ') j : ℝ) : ℂ) := by
    simp only [c, c', PiLp.sub_apply, Complex.ofReal_sub]; ring
  have hd := norm_nonneg (ξ - ξ')
  have hpi : 0 ≤ 2 * π := by positivity
  have t1 : ‖(c - c') • D‖ ≤ 2 * π * C * ‖ξ - ξ'‖ := by
    rw [norm_smul, hcc, FreeDensity.Internal.norm_coord_factor]
    have a1 := FreeDensity.Internal.abs_coord_le j (ξ - ξ')
    calc 2 * π * |(ξ - ξ') j| * ‖D‖ ≤ 2 * π * ‖ξ - ξ'‖ * C := by gcongr
      _ = _ := by ring
  have t2 : ‖c' • (D - D')‖ ≤ 2 * π * R * LD * ‖ξ - ξ'‖ := by
    rw [norm_smul, FreeDensity.Internal.norm_coord_factor]
    have a1 := (FreeDensity.Internal.abs_coord_le j ξ').trans hξ'
    have a2 : 0 ≤ 2 * π * |ξ' j| := by positivity
    have hR : 0 ≤ R := (abs_nonneg _).trans a1
    calc 2 * π * |ξ' j| * ‖D - D'‖ ≤ 2 * π * R * (LD * ‖ξ - ξ'‖) := by gcongr
      _ = _ := by ring
  calc ‖(c - c') • D + c' • (D - D')‖ ≤ ‖(c - c') • D‖ + ‖c' • (D - D')‖ := norm_add_le _ _
    _ ≤ _ := by linarith

end Breakdown.Periodic.FracDensity.Internal

namespace Breakdown.Periodic

open FracDensity.Internal

theorem fracFreeDensityBounds (α : ℝ) (hα : 1 < α) : FracFreeDensityBounds α := by
  intro φ hφ b ε hε
  obtain ⟨C, L, hC, hL, hd, hl⟩ := FreeDensity.Internal.freqTr_bounds φ hφ
  refine ⟨C + 2 * π * C, fun y hy τ hτ ξ => ⟨?_, fun j => ?_⟩⟩
  · refine FreeDensity.Internal.le_mul_rpow_of _ _ ξ ?_
    have h1 := norm_free_le α τ φ y ξ
    have h2 := hd ξ
    have hp : 1 ≤ 1 + ‖ξ‖ := by linarith [norm_nonneg ξ]
    have h3 : (1 + ‖ξ‖) ^ 4 ≤ (1 + ‖ξ‖) ^ 5 := pow_le_pow_right₀ hp (by norm_num)
    have h4 : 0 ≤ (1 + ‖ξ‖) ^ 4 := by positivity
    have h5 : 0 ≤ 2 * π * C := by positivity
    calc (1 + ‖ξ‖) ^ 4 * ‖fracFreeDensity α τ φ y ξ‖ ≤ (1 + ‖ξ‖) ^ 4 * ‖freqTrVec φ ξ‖ := by gcongr
      _ ≤ (1 + ‖ξ‖) ^ 5 * ‖freqTrVec φ ξ‖ := by gcongr
      _ ≤ C + 2 * π * C := by linarith
  · refine FreeDensity.Internal.le_mul_rpow_of _ _ ξ ?_
    have h1 := norm_freeGrad_le α j τ φ y ξ
    have h2 := hd ξ
    have h4 : 0 ≤ (1 + ‖ξ‖) ^ 4 := by positivity
    have h6 : ‖ξ‖ ≤ 1 + ‖ξ‖ := by linarith
    have hn := norm_nonneg (freqTrVec φ ξ)
    calc (1 + ‖ξ‖) ^ 4 * ‖fracFreeGradDensity α j τ φ y ξ‖
        ≤ (1 + ‖ξ‖) ^ 4 * (2 * π * ‖ξ‖ * ‖freqTrVec φ ξ‖) := by gcongr
      _ ≤ (1 + ‖ξ‖) ^ 4 * (2 * π * (1 + ‖ξ‖) * ‖freqTrVec φ ξ‖) := by gcongr
      _ = 2 * π * ((1 + ‖ξ‖) ^ 5 * ‖freqTrVec φ ξ‖) := by ring
      _ ≤ 2 * π * C := by gcongr
      _ ≤ C + 2 * π * C := by linarith

theorem fracFreeDensityIncrement (α : ℝ) (hα : 1 < α) : FracFreeDensityIncrement α := by
  intro φ hφ b ε r R hε hr
  obtain ⟨C, LF, hC, hLF, hd, hl⟩ := FreeDensity.Internal.freqTr_bounds φ hφ
  have hC' : ∀ ξ, ‖freqTrVec φ ξ‖ ≤ C := fun ξ => FreeDensity.Internal.norm_le_of_pow_five C ξ _ (hd ξ)
  have hLh : 0 ≤ factorDiffConst α ε |R| := factorDiffConst_nonneg hα.le hε (abs_nonneg R)
  set LD := 2 * π * |b| * C + factorDiffConst α ε |R| * C + LF
  have hLD : 0 ≤ LD := by positivity
  refine ⟨LD + (2 * π * C + 2 * π * |R| * LD), fun y hy τ hτ ξ ξ' _ hξ _ hξ' => ?_⟩
  have hy' : ‖y‖ ≤ |b| := hy.trans (le_abs_self b)
  have hξR : ‖ξ‖ ≤ |R| := hξ.trans (le_abs_self R)
  have hξR' : ‖ξ'‖ ≤ |R| := hξ'.trans (le_abs_self R)
  have hD := free_sub hα.le φ C LF |b| ε |R| τ hε hτ.2 hC' hl y ξ ξ' hy' hξR hξR'
  have hdn := norm_nonneg (ξ - ξ')
  have hG : 0 ≤ (2 * π * C + 2 * π * |R| * LD) := by positivity
  refine ⟨?_, fun j => ?_⟩
  · nlinarith
  · have := freeGrad_sub α j φ C LD |R| τ y ξ ξ'
      ((norm_free_le α τ φ y ξ).trans (hC' ξ)) hD hξR'
    nlinarith

end Breakdown.Periodic
