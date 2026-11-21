import Breakdown.Uniqueness.RegDefs

open scoped ContDiff ENNReal FourierTransform Topology
open MeasureTheory Set Real Filter

noncomputable section

namespace Breakdown.SmoothFlow

open Breakdown.Freq

private def supWeight (ξ : Space) : ℝ := 1 / (‖ξ‖ ^ 2 * (1 + ‖ξ‖ ^ 2))

private lemma supWeight_lintegral_lt_top :
    ∫⁻ ξ : Space, ENNReal.ofReal (supWeight ξ) < ⊤ := by
  have hint : Integrable (fun x : Space => (fun y : ℝ => 1 / (y ^ 2 * (1 + y ^ 2))) ‖x‖) (volume : Measure Space) := by
    refine (integrable_fun_norm_addHaar (volume : Measure Space) (f := fun y : ℝ => 1 / (y ^ 2 * (1 + y ^ 2)))).2 ?_
    have h3 : Module.finrank ℝ Space = 3 := finrank_euclideanSpace_fin
    rw [h3]
    refine (integrable_inv_one_add_sq.integrableOn).congr_fun (fun y hy => ?_) measurableSet_Ioi
    have hy : (0 : ℝ) < y := hy
    simp only [smul_eq_mul]
    field_simp
  exact hint.lintegral_lt_top

private lemma supBound_scale (c d : ℝ) (hc : 0 < c) (hd : 0 < d) :
    ∫⁻ ξ : Space, ENNReal.ofReal (1 / (d * ‖ξ‖ ^ 2 * (c ^ 2 + ‖ξ‖ ^ 2))) =
      ENNReal.ofReal (1 / (d * c ^ 4)) * ENNReal.ofReal (c ^ 3) *
        ∫⁻ ξ : Space, ENNReal.ofReal (supWeight ξ) := by
  have hpt : ∀ ξ : Space, ENNReal.ofReal (1 / (d * ‖ξ‖ ^ 2 * (c ^ 2 + ‖ξ‖ ^ 2))) =
      ENNReal.ofReal (1 / (d * c ^ 4)) * ENNReal.ofReal (supWeight (c⁻¹ • ξ)) := by
    intro ξ
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    simp only [supWeight, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hc]
    rcases eq_or_ne ‖ξ‖ 0 with h0 | h0
    · simp [h0]
    · field_simp
  simp_rw [hpt]
  have hmeas : Measurable fun ξ : Space => ENNReal.ofReal (supWeight ξ) := by
    unfold supWeight
    fun_prop
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  have hmap := Measure.map_addHaar_smul (volume : Measure Space) (inv_ne_zero hc.ne')
  have hcomp : ∫⁻ ξ : Space, ENNReal.ofReal (supWeight (c⁻¹ • ξ)) =
      ENNReal.ofReal (c ^ 3) * ∫⁻ ξ : Space, ENNReal.ofReal (supWeight ξ) := by
    have := lintegral_map (μ := (volume : Measure Space)) hmeas (measurable_const_smul c⁻¹)
    rw [← this, hmap, lintegral_smul_measure]
    have h3 : Module.finrank ℝ Space = 3 := finrank_euclideanSpace_fin
    rw [h3, inv_pow, inv_inv, abs_of_pos (by positivity)]
    rfl
  rw [hcomp, mul_assoc]

private lemma supBound_real (s r c d : ℝ) (hr : 0 < r) (hc : 0 < c) (hd : 0 < d) :
    2 * s ≤ d * c ^ 2 * (r ^ (2 * 1) * s ^ 2) + d * (r ^ (2 * 2) * s ^ 2) +
      1 / (d * r ^ 2 * (c ^ 2 + r ^ 2)) := by
  have hw : 0 < d * r ^ 2 * (c ^ 2 + r ^ 2) := by positivity
  have key : 0 ≤ (d * r ^ 2 * (c ^ 2 + r ^ 2) * s - 1) ^ 2 / (d * r ^ 2 * (c ^ 2 + r ^ 2)) := by
    positivity
  have e : (d * r ^ 2 * (c ^ 2 + r ^ 2) * s - 1) ^ 2 / (d * r ^ 2 * (c ^ 2 + r ^ 2)) =
      d * c ^ 2 * (r ^ (2 * 1) * s ^ 2) + d * (r ^ (2 * 2) * s ^ 2) +
        1 / (d * r ^ 2 * (c ^ 2 + r ^ 2)) - 2 * s := by
    field_simp
    ring
  linarith

private lemma supBound_ae_ne : ∀ᵐ ξ : Space ∂(volume : Measure Space), ξ ≠ 0 := by
  rw [ae_iff]
  simp

private lemma supBound_param (f : Space → CSpace) (c d : ℝ) (hc : 0 < c) (hd : 0 < d) :
    2 * freqL1Norm f ≤ ENNReal.ofReal (d * c ^ 2) * homNormSq 1 f + ENNReal.ofReal d * homNormSq 2 f +
      ENNReal.ofReal (1 / (d * c ^ 4)) * ENNReal.ofReal (c ^ 3) *
        ∫⁻ ξ : Space, ENNReal.ofReal (supWeight ξ) := by
  obtain ⟨g, hgm, hgle, hgeq⟩ :=
    exists_measurable_le_lintegral_eq (μ := (volume : Measure Space)) (fun ξ => ‖f ξ‖ₑ)
  have hpt : ∀ᵐ ξ : Space ∂volume, 2 * g ξ ≤
      ENNReal.ofReal (d * c ^ 2) * (ENNReal.ofReal (‖ξ‖ ^ (2 * 1)) * g ξ ^ 2) +
        ENNReal.ofReal d * (ENNReal.ofReal (‖ξ‖ ^ (2 * 2)) * g ξ ^ 2) +
          ENNReal.ofReal (1 / (d * ‖ξ‖ ^ 2 * (c ^ 2 + ‖ξ‖ ^ 2))) := by
    filter_upwards [supBound_ae_ne] with ξ hξ
    have hfin : g ξ ≠ ⊤ := ne_top_of_le_ne_top enorm_ne_top (hgle ξ)
    rw [← ENNReal.ofReal_toReal hfin]
    have hs := ENNReal.toReal_nonneg (a := g ξ)
    have hr : 0 < ‖ξ‖ := norm_pos_iff.2 hξ
    have hreal := supBound_real (g ξ).toReal ‖ξ‖ c d hr hc hd
    calc 2 * ENNReal.ofReal (g ξ).toReal = ENNReal.ofReal (2 * (g ξ).toReal) := by
          rw [ENNReal.ofReal_mul (by norm_num)]
          simp
      _ ≤ ENNReal.ofReal (d * c ^ 2 * (‖ξ‖ ^ (2 * 1) * (g ξ).toReal ^ 2) +
            d * (‖ξ‖ ^ (2 * 2) * (g ξ).toReal ^ 2) + 1 / (d * ‖ξ‖ ^ 2 * (c ^ 2 + ‖ξ‖ ^ 2))) :=
          ENNReal.ofReal_le_ofReal hreal
      _ = _ := by
          rw [ENNReal.ofReal_add (p := d * c ^ 2 * (‖ξ‖ ^ (2 * 1) * (g ξ).toReal ^ 2) +
              d * (‖ξ‖ ^ (2 * 2) * (g ξ).toReal ^ 2)) (by positivity) (by positivity),
            ENNReal.ofReal_add (p := d * c ^ 2 * (‖ξ‖ ^ (2 * 1) * (g ξ).toReal ^ 2))
              (by positivity) (by positivity),
            ENNReal.ofReal_mul (p := d * c ^ 2) (by positivity),
            ENNReal.ofReal_mul (p := ‖ξ‖ ^ (2 * 1)) (by positivity),
            ENNReal.ofReal_mul (p := d) (q := ‖ξ‖ ^ (2 * 2) * (g ξ).toReal ^ 2) (by positivity),
            ENNReal.ofReal_mul (p := ‖ξ‖ ^ (2 * 2)) (by positivity),
            ENNReal.ofReal_pow hs]
  have hmono : ∀ k : ℕ, ∫⁻ ξ, ENNReal.ofReal (‖ξ‖ ^ (2 * k)) * g ξ ^ 2 ≤ homNormSq k f := by
    intro k
    exact lintegral_mono fun ξ => by gcongr; exact hgle ξ
  calc 2 * freqL1Norm f = ∫⁻ ξ, 2 * g ξ := by
        rw [lintegral_const_mul _ hgm, freqL1Norm, hgeq]
    _ ≤ ∫⁻ ξ, (ENNReal.ofReal (d * c ^ 2) * (ENNReal.ofReal (‖ξ‖ ^ (2 * 1)) * g ξ ^ 2) +
        ENNReal.ofReal d * (ENNReal.ofReal (‖ξ‖ ^ (2 * 2)) * g ξ ^ 2) +
          ENNReal.ofReal (1 / (d * ‖ξ‖ ^ 2 * (c ^ 2 + ‖ξ‖ ^ 2)))) := lintegral_mono_ae hpt
    _ = ENNReal.ofReal (d * c ^ 2) * (∫⁻ ξ, ENNReal.ofReal (‖ξ‖ ^ (2 * 1)) * g ξ ^ 2) +
        ENNReal.ofReal d * (∫⁻ ξ, ENNReal.ofReal (‖ξ‖ ^ (2 * 2)) * g ξ ^ 2) +
          ∫⁻ ξ : Space, ENNReal.ofReal (1 / (d * ‖ξ‖ ^ 2 * (c ^ 2 + ‖ξ‖ ^ 2))) := by
        rw [lintegral_add_left (by fun_prop), lintegral_add_left (by fun_prop),
          lintegral_const_mul _ (by fun_prop), lintegral_const_mul _ (by fun_prop)]
    _ ≤ _ := by
        rw [supBound_scale c d hc hd]
        gcongr
        · exact hmono 1
        · exact hmono 2

private lemma supBound_zero (f : Space → CSpace) (k : ℕ) (h : homNormSq k f = 0) :
    freqL1Norm f = 0 := by
  obtain ⟨g, hgm, hgle, hgeq⟩ :=
    exists_measurable_le_lintegral_eq (μ := (volume : Measure Space)) (fun ξ => ‖f ξ‖ₑ)
  have h0 : ∫⁻ ξ, ENNReal.ofReal (‖ξ‖ ^ (2 * k)) * g ξ ^ 2 = 0 := by
    refine le_antisymm ?_ (by simp)
    rw [← h]
    exact lintegral_mono fun ξ => by gcongr; exact hgle ξ
  rw [lintegral_eq_zero_iff (by fun_prop)] at h0
  unfold freqL1Norm
  rw [hgeq, lintegral_eq_zero_iff hgm]
  filter_upwards [h0, supBound_ae_ne] with ξ h1 h2
  have hne : ENNReal.ofReal (‖ξ‖ ^ (2 * k)) ≠ 0 := by
    rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]
    exact pow_pos (norm_pos_iff.2 h2) _
  rcases mul_eq_zero.1 h1 with h3 | h3
  · exact absurd h3 hne
  · exact (pow_eq_zero_iff two_ne_zero).1 h3

theorem freqL1_le_supBound : ∃ C : ℝ, ∀ f : Space → CSpace,
    freqL1Norm f ≤ ENNReal.ofReal C * homNormSq 1 f ^ (1 / 4 : ℝ) * homNormSq 2 f ^ (1 / 4 : ℝ) := by
  have hKt : (∫⁻ ξ : Space, ENNReal.ofReal (supWeight ξ)) ≠ ⊤ :=
    supWeight_lintegral_lt_top.ne
  set K := ∫⁻ ξ : Space, ENNReal.ofReal (supWeight ξ) with hK
  refine ⟨1 + K.toReal / 2, fun f => ?_⟩
  have hC : 0 < 1 + K.toReal / 2 := by positivity
  rcases eq_or_ne (homNormSq 1 f) 0 with ha0 | ha0
  · rw [supBound_zero f 1 ha0]
    exact zero_le
  rcases eq_or_ne (homNormSq 2 f) 0 with hb0 | hb0
  · rw [supBound_zero f 2 hb0]
    exact zero_le
  have hCne : ENNReal.ofReal (1 + K.toReal / 2) ≠ 0 := by
    rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]
    exact hC
  have ha4 : homNormSq 1 f ^ (1 / 4 : ℝ) ≠ 0 := by
    rw [ne_eq, ENNReal.rpow_eq_zero_iff]
    push Not
    exact ⟨fun h => absurd h ha0, fun _ => by norm_num⟩
  have hb4 : homNormSq 2 f ^ (1 / 4 : ℝ) ≠ 0 := by
    rw [ne_eq, ENNReal.rpow_eq_zero_iff]
    push Not
    exact ⟨fun h => absurd h hb0, fun _ => by norm_num⟩
  rcases eq_or_ne (homNormSq 1 f) ⊤ with hat | hat
  · rw [hat, ENNReal.top_rpow_of_pos (by norm_num), ENNReal.mul_top hCne, ENNReal.top_mul hb4]
    exact le_top
  rcases eq_or_ne (homNormSq 2 f) ⊤ with hbt | hbt
  · rw [hbt, ENNReal.top_rpow_of_pos (by norm_num), ENNReal.mul_top (mul_ne_zero hCne ha4)]
    exact le_top
  have hA : 0 < (homNormSq 1 f).toReal := ENNReal.toReal_pos ha0 hat
  have hB : 0 < (homNormSq 2 f).toReal := ENNReal.toReal_pos hb0 hbt
  set A := (homNormSq 1 f).toReal with hAdef
  set B := (homNormSq 2 f).toReal with hBdef
  have e1 : homNormSq 1 f = ENNReal.ofReal A := (ENNReal.ofReal_toReal hat).symm
  have e2 : homNormSq 2 f = ENNReal.ofReal B := (ENNReal.ofReal_toReal hbt).symm
  have e3 : K = ENNReal.ofReal K.toReal := (ENNReal.ofReal_toReal hKt).symm
  set p := A ^ (1 / 4 : ℝ) with hpdef
  set q := B ^ (1 / 4 : ℝ) with hqdef
  have hp : 0 < p := Real.rpow_pos_of_pos hA _
  have hq : 0 < q := Real.rpow_pos_of_pos hB _
  have hAp : p ^ 4 = A := by
    rw [hpdef, ← Real.rpow_natCast, ← Real.rpow_mul hA.le]
    norm_num
  have hBq : q ^ 4 = B := by
    rw [hqdef, ← Real.rpow_natCast, ← Real.rpow_mul hB.le]
    norm_num
  have hgoal : ENNReal.ofReal (1 + K.toReal / 2) * homNormSq 1 f ^ (1 / 4 : ℝ) *
      homNormSq 2 f ^ (1 / 4 : ℝ) = ENNReal.ofReal ((1 + K.toReal / 2) * p * q) := by
    rw [e1, e2, ENNReal.ofReal_rpow_of_nonneg hA.le (by norm_num),
      ENNReal.ofReal_rpow_of_nonneg hB.le (by norm_num),
      ENNReal.ofReal_mul (p := (1 + K.toReal / 2) * p) (by positivity),
      ENNReal.ofReal_mul (p := 1 + K.toReal / 2) (by positivity)]
  rw [hgoal]
  set c := q ^ 2 / p ^ 2 with hcdef
  set d := p / q ^ 3 with hddef
  have hc : 0 < c := by positivity
  have hd : 0 < d := by positivity
  have key := supBound_param f c d hc hd
  rw [← hK, e1, e2, e3] at key
  have hR : ENNReal.ofReal (d * c ^ 2) * ENNReal.ofReal A + ENNReal.ofReal d * ENNReal.ofReal B +
      ENNReal.ofReal (1 / (d * c ^ 4)) * ENNReal.ofReal (c ^ 3) * ENNReal.ofReal K.toReal =
      2 * ENNReal.ofReal ((1 + K.toReal / 2) * p * q) := by
    rw [← ENNReal.ofReal_mul (p := d * c ^ 2) (by positivity),
      ← ENNReal.ofReal_mul (p := d) (by positivity),
      ← ENNReal.ofReal_mul (p := 1 / (d * c ^ 4)) (by positivity),
      ← ENNReal.ofReal_mul (p := 1 / (d * c ^ 4) * c ^ 3) (by positivity),
      ← ENNReal.ofReal_add (p := d * c ^ 2 * A) (by positivity) (by positivity),
      ← ENNReal.ofReal_add (p := d * c ^ 2 * A + d * B) (by positivity) (by positivity)]
    have h2 : (2 : ℝ≥0∞) = ENNReal.ofReal 2 := by simp
    rw [h2, ← ENNReal.ofReal_mul (by norm_num)]
    congr 1
    rw [← hAp, ← hBq, hcdef, hddef]
    field_simp
    ring
  rw [hR] at key
  exact (ENNReal.mul_le_mul_iff_right two_ne_zero ENNReal.ofNat_ne_top).1 key

end Breakdown.SmoothFlow
