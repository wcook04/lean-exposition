import Breakdown.Uniqueness.CutoffBounds
import Breakdown.Uniqueness.FundSolEnergy
import Breakdown.Uniqueness.FundSolPointwise
import Breakdown.Uniqueness.StressSplit

open scoped ContDiff ENNReal
open MeasureTheory Set Real

noncomputable section

namespace Breakdown

private theorem abs_triple_le {x y h U l : ℝ} (hl : 0 < l) (hx : |x| ≤ U) :
    |x * y * h| ≤ U * (l / 2 * y ^ 2 + h ^ 2 / (2 * l)) := by
  have key : 2 * l * (|y| * |h|) ≤ l ^ 2 * y ^ 2 + h ^ 2 := by
    nlinarith [sq_nonneg (l * |y| - |h|), sq_abs y, sq_abs h]
  have e : l / 2 * y ^ 2 + h ^ 2 / (2 * l) = (l ^ 2 * y ^ 2 + h ^ 2) / (2 * l) := by
    field_simp
  have hyh : |y| * |h| ≤ l / 2 * y ^ 2 + h ^ 2 / (2 * l) := by
    rw [e, le_div_iff₀ (by positivity)]
    linarith
  rw [abs_mul, abs_mul, mul_assoc]
  exact mul_le_mul hx hyh (by positivity) ((abs_nonneg x).trans hx)

private theorem abs_triple_le' {x y h U l : ℝ} (hl : 0 < l) (hy : |y| ≤ U) :
    |x * y * h| ≤ U * (l / 2 * x ^ 2 + h ^ 2 / (2 * l)) := by
  have e : x * y * h = y * x * h := by ring
  rw [e]
  exact abs_triple_le hl hy

private theorem abs_pairing_le_left (a b : Space) (H : Fin 3 → Fin 3 → ℝ) {U l : ℝ}
    (hl : 0 < l) (ha : ‖a‖ ≤ U) :
    |∑ i, ∑ j, a i * b j * H i j| ≤
      U * (3 * l / 2 * ‖b‖ ^ 2 + (∑ i, ∑ j, H i j ^ 2) / (2 * l)) := by
  have hai : ∀ i, |a i| ≤ U := fun i => by
    rw [← Real.norm_eq_abs]; exact (PiLp.norm_apply_le a i).trans ha
  calc _ ≤ ∑ i, |∑ j, a i * b j * H i j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, ∑ j, |a i * b j * H i j| := by
        gcongr with i; exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, ∑ j, U * (l / 2 * b j ^ 2 + H i j ^ 2 / (2 * l)) := by
        gcongr with i _ j; exact abs_triple_le hl (hai i)
    _ = _ := by
        rw [EuclideanSpace.real_norm_sq_eq]
        simp only [Fin.sum_univ_three]
        ring

private theorem abs_pairing_le_right (a b : Space) (H : Fin 3 → Fin 3 → ℝ) {U l : ℝ}
    (hl : 0 < l) (hb : ‖b‖ ≤ U) :
    |∑ i, ∑ j, a i * b j * H i j| ≤
      U * (3 * l / 2 * ‖a‖ ^ 2 + (∑ i, ∑ j, H i j ^ 2) / (2 * l)) := by
  have hbj : ∀ j, |b j| ≤ U := fun j => by
    rw [← Real.norm_eq_abs]; exact (PiLp.norm_apply_le b j).trans hb
  calc _ ≤ ∑ i, |∑ j, a i * b j * H i j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, ∑ j, |a i * b j * H i j| := by
        gcongr with i; exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, ∑ j, U * (l / 2 * a i ^ 2 + H i j ^ 2 / (2 * l)) := by
        gcongr with i _ j; exact abs_triple_le' hl (hbj j)
    _ = _ := by
        rw [EuclideanSpace.real_norm_sq_eq]
        simp only [Fin.sum_univ_three]
        ring

private theorem abs_integral_le_of_pointwise {F G : Space → ℝ} (hG : Integrable G)
    (h : ∀ x, |F x| ≤ G x) : |∫ x, F x| ≤ ∫ x, G x := by
  calc |∫ x, F x| = ‖∫ x, F x‖ := (Real.norm_eq_abs _).symm
    _ ≤ ∫ x, ‖F x‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ x, G x := by
        refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => norm_nonneg _) hG
          (Filter.Eventually.of_forall fun x => ?_)
        simpa [Real.norm_eq_abs] using h x

private theorem integrable_and_integral_sq_le {A : ℝ} {w : Space → Space}
    (hw : IsFiniteEnergyField A w) :
    Integrable (fun x => ‖w x‖ ^ 2) ∧ ∫ x, ‖w x‖ ^ 2 ≤ A ^ 2 := by
  have hm : AEStronglyMeasurable (fun x => ‖w x‖ ^ 2) volume :=
    ((hw.smooth.continuous.norm).pow 2).aestronglyMeasurable
  have h0 : 0 ≤ᵐ[volume] (fun x => ‖w x‖ ^ 2) :=
    Filter.Eventually.of_forall fun x => by positivity
  have hfin : ∫⁻ x, ENNReal.ofReal (‖w x‖ ^ 2) ≠ (⊤ : ℝ≥0∞) :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hw.energy
  refine ⟨(lintegral_ofReal_ne_top_iff_integrable hm h0).1 hfin, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae h0 hm]
  exact ENNReal.toReal_le_of_le_ofReal (sq_nonneg A) hw.energy

private theorem cutoffSource_fun_eq {r : ℝ} (hr : 0 < r) {w : Space → Space}
    (hw : ContDiff ℝ ∞ w) (hdiv : ∀ x, divergenceAt w x = 0) :
    cutoffSource r w = (fun x => 4 * radialCutoff r x ^ 3) * cutoffFlux r w := by
  funext x
  simp only [Pi.mul_apply]
  exact cutoffSource_eq hr hw hdiv x

private theorem contDiff_cutoffSource {r : ℝ} (hr : 0 < r) {w : Space → Space}
    (hw : ContDiff ℝ ∞ w) (hdiv : ∀ x, divergenceAt w x = 0) :
    ContDiff ℝ ∞ (cutoffSource r w) := by
  rw [cutoffSource_fun_eq hr hw hdiv]
  exact (contDiff_const.mul ((contDiff_radialCutoff hr).pow 3)).mul (contDiff_cutoffFlux hr hw)

private theorem hasCompactSupport_cutoffSource {r : ℝ} (hr : 0 < r) {w : Space → Space}
    (hw : ContDiff ℝ ∞ w) (hdiv : ∀ x, divergenceAt w x = 0) :
    HasCompactSupport (cutoffSource r w) := by
  rw [cutoffSource_fun_eq hr hw hdiv]
  exact (hasCompactSupport_cutoffFlux hr w).mul_left

private theorem sq_cutoffSource_le {c r : ℝ} (hr : 0 < r)
    (hc : ∀ x, ‖fderiv ℝ (radialCutoff r) x‖ ≤ c / r) {w : Space → Space}
    (hw : ContDiff ℝ ∞ w) (hdiv : ∀ x, divergenceAt w x = 0) (x : Space) :
    cutoffSource r w x ^ 2 ≤ 16 * (c / r) ^ 2 * ‖w x‖ ^ 2 := by
  rw [cutoffSource_eq hr hw hdiv x]
  have h0 := radialCutoff_nonneg r x
  have h1 := radialCutoff_le_one r x
  have hp0 : 0 ≤ radialCutoff r x ^ 3 := pow_nonneg h0 3
  have hp1 : radialCutoff r x ^ 3 ≤ 1 := pow_le_one₀ h0 h1
  have hcr : 0 ≤ c / r := (norm_nonneg _).trans (hc x)
  have hf : |cutoffFlux r w x| ≤ c / r * ‖w x‖ := by
    unfold cutoffFlux
    rw [← Real.norm_eq_abs]
    exact ((fderiv ℝ (radialCutoff r) x).le_opNorm (w x)).trans
      (mul_le_mul_of_nonneg_right (hc x) (norm_nonneg _))
  have hab : |4 * radialCutoff r x ^ 3 * cutoffFlux r w x| ≤ 4 * (c / r * ‖w x‖) := by
    rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4), abs_of_nonneg hp0]
    calc 4 * radialCutoff r x ^ 3 * |cutoffFlux r w x| ≤ 4 * 1 * |cutoffFlux r w x| := by
          gcongr
      _ ≤ 4 * (c / r * ‖w x‖) := by linarith
  have hsq := sq_le_sq' (abs_le.1 hab).1 (abs_le.1 hab).2
  calc _ ≤ (4 * (c / r * ‖w x‖)) ^ 2 := hsq
    _ = 16 * (c / r) ^ 2 * ‖w x‖ ^ 2 := by ring

theorem mixed_stress_le : ∃ c : ℝ, ∀ (A U₀ U₁ : ℝ) (u w : Space → Space),
    IsDifferenceData A U₀ U₁ u w → ∀ r : ℝ, 1 ≤ r →
      |stressPairing u w (FundSol.potential (cutoffSource r w)) +
        stressPairing w u (FundSol.potential (cutoffSource r w))| ≤ c * U₀ * A ^ 2 / r := by
  obtain ⟨c₁, hc₁⟩ := norm_fderiv_radialCutoff_le
  refine ⟨3 + 16 * c₁ ^ 2, fun A U₀ U₁ u w hd r hr => ?_⟩
  have hr0 : 0 < r := lt_of_lt_of_le one_pos hr
  have hw := hd.field.smooth
  have hdiv := hd.field.div_free
  have hU : 0 ≤ U₀ := (norm_nonneg _).trans (hd.bound_u 0)
  obtain ⟨hwi, hwA⟩ := integrable_and_integral_sq_le hd.field
  set g := cutoffSource r w with hg
  have hgc := contDiff_cutoffSource hr0 hw hdiv
  have hgs := hasCompactSupport_cutoffSource hr0 hw hdiv
  set S : Space → ℝ := fun x =>
    ∑ i, ∑ j, FundSol.secondPartial (FundSol.potential g) i j x ^ 2 with hS
  have hSi : Integrable S := FundSol.integrable_sum_sq_secondPartial hgc hgs
  have hSint : ∫ x, S x ≤ 16 * (c₁ / r) ^ 2 * A ^ 2 := by
    rw [hS, FundSol.integral_sum_sq_secondPartial hgc hgs]
    calc ∫ x, g x ^ 2 ≤ ∫ x, 16 * (c₁ / r) ^ 2 * ‖w x‖ ^ 2 := by
          refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => sq_nonneg _)
            (hwi.const_mul _) (Filter.Eventually.of_forall fun x => ?_)
          exact sq_cutoffSource_le hr0 (hc₁ r hr0) hw hdiv x
      _ = 16 * (c₁ / r) ^ 2 * ∫ x, ‖w x‖ ^ 2 := integral_const_mul _ _
      _ ≤ 16 * (c₁ / r) ^ 2 * A ^ 2 := by gcongr
  have hl : (0 : ℝ) < 1 / r := by positivity
  set G : Space → ℝ := fun x => U₀ * (3 * (1 / r) / 2 * ‖w x‖ ^ 2 + S x / (2 * (1 / r)))
    with hG
  have hGi : Integrable G :=
    ((hwi.const_mul _).add (hSi.div_const _)).const_mul _
  have hGint : ∫ x, G x = U₀ * (3 * (1 / r) / 2 * (∫ x, ‖w x‖ ^ 2) + (∫ x, S x) / (2 * (1 / r))) := by
    rw [hG, integral_const_mul, integral_add (hwi.const_mul _) (hSi.div_const _),
      integral_const_mul, integral_div]
  have h1 : |stressPairing u w (FundSol.potential g)| ≤ ∫ x, G x :=
    abs_integral_le_of_pointwise hGi fun x =>
      abs_pairing_le_left (u x) (w x) (fun i j => FundSol.secondPartial (FundSol.potential g) i j x)
        hl (hd.bound_u x)
  have h2 : |stressPairing w u (FundSol.potential g)| ≤ ∫ x, G x :=
    abs_integral_le_of_pointwise hGi fun x =>
      abs_pairing_le_right (w x) (u x) (fun i j => FundSol.secondPartial (FundSol.potential g) i j x)
        hl (hd.bound_u x)
  have hbound : ∫ x, G x ≤ U₀ * ((3 / 2 + 8 * c₁ ^ 2) * A ^ 2 / r) := by
    rw [hGint]
    apply mul_le_mul_of_nonneg_left _ hU
    have e1 : 3 * (1 / r) / 2 * (∫ x, ‖w x‖ ^ 2) ≤ 3 * (1 / r) / 2 * A ^ 2 := by gcongr
    have e2 : (∫ x, S x) / (2 * (1 / r)) ≤ 16 * (c₁ / r) ^ 2 * A ^ 2 / (2 * (1 / r)) := by
      gcongr
    have e3 : 3 * (1 / r) / 2 * A ^ 2 + 16 * (c₁ / r) ^ 2 * A ^ 2 / (2 * (1 / r)) =
        (3 / 2 + 8 * c₁ ^ 2) * A ^ 2 / r := by
      field_simp
      ring
    linarith
  calc _ ≤ |stressPairing u w (FundSol.potential g)| + |stressPairing w u (FundSol.potential g)| :=
        abs_add_le _ _
    _ ≤ U₀ * ((3 / 2 + 8 * c₁ ^ 2) * A ^ 2 / r) + U₀ * ((3 / 2 + 8 * c₁ ^ 2) * A ^ 2 / r) := by
        linarith
    _ = (3 + 16 * c₁ ^ 2) * U₀ * A ^ 2 / r := by ring

end Breakdown
