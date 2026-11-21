import Breakdown.CertTorus.DecayStatements
import Breakdown.Uniqueness.ProductBound

open MeasureTheory Set Real Filter Topology
open scoped ContDiff ENNReal

noncomputable section

namespace Breakdown.FarField

private def farProfile (i : Fin 3) (M : ℝ) (x : Space) : ℝ :=
  FundSol.kernelGrad (-x) i * (1 - Real.smoothTransition (2 - 8 * ‖x‖ ^ 2 / M ^ 2))

private theorem farWeight_eq_farProfile (i : Fin 3) (y : Space) :
    farWeight i y = fun z => farProfile i (max 1 ‖y‖) (z - y) := by
  funext z
  simp only [farWeight, farProfile, nearCutoff, neg_sub]

private theorem kernelGrad_smul {c : ℝ} (hc : 0 < c) (x : Space) :
    FundSol.kernelGrad (c • x) = (c ^ 2)⁻¹ • FundSol.kernelGrad x := by
  unfold FundSol.kernelGrad
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hc, smul_smul, smul_smul]
  congr 1
  have hc3 : c⁻¹ ^ 3 * c = (c ^ 2)⁻¹ := by
    field_simp
  have e : (c * ‖x‖)⁻¹ ^ 3 = c⁻¹ ^ 3 * ‖x‖⁻¹ ^ 3 := by
    rw [mul_inv, mul_pow]
  rw [e]
  linear_combination (4⁻¹ * π⁻¹ * ‖x‖⁻¹ ^ 3) * hc3

private theorem farProfile_scale (i : Fin 3) {M : ℝ} (hM : 0 < M) (x : Space) :
    farProfile i M x = (M⁻¹) ^ 2 * farProfile i 1 (M⁻¹ • x) := by
  have hx : -x = M • (-(M⁻¹ • x)) := by
    rw [smul_neg, smul_smul, mul_inv_cancel₀ hM.ne', one_smul]
  have hcut : 2 - 8 * ‖M⁻¹ • x‖ ^ 2 / (1 : ℝ) ^ 2 = 2 - 8 * ‖x‖ ^ 2 / M ^ 2 := by
    rw [norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hM]
    field_simp
  unfold farProfile
  rw [hcut]
  conv_lhs => rw [hx, kernelGrad_smul hM]
  rw [PiLp.smul_apply, smul_eq_mul, inv_pow]
  ring

private theorem farProfile_eq_zero (i : Fin 3) {M : ℝ} (hM : 0 < M) {x : Space}
    (hx : 3 * ‖x‖ < M) : farProfile i M x = 0 := by
  unfold farProfile
  have h1 : 1 ≤ 2 - 8 * ‖x‖ ^ 2 / M ^ 2 := by
    have hx2 : 8 * ‖x‖ ^ 2 ≤ M ^ 2 := by nlinarith [norm_nonneg x]
    have : 8 * ‖x‖ ^ 2 / M ^ 2 ≤ 1 := by
      rw [div_le_one (by positivity)]
      exact hx2
    linarith
  rw [Real.smoothTransition.one_of_one_le h1, sub_self, mul_zero]

private theorem farProfile_eq_kernel (i : Fin 3) {M : ℝ} (hM : 0 < M) {x : Space}
    (hx : M < 2 * ‖x‖) : farProfile i M x = FundSol.kernelGrad (-x) i := by
  unfold farProfile
  have h1 : 2 - 8 * ‖x‖ ^ 2 / M ^ 2 ≤ 0 := by
    have hx2 : 2 * M ^ 2 ≤ 8 * ‖x‖ ^ 2 := by nlinarith
    have : 2 ≤ 8 * ‖x‖ ^ 2 / M ^ 2 := by
      rw [le_div_iff₀ (by positivity)]
      exact hx2
    linarith
  rw [Real.smoothTransition.zero_of_nonpos h1, sub_zero, mul_one]

private theorem eventually_farProfile_eq_zero (i : Fin 3) {M : ℝ} (hM : 0 < M) {x : Space}
    (hx : 3 * ‖x‖ < M) : farProfile i M =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
  have h : ∀ᶠ w in 𝓝 x, 3 * ‖w‖ < M :=
    (continuous_const.mul continuous_norm).continuousAt.eventually_lt continuousAt_const hx
  exact h.mono fun w hw => farProfile_eq_zero i hM hw

private theorem farProfile_contDiff (i : Fin 3) {M : ℝ} (hM : 0 < M) :
    ContDiff ℝ 2 (farProfile i M) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : 3 * ‖x‖ < M
  · exact contDiffAt_const.congr_of_eventuallyEq (eventually_farProfile_eq_zero i hM hx)
  · have hx0 : x ≠ 0 := by
      rintro rfl
      simp at hx
      linarith
    have hfun : (fun w : Space => FundSol.kernelGrad (-w) i) =
        fun w => (4 * π)⁻¹ * ‖w‖⁻¹ ^ 3 * -(EuclideanSpace.proj i w) := by
      funext w
      simp [FundSol.kernelGrad, norm_neg]
    have hk : ContDiffAt ℝ 2 (fun w : Space => FundSol.kernelGrad (-w) i) x := by
      rw [hfun]
      exact (contDiffAt_const.mul (((contDiffAt_norm ℝ hx0).inv
        (norm_ne_zero_iff.mpr hx0)).pow 3)).mul
        (EuclideanSpace.proj i : Space →L[ℝ] ℝ).contDiff.contDiffAt.neg
    have hc : ContDiff ℝ 2
        (fun w : Space => 1 - Real.smoothTransition (2 - 8 * ‖w‖ ^ 2 / M ^ 2)) := by
      have hs : ContDiff ℝ 2 Real.smoothTransition := Real.smoothTransition.contDiff
      exact contDiff_const.sub (hs.comp (contDiff_const.sub
        ((contDiff_const.mul (contDiff_norm_sq ℝ)).div_const _)))
    exact hk.mul hc.contDiffAt

private theorem iteratedFDeriv_farProfile_eq_zero (i : Fin 3) {M : ℝ} (hM : 0 < M) {x : Space}
    (hx : 3 * ‖x‖ < M) : iteratedFDeriv ℝ 2 (farProfile i M) x = 0 := by
  rw [((eventually_farProfile_eq_zero i hM hx).iteratedFDeriv ℝ 2).eq_of_nhds]
  simp

private theorem norm_iteratedFDeriv_farProfile_le (i : Fin 3) {M : ℝ} (hM : 0 < M) (x : Space) :
    ‖iteratedFDeriv ℝ 2 (farProfile i M) x‖ ≤
      (M⁻¹) ^ 4 * ‖iteratedFDeriv ℝ 2 (farProfile i 1) (M⁻¹ • x)‖ := by
  set L : Space →L[ℝ] Space := M⁻¹ • ContinuousLinearMap.id ℝ Space with hLdef
  have hLx : ∀ w, L w = M⁻¹ • w := fun w => rfl
  have hfun : farProfile i M = fun w => (M⁻¹) ^ 2 • (farProfile i 1 ∘ L) w := by
    funext w
    rw [farProfile_scale i hM, Function.comp_apply, hLx, smul_eq_mul]
  have hs : ContDiff ℝ 2 (farProfile i 1) := farProfile_contDiff i one_pos
  have hL : ‖L‖ ≤ M⁻¹ := by
    calc ‖L‖ ≤ ‖M⁻¹‖ * ‖ContinuousLinearMap.id ℝ Space‖ := norm_smul_le _ _
      _ ≤ M⁻¹ * 1 := by
        rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hM)]
        exact mul_le_mul_of_nonneg_left ContinuousLinearMap.norm_id_le (inv_pos.mpr hM).le
      _ = M⁻¹ := mul_one _
  rw [hfun, iteratedFDeriv_const_smul_apply' ((hs.comp L.contDiff).contDiffAt), norm_smul,
    L.iteratedFDeriv_comp_right hs x le_rfl, hLx]
  have hc := ContinuousMultilinearMap.norm_compContinuousLinearMap_le
    (iteratedFDeriv ℝ 2 (farProfile i 1) (M⁻¹ • x)) (fun _ : Fin 2 => L)
  rw [Fin.prod_univ_two] at hc
  have hM0 : 0 ≤ M⁻¹ := (inv_pos.mpr hM).le
  have hN := norm_nonneg (iteratedFDeriv ℝ 2 (farProfile i 1) (M⁻¹ • x))
  have hLL : ‖L‖ * ‖L‖ ≤ M⁻¹ * M⁻¹ := mul_le_mul hL hL (norm_nonneg _) hM0
  rw [norm_pow, Real.norm_eq_abs, abs_of_nonneg hM0]
  calc (M⁻¹) ^ 2 * ‖(iteratedFDeriv ℝ 2 (farProfile i 1) (M⁻¹ • x)).compContinuousLinearMap
        fun _ => L‖
      ≤ (M⁻¹) ^ 2 * (‖iteratedFDeriv ℝ 2 (farProfile i 1) (M⁻¹ • x)‖ * (‖L‖ * ‖L‖)) :=
        mul_le_mul_of_nonneg_left hc (by positivity)
    _ ≤ (M⁻¹) ^ 2 * (‖iteratedFDeriv ℝ 2 (farProfile i 1) (M⁻¹ • x)‖ * (M⁻¹ * M⁻¹)) := by
        gcongr
    _ = (M⁻¹) ^ 4 * ‖iteratedFDeriv ℝ 2 (farProfile i 1) (M⁻¹ • x)‖ := by ring


private theorem farProfile_bound (i : Fin 3) : ∃ B : ℝ, 0 ≤ B ∧ ∀ u : Space,
    ‖iteratedFDeriv ℝ 2 (farProfile i 1) u‖ ≤ B ∧
      ‖iteratedFDeriv ℝ 2 (farProfile i 1) u‖ ≤ B * ‖u‖⁻¹ ^ 4 := by
  have hs := farProfile_contDiff i one_pos
  have hcont : Continuous (iteratedFDeriv ℝ 2 (farProfile i 1)) :=
    hs.continuous_iteratedFDeriv le_rfl
  obtain ⟨B₀, hB₀⟩ :=
    (isCompact_closedBall (0 : Space) 1).exists_bound_of_continuousOn hcont.continuousOn
  refine ⟨max B₀ 0, le_max_right _ _, fun u => ?_⟩
  set B := max B₀ 0 with hBdef
  have hB : 0 ≤ B := le_max_right _ _
  have hin : ∀ w : Space, ‖w‖ ≤ 1 → ‖iteratedFDeriv ℝ 2 (farProfile i 1) w‖ ≤ B := by
    intro w hw
    exact (hB₀ w (by simpa using hw)).trans (le_max_left _ _)
  by_cases hu : ‖u‖ ≤ 1
  · refine ⟨hin u hu, ?_⟩
    by_cases h3 : 3 * ‖u‖ < 1
    · rw [iteratedFDeriv_farProfile_eq_zero i one_pos h3, norm_zero]
      positivity
    · have hpos : 0 < ‖u‖ := by linarith
      have h1 : 1 ≤ ‖u‖⁻¹ := (one_le_inv₀ hpos).mpr hu
      have h4 : 1 ≤ ‖u‖⁻¹ ^ 4 := one_le_pow₀ h1
      calc ‖iteratedFDeriv ℝ 2 (farProfile i 1) u‖ ≤ B := hin u hu
        _ = B * 1 := (mul_one B).symm
        _ ≤ B * ‖u‖⁻¹ ^ 4 := mul_le_mul_of_nonneg_left h4 hB
  · push Not at hu
    set t := ‖u‖ with htdef
    have ht : 0 < t := by linarith
    have hev : farProfile i 1 =ᶠ[𝓝 u] farProfile i t := by
      have h : ∀ᶠ w in 𝓝 u, t < 2 * ‖w‖ :=
        continuousAt_const.eventually_lt (continuous_const.mul continuous_norm).continuousAt
          (by linarith)
      refine h.mono fun w hw => ?_
      rw [farProfile_eq_kernel i one_pos (by linarith), farProfile_eq_kernel i ht hw]
    have hD : iteratedFDeriv ℝ 2 (farProfile i 1) u = iteratedFDeriv ℝ 2 (farProfile i t) u :=
      (hev.iteratedFDeriv ℝ 2).eq_of_nhds
    have hnorm : ‖t⁻¹ • u‖ = 1 := by
      rw [norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos ht, ← htdef, inv_mul_cancel₀ ht.ne']
    have hle : ‖iteratedFDeriv ℝ 2 (farProfile i 1) u‖ ≤ t⁻¹ ^ 4 * B := by
      rw [hD]
      exact (norm_iteratedFDeriv_farProfile_le i ht u).trans
        (mul_le_mul_of_nonneg_left (hin _ hnorm.le) (by positivity))
    have ht1 : t⁻¹ ^ 4 ≤ 1 := pow_le_one₀ (by positivity) (inv_le_one_of_one_le₀ hu.le)
    constructor
    · calc _ ≤ t⁻¹ ^ 4 * B := hle
        _ ≤ 1 * B := mul_le_mul_of_nonneg_right ht1 hB
        _ = B := one_mul B
    · calc _ ≤ t⁻¹ ^ 4 * B := hle
        _ = B * ‖u‖⁻¹ ^ 4 := by rw [htdef]; ring

private theorem farProfile_uniform : ∃ B : ℝ, 0 ≤ B ∧ ∀ (i : Fin 3) (M : ℝ), 0 < M →
    ∀ x : Space, ‖iteratedFDeriv ℝ 2 (farProfile i M) x‖ ≤ B * (M⁻¹) ^ 4 ∧
      ‖iteratedFDeriv ℝ 2 (farProfile i M) x‖ ≤ B * ‖x‖⁻¹ ^ 4 := by
  choose B hB0 hB using farProfile_bound
  refine ⟨∑ j, B j, Finset.sum_nonneg fun j _ => hB0 j, fun i M hM x => ?_⟩
  have hBi : B i ≤ ∑ j, B j := Finset.single_le_sum (fun j _ => hB0 j) (Finset.mem_univ i)
  have h := norm_iteratedFDeriv_farProfile_le i hM x
  obtain ⟨h1, h2⟩ := hB i (M⁻¹ • x)
  have hMi : 0 ≤ (M⁻¹) ^ 4 := by positivity
  constructor
  · calc _ ≤ (M⁻¹) ^ 4 * ‖iteratedFDeriv ℝ 2 (farProfile i 1) (M⁻¹ • x)‖ := h
      _ ≤ (M⁻¹) ^ 4 * B i := mul_le_mul_of_nonneg_left h1 hMi
      _ ≤ (M⁻¹) ^ 4 * ∑ j, B j := mul_le_mul_of_nonneg_left hBi hMi
      _ = (∑ j, B j) * (M⁻¹) ^ 4 := mul_comm _ _
  · have hn : ‖M⁻¹ • x‖⁻¹ ^ 4 = M ^ 4 * ‖x‖⁻¹ ^ 4 := by
      rw [norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hM, mul_inv, inv_inv, mul_pow]
    calc _ ≤ (M⁻¹) ^ 4 * ‖iteratedFDeriv ℝ 2 (farProfile i 1) (M⁻¹ • x)‖ := h
      _ ≤ (M⁻¹) ^ 4 * (B i * (M ^ 4 * ‖x‖⁻¹ ^ 4)) := by
        rw [← hn]
        exact mul_le_mul_of_nonneg_left h2 hMi
      _ = B i * ‖x‖⁻¹ ^ 4 := by
        field_simp
      _ ≤ (∑ j, B j) * ‖x‖⁻¹ ^ 4 := mul_le_mul_of_nonneg_right hBi (by positivity)

private theorem lintegral_ball_inv_sq_le {ρ : ℝ} (hρ : 0 < ρ) :
    ∫⁻ z in Metric.ball (0 : Space) ρ, ENNReal.ofReal (‖z‖⁻¹ ^ 2) ≤
      ENNReal.ofReal (20 * π / 3 * ρ) := by
  have hpt : ∀ z ∈ Metric.ball (0 : Space) ρ, ENNReal.ofReal (‖z‖⁻¹ ^ 2) ≤
      ENNReal.ofReal (ρ ^ (2 / 5 : ℝ)) * ENNReal.ofReal (‖z‖⁻¹ ^ 2) ^ (6 / 5 : ℝ) := by
    intro z hz
    rw [mem_ball_zero_iff] at hz
    rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num),
      ← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    rcases eq_or_lt_of_le (norm_nonneg z) with h0 | hpos
    · rw [← h0]
      simp
    · set s := ‖z‖ with hs
      have ha : 0 < s⁻¹ := inv_pos.mpr hpos
      have e1 : (s⁻¹ ^ 2) ^ (6 / 5 : ℝ) = s⁻¹ ^ (12 / 5 : ℝ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul ha.le]
        norm_num
      have e2 : s⁻¹ ^ 2 = s⁻¹ ^ (12 / 5 : ℝ) * s ^ (2 / 5 : ℝ) := by
        rw [Real.inv_rpow hpos.le, ← Real.rpow_neg hpos.le, ← Real.rpow_add hpos, inv_pow,
          ← Real.rpow_natCast, ← Real.rpow_neg hpos.le]
        norm_num
      rw [e1, e2, mul_comm (ρ ^ (2 / 5 : ℝ))]
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow hpos.le hz.le (by norm_num)) (by positivity)
  calc ∫⁻ z in Metric.ball (0 : Space) ρ, ENNReal.ofReal (‖z‖⁻¹ ^ 2)
      ≤ ∫⁻ z in Metric.ball (0 : Space) ρ,
          ENNReal.ofReal (ρ ^ (2 / 5 : ℝ)) * ENNReal.ofReal (‖z‖⁻¹ ^ 2) ^ (6 / 5 : ℝ) :=
        setLIntegral_mono' measurableSet_ball hpt
    _ = ENNReal.ofReal (ρ ^ (2 / 5 : ℝ)) * ∫⁻ z in Metric.ball (0 : Space) ρ,
          ENNReal.ofReal (‖z‖⁻¹ ^ 2) ^ (6 / 5 : ℝ) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal (ρ ^ (2 / 5 : ℝ)) * ENNReal.ofReal (20 * π / 3 * ρ ^ (3 / 5 : ℝ)) :=
        by gcongr; exact lintegral_inner_kernel_le hρ
    _ = ENNReal.ofReal (20 * π / 3 * ρ) := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        congr 1
        have : ρ ^ (2 / 5 : ℝ) * ρ ^ (3 / 5 : ℝ) = ρ := by
          rw [← Real.rpow_add hρ]
          norm_num
        calc ρ ^ (2 / 5 : ℝ) * (20 * π / 3 * ρ ^ (3 / 5 : ℝ))
            = 20 * π / 3 * (ρ ^ (2 / 5 : ℝ) * ρ ^ (3 / 5 : ℝ)) := by ring
          _ = 20 * π / 3 * ρ := by rw [this]

private theorem lintegral_compl_ball_inv_six_le {ρ : ℝ} (hρ : 0 < ρ) :
    ∫⁻ z in (Metric.ball (0 : Space) ρ)ᶜ, ENNReal.ofReal (‖z‖⁻¹ ^ 6) ≤
      ENNReal.ofReal (4 * π / 3 * ρ⁻¹ ^ 3) := by
  have h : ∀ z : Space, ENNReal.ofReal (‖z‖⁻¹ ^ 6) = ENNReal.ofReal (‖z‖⁻¹ ^ 3) ^ (2 : ℝ) := by
    intro z
    rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num), Real.rpow_two, ← pow_mul]
  simp_rw [h]
  exact lintegral_outer_kernel_le hρ

private theorem abs_apply_unitVector_le
    (m : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => Space) ℝ) (a b : Fin 3) :
    |m ![unitVector a, unitVector b]| ≤ ‖m‖ := by
  have h := m.le_opNorm ![unitVector a, unitVector b]
  have hu : ∀ c : Fin 3, ‖unitVector c‖ = 1 := by
    intro c
    simp [unitVector]
  rw [Fin.prod_univ_two] at h
  simpa [hu, Real.norm_eq_abs] using h

private theorem abs_sum_le (f : Space → Fin 3 → Fin 3 → ℝ) (i : Fin 3) (M : ℝ) (y z : Space)
    (hD : iteratedFDeriv ℝ 2 (farWeight i y) z = iteratedFDeriv ℝ 2 (farProfile i M) (z - y)) :
    |∑ a : Fin 3, ∑ b : Fin 3,
        iteratedFDeriv ℝ 2 (farWeight i y) z ![unitVector a, unitVector b] * f z a b| ≤
      9 * (‖iteratedFDeriv ℝ 2 (farProfile i M) (z - y)‖ * ‖f z‖) := by
  rw [hD]
  set m := iteratedFDeriv ℝ 2 (farProfile i M) (z - y)
  have hterm : ∀ a b : Fin 3, |m ![unitVector a, unitVector b] * f z a b| ≤ ‖m‖ * ‖f z‖ := by
    intro a b
    rw [abs_mul]
    have hf : |f z a b| ≤ ‖f z‖ := by
      rw [← Real.norm_eq_abs]
      exact (norm_le_pi_norm (f z a) b).trans (norm_le_pi_norm (f z) a)
    exact mul_le_mul (abs_apply_unitVector_le m a b) hf (abs_nonneg _) (norm_nonneg _)
  calc |∑ a : Fin 3, ∑ b : Fin 3, m ![unitVector a, unitVector b] * f z a b|
      ≤ ∑ a : Fin 3, |∑ b : Fin 3, m ![unitVector a, unitVector b] * f z a b| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ a : Fin 3, ∑ b : Fin 3, |m ![unitVector a, unitVector b] * f z a b| :=
        Finset.sum_le_sum fun a _ => Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _a : Fin 3, ∑ _b : Fin 3, ‖m‖ * ‖f z‖ :=
        Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => hterm a b
    _ = 9 * (‖m‖ * ‖f z‖) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

theorem newtonFarEstimate_holds : NewtonFarEstimate := by
  obtain ⟨B, hB0, hB⟩ := farProfile_uniform
  refine ⟨1152 * π * B, ?_⟩
  intro f A _hf hfA i y
  have hA : 0 ≤ A := by
    have h0 := hfA 0
    rw [norm_zero, add_zero, one_pow, div_one] at h0
    exact (norm_nonneg _).trans h0
  set M := max 1 ‖y‖ with hMdef
  have hStrain : 1 ≤ M := le_max_left _ _
  have hM : 0 < M := by linarith
  have hyM : ‖y‖ ≤ M := le_max_right _ _
  set g : Space → ℝ := fun z => ∑ a : Fin 3, ∑ b : Fin 3,
    iteratedFDeriv ℝ 2 (farWeight i y) z ![unitVector a, unitVector b] * f z a b with hgdef
  have hD : ∀ z, iteratedFDeriv ℝ 2 (farWeight i y) z =
      iteratedFDeriv ℝ 2 (farProfile i M) (z - y) := by
    intro z
    rw [farWeight_eq_farProfile]
    exact iteratedFDeriv_comp_sub 2 y z
  set near : Space → ℝ≥0∞ := (Metric.ball (0 : Space) (2 * M)).indicator
    (fun z => ENNReal.ofReal (‖z‖⁻¹ ^ 2)) with hneardef
  set far : Space → ℝ≥0∞ := (Metric.ball (0 : Space) (2 * M))ᶜ.indicator
    (fun z => ENNReal.ofReal (‖z‖⁻¹ ^ 6)) with hfardef
  have hnear_meas : Measurable near :=
    Measurable.indicator (by fun_prop) measurableSet_ball
  have hfar_meas : Measurable far :=
    Measurable.indicator (by fun_prop) measurableSet_ball.compl
  have hpt : ∀ z : Space, z ≠ 0 → ENNReal.ofReal ‖g z‖ ≤
      ENNReal.ofReal (9 * B * A * (M⁻¹) ^ 4) * near z +
        ENNReal.ofReal (144 * B * A) * far z := by
    intro z hz
    have hzpos : 0 < ‖z‖ := norm_pos_iff.mpr hz
    have hgz : ‖g z‖ ≤ 9 * (‖iteratedFDeriv ℝ 2 (farProfile i M) (z - y)‖ * ‖f z‖) := by
      rw [Real.norm_eq_abs]
      exact abs_sum_le f i M y z (hD z)
    have hfz : ‖f z‖ ≤ A * ‖z‖⁻¹ ^ 2 := by
      refine (hfA z).trans ?_
      rw [inv_pow, ← div_eq_mul_inv]
      exact div_le_div_of_nonneg_left hA (by positivity)
        (pow_le_pow_left₀ (norm_nonneg z) (by linarith) 2)
    obtain ⟨hDM, hDx⟩ := hB i M hM (z - y)
    by_cases hzM : ‖z‖ < 2 * M
    · have hin : z ∈ Metric.ball (0 : Space) (2 * M) := mem_ball_zero_iff.mpr hzM
      rw [hneardef, hfardef, Set.indicator_of_mem hin,
        Set.indicator_of_notMem (show z ∉ (Metric.ball (0 : Space) (2 * M))ᶜ from fun h => h hin), mul_zero, add_zero,
        ← ENNReal.ofReal_mul (by positivity)]
      apply ENNReal.ofReal_le_ofReal
      calc ‖g z‖ ≤ 9 * (‖iteratedFDeriv ℝ 2 (farProfile i M) (z - y)‖ * ‖f z‖) := hgz
        _ ≤ 9 * ((B * (M⁻¹) ^ 4) * (A * ‖z‖⁻¹ ^ 2)) := by
          gcongr
        _ = 9 * B * A * (M⁻¹) ^ 4 * ‖z‖⁻¹ ^ 2 := by ring
    · push Not at hzM
      have hout : z ∉ Metric.ball (0 : Space) (2 * M) := by
        rw [mem_ball_zero_iff]
        linarith
      rw [hneardef, hfardef, Set.indicator_of_notMem hout, Set.indicator_of_mem hout, mul_zero,
        zero_add, ← ENNReal.ofReal_mul (by positivity)]
      apply ENNReal.ofReal_le_ofReal
      have hxz : ‖z‖ / 2 ≤ ‖z - y‖ := by
        have := norm_sub_norm_le z y
        linarith
      have hxinv : ‖z - y‖⁻¹ ≤ 2 * ‖z‖⁻¹ := by
        have h2 : ‖z - y‖⁻¹ ≤ (‖z‖ / 2)⁻¹ := inv_anti₀ (by positivity) hxz
        rw [inv_div] at h2
        rw [div_eq_mul_inv] at h2
        linarith
      have hx4 : ‖z - y‖⁻¹ ^ 4 ≤ 16 * ‖z‖⁻¹ ^ 4 := by
        calc ‖z - y‖⁻¹ ^ 4 ≤ (2 * ‖z‖⁻¹) ^ 4 := pow_le_pow_left₀ (by positivity) hxinv 4
          _ = 16 * ‖z‖⁻¹ ^ 4 := by ring
      calc ‖g z‖ ≤ 9 * (‖iteratedFDeriv ℝ 2 (farProfile i M) (z - y)‖ * ‖f z‖) := hgz
        _ ≤ 9 * ((B * ‖z - y‖⁻¹ ^ 4) * (A * ‖z‖⁻¹ ^ 2)) := by
          gcongr
        _ ≤ 9 * ((B * (16 * ‖z‖⁻¹ ^ 4)) * (A * ‖z‖⁻¹ ^ 2)) := by
          gcongr
        _ = 144 * B * A * ‖z‖⁻¹ ^ 6 := by ring
  have hae : ∀ᵐ z ∂(volume : Measure Space), ENNReal.ofReal ‖g z‖ ≤
      ENNReal.ofReal (9 * B * A * (M⁻¹) ^ 4) * near z +
        ENNReal.ofReal (144 * B * A) * far z := by
    have h0 : ∀ᵐ z ∂(volume : Measure Space), z ≠ 0 := by
      rw [ae_iff]
      simp
    exact h0.mono hpt
  have hnear_int : ∫⁻ z, near z ≤ ENNReal.ofReal (20 * π / 3 * (2 * M)) := by
    rw [hneardef, lintegral_indicator measurableSet_ball]
    exact lintegral_ball_inv_sq_le (by positivity)
  have hfar_int : ∫⁻ z, far z ≤ ENNReal.ofReal (4 * π / 3 * (2 * M)⁻¹ ^ 3) := by
    rw [hfardef, lintegral_indicator measurableSet_ball.compl]
    exact lintegral_compl_ball_inv_six_le (by positivity)
  have hlint : ∫⁻ z, ENNReal.ofReal ‖g z‖ ≤ ENNReal.ofReal (144 * π * B * A * M⁻¹ ^ 3) := by
    calc ∫⁻ z, ENNReal.ofReal ‖g z‖
        ≤ ∫⁻ z, (ENNReal.ofReal (9 * B * A * (M⁻¹) ^ 4) * near z +
            ENNReal.ofReal (144 * B * A) * far z) := lintegral_mono_ae hae
      _ = ENNReal.ofReal (9 * B * A * (M⁻¹) ^ 4) * (∫⁻ z, near z) +
            ENNReal.ofReal (144 * B * A) * (∫⁻ z, far z) := by
          rw [lintegral_add_left (hnear_meas.const_mul _), lintegral_const_mul _ hnear_meas,
            lintegral_const_mul _ hfar_meas]
      _ ≤ ENNReal.ofReal (9 * B * A * (M⁻¹) ^ 4) * ENNReal.ofReal (20 * π / 3 * (2 * M)) +
            ENNReal.ofReal (144 * B * A) * ENNReal.ofReal (4 * π / 3 * (2 * M)⁻¹ ^ 3) := by
          gcongr
      _ = ENNReal.ofReal (144 * π * B * A * M⁻¹ ^ 3) := by
          rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
            ← ENNReal.ofReal_add (by positivity) (by positivity)]
          congr 1
          field_simp
          ring
  have hMy : M⁻¹ ^ 3 ≤ 8 / (1 + ‖y‖) ^ 3 := by
    have h1 : 1 + ‖y‖ ≤ 2 * M := by linarith
    have h2 : (1 + ‖y‖) ^ 3 ≤ (2 * M) ^ 3 := pow_le_pow_left₀ (by positivity) h1 3
    rw [inv_pow, le_div_iff₀ (by positivity)]
    calc (M ^ 3)⁻¹ * (1 + ‖y‖) ^ 3 ≤ (M ^ 3)⁻¹ * (2 * M) ^ 3 :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = 8 := by
          field_simp
          ring
  have hfin : 144 * π * B * A * M⁻¹ ^ 3 ≤ 1152 * π * B * A / (1 + ‖y‖) ^ 3 := by
    have hc : 0 ≤ 144 * π * B * A := by positivity
    calc 144 * π * B * A * M⁻¹ ^ 3 ≤ 144 * π * B * A * (8 / (1 + ‖y‖) ^ 3) :=
          mul_le_mul_of_nonneg_left hMy hc
      _ = 1152 * π * B * A / (1 + ‖y‖) ^ 3 := by ring
  calc |∫ z, g z| = ‖∫ z, g z‖ := (Real.norm_eq_abs _).symm
    _ ≤ (∫⁻ z, ENNReal.ofReal ‖g z‖).toReal := norm_integral_le_lintegral_norm g
    _ ≤ (ENNReal.ofReal (144 * π * B * A * M⁻¹ ^ 3)).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top hlint
    _ = 144 * π * B * A * M⁻¹ ^ 3 := ENNReal.toReal_ofReal (by positivity)
    _ ≤ 1152 * π * B * A / (1 + ‖y‖) ^ 3 := hfin
    _ = 1152 * π * B * A / (1 + ‖y‖) ^ 3 := rfl

end Breakdown.FarField
