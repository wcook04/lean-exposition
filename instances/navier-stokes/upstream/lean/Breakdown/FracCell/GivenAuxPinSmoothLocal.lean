import Breakdown.FracCell.GivenAuxActuatorSmooth
import Breakdown.FracCell.GivenAuxPinSmoothLocalLeaves

open scoped ContDiff
open MeasureTheory

noncomputable section

namespace Breakdown

namespace CellCert

namespace GivenFields

section Tame

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

private def TameAt (f : E → F) (y : E) : Prop :=
  ∃ r > 0, ∃ f' : E → (E →L[ℝ] F), ∃ K : ℝ, 0 ≤ K ∧ (∀ z ∈ Metric.ball y r, HasFDerivAt f (f' z) z) ∧
    ∀ z ∈ Metric.ball y r, ∀ w ∈ Metric.ball y r, ‖f' z - f' w‖ ≤ K * ‖z - w‖

private theorem tame_bounds {f : E → F} {y : E} {r : ℝ} {f' : E → (E →L[ℝ] F)} {K : ℝ} (hr : 0 < r)
    (hK0 : 0 ≤ K) (hd : ∀ z ∈ Metric.ball y r, HasFDerivAt f (f' z) z)
    (hK : ∀ z ∈ Metric.ball y r, ∀ w ∈ Metric.ball y r, ‖f' z - f' w‖ ≤ K * ‖z - w‖) :
    ∃ M : ℝ, 0 ≤ M ∧ (∀ z ∈ Metric.ball y r, ‖f' z‖ ≤ M) ∧
      (∀ z ∈ Metric.ball y r, ∀ w ∈ Metric.ball y r, ‖f z - f w‖ ≤ M * ‖z - w‖) ∧
      (∀ z ∈ Metric.ball y r, ‖f z‖ ≤ ‖f y‖ + M * r) := by
  have hy : y ∈ Metric.ball y r := Metric.mem_ball_self hr
  have hb : ∀ z ∈ Metric.ball y r, ‖f' z‖ ≤ ‖f' y‖ + K * r := by
    intro z hz
    have h1 := hK z hz y hy
    have h2 : ‖z - y‖ < r := by rw [Metric.mem_ball, dist_eq_norm] at hz; exact hz
    have h3 : ‖f' z‖ ≤ ‖f' y‖ + ‖f' z - f' y‖ := by
      have := norm_add_le (f' y) (f' z - f' y)
      simpa using this
    nlinarith [norm_nonneg (z - y)]
  have hM0 : 0 ≤ ‖f' y‖ + K * r := by positivity
  have hl : ∀ z ∈ Metric.ball y r, ∀ w ∈ Metric.ball y r, ‖f z - f w‖ ≤ (‖f' y‖ + K * r) * ‖z - w‖ := by
    intro z hz w hw
    have := (convex_ball y r).norm_image_sub_le_of_norm_hasFDerivWithin_le
      (fun x hx => (hd x hx).hasFDerivWithinAt) hb hw hz
    exact this
  refine ⟨‖f' y‖ + K * r, hM0, hb, hl, fun z hz => ?_⟩
  have h1 := hl z hz y hy
  have h2 : ‖z - y‖ < r := by rw [Metric.mem_ball, dist_eq_norm] at hz; exact hz
  have h3 : ‖f z‖ ≤ ‖f y‖ + ‖f z - f y‖ := by
    have := norm_add_le (f y) (f z - f y)
    simpa using this
  nlinarith [norm_nonneg (z - y)]

private theorem tame_of_contDiffAt {f : E → F} {y : E} (hf : ContDiffAt ℝ 2 f y) : TameAt f y := by
  have h1 : ContDiffAt ℝ 1 (fderiv ℝ f) y := hf.fderiv_right (by norm_num)
  obtain ⟨K, t, ht, hK⟩ := h1.exists_lipschitzOnWith
  have hev : ∀ᶠ z in nhds y, ContDiffAt ℝ 2 f z := hf.eventually (by simp)
  obtain ⟨r, hr, hsub⟩ := Metric.mem_nhds_iff.1 (Filter.inter_mem ht hev)
  refine ⟨r, hr, fderiv ℝ f, K, K.2, fun z hz => ((show ContDiffAt ℝ 2 f z from (hsub hz).2).differentiableAt (by norm_num)).hasFDerivAt,
    fun z hz w hw => ?_⟩
  have := hK.dist_le_mul z (hsub hz).1 w (hsub hw).1
  rwa [dist_eq_norm, dist_eq_norm] at this

private theorem tame_of_global {f : E → F} (hd : Differentiable ℝ f) (hl : LocallyLipschitz (fderiv ℝ f))
    (y : E) : TameAt f y := by
  obtain ⟨K, t, ht, hK⟩ := hl y
  obtain ⟨r, hr, hsub⟩ := Metric.mem_nhds_iff.1 ht
  refine ⟨r, hr, fderiv ℝ f, K, K.2, fun z _ => (hd z).hasFDerivAt, fun z hz w hw => ?_⟩
  have := hK.dist_le_mul z (hsub hz) w (hsub hw)
  rwa [dist_eq_norm, dist_eq_norm] at this

private theorem tame_slope {f : E → F} {y : E} (h : TameAt f y) :
    ∃ K : NNReal, ∃ U ∈ nhds y, LipschitzOnWith K (fderiv ℝ f) U := by
  obtain ⟨r, hr, f', K, hK0, h1, h2⟩ := h
  refine ⟨⟨K, hK0⟩, Metric.ball y r, Metric.ball_mem_nhds y hr, LipschitzOnWith.of_dist_le_mul fun z hz w hw => ?_⟩
  rw [(h1 z hz).fderiv, (h1 w hw).fderiv, dist_eq_norm, dist_eq_norm]
  exact h2 z hz w hw

private theorem tame_congr {f g : E → F} {y : E} (hg : TameAt g y) (h : f =ᶠ[nhds y] g) : TameAt f y := by
  obtain ⟨r, hr, g', K, hK0, h1, h2⟩ := hg
  obtain ⟨s, hs, hsub⟩ := Metric.mem_nhds_iff.1 h
  have sr : Metric.ball y (min r s) ⊆ Metric.ball y r := Metric.ball_subset_ball (min_le_left _ _)
  refine ⟨min r s, lt_min hr hs, g', K, hK0, fun z hz => ?_, fun z hz w hw => h2 z (sr hz) w (sr hw)⟩
  have hz' : z ∈ Metric.ball y s := Metric.ball_subset_ball (min_le_right _ _) hz
  have hev : f =ᶠ[nhds z] g :=
    Filter.mem_of_superset (Metric.isOpen_ball.mem_nhds hz') (fun x hx => hsub hx)
  exact (h1 z (sr hz)).congr_of_eventuallyEq hev

private theorem tame_add {f g : E → F} {y : E} (hf : TameAt f y) (hg : TameAt g y) :
    TameAt (fun z => f z + g z) y := by
  obtain ⟨r1, hr1, f', K1, hK1, h1, h2⟩ := hf
  obtain ⟨r2, hr2, g', K2, hK2, k1, k2⟩ := hg
  have s1 : Metric.ball y (min r1 r2) ⊆ Metric.ball y r1 := Metric.ball_subset_ball (min_le_left _ _)
  have s2 : Metric.ball y (min r1 r2) ⊆ Metric.ball y r2 := Metric.ball_subset_ball (min_le_right _ _)
  refine ⟨min r1 r2, lt_min hr1 hr2, fun z => f' z + g' z, K1 + K2, by positivity,
    fun z hz => (h1 z (s1 hz)).add (k1 z (s2 hz)), fun z hz w hw => ?_⟩
  have e : f' z + g' z - (f' w + g' w) = (f' z - f' w) + (g' z - g' w) := by abel
  rw [e]
  have a1 := h2 z (s1 hz) w (s1 hw)
  have a2 := k2 z (s2 hz) w (s2 hw)
  calc _ ≤ ‖f' z - f' w‖ + ‖g' z - g' w‖ := norm_add_le _ _
    _ ≤ K1 * ‖z - w‖ + K2 * ‖z - w‖ := add_le_add a1 a2
    _ = (K1 + K2) * ‖z - w‖ := by ring

private theorem tame_clm {f : E → F} {y : E} (L : F →L[ℝ] G) (hf : TameAt f y) :
    TameAt (fun z => L (f z)) y := by
  obtain ⟨r, hr, f', K, hK0, h1, h2⟩ := hf
  refine ⟨r, hr, fun z => L.comp (f' z), ‖L‖ * K, by positivity,
    fun z hz => L.hasFDerivAt.comp z (h1 z hz), fun z hz w hw => ?_⟩
  rw [← ContinuousLinearMap.comp_sub]
  calc _ ≤ ‖L‖ * ‖f' z - f' w‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖L‖ * (K * ‖z - w‖) := mul_le_mul_of_nonneg_left (h2 z hz w hw) (norm_nonneg _)
    _ = ‖L‖ * K * ‖z - w‖ := by ring

private theorem tame_comp {Φ : E → F} {g : F → G} {y : E} (hg : TameAt g (Φ y)) (hΦ : TameAt Φ y) :
    TameAt (fun z => g (Φ z)) y := by
  obtain ⟨r1, hr1, g', K1, hK1, hg1, hg2⟩ := hg
  obtain ⟨r2, hr2, Φ', K2, hK2, hΦ1, hΦ2⟩ := hΦ
  obtain ⟨M1, hM1, hb1, -, -⟩ := tame_bounds hr1 hK1 hg1 hg2
  obtain ⟨M2, hM2, hb2, hl2, -⟩ := tame_bounds hr2 hK2 hΦ1 hΦ2
  have hq : 0 < r1 / (M2 + 1) := div_pos hr1 (by linarith)
  have s2 : Metric.ball y (min r2 (r1 / (M2 + 1))) ⊆ Metric.ball y r2 := Metric.ball_subset_ball (min_le_left _ _)
  have hmap : ∀ z ∈ Metric.ball y (min r2 (r1 / (M2 + 1))), Φ z ∈ Metric.ball (Φ y) r1 := by
    intro z hz
    have h := hl2 z (s2 hz) y (Metric.mem_ball_self hr2)
    have hzr : ‖z - y‖ < r1 / (M2 + 1) := by
      rw [Metric.mem_ball, dist_eq_norm] at hz
      exact lt_of_lt_of_le hz (min_le_right _ _)
    have h3 : ‖z - y‖ * (M2 + 1) < r1 := (lt_div_iff₀ (by linarith)).1 hzr
    rw [Metric.mem_ball, dist_eq_norm]
    nlinarith [norm_nonneg (z - y)]
  refine ⟨min r2 (r1 / (M2 + 1)), lt_min hr2 hq, fun z => (g' (Φ z)).comp (Φ' z), K1 * M2 * M2 + M1 * K2,
    by positivity, fun z hz => (hg1 (Φ z) (hmap z hz)).comp z (hΦ1 z (s2 hz)), fun z hz w hw => ?_⟩
  have e : (g' (Φ z)).comp (Φ' z) - (g' (Φ w)).comp (Φ' w) =
      (g' (Φ z) - g' (Φ w)).comp (Φ' z) + (g' (Φ w)).comp (Φ' z - Φ' w) := by
    rw [ContinuousLinearMap.sub_comp, ContinuousLinearMap.comp_sub]
    abel
  rw [e]
  have a1 := hg2 (Φ z) (hmap z hz) (Φ w) (hmap w hw)
  have a2 := hl2 z (s2 hz) w (s2 hw)
  have a3 := hb2 z (s2 hz)
  have a4 := hb1 (Φ w) (hmap w hw)
  have a5 := hΦ2 z (s2 hz) w (s2 hw)
  calc _ ≤ ‖g' (Φ z) - g' (Φ w)‖ * ‖Φ' z‖ + ‖g' (Φ w)‖ * ‖Φ' z - Φ' w‖ :=
        (norm_add_le _ _).trans (add_le_add (ContinuousLinearMap.opNorm_comp_le _ _)
          (ContinuousLinearMap.opNorm_comp_le _ _))
    _ ≤ (K1 * (M2 * ‖z - w‖)) * M2 + M1 * (K2 * ‖z - w‖) := by
        refine add_le_add (mul_le_mul (a1.trans (mul_le_mul_of_nonneg_left a2 hK1)) a3 (norm_nonneg _)
          (by positivity)) (mul_le_mul a4 a5 (norm_nonneg _) hM1)
    _ = (K1 * M2 * M2 + M1 * K2) * ‖z - w‖ := by ring

private theorem tame_mul {c d : E → ℂ} {y : E} (hc : TameAt c y) (hd : TameAt d y) :
    TameAt (fun z => c z * d z) y := by
  obtain ⟨r1, hr1, c', K1, hK1, hc1, hc2⟩ := hc
  obtain ⟨r2, hr2, d', K2, hK2, hd1, hd2⟩ := hd
  obtain ⟨M1, hM1, hb1, hl1, hv1⟩ := tame_bounds hr1 hK1 hc1 hc2
  obtain ⟨M2, hM2, hb2, hl2, hv2⟩ := tame_bounds hr2 hK2 hd1 hd2
  have s1 : Metric.ball y (min r1 r2) ⊆ Metric.ball y r1 := Metric.ball_subset_ball (min_le_left _ _)
  have s2 : Metric.ball y (min r1 r2) ⊆ Metric.ball y r2 := Metric.ball_subset_ball (min_le_right _ _)
  have hA1 : 0 ≤ ‖c y‖ + M1 * r1 := by positivity
  have hA2 : 0 ≤ ‖d y‖ + M2 * r2 := by positivity
  refine ⟨min r1 r2, lt_min hr1 hr2, fun z => c z • d' z + d z • c' z,
    (‖c y‖ + M1 * r1) * K2 + M1 * M2 + (‖d y‖ + M2 * r2) * K1 + M2 * M1, by positivity,
    fun z hz => (hc1 z (s1 hz)).mul (hd1 z (s2 hz)), fun z hz w hw => ?_⟩
  have e : (c z • d' z + d z • c' z) - (c w • d' w + d w • c' w) =
      (c z • (d' z - d' w) + (c z - c w) • d' w) + (d z • (c' z - c' w) + (d z - d w) • c' w) := by
    simp only [smul_sub, sub_smul]
    abel
  rw [e]
  have t1 : ‖c z • (d' z - d' w)‖ ≤ (‖c y‖ + M1 * r1) * (K2 * ‖z - w‖) :=
    (norm_smul_le _ _).trans (mul_le_mul (hv1 z (s1 hz)) (hd2 z (s2 hz) w (s2 hw)) (norm_nonneg _) hA1)
  have t2 : ‖(c z - c w) • d' w‖ ≤ (M1 * ‖z - w‖) * M2 :=
    (norm_smul_le _ _).trans (mul_le_mul (hl1 z (s1 hz) w (s1 hw)) (hb2 w (s2 hw)) (norm_nonneg _)
      (by positivity))
  have t3 : ‖d z • (c' z - c' w)‖ ≤ (‖d y‖ + M2 * r2) * (K1 * ‖z - w‖) :=
    (norm_smul_le _ _).trans (mul_le_mul (hv2 z (s2 hz)) (hc2 z (s1 hz) w (s1 hw)) (norm_nonneg _) hA2)
  have t4 : ‖(d z - d w) • c' w‖ ≤ (M2 * ‖z - w‖) * M1 :=
    (norm_smul_le _ _).trans (mul_le_mul (hl2 z (s2 hz) w (s2 hw)) (hb1 w (s1 hw)) (norm_nonneg _)
      (by positivity))
  calc _ ≤ (‖c z • (d' z - d' w)‖ + ‖(c z - c w) • d' w‖) + (‖d z • (c' z - c' w)‖ + ‖(d z - d w) • c' w‖) :=
        (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) (norm_add_le _ _))
    _ ≤ ((‖c y‖ + M1 * r1) * (K2 * ‖z - w‖) + (M1 * ‖z - w‖) * M2) +
        ((‖d y‖ + M2 * r2) * (K1 * ‖z - w‖) + (M2 * ‖z - w‖) * M1) :=
        add_le_add (add_le_add t1 t2) (add_le_add t3 t4)
    _ = _ := by ring

private theorem tame_neg {f : E → F} {y : E} (hf : TameAt f y) : TameAt (fun z => -f z) y :=
  tame_congr (tame_clm (-(ContinuousLinearMap.id ℝ F)) hf) (Filter.Eventually.of_forall fun z => by simp)

private theorem tame_sub {f g : E → F} {y : E} (hf : TameAt f y) (hg : TameAt g y) :
    TameAt (fun z => f z - g z) y :=
  tame_congr (tame_add hf (tame_neg hg)) (Filter.Eventually.of_forall fun z => by simp [sub_eq_add_neg])

end Tame

private theorem pin_coord (i : Fin 3) : ContDiff ℝ ⊤ (fun y : Space => y i) :=
  (EuclideanSpace.proj i : Space →L[ℝ] ℝ).contDiff

private theorem pin_norm {y : Space} (hy : y ≠ 0) : ContDiffAt ℝ ⊤ (fun y : Space => ‖y‖) y :=
  contDiffAt_norm ℝ hy

private theorem pin_ratio {y : Space} (hy : y ≠ 0) (j : Fin 3) : ContDiffAt ℝ ⊤ (fun y : Space => y j / ‖y‖) y :=
  (pin_coord j).contDiffAt.div (pin_norm hy) (norm_ne_zero_iff.2 hy)

private theorem pin_chartT (P : ChartParams) (hP : IsChartParams P) {y : Space} (hy : y ≠ 0) :
    ContDiffAt ℝ ⊤ (chartT P) y := by
  have h1 := pin_norm hy
  have hne : ‖y‖ + P.L0 ≠ 0 := by have := hP.L0_pos; positivity
  exact h1.div (h1.add contDiffAt_const) hne

private theorem pin_height {y : Space} (hy : y ≠ 0) : ContDiffAt ℝ ⊤ heightRatio y :=
  pin_ratio hy 2

private theorem pin_decay (P : ChartParams) (hP : IsChartParams P) {y : Space} (hy : y ≠ 0) :
    ContDiffAt ℝ ⊤ (decayFactor P) y := by
  have hs : chartS P y ≠ 0 := by
    unfold chartS chartT
    have hL := hP.L0_pos
    have hd : 0 < ‖y‖ + P.L0 := by positivity
    rw [sub_ne_zero]
    intro h
    rw [eq_comm, div_eq_one_iff_eq hd.ne'] at h
    linarith
  exact (contDiffAt_const.sub (pin_chartT P hP hy)).rpow_const_of_ne hs

private theorem pin_logPhase (P : ChartParams) (hP : IsChartParams P) : ContDiff ℝ ⊤ (logPhase P) := by
  unfold logPhase
  refine contDiff_const.mul (ContDiff.log (contDiff_const.add ((contDiff_norm_sq ℝ).div_const _)) ?_)
  intro y
  have := hP.rc_pos
  positivity

private theorem pin_radial {y : Space} (hy : y ≠ 0) (i : Fin 3) : ContDiffAt ℝ ⊤ (fun y => radialVec y i) y :=
  pin_ratio hy i

private theorem pin_polar {y : Space} (hy : y ≠ 0) (i : Fin 3) : ContDiffAt ℝ ⊤ (fun y => polarVecQ y i) y := by
  have hh := pin_height hy
  fin_cases i
  · simpa [polarVecQ, mul_div_assoc] using hh.mul (pin_ratio hy 0)
  · simpa [polarVecQ, mul_div_assoc] using hh.mul (pin_ratio hy 1)
  · simpa [polarVecQ, qOf] using (contDiffAt_const.sub (hh.pow 2)).neg

private theorem pin_azim {y : Space} (hy : y ≠ 0) (i : Fin 3) : ContDiffAt ℝ ⊤ (fun y => azimVecQ y i) y := by
  fin_cases i
  · simpa [azimVecQ, neg_div] using (pin_ratio hy 1).neg
  · simpa [azimVecQ] using pin_ratio hy 0
  · simpa [azimVecQ] using (contDiffAt_const : ContDiffAt ℝ ⊤ (fun _ : Space => (0 : ℝ)) y)

private def pinPlane (y : Space) : ℂ := ⟨y 0, y 1⟩

private theorem pinPlane_contDiff : ContDiff ℝ ⊤ pinPlane := by
  have e : pinPlane = fun y => ((y 0 : ℝ) : ℂ) + ((y 1 : ℝ) : ℂ) * Complex.I := by
    funext y
    apply Complex.ext <;> simp [pinPlane]
  rw [e]
  exact (Complex.ofRealCLM.contDiff.comp (pin_coord 0)).add
    ((Complex.ofRealCLM.contDiff.comp (pin_coord 1)).mul contDiff_const)

private theorem pin_exp_arg (w : ℂ) (hw : w ≠ 0) (k : ℤ) :
    Complex.exp (Complex.I * (((k : ℝ) * Complex.arg w : ℝ) : ℂ)) = (w * ((‖w‖⁻¹ : ℝ) : ℂ)) ^ k := by
  have h1 : Complex.I * (((k : ℝ) * Complex.arg w : ℝ) : ℂ) = (k : ℂ) * ((Complex.arg w : ℂ) * Complex.I) := by
    push_cast
    ring
  rw [h1, Complex.exp_int_mul]
  congr 1
  have h2 := Complex.norm_mul_exp_arg_mul_I w
  have h3 : (‖w‖ : ℂ) ≠ 0 := by exact_mod_cast (norm_ne_zero_iff.2 hw)
  rw [Complex.ofReal_inv, eq_mul_inv_iff_mul_eq₀ h3, mul_comm]
  exact h2

private theorem pin_zpow {f : Space → ℂ} {y : Space} (hf : ContDiffAt ℝ 2 f y) (hy : f y ≠ 0) (j : ℤ) :
    ContDiffAt ℝ 2 (fun z => f z ^ j) y := by
  cases j with
  | ofNat k => simpa using hf.pow k
  | negSucc k =>
    simp only [zpow_negSucc]
    exact (hf.pow (k + 1)).inv (pow_ne_zero _ hy)

private theorem pin_phase (P : ChartParams) (hP : IsChartParams P) (n : ℤ) (β : ℝ) {y : Space}
    (hw : pinPlane y ≠ 0) : ContDiffAt ℝ 2 (modePhase P n β) y := by
  have hpl : ContDiffAt ℝ 2 pinPlane y := pinPlane_contDiff.contDiffAt.of_le le_top
  have hnorm : ContDiffAt ℝ 2 (fun z => ‖pinPlane z‖) y := hpl.norm ℝ hw
  have hinv : ContDiffAt ℝ 2 (fun z => ‖pinPlane z‖⁻¹) y := hnorm.inv (norm_ne_zero_iff.2 hw)
  have hu : ContDiffAt ℝ 2 (fun z => pinPlane z * ((‖pinPlane z‖⁻¹ : ℝ) : ℂ)) y :=
    hpl.mul (Complex.ofRealCLM.contDiff.contDiffAt.comp y hinv)
  have hu0 : pinPlane y * ((‖pinPlane y‖⁻¹ : ℝ) : ℂ) ≠ 0 :=
    mul_ne_zero hw (Complex.ofReal_ne_zero.2 (inv_ne_zero (norm_ne_zero_iff.2 hw)))
  have hE : ContDiffAt ℝ 2 (fun z => Complex.exp (Complex.I * ((n * β * logPhase P z : ℝ) : ℂ))) y :=
    (Complex.contDiff_exp.contDiffAt.comp y (contDiffAt_const.mul (Complex.ofRealCLM.contDiff.contDiffAt.comp y
      (contDiffAt_const.mul ((pin_logPhase P hP).contDiffAt))))).of_le le_top
  have hall := (pin_zpow hu hu0 (n * P.m)).mul hE
  have hev : ∀ᶠ z in nhds y, pinPlane z ≠ 0 := pinPlane_contDiff.continuous.continuousAt.eventually_ne hw
  refine hall.congr_of_eventuallyEq ?_
  filter_upwards [hev] with z hz
  unfold modePhase
  rw [← pin_exp_arg _ hz, ← Complex.exp_add, ← mul_add]
  congr 2
  push_cast
  simp [angleOf, pinPlane]

private theorem pin_single (i : Fin 3) (a : ℝ) :
    EuclideanSpace.single i a = a • EuclideanSpace.single i (1 : ℝ) := by
  ext j
  by_cases h : j = i <;> simp [h]

private theorem tame_ofComponents {w : Fin 3 → Space → ℝ} {y : Space} (h : ∀ i, TameAt (w i) y) :
    TameAt (fun z => ofComponents (fun i => w i z)) y := by
  have e : (fun z => ofComponents (fun i => w i z)) = fun z =>
      ContinuousLinearMap.toSpanSingleton ℝ (EuclideanSpace.single (0 : Fin 3) (1 : ℝ)) (w 0 z) +
      ContinuousLinearMap.toSpanSingleton ℝ (EuclideanSpace.single (1 : Fin 3) (1 : ℝ)) (w 1 z) +
      ContinuousLinearMap.toSpanSingleton ℝ (EuclideanSpace.single (2 : Fin 3) (1 : ℝ)) (w 2 z) := by
    funext z
    simp only [ofComponents, ContinuousLinearMap.toSpanSingleton_apply]
    rw [pin_single 0 (w 0 z), pin_single 1 (w 1 z), pin_single 2 (w 2 z)]
  rw [e]
  exact tame_add (tame_add (tame_clm _ (h 0)) (tame_clm _ (h 1))) (tame_clm _ (h 2))

private theorem pin_tame_all {f : ℝ × ℝ → ℂ} (hf : ContDiff ℝ 2 f) (q : ℝ × ℝ) : TameAt f q :=
  tame_of_contDiffAt hf.contDiffAt

private theorem pin_partial_t {G : ℝ → ℝ → ℂ} (hG : ContDiff ℝ 3 (fun p : ℝ × ℝ => G p.1 p.2)) :
    ContDiff ℝ 2 (fun p : ℝ × ℝ => deriv (fun t => G t p.2) p.1) := by
  have e : (fun p : ℝ × ℝ => deriv (fun t => G t p.2) p.1) =
      fun p => fderiv ℝ (fun q : ℝ × ℝ => G q.1 q.2) p ((1 : ℝ), (0 : ℝ)) := by
    funext p
    have hd : DifferentiableAt ℝ (fun q : ℝ × ℝ => G q.1 q.2) (p.1, p.2) :=
      (hG.differentiable (by norm_num)) _
    have h1 : HasDerivAt (fun t : ℝ => (t, p.2)) ((1 : ℝ), (0 : ℝ)) p.1 :=
      (hasDerivAt_id p.1).prodMk (hasDerivAt_const p.1 p.2)
    exact (hd.hasFDerivAt.comp_hasDerivAt p.1 h1).deriv
  rw [e]
  exact (hG.fderiv_right (by norm_num)).clm_apply contDiff_const

private theorem pin_partial_x {G : ℝ → ℝ → ℂ} (hG : ContDiff ℝ 3 (fun p : ℝ × ℝ => G p.1 p.2)) :
    ContDiff ℝ 2 (fun p : ℝ × ℝ => deriv (fun x => G p.1 x) p.2) := by
  have e : (fun p : ℝ × ℝ => deriv (fun x => G p.1 x) p.2) =
      fun p => fderiv ℝ (fun q : ℝ × ℝ => G q.1 q.2) p ((0 : ℝ), (1 : ℝ)) := by
    funext p
    have hd : DifferentiableAt ℝ (fun q : ℝ × ℝ => G q.1 q.2) (p.1, p.2) :=
      (hG.differentiable (by norm_num)) _
    have h1 : HasDerivAt (fun x : ℝ => (p.1, x)) ((0 : ℝ), (1 : ℝ)) p.2 :=
      (hasDerivAt_const p.2 p.1).prodMk (hasDerivAt_id p.2)
    exact (hd.hasFDerivAt.comp_hasDerivAt p.2 h1).deriv
  rw [e]
  exact (hG.fderiv_right (by norm_num)).clm_apply contDiff_const

private theorem pin_tderiv_mul {G F : ℝ → ℝ → ℂ} (hG : ContDiff ℝ 3 (fun p : ℝ × ℝ => G p.1 p.2))
    (hF : Differentiable ℝ (fun p : ℝ × ℝ => F p.1 p.2)) (hF2 : ∀ q, TameAt (fun p : ℝ × ℝ => F p.1 p.2) q)
    (hFt : ∀ q, TameAt (fun p : ℝ × ℝ => deriv (fun t => F t p.2) p.1) q) (q : ℝ × ℝ) :
    TameAt (fun p : ℝ × ℝ => deriv (fun t => G t p.2 * F t p.2) p.1) q := by
  have e : (fun p : ℝ × ℝ => deriv (fun t => G t p.2 * F t p.2) p.1) =
      fun p => deriv (fun t => G t p.2) p.1 * F p.1 p.2 + G p.1 p.2 * deriv (fun t => F t p.2) p.1 := by
    funext p
    have h1 : DifferentiableAt ℝ (fun t : ℝ => (t, p.2)) p.1 :=
      differentiableAt_id.prodMk (differentiableAt_const _)
    have hdF : DifferentiableAt ℝ (fun t => F t p.2) p.1 := (hF _).comp p.1 h1
    have hdG : DifferentiableAt ℝ (fun t => G t p.2) p.1 := ((hG.differentiable (by norm_num)) _).comp p.1 h1
    exact deriv_mul hdG hdF
  rw [e]
  exact tame_add (tame_mul (pin_tame_all (pin_partial_t hG) q) (hF2 q))
    (tame_mul (pin_tame_all (hG.of_le (by norm_num)) q) (hFt q))

private theorem pin_xderiv_mul {G F : ℝ → ℝ → ℂ} (hG : ContDiff ℝ 3 (fun p : ℝ × ℝ => G p.1 p.2))
    (hF : Differentiable ℝ (fun p : ℝ × ℝ => F p.1 p.2)) (hF2 : ∀ q, TameAt (fun p : ℝ × ℝ => F p.1 p.2) q)
    (hFx : ∀ q, TameAt (fun p : ℝ × ℝ => deriv (fun x => F p.1 x) p.2) q) (q : ℝ × ℝ) :
    TameAt (fun p : ℝ × ℝ => deriv (fun x => G p.1 x * F p.1 x) p.2) q := by
  have e : (fun p : ℝ × ℝ => deriv (fun x => G p.1 x * F p.1 x) p.2) =
      fun p => deriv (fun x => G p.1 x) p.2 * F p.1 p.2 + G p.1 p.2 * deriv (fun x => F p.1 x) p.2 := by
    funext p
    have h1 : DifferentiableAt ℝ (fun x : ℝ => (p.1, x)) p.2 :=
      (differentiableAt_const _).prodMk differentiableAt_id
    have hdF : DifferentiableAt ℝ (fun x => F p.1 x) p.2 := (hF _).comp p.2 h1
    have hdG : DifferentiableAt ℝ (fun x => G p.1 x) p.2 := ((hG.differentiable (by norm_num)) _).comp p.2 h1
    exact deriv_mul hdG hdF
  rw [e]
  exact tame_add (tame_mul (pin_tame_all (pin_partial_x hG) q) (hF2 q))
    (tame_mul (pin_tame_all (hG.of_le (by norm_num)) q) (hFx q))

private theorem pin_coreRatio (P : ChartParams) (hP : IsChartParams P) : ContDiff ℝ 2 (coreRatioT P) := by
  unfold coreRatioT
  refine ContDiff.div (by fun_prop) (by fun_prop) ?_
  intro t
  have hL := hP.L0_pos
  have hr := hP.rc_pos
  by_cases ht : t = 0
  · subst ht
    simp
    exact hr.ne'
  · have h1 : 0 < P.L0 ^ 2 * t ^ 2 := by positivity
    have h2 : 0 ≤ P.rc ^ 2 * (1 - t) ^ 2 := by positivity
    linarith

private theorem pin_scaleA : ContDiff ℝ 2 (fun p : ℝ × ℝ => ((p.1 * (1 - p.1) : ℝ) : ℂ)) :=
  Complex.ofRealCLM.contDiff.comp (contDiff_fst.mul (contDiff_const.sub contDiff_fst))

private theorem pin_scaleB (P : ChartParams) (hP : IsChartParams P) (m : ℤ) (β : ℝ) :
    ContDiff ℝ 2 (fun p : ℝ × ℝ => Complex.I * (((m : ℝ) * β * coreRatioT P p.1 : ℝ) : ℂ) -
      ((2 * P.eps * p.1 : ℝ) : ℂ)) := by
  refine (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp ?_)).sub
    (Complex.ofRealCLM.contDiff.comp (contDiff_const.mul contDiff_fst))
  exact contDiff_const.mul ((pin_coreRatio P hP).comp contDiff_fst)

private theorem pin_weight (a e k : ℕ) :
    ContDiff ℝ 3 (fun p : ℝ × ℝ => weightPoly a e p.1 * ((1 - p.2 ^ 2 : ℝ) : ℂ) ^ k) := by
  unfold weightPoly
  have h1 : ContDiff ℝ 3 (fun p : ℝ × ℝ => p.1 ^ a * (1 - p.1) ^ e) := by fun_prop
  have h2 : ContDiff ℝ 3 (fun p : ℝ × ℝ => 1 - p.2 ^ 2) := by fun_prop
  exact (Complex.ofRealCLM.contDiff.comp h1).mul ((Complex.ofRealCLM.contDiff.comp h2).pow k)

private theorem pin_q : ContDiff ℝ 3 (fun p : ℝ × ℝ => ((1 - p.2 ^ 2 : ℝ) : ℂ)) :=
  Complex.ofRealCLM.contDiff.comp (by fun_prop : ContDiff ℝ 3 (fun p : ℝ × ℝ => 1 - p.2 ^ 2))

private theorem pin_p (a e : ℕ) : ContDiff ℝ 3 (fun p : ℝ × ℝ => weightPoly a e p.1) := by
  unfold weightPoly
  have h1 : ContDiff ℝ 3 (fun p : ℝ × ℝ => p.1 ^ a * (1 - p.1) ^ e) := by fun_prop
  exact Complex.ofRealCLM.contDiff.comp h1

private theorem pin_spline {S : Spline} {a b : ℕ} {odd : Bool} (hS : IsSplineClass a b odd S) (ha : 1 ≤ a)
    (hb : 1 ≤ b) (q : ℝ × ℝ) : TameAt (fun p : ℝ × ℝ => S.eval odd p.1 p.2) q :=
  tame_of_global ((spline_eval_contDiff S hS ha hb).differentiable (by norm_num))
    (spline_eval_localSlope S hS ha hb) q

private theorem pin_spline_t {S : Spline} {a b : ℕ} {odd : Bool} (hS : IsSplineClass a b odd S) (ha : 2 ≤ a)
    (hb : 1 ≤ b) (q : ℝ × ℝ) : TameAt (fun p : ℝ × ℝ => deriv (fun t => S.eval odd t p.2) p.1) q :=
  tame_of_global ((spline_tderiv_contDiff S hS ha hb).differentiable (by norm_num))
    (spline_tderiv_localSlope S hS ha hb) q

private theorem pin_spline_x {S : Spline} {a b : ℕ} {odd : Bool} (hS : IsSplineClass a b odd S) (ha : 1 ≤ a)
    (hb : 2 ≤ b) (q : ℝ × ℝ) : TameAt (fun p : ℝ × ℝ => deriv (fun x => S.eval odd p.1 x) p.2) q :=
  tame_of_global ((spline_xderiv_contDiff S hS ha hb).differentiable (by norm_num))
    (spline_xderiv_localSlope S hS ha hb) q

theorem reducedField_fderiv_localSlope_wave (P : ChartParams) (hP : IsChartParams P) {e : ℕ} {D : FieldData}
    (hD : IsFieldData P e D) (β : ℝ) (n : ℤ) (hn : n ∈ D.modes) (h0 : n ≠ 0) (k : Fin 3) :
    LocallyLipschitz (fderiv ℝ (fun p : ℝ × ℝ => reducedField P D n β p.1 p.2 k)) := by
  intro q
  refine tame_slope ?_
  have hR := hD.waveRadial n hn h0
  have hT := hD.wavePolar n hn h0
  have dR := (spline_eval_contDiff _ hR (by norm_num) (by norm_num)).differentiable (by norm_num)
  have dT := (spline_eval_contDiff _ hT (by norm_num) (by norm_num)).differentiable (by norm_num)
  have eR := pin_spline hR (by norm_num) (by norm_num)
  have eT := pin_spline hT (by norm_num) (by norm_num)
  have tR := pin_spline_t hR (by norm_num) (by norm_num)
  have xT := pin_spline_x hT (by norm_num) (by norm_num)
  have hW := pin_weight (D.lowOrder n) D.highOrder (D.axisOrder n)
  have hur : ∀ q, TameAt (fun p : ℝ × ℝ => weightPoly (D.lowOrder n) D.highOrder p.1 *
      ((1 - p.2 ^ 2 : ℝ) : ℂ) ^ D.axisOrder n * (D.amp n).radialAmp.eval false p.1 p.2) q := fun q =>
    tame_mul (pin_tame_all (hW.of_le (by norm_num)) q) (eR q)
  fin_cases k
  · refine tame_congr (hur q) (Filter.Eventually.of_forall fun p => ?_)
    simp [reducedField, h0]
  · refine tame_congr (tame_mul (pin_tame_all (hW.of_le (by norm_num)) q) (eT q))
      (Filter.Eventually.of_forall fun p => ?_)
    simp [reducedField, h0]
  · have hA := pin_tderiv_mul (G := fun t x => weightPoly (D.lowOrder n) D.highOrder t *
        ((1 - x ^ 2 : ℝ) : ℂ) ^ D.axisOrder n) (F := fun t x => (D.amp n).radialAmp.eval false t x)
        hW dR eR tR q
    have hB := pin_xderiv_mul (G := fun t x => ((1 - x ^ 2 : ℝ) : ℂ) * (weightPoly (D.lowOrder n) D.highOrder t *
        ((1 - x ^ 2 : ℝ) : ℂ) ^ D.axisOrder n)) (F := fun t x => (D.amp n).polarAmp.eval true t x)
        (pin_q.mul hW) dT eT xT q
    have hall := tame_mul (pin_tame_all (contDiff_const (c := Complex.I / ((n * P.m : ℤ) : ℂ))) q)
      (tame_sub (tame_add (tame_add (tame_mul (pin_tame_all pin_scaleA q) hA)
        (tame_mul (pin_tame_all (pin_scaleB P hP n β) q) (hur q)))
        (tame_mul (pin_tame_all (contDiff_const (c := (2 : ℂ))) q) (hur q))) hB)
    refine tame_congr hall (Filter.Eventually.of_forall fun p => ?_)
    simp [reducedField, h0, twistedScale, radialScale, heightDeriv, mul_assoc]

theorem reducedField_fderiv_localSlope_mean (P : ChartParams) (hP : IsChartParams P) {e : ℕ} {D : FieldData}
    (hD : IsFieldData P e D) (β : ℝ) (hn : (0 : ℤ) ∈ D.modes) (k : Fin 3) :
    LocallyLipschitz (fderiv ℝ (fun p : ℝ × ℝ => reducedField P D 0 β p.1 p.2 k)) := by
  intro q
  refine tame_slope ?_
  have hS := (hD.meanStream hn).1
  have hG := (hD.meanSwirl hn).1
  have dS := (spline_eval_contDiff _ hS (by norm_num) (by norm_num)).differentiable (by norm_num)
  have eS := pin_spline hS (by norm_num) (by norm_num)
  have eG := pin_spline hG (by norm_num) (by norm_num)
  have tS := pin_spline_t hS (by norm_num) (by norm_num)
  have xS := pin_spline_x hS (by norm_num) (by norm_num)
  have hp := pin_p 1 D.highOrder
  fin_cases k
  · have hB := pin_xderiv_mul (G := fun t x => ((1 - x ^ 2 : ℝ) : ℂ))
        (F := fun t x => (D.amp 0).streamAmp.eval true t x) pin_q dS eS xS q
    have hall := tame_neg (tame_mul (pin_tame_all (hp.of_le (by norm_num)) q) hB)
    refine tame_congr hall (Filter.Eventually.of_forall fun p => ?_)
    simp [reducedField, heightDeriv]
  · have hA := pin_tderiv_mul (G := fun t x => weightPoly 1 D.highOrder t)
        (F := fun t x => (D.amp 0).streamAmp.eval true t x) hp dS eS tS q
    have hpS := tame_mul (pin_tame_all (hp.of_le (by norm_num)) q) (eS q)
    have hall := tame_neg (tame_add (tame_add (tame_mul (pin_tame_all pin_scaleA q) hA)
      (tame_mul (pin_tame_all (pin_scaleB P hP 0 β) q) hpS))
      (tame_mul (pin_tame_all (contDiff_const (c := (2 : ℂ))) q) hpS))
    refine tame_congr hall (Filter.Eventually.of_forall fun p => ?_)
    simp [reducedField, twistedScale, radialScale]
  · refine tame_congr (tame_mul (pin_tame_all (hp.of_le (by norm_num)) q) (eG q))
      (Filter.Eventually.of_forall fun p => ?_)
    simp [reducedField]

private theorem pin_field_tame (P : ChartParams) (hP : IsChartParams P) (D : FieldData) (β : ℝ) (n : ℤ)
    (hred : ∀ k : Fin 3, Differentiable ℝ (fun p : ℝ × ℝ => reducedField P D n β p.1 p.2 k))
    (hsl : ∀ k : Fin 3, LocallyLipschitz (fderiv ℝ (fun p : ℝ × ℝ => reducedField P D n β p.1 p.2 k)))
    (y : Space) (hy : y ≠ 0) (hph : ContDiffAt ℝ 2 (modePhase P n β) y) :
    TameAt (modeFieldOf P D β n) y := by
  have hc : ContDiffAt ℝ 2 (fun z : Space => (chartT P z, heightRatio z)) y :=
    ((pin_chartT P hP hy).of_le le_top).prodMk ((pin_height hy).of_le le_top)
  have hR : ∀ k : Fin 3, TameAt (fun z => reducedField P D n β (chartT P z) (heightRatio z) k) y := fun k =>
    tame_comp (g := fun p : ℝ × ℝ => reducedField P D n β p.1 p.2 k)
      (Φ := fun z : Space => (chartT P z, heightRatio z)) (tame_of_global (hred k) (hsl k) _)
      (tame_of_contDiffAt hc)
  have hv : ∀ f : Space → ℝ, ContDiffAt ℝ ⊤ f y → TameAt (fun z => (f z : ℂ)) y := fun f hf =>
    tame_of_contDiffAt (Complex.ofRealCLM.contDiff.contDiffAt.comp y (hf.of_le le_top))
  have hX : ∀ i : Fin 3, TameAt (fun z => ((decayFactor P z : ℂ) * (modePhase P n β z *
      (reducedField P D n β (chartT P z) (heightRatio z) 0 * radialVec z i +
        reducedField P D n β (chartT P z) (heightRatio z) 1 * polarVecQ z i +
        reducedField P D n β (chartT P z) (heightRatio z) 2 * azimVecQ z i))).re) y := by
    intro i
    have := tame_clm Complex.reCLM (tame_mul (hv _ (pin_decay P hP hy)) (tame_mul (tame_of_contDiffAt hph)
      (tame_add (tame_add (tame_mul (hR 0) (hv _ (pin_radial hy i))) (tame_mul (hR 1) (hv _ (pin_polar hy i))))
        (tame_mul (hR 2) (hv _ (pin_azim hy i))))))
    simpa only [Complex.reCLM_apply] using this
  exact tame_ofComponents hX

private def planeMap (j : ℤ) (w : ℂ) : ℂ :=
  ((‖w‖ ^ 2 : ℝ) : ℂ) * Complex.exp (Complex.I * (((j : ℝ) * Complex.arg w : ℝ) : ℂ))

private theorem planeMap_diff (j : ℤ) : Differentiable ℝ (planeMap j) :=
  (planePhase_contDiff j).differentiable (by norm_num)

private theorem planeMap_scale (j : ℤ) {s : ℝ} (hs : 0 < s) :
    (fun w => planeMap j ((s : ℂ) * w)) = fun w => ((s ^ 2 : ℝ) : ℂ) * planeMap j w := by
  funext w
  unfold planeMap
  rw [Complex.arg_real_mul w hs, norm_mul, Complex.norm_real, Real.norm_of_nonneg hs.le]
  push_cast
  ring

private theorem planeMap_fderiv_scale (j : ℤ) {s : ℝ} (hs : 0 < s) (w : ℂ) :
    fderiv ℝ (planeMap j) ((s : ℂ) * w) = s • fderiv ℝ (planeMap j) w := by
  have hd := planeMap_diff j
  have hlin : HasFDerivAt (fun w : ℂ => (s : ℂ) * w) (s • ContinuousLinearMap.id ℝ ℂ) w := by
    have e : (fun w : ℂ => (s : ℂ) * w) = fun w => s • w := by
      funext x
      simp [Complex.real_smul]
    rw [e]
    exact (hasFDerivAt_id (𝕜 := ℝ) w).const_smul s
  have h1 : HasFDerivAt (fun w => planeMap j ((s : ℂ) * w))
      ((fderiv ℝ (planeMap j) ((s : ℂ) * w)).comp (s • ContinuousLinearMap.id ℝ ℂ)) w :=
    (hd _).hasFDerivAt.comp w hlin
  have h2 : HasFDerivAt (fun w => ((s ^ 2 : ℝ) : ℂ) * planeMap j w) ((s ^ 2) • fderiv ℝ (planeMap j) w) w := by
    have e : (fun w => ((s ^ 2 : ℝ) : ℂ) * planeMap j w) = fun w => (s ^ 2) • planeMap j w := by
      funext x
      simp [Complex.real_smul]
    rw [e]
    exact (hd w).hasFDerivAt.const_smul (s ^ 2)
  rw [planeMap_scale j hs] at h1
  have e := h1.unique h2
  have hc : (fderiv ℝ (planeMap j) ((s : ℂ) * w)).comp (s • ContinuousLinearMap.id ℝ ℂ) =
      s • fderiv ℝ (planeMap j) ((s : ℂ) * w) := by
    refine ContinuousLinearMap.ext fun x => ?_
    simp
  rw [hc] at e
  have hs0 : s ≠ 0 := hs.ne'
  calc fderiv ℝ (planeMap j) ((s : ℂ) * w) = s⁻¹ • (s • fderiv ℝ (planeMap j) ((s : ℂ) * w)) := by
        rw [smul_smul, inv_mul_cancel₀ hs0, one_smul]
    _ = s⁻¹ • (s ^ 2 • fderiv ℝ (planeMap j) w) := by rw [e]
    _ = s • fderiv ℝ (planeMap j) w := by
        rw [smul_smul]
        congr 1
        field_simp

private theorem planeMap_fderiv_zero (j : ℤ) : fderiv ℝ (planeMap j) 0 = 0 := by
  have h := planeMap_fderiv_scale j (s := 2) (by norm_num) 0
  rw [mul_zero] at h
  have h3 : (2 : ℝ) • fderiv ℝ (planeMap j) 0 - fderiv ℝ (planeMap j) 0 = 0 := by rw [← h, sub_self]
  rwa [two_smul, add_sub_cancel_right] at h3

private theorem plane_exp_arg (w : ℂ) (hw : w ≠ 0) (k : ℤ) :
    Complex.exp (Complex.I * (((k : ℝ) * Complex.arg w : ℝ) : ℂ)) = (w * ((‖w‖⁻¹ : ℝ) : ℂ)) ^ k := by
  have h1 : Complex.I * (((k : ℝ) * Complex.arg w : ℝ) : ℂ) = (k : ℂ) * ((Complex.arg w : ℂ) * Complex.I) := by
    push_cast
    ring
  rw [h1, Complex.exp_int_mul]
  congr 1
  have h2 := Complex.norm_mul_exp_arg_mul_I w
  have h3 : (‖w‖ : ℂ) ≠ 0 := by exact_mod_cast (norm_ne_zero_iff.2 hw)
  rw [Complex.ofReal_inv, eq_mul_inv_iff_mul_eq₀ h3, mul_comm]
  exact h2

private theorem plane_zpow {f : ℂ → ℂ} {y : ℂ} (hf : ContDiffAt ℝ 2 f y) (hy : f y ≠ 0) (j : ℤ) :
    ContDiffAt ℝ 2 (fun z => f z ^ j) y := by
  cases j with
  | ofNat k => simpa using hf.pow k
  | negSucc k =>
    simp only [zpow_negSucc]
    exact (hf.pow (k + 1)).inv (pow_ne_zero _ hy)

private theorem planeMap_smooth (j : ℤ) {w : ℂ} (hw : w ≠ 0) : ContDiffAt ℝ 2 (planeMap j) w := by
  have hid : ContDiffAt ℝ 2 (fun z : ℂ => z) w := contDiffAt_id
  have hnorm : ContDiffAt ℝ 2 (fun z : ℂ => ‖z‖) w := hid.norm ℝ hw
  have hinv : ContDiffAt ℝ 2 (fun z : ℂ => ‖z‖⁻¹) w := hnorm.inv (norm_ne_zero_iff.2 hw)
  have hu : ContDiffAt ℝ 2 (fun z : ℂ => z * ((‖z‖⁻¹ : ℝ) : ℂ)) w :=
    hid.mul (Complex.ofRealCLM.contDiff.contDiffAt.comp w hinv)
  have hu0 : w * ((‖w‖⁻¹ : ℝ) : ℂ) ≠ 0 :=
    mul_ne_zero hw (Complex.ofReal_ne_zero.2 (inv_ne_zero (norm_ne_zero_iff.2 hw)))
  have hsq : ContDiffAt ℝ 2 (fun z : ℂ => ((‖z‖ ^ 2 : ℝ) : ℂ)) w :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp w (hnorm.pow 2)
  have hall := hsq.mul (plane_zpow hu hu0 j)
  refine hall.congr_of_eventuallyEq ?_
  filter_upwards [eventually_ne_nhds hw] with z hz
  unfold planeMap
  rw [plane_exp_arg z hz j]

theorem planePhase_fderiv_localSlope (j : ℤ) :
    LocallyLipschitz (fderiv ℝ (fun w : ℂ => ((‖w‖ ^ 2 : ℝ) : ℂ) *
      Complex.exp (Complex.I * (((j : ℝ) * Complex.arg w : ℝ) : ℂ)))) := by
  show LocallyLipschitz (fderiv ℝ (planeMap j))
  set F := fderiv ℝ (planeMap j) with hF
  have hcont : Continuous F := (planePhase_contDiff j).continuous_fderiv (by norm_num)
  set S : Set ℂ := {w | 1 / 2 ≤ ‖w‖ ∧ ‖w‖ ≤ 1} with hS
  have hSc : IsCompact S := by
    refine (isCompact_closedBall (0 : ℂ) 1).of_isClosed_subset ?_ ?_
    · exact (isClosed_le continuous_const continuous_norm).inter (isClosed_le continuous_norm continuous_const)
    · intro w hw
      simpa using hw.2
  have hloc : LocallyLipschitzOn S F := by
    intro w hw
    have hw0 : w ≠ 0 := by
      intro h
      have h1 := hw.1
      rw [h, norm_zero] at h1
      norm_num at h1
    obtain ⟨K, t, ht, hK⟩ := ((planeMap_smooth j hw0).fderiv_right (m := 1) (by norm_num)).exists_lipschitzOnWith
    exact ⟨K, t, mem_nhdsWithin_of_mem_nhds ht, hK⟩
  obtain ⟨L, hL⟩ := hloc.exists_lipschitzOnWith_of_compact hSc
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : ℂ) 1).exists_bound_of_continuousOn hcont.continuousOn
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hM 0 (Metric.mem_closedBall_self zero_le_one))
  have key : ∀ z w : ℂ, ‖w‖ ≤ ‖z‖ → ‖F z - F w‖ ≤ (L + 4 * M) * ‖z - w‖ := by
    intro z w hzw
    by_cases hz : z = 0
    · have hw : w = 0 := by
        rw [hz, norm_zero] at hzw
        exact norm_le_zero_iff.1 hzw
      rw [hz, hw]
      simp
    set s := ‖z‖ with hs
    have hs0 : 0 < s := norm_pos_iff.2 hz
    set z' := ((s⁻¹ : ℝ) : ℂ) * z with hz'
    set w' := ((s⁻¹ : ℝ) : ℂ) * w with hw'
    have ez : z = (s : ℂ) * z' := by
      rw [hz', ← mul_assoc, ← Complex.ofReal_mul, mul_inv_cancel₀ hs0.ne', Complex.ofReal_one, one_mul]
    have ew : w = (s : ℂ) * w' := by
      rw [hw', ← mul_assoc, ← Complex.ofReal_mul, mul_inv_cancel₀ hs0.ne', Complex.ofReal_one, one_mul]
    have nz : ‖z'‖ = 1 := by
      rw [hz', norm_mul, Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.2 hs0.le), ← hs,
        inv_mul_cancel₀ hs0.ne']
    have nw : ‖w'‖ = ‖w‖ / s := by
      rw [hw', norm_mul, Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.2 hs0.le), inv_mul_eq_div]
    have nd : ‖z - w‖ = s * ‖z' - w'‖ := by
      rw [ez, ew, ← mul_sub, norm_mul, Complex.norm_real, Real.norm_of_nonneg hs0.le]
    have nw1 : ‖w'‖ ≤ 1 := by rw [nw, div_le_one hs0]; exact hzw
    have eF : F z - F w = s • (F z' - F w') := by
      rw [ez, ew, hF, planeMap_fderiv_scale j hs0, planeMap_fderiv_scale j hs0, smul_sub]
    rw [eF, norm_smul, Real.norm_of_nonneg hs0.le, nd]
    have hfin : ‖F z' - F w'‖ ≤ (L + 4 * M) * ‖z' - w'‖ := by
      by_cases hc : 1 / 2 ≤ ‖w'‖
      · have h1 := hL.dist_le_mul z' ⟨by rw [nz]; norm_num, le_of_eq nz⟩ w' ⟨hc, nw1⟩
        rw [dist_eq_norm, dist_eq_norm] at h1
        have h2 : 0 ≤ 4 * M * ‖z' - w'‖ := by positivity
        nlinarith
      · push Not at hc
        have a1 := hM z' (by rw [Metric.mem_closedBall, dist_zero_right, nz])
        have a2 := hM w' (by rw [Metric.mem_closedBall, dist_zero_right]; exact nw1)
        have a3 : 1 / 2 ≤ ‖z' - w'‖ := by
          have := norm_sub_norm_le z' w'
          rw [nz] at this
          linarith
        have a4 : ‖F z' - F w'‖ ≤ ‖F z'‖ + ‖F w'‖ := norm_sub_le _ _
        have a5 : 0 ≤ (L : ℝ) * ‖z' - w'‖ := by positivity
        nlinarith
    calc s * ‖F z' - F w'‖ ≤ s * ((L + 4 * M) * ‖z' - w'‖) := mul_le_mul_of_nonneg_left hfin hs0.le
      _ = (L + 4 * M) * (s * ‖z' - w'‖) := by ring
  have hglob : LipschitzWith ⟨L + 4 * M, by positivity⟩ F := by
    refine LipschitzWith.of_dist_le_mul fun z w => ?_
    rw [dist_eq_norm, dist_eq_norm]
    rcases le_total ‖w‖ ‖z‖ with h | h
    · exact key z w h
    · rw [norm_sub_rev (F z), norm_sub_rev z]
      exact key w z h
  exact hglob.locallyLipschitz

private theorem tame_contDiff {f : ℝ × ℝ → ℂ} (h : ∀ y, TameAt f y) :
    ContDiff ℝ 1 f ∧ LocallyLipschitz (fderiv ℝ f) := by
  have hl : LocallyLipschitz (fderiv ℝ f) := fun y => tame_slope (h y)
  refine ⟨contDiff_one_iff_fderiv.2 ⟨fun y => ?_, hl.continuous⟩, hl⟩
  obtain ⟨r, hr, f', K, -, h1, -⟩ := h y
  exact (h1 y (Metric.mem_ball_self hr)).differentiableAt

theorem reducedField_wave_axisFactor_slope (P : ChartParams) (hP : IsChartParams P) {e : ℕ} {D : FieldData}
    (hD : IsFieldData P e D) (β : ℝ) (n : ℤ) (hn : n ∈ D.modes) (h0 : n ≠ 0) :
    ∃ H : ℝ → ℝ → Fin 3 → ℂ, (∀ k : Fin 3, ContDiff ℝ 1 (fun p : ℝ × ℝ => H p.1 p.2 k) ∧
      LocallyLipschitz (fderiv ℝ (fun p : ℝ × ℝ => H p.1 p.2 k))) ∧
      ∀ t x k, reducedField P D n β t x k = ((1 - x ^ 2 : ℝ) : ℂ) * H t x k := by
  obtain ⟨k1, hk1⟩ : ∃ k1, D.axisOrder n = k1 + 1 :=
    ⟨D.axisOrder n - 1, by have := hD.axisOrder_ge n hn h0; omega⟩
  have hR := hD.waveRadial n hn h0
  have hT := hD.wavePolar n hn h0
  have cT := spline_eval_contDiff _ hT (by norm_num) (by norm_num)
  have dR := (spline_eval_contDiff _ hR (by norm_num) (by norm_num)).differentiable (by norm_num)
  have eR := pin_spline hR (by norm_num) (by norm_num)
  have eT := pin_spline hT (by norm_num) (by norm_num)
  have tR := pin_spline_t hR (by norm_num) (by norm_num)
  have xT := pin_spline_x hT (by norm_num) (by norm_num)
  set a := D.lowOrder n
  set ee := D.highOrder
  set R := (D.amp n).radialAmp
  set Θ := (D.amp n).polarAmp
  set q : ℝ → ℂ := fun x => ((1 - x ^ 2 : ℝ) : ℂ) with hq
  set A : ℝ → ℝ → ℂ := fun t x => weightPoly a ee t * q x ^ k1 * R.eval false t x with hA
  set B : ℝ → ℝ → ℂ := fun t x => weightPoly a ee t * q x ^ k1 * Θ.eval true t x with hB
  set C : ℝ → ℝ → ℂ := fun t x => (Complex.I / ((n * P.m : ℤ) : ℂ)) *
    (((t * (1 - t) : ℝ) : ℂ) * deriv (fun t' => A t' x) t +
      (Complex.I * ((n : ℝ) * β * coreRatioT P t : ℝ) - ((2 * P.eps * t : ℝ) : ℂ)) * A t x + 2 * A t x -
      (((D.axisOrder n + 1 : ℕ) : ℂ) * q x ^ k1 * ((-2 * x : ℝ) : ℂ) * (weightPoly a ee t * Θ.eval true t x) +
        q x ^ D.axisOrder n * (weightPoly a ee t * deriv (fun x' => Θ.eval true t x') x))) with hC
  have hW := pin_weight a ee k1
  have hAc : ∀ q0, TameAt (fun p : ℝ × ℝ => A p.1 p.2) q0 := fun q0 =>
    tame_mul (pin_tame_all (hW.of_le (by norm_num)) q0) (eR q0)
  have hTa : ∀ k : Fin 3, ∀ q0, TameAt (fun p : ℝ × ℝ => ![A p.1 p.2, B p.1 p.2, C p.1 p.2] k) q0 := by
    intro k q0
    fin_cases k
    · refine tame_congr (hAc q0) (Filter.Eventually.of_forall fun p => ?_)
      simp
    · refine tame_congr (tame_mul (pin_tame_all (hW.of_le (by norm_num)) q0) (eT q0))
        (Filter.Eventually.of_forall fun p => ?_)
      simp [hB, hq]
    · have hAt := pin_tderiv_mul (G := fun t x => weightPoly a ee t * ((1 - x ^ 2 : ℝ) : ℂ) ^ k1)
        (F := fun t x => R.eval false t x) hW dR eR tR q0
      have hqk : ContDiff ℝ 2 (fun p : ℝ × ℝ => ((1 - p.2 ^ 2 : ℝ) : ℂ) ^ k1 * ((-2 * p.2 : ℝ) : ℂ)) :=
        ((pin_q.of_le (by norm_num)).pow k1).mul
          (Complex.ofRealCLM.contDiff.comp (contDiff_const.mul contDiff_snd))
      have hqk0 : ContDiff ℝ 2 (fun p : ℝ × ℝ => ((1 - p.2 ^ 2 : ℝ) : ℂ) ^ D.axisOrder n) :=
        (pin_q.of_le (by norm_num)).pow _
      have hp : ContDiff ℝ 2 (fun p : ℝ × ℝ => weightPoly a ee p.1) := (pin_p a ee).of_le (by norm_num)
      have hall := tame_mul (pin_tame_all (contDiff_const (c := Complex.I / ((n * P.m : ℤ) : ℂ))) q0)
        (tame_sub (tame_add (tame_add (tame_mul (pin_tame_all pin_scaleA q0) hAt)
          (tame_mul (pin_tame_all (pin_scaleB P hP n β) q0) (hAc q0)))
          (tame_mul (pin_tame_all (contDiff_const (c := (2 : ℂ))) q0) (hAc q0)))
          (tame_add (tame_mul (tame_mul (pin_tame_all (contDiff_const (c := ((D.axisOrder n + 1 : ℕ) : ℂ))) q0)
            (pin_tame_all hqk q0)) (tame_mul (pin_tame_all hp q0) (eT q0)))
            (tame_mul (pin_tame_all hqk0 q0) (tame_mul (pin_tame_all hp q0) (xT q0)))))
      refine tame_congr hall (Filter.Eventually.of_forall fun p => ?_)
      simp [hC, hA, hq, mul_assoc]
  refine ⟨fun t x => ![A t x, B t x, C t x], fun k => tame_contDiff (hTa k), ?_⟩
  have hdT : ∀ t x, HasDerivAt (fun x' => Θ.eval true t x') (deriv (fun x' => Θ.eval true t x') x) x := by
    intro t x
    have h1 : DifferentiableAt ℝ (fun x' : ℝ => (t, x')) x :=
      (differentiableAt_const _).prodMk differentiableAt_id
    exact (((cT.differentiable (by norm_num)) _).comp x h1).hasDerivAt
  have hdq : ∀ x : ℝ, HasDerivAt q (((-2 * x : ℝ)) : ℂ) x := by
    intro x
    have := ((hasDerivAt_pow 2 x).const_sub 1).ofReal_comp
    convert this using 1
    push_cast
    ring
  intro t x k
  fin_cases k
  · simp only [reducedField, if_neg h0, hk1]
    simp [hA, hq, pow_succ]
    ring
  · simp only [reducedField, if_neg h0, hk1]
    simp [hB, hq, pow_succ]
    ring
  · show reducedField P D n β t x 2 = q x * C t x
    have hder1 : deriv (fun t' => weightPoly a ee t' * ((1 - x ^ 2 : ℝ) : ℂ) ^ D.axisOrder n * R.eval false t' x) t =
        q x * deriv (fun t' => A t' x) t := by
      have e1 : (fun t' => weightPoly a ee t' * ((1 - x ^ 2 : ℝ) : ℂ) ^ D.axisOrder n * R.eval false t' x) =
          fun t' => q x * A t' x := by
        funext t'
        simp only [hA, hq, hk1, pow_succ]
        ring
      rw [e1, deriv_const_mul_field]
    have hder2 : deriv (fun x' => ((1 - x' ^ 2 : ℝ) : ℂ) * (weightPoly a ee t * ((1 - x' ^ 2 : ℝ) : ℂ) ^ D.axisOrder n *
        Θ.eval true t x')) x =
        q x * (((D.axisOrder n + 1 : ℕ) : ℂ) * q x ^ k1 * ((-2 * x : ℝ) : ℂ) * (weightPoly a ee t * Θ.eval true t x) +
          q x ^ D.axisOrder n * (weightPoly a ee t * deriv (fun x' => Θ.eval true t x') x)) := by
      have e2 : (fun x' => ((1 - x' ^ 2 : ℝ) : ℂ) * (weightPoly a ee t * ((1 - x' ^ 2 : ℝ) : ℂ) ^ D.axisOrder n *
          Θ.eval true t x')) = fun x' => weightPoly a ee t * (q x' ^ (D.axisOrder n + 1) * Θ.eval true t x') := by
        funext x'
        simp only [hq, pow_succ]
        ring
      rw [e2]
      have hh := (((hdq x).pow (D.axisOrder n + 1)).mul (hdT t x)).const_mul (weightPoly a ee t)
      have hh' : HasDerivAt (fun x' => weightPoly a ee t * (q x' ^ (D.axisOrder n + 1) * Θ.eval true t x'))
          (weightPoly a ee t * (((D.axisOrder n + 1 : ℕ) : ℂ) * q x ^ (D.axisOrder n + 1 - 1) * ((-2 * x : ℝ) : ℂ) *
            Θ.eval true t x + q x ^ (D.axisOrder n + 1) * deriv (fun x' => Θ.eval true t x') x)) x := hh
      rw [hh'.deriv]
      simp only [hk1, Nat.add_sub_cancel]
      push_cast
      ring
    simp only [reducedField, if_neg h0, twistedScale, radialScale, heightDeriv]
    try simp only [Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
    rw [hder1, hder2]
    simp only [hC, hA, hq, hk1, pow_succ]
    ring

private theorem pin_one_sub_height (y : Space) (hy : y ≠ 0) :
    1 - heightRatio y ^ 2 = ‖pinPlane y‖ ^ 2 / ‖y‖ ^ 2 := by
  have hn : ‖y‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.2 hy)
  have e1 : ‖y‖ ^ 2 = y 0 ^ 2 + y 1 ^ 2 + y 2 ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_three]
    simp [sq_abs]
  have e2 : ‖pinPlane y‖ ^ 2 = y 0 ^ 2 + y 1 ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp [pinPlane]
    ring
  unfold heightRatio
  rw [div_pow, e2]
  field_simp
  linarith

private theorem pin_axis_tame (P : ChartParams) (hP : IsChartParams P) {e : ℕ} {D : FieldData}
    (hD : IsFieldData P e D) (β : ℝ) (n : ℤ) (hn : n ∈ D.modes) (h0 : n ≠ 0) (y : Space) (hy : y ≠ 0) :
    TameAt (modeFieldOf P D β n) y := by
  obtain ⟨H, hH, hRH⟩ := reducedField_wave_axisFactor_slope P hP hD β n hn h0
  have hv : ∀ f : Space → ℝ, ContDiffAt ℝ ⊤ f y → TameAt (fun z => (f z : ℂ)) y := fun f hf =>
    tame_of_contDiffAt (Complex.ofRealCLM.contDiff.contDiffAt.comp y (hf.of_le le_top))
  have hc : ContDiffAt ℝ 2 (fun z : Space => (chartT P z, heightRatio z)) y :=
    ((pin_chartT P hP hy).of_le le_top).prodMk ((pin_height hy).of_le le_top)
  have hA : TameAt (fun z => ((‖pinPlane z‖ ^ 2 : ℝ) : ℂ) *
      Complex.exp (Complex.I * ((((n * P.m : ℤ) : ℝ) * Complex.arg (pinPlane z) : ℝ) : ℂ))) y :=
    tame_comp (g := fun w : ℂ => ((‖w‖ ^ 2 : ℝ) : ℂ) *
      Complex.exp (Complex.I * ((((n * P.m : ℤ) : ℝ) * Complex.arg w : ℝ) : ℂ))) (Φ := pinPlane)
      (tame_of_global ((planePhase_contDiff (n * P.m)).differentiable (by norm_num))
        (planePhase_fderiv_localSlope (n * P.m)) _)
      (tame_of_contDiffAt (pinPlane_contDiff.contDiffAt.of_le le_top))
  have hB : TameAt (fun z : Space => (((‖z‖ ^ 2)⁻¹ : ℝ) : ℂ)) y :=
    hv _ (((contDiff_norm_sq ℝ).contDiffAt).inv (pow_ne_zero 2 (norm_ne_zero_iff.2 hy)))
  have hC : TameAt (fun z => Complex.exp (Complex.I * ((n * β * logPhase P z : ℝ) : ℂ))) y :=
    tame_of_contDiffAt ((Complex.contDiff_exp.contDiffAt.comp y (contDiffAt_const.mul
      (Complex.ofRealCLM.contDiff.contDiffAt.comp y
        (contDiffAt_const.mul ((pin_logPhase P hP).contDiffAt))))).of_le le_top)
  have hPR : ∀ k : Fin 3, TameAt (fun z => modePhase P n β z *
      reducedField P D n β (chartT P z) (heightRatio z) k) y := by
    intro k
    have hD' : TameAt (fun z => H (chartT P z) (heightRatio z) k) y :=
      tame_comp (g := fun p : ℝ × ℝ => H p.1 p.2 k) (Φ := fun z : Space => (chartT P z, heightRatio z))
        (tame_of_global ((hH k).1.differentiable (by norm_num)) (hH k).2 _) (tame_of_contDiffAt hc)
    refine tame_congr (tame_mul (tame_mul (tame_mul hA hB) hC) hD') ?_
    have hev : ∀ᶠ z in nhds y, z ≠ 0 := eventually_ne_nhds hy
    filter_upwards [hev] with z hz
    rw [hRH, pin_one_sub_height z hz]
    unfold modePhase
    have ea : Complex.exp (Complex.I * ((((n * P.m : ℤ) : ℝ) * angleOf z + n * β * logPhase P z : ℝ) : ℂ)) =
        Complex.exp (Complex.I * ((((n * P.m : ℤ) : ℝ) * Complex.arg (pinPlane z) : ℝ) : ℂ)) *
          Complex.exp (Complex.I * ((n * β * logPhase P z : ℝ) : ℂ)) := by
      rw [← Complex.exp_add, ← mul_add]
      congr 2
      push_cast
      simp [angleOf, pinPlane]
    rw [ea]
    push_cast
    ring
  have hX : ∀ i : Fin 3, TameAt (fun z => ((decayFactor P z : ℂ) * (modePhase P n β z *
      (reducedField P D n β (chartT P z) (heightRatio z) 0 * radialVec z i +
        reducedField P D n β (chartT P z) (heightRatio z) 1 * polarVecQ z i +
        reducedField P D n β (chartT P z) (heightRatio z) 2 * azimVecQ z i))).re) y := by
    intro i
    have hd := hv _ (pin_decay P hP hy)
    have h := tame_clm Complex.reCLM (tame_add (tame_add
      (tame_mul (tame_mul hd (hPR 0)) (hv _ (pin_radial hy i)))
      (tame_mul (tame_mul hd (hPR 1)) (hv _ (pin_polar hy i))))
      (tame_mul (tame_mul hd (hPR 2)) (hv _ (pin_azim hy i))))
    refine tame_congr h (Filter.Eventually.of_forall fun z => ?_)
    simp only [Complex.reCLM_apply]
    congr 1
    ring
  exact tame_ofComponents hX

theorem modeFieldOf_fderiv_localSlope_mean (P : ChartParams) (hP : IsChartParams P) {e : ℕ} {D : FieldData}
    (hD : IsFieldData P e D) (β : ℝ) (hn : (0 : ℤ) ∈ D.modes) :
    LocallyLipschitz (fderiv ℝ (modeFieldOf P D β 0)) := by
  intro y
  by_cases hy : y = 0
  · subst hy
    exact modeFieldOf_fderiv_slopeNearOrigin_mean P hP hD β hn
  · have hph : modePhase P 0 β = fun _ => 1 := by
      funext z
      simp [modePhase]
    refine tame_slope (pin_field_tame P hP D β 0
      (fun k => (reducedField_mean_contDiff P hP hD β hn k).differentiable (by norm_num))
      (fun k => reducedField_fderiv_localSlope_mean P hP hD β hn k) y hy ?_)
    rw [hph]
    exact contDiffAt_const

theorem modeFieldOf_fderiv_localSlope_wave (P : ChartParams) (hP : IsChartParams P) {e : ℕ} {D : FieldData}
    (hD : IsFieldData P e D) (β : ℝ) (n : ℤ) (hn : n ∈ D.modes) (h0 : n ≠ 0) :
    LocallyLipschitz (fderiv ℝ (modeFieldOf P D β n)) := by
  intro y
  by_cases hy : y = 0
  · subst hy
    exact modeFieldOf_fderiv_slopeNearOrigin_wave P hP hD β n hn h0
  by_cases hax : y 0 = 0 ∧ y 1 = 0
  · exact tame_slope (pin_axis_tame P hP hD β n hn h0 y hy)
  have hw : pinPlane y ≠ 0 := by
    intro h
    apply hax
    exact ⟨congrArg Complex.re h, congrArg Complex.im h⟩
  exact tame_slope (pin_field_tame P hP D β n
    (fun k => (reducedField_wave_contDiff P hP hD β n hn h0 k).differentiable (by norm_num))
    (fun k => reducedField_fderiv_localSlope_wave P hP hD β n hn h0 k) y hy (pin_phase P hP n β hw))

theorem modeFieldOf_fderiv_slopeOn_mean (P : ChartParams) (hP : IsChartParams P) {e : ℕ} {D : FieldData}
    (hD : IsFieldData P e D) (β : ℝ) (hn : (0 : ℤ) ∈ D.modes) (R : ℝ) :
    ∃ C : NNReal, LipschitzOnWith C (fderiv ℝ (modeFieldOf P D β 0)) (Metric.closedBall 0 R) :=
  (modeFieldOf_fderiv_localSlope_mean P hP hD β hn).locallyLipschitzOn.exists_lipschitzOnWith_of_compact
    (isCompact_closedBall 0 R)

theorem modeFieldOf_fderiv_slopeOn_wave (P : ChartParams) (hP : IsChartParams P) {e : ℕ} {D : FieldData}
    (hD : IsFieldData P e D) (β : ℝ) (n : ℤ) (hn : n ∈ D.modes) (h0 : n ≠ 0) (R : ℝ) :
    ∃ C : NNReal, LipschitzOnWith C (fderiv ℝ (modeFieldOf P D β n)) (Metric.closedBall 0 R) :=
  (modeFieldOf_fderiv_localSlope_wave P hP hD β n hn h0).locallyLipschitzOn.exists_lipschitzOnWith_of_compact
    (isCompact_closedBall 0 R)

private theorem slopeOn_finsetSum {E : Type*} [NormedAddCommGroup E] {s : Set Space} (u : Finset ℤ)
    (g : ℤ → Space → E) (hg : ∀ n ∈ u, ∃ C : NNReal, LipschitzOnWith C (g n) s) :
    ∃ C : NNReal, LipschitzOnWith C (fun y => ∑ n ∈ u, g n y) s := by
  classical
  induction u using Finset.induction_on with
  | empty => exact ⟨0, LipschitzOnWith.of_dist_le_mul fun x _ y _ => by simp⟩
  | insert a u ha ih =>
    obtain ⟨C1, h1⟩ := hg a (Finset.mem_insert_self a u)
    obtain ⟨C2, h2⟩ := ih (fun n hn => hg n (Finset.mem_insert_of_mem hn))
    refine ⟨C1 + C2, LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_⟩
    simp only [Finset.sum_insert ha]
    rw [dist_eq_norm]
    have e1 : (g a x + ∑ n ∈ u, g n x) - (g a y + ∑ n ∈ u, g n y) =
        (g a x - g a y) + ((∑ n ∈ u, g n x) - ∑ n ∈ u, g n y) := by abel
    rw [e1, NNReal.coe_add, add_mul]
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [← dist_eq_norm]; exact h1.dist_le_mul x hx y hy
    · rw [← dist_eq_norm]; exact h2.dist_le_mul x hx y hy

theorem compactField_fderiv_slopeOn (P : ChartParams) (hP : IsChartParams P) {e : ℕ} {tb : ℝ} (D : FieldData)
    (hD : IsCompactFieldData P e tb D) (hpos : 0 < tb) (β : ℝ) (R : ℝ) :
    ∃ C : NNReal, LipschitzOnWith C (fderiv ℝ (fieldOf P D β)) (Metric.closedBall 0 R) := by
  have hdiff : ∀ n ∈ D.modes, ∀ y, DifferentiableAt ℝ (modeFieldOf P D β n) y := by
    intro n hn y
    by_cases h0 : n = 0
    · subst h0
      exact (modeFieldOf_contDiff_mean P hP hD hpos β hn).differentiable (by norm_num) y
    · exact (modeFieldOf_contDiff_wave P hP hD hpos β n hn h0).differentiable (by norm_num) y
  have he : fderiv ℝ (fieldOf P D β) = fun y => ∑ n ∈ D.modes, fderiv ℝ (modeFieldOf P D β n) y := by
    funext y
    rw [fieldOf_eq_sum_modes]
    exact fderiv_fun_sum (fun n hn => hdiff n hn y)
  rw [he]
  refine slopeOn_finsetSum D.modes (fun n y => fderiv ℝ (modeFieldOf P D β n) y) (fun n hn => ?_)
  by_cases h0 : n = 0
  · subst h0
    exact modeFieldOf_fderiv_slopeOn_mean P hP hD.field β hn R
  · exact modeFieldOf_fderiv_slopeOn_wave P hP hD.field β n hn h0 R

end GivenFields

end CellCert

end Breakdown
