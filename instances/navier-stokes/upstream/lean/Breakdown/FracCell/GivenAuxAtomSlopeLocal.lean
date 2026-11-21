import Breakdown.FracCell.GivenAuxDefs
import Breakdown.FracCell.GivenAuxAtomAxis
import Breakdown.FracCell.GivenAuxPinSmoothLocal

open scoped ContDiff ENNReal Topology
open MeasureTheory

noncomputable section

namespace Breakdown

namespace CellCert

namespace GivenFields

open SteadyCert

namespace AtomSlopeLocalInternal

section Tame

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

def TameAt (f : E → F) (y : E) : Prop :=
  ∃ r > 0, ∃ f' : E → (E →L[ℝ] F), ∃ K : ℝ, 0 ≤ K ∧ (∀ z ∈ Metric.ball y r, HasFDerivAt f (f' z) z) ∧
    ∀ z ∈ Metric.ball y r, ∀ w ∈ Metric.ball y r, ‖f' z - f' w‖ ≤ K * ‖z - w‖

theorem tame_bounds {f : E → F} {y : E} {r : ℝ} {f' : E → (E →L[ℝ] F)} {K : ℝ} (hr : 0 < r)
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
    exact (convex_ball y r).norm_image_sub_le_of_norm_hasFDerivWithin_le
      (fun x hx => (hd x hx).hasFDerivWithinAt) hb hw hz
  refine ⟨‖f' y‖ + K * r, hM0, hb, hl, fun z hz => ?_⟩
  have h1 := hl z hz y hy
  have h2 : ‖z - y‖ < r := by rw [Metric.mem_ball, dist_eq_norm] at hz; exact hz
  have h3 : ‖f z‖ ≤ ‖f y‖ + ‖f z - f y‖ := by
    have := norm_add_le (f y) (f z - f y)
    simpa using this
  nlinarith [norm_nonneg (z - y)]

theorem tame_of_contDiffAt {f : E → F} {y : E} (hf : ContDiffAt ℝ 2 f y) : TameAt f y := by
  have h1 : ContDiffAt ℝ 1 (fderiv ℝ f) y := hf.fderiv_right (by norm_num)
  obtain ⟨K, t, ht, hK⟩ := h1.exists_lipschitzOnWith
  have hev : ∀ᶠ z in nhds y, ContDiffAt ℝ 2 f z := hf.eventually (by simp)
  obtain ⟨r, hr, hsub⟩ := Metric.mem_nhds_iff.1 (Filter.inter_mem ht hev)
  refine ⟨r, hr, fderiv ℝ f, K, K.2, fun z hz =>
    ((show ContDiffAt ℝ 2 f z from (hsub hz).2).differentiableAt (by norm_num)).hasFDerivAt, fun z hz w hw => ?_⟩
  have := hK.dist_le_mul z (hsub hz).1 w (hsub hw).1
  rwa [dist_eq_norm, dist_eq_norm] at this

theorem tame_of_global {f : E → F} (hd : Differentiable ℝ f) (hl : LocallyLipschitz (fderiv ℝ f))
    (y : E) : TameAt f y := by
  obtain ⟨K, t, ht, hK⟩ := hl y
  obtain ⟨r, hr, hsub⟩ := Metric.mem_nhds_iff.1 ht
  refine ⟨r, hr, fderiv ℝ f, K, K.2, fun z _ => (hd z).hasFDerivAt, fun z hz w hw => ?_⟩
  have := hK.dist_le_mul z (hsub hz) w (hsub hw)
  rwa [dist_eq_norm, dist_eq_norm] at this

theorem tame_slope {f : E → F} {y : E} (h : TameAt f y) :
    ∃ K : NNReal, ∃ U ∈ nhds y, LipschitzOnWith K (fderiv ℝ f) U := by
  obtain ⟨r, hr, f', K, hK0, h1, h2⟩ := h
  refine ⟨⟨K, hK0⟩, Metric.ball y r, Metric.ball_mem_nhds y hr, LipschitzOnWith.of_dist_le_mul fun z hz w hw => ?_⟩
  rw [(h1 z hz).fderiv, (h1 w hw).fderiv, dist_eq_norm, dist_eq_norm]
  exact h2 z hz w hw

theorem tame_congr {f g : E → F} {y : E} (hg : TameAt g y) (h : f =ᶠ[nhds y] g) : TameAt f y := by
  obtain ⟨r, hr, g', K, hK0, h1, h2⟩ := hg
  obtain ⟨s, hs, hsub⟩ := Metric.mem_nhds_iff.1 h
  have sr : Metric.ball y (min r s) ⊆ Metric.ball y r := Metric.ball_subset_ball (min_le_left _ _)
  refine ⟨min r s, lt_min hr hs, g', K, hK0, fun z hz => ?_, fun z hz w hw => h2 z (sr hz) w (sr hw)⟩
  have hz' : z ∈ Metric.ball y s := Metric.ball_subset_ball (min_le_right _ _) hz
  have hev : f =ᶠ[nhds z] g :=
    Filter.mem_of_superset (Metric.isOpen_ball.mem_nhds hz') (fun x hx => hsub hx)
  exact (h1 z (sr hz)).congr_of_eventuallyEq hev

theorem tame_comp {Φ : E → F} {g : F → G} {y : E} (hg : TameAt g (Φ y)) (hΦ : TameAt Φ y) :
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

theorem tame_mul {c d : E → ℂ} {y : E} (hc : TameAt c y) (hd : TameAt d y) :
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

end Tame

theorem norm2 {y : Space} (hy : y ≠ 0) : ContDiffAt ℝ 2 (fun z : Space => ‖z‖) y :=
  contDiffAt_norm ℝ hy

theorem coord2 (i : Fin 3) (y : Space) : ContDiffAt ℝ 2 (fun z : Space => z i) y :=
  (EuclideanSpace.proj i : Space →L[ℝ] ℝ).contDiff.contDiffAt

theorem height2 {y : Space} (hy : y ≠ 0) : ContDiffAt ℝ 2 heightRatio y :=
  (coord2 2 y).div (norm2 hy) (norm_ne_zero_iff.2 hy)

theorem chartT2 (P : ChartParams) (hP : IsChartParams P) {y : Space} (hy : y ≠ 0) :
    ContDiffAt ℝ 2 (chartT P) y := by
  have hne : ‖y‖ + P.L0 ≠ 0 := by have := hP.L0_pos; positivity
  exact (norm2 hy).div ((norm2 hy).add contDiffAt_const) hne

theorem decay2 (P : ChartParams) (hP : IsChartParams P) {y : Space} (hy : y ≠ 0) :
    ContDiffAt ℝ 2 (decayFactor P) y := by
  have hs : chartS P y ≠ 0 := by
    unfold chartS chartT
    have hL := hP.L0_pos
    have hn : 0 ≤ ‖y‖ := norm_nonneg y
    have hd : 0 < ‖y‖ + P.L0 := by positivity
    rw [sub_ne_zero]
    intro h
    rw [eq_comm, div_eq_one_iff_eq hd.ne'] at h
    linarith
  exact (contDiffAt_const.sub (chartT2 P hP hy)).rpow_const_of_ne hs

theorem logPhase2 (P : ChartParams) (hP : IsChartParams P) : ContDiff ℝ 2 (logPhase P) := by
  unfold logPhase
  refine contDiff_const.mul (ContDiff.log (contDiff_const.add ((contDiff_norm_sq ℝ).div_const _)) ?_)
  intro z
  have := hP.rc_pos
  positivity

theorem ofReal2 {f : Space → ℝ} {y : Space} (hf : ContDiffAt ℝ 2 f y) :
    ContDiffAt ℝ 2 (fun z => (f z : ℂ)) y :=
  Complex.ofRealCLM.contDiff.contDiffAt.comp y hf

theorem plane2 : ContDiff ℝ 2 (fun y : Space => (⟨y 0, y 1⟩ : ℂ)) :=
  AtomAxisInternal.planeW_contDiff.of_le le_top

theorem zpow2 {g : Space → ℂ} {y : Space} (hg : ContDiffAt ℝ 2 g y) (hy : g y ≠ 0) (k : ℤ) :
    ContDiffAt ℝ 2 (fun z => g z ^ k) y := by
  obtain ⟨m, rfl | rfl⟩ := Int.eq_nat_or_neg k
  · simpa using hg.pow m
  · simp only [zpow_neg, zpow_natCast]
    exact (hg.pow m).inv (pow_ne_zero _ hy)

theorem exp_arg_zpow (w : ℂ) (hw : w ≠ 0) (k : ℤ) :
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

theorem tame_spline {S : Spline} {odd : Bool} (hS : IsSplineClass 1 1 odd S) (q : ℝ × ℝ) :
    TameAt (fun p : ℝ × ℝ => S.eval odd p.1 p.2) q :=
  tame_of_global ((spline_eval_contDiff S hS le_rfl le_rfl).differentiable (by simp))
    (spline_eval_localSlope S hS le_rfl le_rfl) q

theorem tame_chartSpline (P : ChartParams) (hP : IsChartParams P) {S : Spline} {odd : Bool}
    (hS : IsSplineClass 1 1 odd S) (c : ℝ) {y : Space} (hy : y ≠ 0) :
    TameAt (fun z => S.eval odd (chartT P z) (c * heightRatio z)) y :=
  tame_comp (g := fun p : ℝ × ℝ => S.eval odd p.1 p.2) (Φ := fun z => (chartT P z, c * heightRatio z))
    (tame_spline hS _) (tame_of_contDiffAt ((chartT2 P hP hy).prodMk (contDiffAt_const.mul (height2 hy))))

theorem tame_chartSpline_one (P : ChartParams) (hP : IsChartParams P) {S : Spline} {odd : Bool}
    (hS : IsSplineClass 1 1 odd S) {y : Space} (hy : y ≠ 0) :
    TameAt (fun z => S.eval odd (chartT P z) (heightRatio z)) y :=
  tame_congr (tame_chartSpline P hP hS 1 hy) (Filter.Eventually.of_forall fun z => by simp)

theorem tame_offAxis (P : ChartParams) (hP : IsChartParams P) (j a : ℕ) (M : ℤ) (β : ℝ) (S : Spline)
    (hS : IsAtomSpline (decide (a = 0)) S j) {y : Space} (hw : (⟨y 0, y 1⟩ : ℂ) ≠ 0) :
    TameAt (fun y => ((decayFactor P y : ℝ) : ℂ) * atomTerm P j a M β S y) y := by
  have hy : y ≠ 0 := fun h => hw (by rw [h]; exact Complex.ext (by simp) (by simp))
  have hq : qOf y ≠ 0 := by
    have e1 : ‖y‖ ^ 2 = y 0 ^ 2 + y 1 ^ 2 + y 2 ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_three]
      simp [sq_abs]
    have hp : 0 < y 0 ^ 2 + y 1 ^ 2 := by
      by_contra h
      rw [not_lt] at h
      have h0 : y 0 = 0 := by nlinarith [sq_nonneg (y 0), sq_nonneg (y 1)]
      have h1 : y 1 = 0 := by nlinarith [sq_nonneg (y 0), sq_nonneg (y 1)]
      exact hw (Complex.ext (by simp [h0]) (by simp [h1]))
    unfold qOf heightRatio
    rw [div_pow, e1]
    have hpos : 0 < y 0 ^ 2 + y 1 ^ 2 + y 2 ^ 2 := by positivity
    rw [sub_ne_zero]
    intro h
    rw [eq_comm, div_eq_one_iff_eq hpos.ne'] at h
    linarith
  have hQ : ContDiffAt ℝ 2 (fun y => ((Real.sqrt (qOf y) ^ a : ℝ) : ℂ)) y :=
    ofReal2 (((contDiffAt_const.sub ((height2 hy).pow 2)).sqrt hq).pow a)
  have hE : ContDiffAt ℝ 2
      (fun y => Complex.exp (Complex.I * (((j : ℝ) * β * logPhase P y + (M : ℝ) * angleOf y : ℝ) : ℂ))) y := by
    have hw' : ∀ᶠ z in 𝓝 y, (⟨z 0, z 1⟩ : ℂ) ≠ 0 := plane2.continuous.continuousAt.eventually_ne hw
    have heq : (fun z : Space => Complex.exp (Complex.I * (((j : ℝ) * β * logPhase P z : ℝ) : ℂ)) *
        ((⟨z 0, z 1⟩ : ℂ) * ((‖(⟨z 0, z 1⟩ : ℂ)‖⁻¹ : ℝ) : ℂ)) ^ M) =ᶠ[𝓝 y]
        fun z => Complex.exp (Complex.I * (((j : ℝ) * β * logPhase P z + (M : ℝ) * angleOf z : ℝ) : ℂ)) := by
      filter_upwards [hw'] with z hz
      rw [← exp_arg_zpow _ hz M, ← Complex.exp_add, ← mul_add]
      congr 2
      push_cast
      simp [angleOf]
    refine ContDiffAt.congr_of_eventuallyEq ?_ heq.symm
    have h1 : ContDiffAt ℝ 2 (fun z : Space => Complex.exp (Complex.I * (((j : ℝ) * β * logPhase P z : ℝ) : ℂ))) y :=
      Complex.contDiff_exp.contDiffAt.comp y (contDiffAt_const.mul
        (ofReal2 (contDiffAt_const.mul (logPhase2 P hP).contDiffAt)))
    have hu : ContDiffAt ℝ 2 (fun z : Space => (⟨z 0, z 1⟩ : ℂ) * ((‖(⟨z 0, z 1⟩ : ℂ)‖⁻¹ : ℝ) : ℂ)) y :=
      plane2.contDiffAt.mul (ofReal2
        (((contDiffAt_norm ℝ hw).comp y plane2.contDiffAt).inv (norm_ne_zero_iff.2 hw)))
    have hu0 : (⟨y 0, y 1⟩ : ℂ) * ((‖(⟨y 0, y 1⟩ : ℂ)‖⁻¹ : ℝ) : ℂ) ≠ 0 :=
      mul_ne_zero hw (by exact_mod_cast (inv_ne_zero (norm_ne_zero_iff.2 hw)))
    exact h1.mul (zpow2 hu hu0 M)
  have hV := tame_chartSpline_one P hP hS.spline hy
  have hD : ContDiffAt ℝ 2 (fun y => ((decayFactor P y : ℝ) : ℂ)) y := ofReal2 (decay2 P hP hy)
  exact tame_mul (tame_of_contDiffAt hD) (tame_mul (tame_of_contDiffAt (hE.mul hQ)) hV)

theorem sqrt_q_eq {y : Space} (hy : y ≠ 0) : Real.sqrt (qOf y) = ‖(⟨y 0, y 1⟩ : ℂ)‖ / ‖y‖ := by
  have hn : 0 < ‖y‖ := norm_pos_iff.2 hy
  have e1 : ‖y‖ ^ 2 = y 0 ^ 2 + y 1 ^ 2 + y 2 ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_three]
    simp [sq_abs]
  have e2 : ‖(⟨y 0, y 1⟩ : ℂ)‖ ^ 2 = y 0 ^ 2 + y 1 ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    show y 0 * y 0 + y 1 * y 1 = _
    ring
  have hq : qOf y = (‖(⟨y 0, y 1⟩ : ℂ)‖ / ‖y‖) ^ 2 := by
    unfold qOf heightRatio
    rw [div_pow, div_pow, e2, eq_div_iff (by positivity), sub_mul, one_mul, div_mul_cancel₀ _ (by positivity)]
    linarith
  rw [hq, Real.sqrt_sq (by positivity)]

theorem phase_plus (w : ℂ) :
    Complex.exp (Complex.I * ((((1 : ℤ) : ℝ) * Complex.arg w : ℝ) : ℂ)) * (‖w‖ : ℂ) = w := by
  have e : Complex.I * ((((1 : ℤ) : ℝ) * Complex.arg w : ℝ) : ℂ) = (Complex.arg w : ℂ) * Complex.I := by
    push_cast
    ring
  rw [e, mul_comm]
  exact Complex.norm_mul_exp_arg_mul_I w

theorem phase_minus (w : ℂ) :
    Complex.exp (Complex.I * ((((-1 : ℤ) : ℝ) * Complex.arg w : ℝ) : ℂ)) * (‖w‖ : ℂ) = (starRingEnd ℂ) w := by
  have e : Complex.I * ((((-1 : ℤ) : ℝ) * Complex.arg w : ℝ) : ℂ) =
      (starRingEnd ℂ) ((Complex.arg w : ℂ) * Complex.I) := by
    rw [map_mul, Complex.conj_ofReal, Complex.conj_I]
    push_cast
    ring
  rw [e, Complex.exp_conj, ← Complex.conj_ofReal ‖w‖, ← map_mul, mul_comm, Complex.norm_mul_exp_arg_mul_I]

theorem tame_harmonicZero (P : ChartParams) (hP : IsChartParams P) (a : ℕ) (M : ℤ) (β : ℝ) (S : Spline)
    (ha : a ≤ 1) (hS : IsAtomSpline (decide (a = 0)) S 0) (hM : M.natAbs = a) {y : Space} (hy : y ≠ 0) :
    TameAt (fun y => ((decayFactor P y : ℝ) : ℂ) * atomTerm P 0 a M β S y) y := by
  have hne : ‖y‖ ≠ 0 := norm_ne_zero_iff.2 hy
  have hV := tame_chartSpline_one P hP hS.spline hy
  have hDc : TameAt (fun y => ((decayFactor P y : ℝ) : ℂ)) y := tame_of_contDiffAt (ofReal2 (decay2 P hP hy))
  have hinv : ContDiffAt ℝ 2 (fun y : Space => ((‖y‖⁻¹ : ℝ) : ℂ)) y := ofReal2 ((norm2 hy).inv hne)
  have hev : ∀ᶠ z in 𝓝 y, z ≠ 0 := eventually_ne_nhds hy
  interval_cases a
  · have hM0 : M = 0 := Int.natAbs_eq_zero.1 hM
    subst hM0
    refine tame_congr (tame_mul hDc hV) (Filter.Eventually.of_forall fun z => ?_)
    simp [atomTerm]
  · have hM' := Int.natAbs_eq M
    rw [hM] at hM'
    rcases hM' with h1 | h1
    · subst h1
      have e : (fun z => ((decayFactor P z : ℝ) : ℂ) * atomTerm P 0 1 ((1 : ℕ) : ℤ) β S z) =ᶠ[𝓝 y]
          (fun z => ((decayFactor P z : ℝ) : ℂ) * (((⟨z 0, z 1⟩ : ℂ) * ((‖z‖⁻¹ : ℝ) : ℂ)) *
            S.eval (decide (1 = 0)) (chartT P z) (heightRatio z))) := by
        filter_upwards [hev] with z hz
        unfold atomTerm
        rw [sqrt_q_eq hz, pow_one]
        have e2 : (((0 : ℕ) : ℝ) * β * logPhase P z + (((1 : ℕ) : ℤ) : ℝ) * angleOf z : ℝ) =
            (((1 : ℤ) : ℝ) * Complex.arg (⟨z 0, z 1⟩ : ℂ) : ℝ) := by
          simp [angleOf]
        rw [e2]
        have e3 : ((‖(⟨z 0, z 1⟩ : ℂ)‖ / ‖z‖ : ℝ) : ℂ) = (‖(⟨z 0, z 1⟩ : ℂ)‖ : ℂ) * ((‖z‖⁻¹ : ℝ) : ℂ) := by
          push_cast
          ring
        rw [e3, ← mul_assoc (Complex.exp _), phase_plus]
      exact tame_congr (tame_mul hDc (tame_mul (tame_of_contDiffAt (plane2.contDiffAt.mul hinv)) hV)) e
    · subst h1
      have e : (fun z => ((decayFactor P z : ℝ) : ℂ) * atomTerm P 0 1 (-((1 : ℕ) : ℤ)) β S z) =ᶠ[𝓝 y]
          (fun z => ((decayFactor P z : ℝ) : ℂ) * (((starRingEnd ℂ) (⟨z 0, z 1⟩ : ℂ) * ((‖z‖⁻¹ : ℝ) : ℂ)) *
            S.eval (decide (1 = 0)) (chartT P z) (heightRatio z))) := by
        filter_upwards [hev] with z hz
        unfold atomTerm
        rw [sqrt_q_eq hz, pow_one]
        have e2 : (((0 : ℕ) : ℝ) * β * logPhase P z + ((-((1 : ℕ) : ℤ) : ℤ) : ℝ) * angleOf z : ℝ) =
            (((-1 : ℤ) : ℝ) * Complex.arg (⟨z 0, z 1⟩ : ℂ) : ℝ) := by
          simp [angleOf]
        rw [e2]
        have e3 : ((‖(⟨z 0, z 1⟩ : ℂ)‖ / ‖z‖ : ℝ) : ℂ) = (‖(⟨z 0, z 1⟩ : ℂ)‖ : ℂ) * ((‖z‖⁻¹ : ℝ) : ℂ) := by
          push_cast
          ring
        rw [e3, ← mul_assoc (Complex.exp _), phase_minus]
      have hc : ContDiffAt ℝ 2 (fun z : Space => (starRingEnd ℂ) (⟨z 0, z 1⟩ : ℂ)) y :=
        Complex.conjCLE.contDiff.contDiffAt.comp y plane2.contDiffAt
      exact tame_congr (tame_mul hDc (tame_mul (tame_of_contDiffAt (hc.mul hinv)) hV)) e

theorem tame_axis (P : ChartParams) (hP : IsChartParams P) (j a : ℕ) (M : ℤ) (β : ℝ) (S : Spline)
    (hS : IsAtomSpline (decide (a = 0)) S j) (hj : j ≠ 0) (y : Space) (hy : y ≠ 0)
    (h0 : y 0 = 0) (h1 : y 1 = 0) :
    TameAt (fun y => ((decayFactor P y : ℝ) : ℂ) * atomTerm P j a M β S y) y := by
  set s : ℝ := if 0 < y 2 then 1 else -1 with hsdef
  have hw0 : AtomAxisInternal.planeW y = 0 := by
    apply Complex.ext <;> simp [AtomAxisInternal.planeW, h0, h1]
  have hny : ‖y‖ ^ 2 = y 2 ^ 2 := by rw [AtomAxisInternal.norm_sq_split, hw0]; simp
  have hnpos : 0 < ‖y‖ := norm_pos_iff.2 hy
  have hsy : s * y 2 = ‖y‖ := by
    have habs : ‖y‖ = |y 2| := by
      rw [← Real.sqrt_sq (norm_nonneg y), hny, Real.sqrt_sq_eq_abs]
    rw [habs]
    by_cases h : 0 < y 2
    · simp [hsdef, h, abs_of_pos h]
    · have h' : y 2 ≤ 0 := not_lt.1 h
      simp [hsdef, h, abs_of_nonpos h']
  have hs2 : s = 1 ∨ s = -1 := by by_cases h : 0 < y 2 <;> simp [hsdef, h]
  have hxy : s * heightRatio y = 1 := by
    unfold heightRatio
    rw [← mul_div_assoc, hsy, div_self hnpos.ne']
  have hdy : ‖y‖ + s * y 2 = 2 * ‖y‖ := by rw [hsy]; ring
  have hcx : ContinuousAt (fun z => s * heightRatio z) y :=
    continuousAt_const.mul (height2 hy).continuousAt
  have hcd : ContinuousAt (fun z : Space => ‖z‖ + s * z 2) y :=
    (norm2 hy).continuousAt.add (continuousAt_const.mul (coord2 2 y).continuousAt)
  have E1 : ∀ᶠ z in 𝓝 y, z ≠ 0 := eventually_ne_nhds hy
  have E2 : ∀ᶠ z in 𝓝 y, 0 < s * heightRatio z :=
    hcx.eventually (lt_mem_nhds (by show 0 < s * heightRatio y; rw [hxy]; norm_num))
  have E3 : ∀ᶠ z in 𝓝 y, ∀ b ∈ ((S.mesh.xBreaks.drop 1).dropLast).toFinset, b ≤ s * heightRatio z := by
    rw [Filter.eventually_all_finset]
    intro b hb
    have hb1 := AtomAxisInternal.interior_lt_one _ hS.spline.mesh.x_sorted hS.spline.mesh.x_last b
      (List.mem_toFinset.1 hb)
    exact (hcx.eventually (lt_mem_nhds (by show b < s * heightRatio y; rw [hxy]; exact hb1))).mono
      fun z hz => hz.le
  have E4 : ∀ᶠ z in 𝓝 y, 0 < ‖z‖ + s * z 2 :=
    hcd.eventually (lt_mem_nhds (by show 0 < ‖y‖ + s * y 2; rw [hdy]; positivity))
  have heq : (fun y => ((decayFactor P y : ℝ) : ℂ) * atomTerm P j a M β S y) =ᶠ[𝓝 y]
      AtomAxisInternal.axisForm P j a M β S s := by
    filter_upwards [E1, E2, E3, E4] with z hz hx hall hd
    exact AtomAxisInternal.point_identity P j a M β S hS hj s hs2 z hz hx
      (fun b hb => hall b (List.mem_toFinset.2 hb)) hd
  refine tame_congr ?_ heq
  have tG := tame_chartSpline P hP (AtomAxisInternal.quotSpline_class hS hj) s hy
  have hW : ContDiff ℝ 2 AtomAxisInternal.planeW := AtomAxisInternal.planeW_contDiff.of_le le_top
  have tΦ : TameAt (fun z => ((‖AtomAxisInternal.planeW z‖ ^ 2 : ℝ) : ℂ) *
      Complex.exp (Complex.I * ((((M - a : ℤ) : ℝ) * Complex.arg (AtomAxisInternal.planeW z) : ℝ) : ℂ))) y :=
    tame_comp (g := fun w : ℂ => ((‖w‖ ^ 2 : ℝ) : ℂ) * Complex.exp (Complex.I * ((((M - a : ℤ) : ℝ) * Complex.arg w : ℝ) : ℂ)))
      (Φ := AtomAxisInternal.planeW)
      (tame_of_global ((planePhase_contDiff (M - a)).differentiable (by simp))
        (planePhase_fderiv_localSlope (M - a)) _) (tame_of_contDiffAt hW.contDiffAt)
  have cD := ofReal2 (decay2 P hP hy)
  have cE : ContDiffAt ℝ 2 (fun z => Complex.exp (Complex.I * (((j : ℝ) * β * logPhase P z : ℝ) : ℂ))) y :=
    Complex.contDiff_exp.contDiffAt.comp y
      (contDiffAt_const.mul (ofReal2 (contDiffAt_const.mul (logPhase2 P hP).contDiffAt)))
  have cWa : ContDiffAt ℝ 2 (fun z => AtomAxisInternal.planeW z ^ a) y := hW.contDiffAt.pow a
  have hne2 : ‖y‖ * (‖y‖ + s * y 2) ≠ 0 := by
    rw [hdy]
    exact mul_ne_zero hnpos.ne' (mul_ne_zero two_ne_zero hnpos.ne')
  have cK : ContDiffAt ℝ 2
      (fun z : Space => (‖z‖ ^ a)⁻¹ * (‖z‖ * (‖z‖ + s * z 2))⁻¹ * (s * heightRatio z)⁻¹) y :=
    ((((norm2 hy).pow a).inv (pow_ne_zero _ hnpos.ne')).mul
      (((norm2 hy).mul ((norm2 hy).add (contDiffAt_const.mul (coord2 2 y)))).inv hne2)).mul
      ((contDiffAt_const.mul (height2 hy)).inv (by rw [hxy]; norm_num))
  exact tame_mul (tame_mul (tame_mul (tame_mul (tame_of_contDiffAt (cD.mul cE))
    (tame_mul tΦ (tame_of_contDiffAt cWa))) (tame_of_contDiffAt (ofReal2 cK)))
    (tame_of_contDiffAt contDiffAt_const)) tG

end AtomSlopeLocalInternal

theorem atomScalar_fderiv_locallySlopeBound (P : ChartParams) (hP : IsChartParams P) (j a : ℕ) (M : ℤ) (β : ℝ) (S : Spline)
    (ha : a ≤ 1) (hS : IsAtomSpline (decide (a = 0)) S j) (hM : j = 0 → M.natAbs = a) :
    LocallyLipschitzOn {y : Space | y ≠ 0} (fderiv ℝ (fun y => ((decayFactor P y : ℝ) : ℂ) * atomTerm P j a M β S y)) := by
  intro y hy
  have hy' : y ≠ 0 := hy
  have ht : AtomSlopeLocalInternal.TameAt (fun y => ((decayFactor P y : ℝ) : ℂ) * atomTerm P j a M β S y) y := by
    by_cases hw : (⟨y 0, y 1⟩ : ℂ) = 0
    · have h0 : y 0 = 0 := by simpa using congrArg Complex.re hw
      have h1 : y 1 = 0 := by simpa using congrArg Complex.im hw
      by_cases hj : j = 0
      · subst hj
        exact AtomSlopeLocalInternal.tame_harmonicZero P hP a M β S ha hS (hM rfl) hy'
      · exact AtomSlopeLocalInternal.tame_axis P hP j a M β S hS hj y hy' h0 h1
    · exact AtomSlopeLocalInternal.tame_offAxis P hP j a M β S hS hw
  obtain ⟨K, U, hU, hK⟩ := AtomSlopeLocalInternal.tame_slope ht
  exact ⟨K, U, mem_nhdsWithin_of_mem_nhds hU, hK⟩

end GivenFields

end CellCert

end Breakdown
