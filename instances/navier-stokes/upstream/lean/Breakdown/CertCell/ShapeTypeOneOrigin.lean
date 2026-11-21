import Breakdown.CertCell.ShapeStatements
import Breakdown.FracCell.GivenAuxPinSmoothLocal

open scoped ContDiff
open MeasureTheory

noncomputable section

namespace Breakdown

namespace CertCell

namespace GivenShape

open CellCert.GivenFields (Spline weightPoly radialScale heightDeriv heightRatio radialVec polarVecQ azimVecQ qOf
  planePhase_contDiff planePhase_fderiv_localSlope)

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
    exact (convex_ball y r).norm_image_sub_le_of_norm_hasFDerivWithin_le
      (fun x hx => (hd x hx).hasFDerivWithinAt) hb hw hz
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
  refine ⟨r, hr, fderiv ℝ f, K, K.2, fun z hz =>
    ((show ContDiffAt ℝ 2 f z from (hsub hz).2).differentiableAt (by norm_num)).hasFDerivAt, fun z hz w hw => ?_⟩
  have := hK.dist_le_mul z (hsub hz).1 w (hsub hw).1
  rwa [dist_eq_norm, dist_eq_norm] at this

private theorem tame_of_global {f : E → F} (hd : Differentiable ℝ f) (hl : LocallyLipschitz (fderiv ℝ f))
    (y : E) : TameAt f y := by
  obtain ⟨K, t, ht, hK⟩ := hl y
  obtain ⟨r, hr, hsub⟩ := Metric.mem_nhds_iff.1 ht
  refine ⟨r, hr, fderiv ℝ f, K, K.2, fun z _ => (hd z).hasFDerivAt, fun z hz w hw => ?_⟩
  have := hK.dist_le_mul z (hsub hz) w (hsub hw)
  rwa [dist_eq_norm, dist_eq_norm] at this

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
  obtain ⟨M1, hStrain, hb1, -, -⟩ := tame_bounds hr1 hK1 hg1 hg2
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
          (by positivity)) (mul_le_mul a4 a5 (norm_nonneg _) hStrain)
    _ = (K1 * M2 * M2 + M1 * K2) * ‖z - w‖ := by ring

private theorem tame_mul {c d : E → ℂ} {y : E} (hc : TameAt c y) (hd : TameAt d y) :
    TameAt (fun z => c z * d z) y := by
  obtain ⟨r1, hr1, c', K1, hK1, hc1, hc2⟩ := hc
  obtain ⟨r2, hr2, d', K2, hK2, hd1, hd2⟩ := hd
  obtain ⟨M1, hStrain, hb1, hl1, hv1⟩ := tame_bounds hr1 hK1 hc1 hc2
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

private theorem tame_region {f : E → F} {y : E} (h : TameAt f y) :
    ∃ U ∈ nhds y, (∀ q ∈ U, DifferentiableAt ℝ f q) ∧ ∃ K : NNReal, LipschitzOnWith K (fderiv ℝ f) U := by
  obtain ⟨r, hr, f', K, hK0, h1, h2⟩ := h
  refine ⟨Metric.ball y r, Metric.ball_mem_nhds y hr, fun z hz => (h1 z hz).differentiableAt, ⟨K, hK0⟩,
    LipschitzOnWith.of_dist_le_mul fun z hz w hw => ?_⟩
  rw [(h1 z hz).fderiv, (h1 w hw).fderiv, dist_eq_norm, dist_eq_norm]
  exact h2 z hz w hw

private def unitSlot (i : Fin 3) : ℂ →L[ℝ] (Fin 3 → ℂ) :=
  ContinuousLinearMap.pi fun j => if j = i then ContinuousLinearMap.id ℝ ℂ else 0

private theorem tame_pi {f : E → Fin 3 → ℂ} {y : E} (h : ∀ i, TameAt (fun z => f z i) y) : TameAt f y := by
  have e : f = fun z => unitSlot 0 (f z 0) + unitSlot 1 (f z 1) + unitSlot 2 (f z 2) := by
    funext z i
    fin_cases i <;> simp [unitSlot]
  rw [e]
  exact tame_add (tame_add (tame_clm _ (h 0)) (tame_clm _ (h 1))) (tame_clm _ (h 2))

end Tame

private theorem spline_tame (hsm : JoinedSplineSmooth) (hsl : JoinedSplineGradSlopeBound) {a b : ℕ} {S : Spline}
    (hS : IsJoinedSpline a b S) (ha : 1 ≤ a) (hb : 1 ≤ b) (q : ℝ × ℝ) :
    TameAt (fun p : ℝ × ℝ => S.evalHalf p.1 p.2) q := by
  have hle : (1 : WithTop ℕ∞) ≤ ((min a b : ℕ) : WithTop ℕ∞) := by exact_mod_cast le_min ha hb
  have hc : ContDiff ℝ 1 (fun z : ℝ × ℝ => S.evalHalf z.1 z.2) := (hsm a b S hS).of_le hle
  refine tame_of_global (hc.differentiable (by norm_num)) (fun z => ?_) q
  obtain ⟨L, hL⟩ := hsl a b S hS ha hb (‖z‖ + 1)
  refine ⟨L, Metric.closedBall 0 (‖z‖ + 1), Filter.mem_of_superset (Metric.isOpen_ball.mem_nhds ?_)
    Metric.ball_subset_closedBall, hL⟩
  rw [Metric.mem_ball, dist_zero_right]
  linarith

private theorem spline_diff (hsm : JoinedSplineSmooth) {a b : ℕ} {S : Spline}
    (hS : IsJoinedSpline a b S) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    Differentiable ℝ (fun p : ℝ × ℝ => S.evalHalf p.1 p.2) := by
  have hle : (1 : WithTop ℕ∞) ≤ ((min a b : ℕ) : WithTop ℕ∞) := by exact_mod_cast le_min ha hb
  exact ((hsm a b S hS).of_le hle).differentiable (by norm_num)

private theorem spline_tderiv_tame (hsm : JoinedSplineSmooth) (hsl : JoinedSplineGradSlopeBound)
    (hsd : SplineDerivatives) {a b : ℕ} {S : Spline} (hS : IsJoinedSpline a b S) (ha : 2 ≤ a) (hb : 1 ≤ b)
    (q : ℝ × ℝ) : TameAt (fun p : ℝ × ℝ => deriv (fun t => S.evalHalf t p.2) p.1) q := by
  obtain ⟨h1, h2⟩ := (hsd a b S hS).1 (by omega)
  have e : (fun p : ℝ × ℝ => deriv (fun t => S.evalHalf t p.2) p.1) =
      fun p => (tDerivSpline S).evalHalf p.1 p.2 := by
    funext p
    exact h2 p.1 p.2
  rw [e]
  exact spline_tame hsm hsl h1 (by omega) hb q

private theorem spline_xderiv_tame (hsm : JoinedSplineSmooth) (hsl : JoinedSplineGradSlopeBound)
    (hsd : SplineDerivatives) {a b : ℕ} {S : Spline} (hS : IsJoinedSpline a b S) (ha : 1 ≤ a) (hb : 2 ≤ b)
    (q : ℝ × ℝ) : TameAt (fun p : ℝ × ℝ => deriv (fun x => S.evalHalf p.1 x) p.2) q := by
  obtain ⟨h1, h2⟩ := (hsd a b S hS).2 (by omega)
  have e : (fun p : ℝ × ℝ => deriv (fun x => S.evalHalf p.1 x) p.2) =
      fun p => (xDerivSpline S).evalHalf p.1 p.2 := by
    funext p
    exact h2 p.1 p.2
  rw [e]
  exact spline_tame hsm hsl h1 ha (by omega) q

private theorem partial_t_contDiff {G : ℝ → ℝ → ℂ} (hG : ContDiff ℝ 3 (fun p : ℝ × ℝ => G p.1 p.2)) :
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

private theorem tderiv_mul_tame {G F : ℝ → ℝ → ℂ} (hG : ContDiff ℝ 3 (fun p : ℝ × ℝ => G p.1 p.2))
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
  exact tame_add (tame_mul (tame_of_contDiffAt (partial_t_contDiff hG).contDiffAt) (hF2 q))
    (tame_mul (tame_of_contDiffAt (hG.of_le (by norm_num)).contDiffAt) (hFt q))

private theorem chartRadius_contDiffAt (P : ShapeParams) {t : ℝ} (ht : t < 1) :
    ContDiffAt ℝ 2 (chartRadius P) t := by
  unfold chartRadius
  exact (contDiffAt_const.mul contDiffAt_id).div (contDiffAt_const.sub contDiffAt_id) (by linarith)

private theorem phaseSlope_contDiffAt {P : ShapeParams} (hP : IsShapeParams P) {t : ℝ} (ht : t < 1) :
    ContDiffAt ℝ 2 (phaseSlope P) t := by
  obtain ⟨δ, hδ, hf⟩ := hP.phase.smooth
  have hr := chartRadius_contDiffAt P ht
  have hs : chartRadius P t ^ 2 ∈ Set.Ioi (-δ) := by
    rw [Set.mem_Ioi]
    nlinarith [sq_nonneg (chartRadius P t)]
  have h3 : ContDiffAt ℝ 3 P.radialPhase (chartRadius P t ^ 2) := hf.contDiffAt (isOpen_Ioi.mem_nhds hs)
  have hd : ContDiffAt ℝ 2 (deriv P.radialPhase) (chartRadius P t ^ 2) := by
    have h4 : ContDiffAt ℝ 2 (fun s => fderiv ℝ P.radialPhase s 1) (chartRadius P t ^ 2) :=
      (h3.fderiv_right (m := 2) (by norm_num)).clm_apply contDiffAt_const
    exact h4
  have hc : ContDiffAt ℝ 2 (fun t' => deriv P.radialPhase (chartRadius P t' ^ 2)) t :=
    ContDiffAt.comp (g := deriv P.radialPhase) (f := fun t' => chartRadius P t' ^ 2) t hd (hr.pow 2)
  unfold phaseSlope
  exact (contDiffAt_const.mul (hr.pow 2)).mul hc

private theorem weightPoly_add_two (a e : ℕ) (t : ℝ) :
    weightPoly (a + 2) e t = ((t ^ 2 : ℝ) : ℂ) * weightPoly a e t := by
  unfold weightPoly
  push_cast
  ring

private theorem weight_contDiff (a e k : ℕ) :
    ContDiff ℝ 3 (fun p : ℝ × ℝ => weightPoly a e p.1 * ((1 - p.2 ^ 2 : ℝ) : ℂ) ^ k) := by
  unfold weightPoly
  have h1 : ContDiff ℝ 3 (fun p : ℝ × ℝ => p.1 ^ a * (1 - p.1) ^ e) := by fun_prop
  have h2 : ContDiff ℝ 3 (fun p : ℝ × ℝ => 1 - p.2 ^ 2) := by fun_prop
  exact (Complex.ofRealCLM.contDiff.comp h1).mul ((Complex.ofRealCLM.contDiff.comp h2).pow k)

private theorem weight_q_contDiff (a e : ℕ) :
    ContDiff ℝ 3 (fun p : ℝ × ℝ => weightPoly a e p.1 * ((1 - p.2 ^ 2 : ℝ) : ℂ)) := by
  unfold weightPoly
  have h1 : ContDiff ℝ 3 (fun p : ℝ × ℝ => p.1 ^ a * (1 - p.1) ^ e) := by fun_prop
  have h2 : ContDiff ℝ 3 (fun p : ℝ × ℝ => 1 - p.2 ^ 2) := by fun_prop
  exact (Complex.ofRealCLM.contDiff.comp h1).mul (Complex.ofRealCLM.contDiff.comp h2)

private theorem typeOne_factor (hsm : JoinedSplineSmooth) (hsl : JoinedSplineGradSlopeBound)
    (hsd : SplineDerivatives) {P : ShapeParams} {D : TimeFieldData} {κ : FieldKey} (hP : IsShapeParams P)
    (hD : IsTimeFieldData D) (hκ : κ ∈ D.keys) (h1 : κ.label.1 ≠ 0) :
    ∃ H : ℝ → ℝ → Fin 3 → ℂ, (∀ k : Fin 3, ∀ q0 : ℝ × ℝ, q0.1 < 1 → TameAt (fun p : ℝ × ℝ => H p.1 p.2 k) q0) ∧
      ∀ t x k, reducedComps P κ (D.amp κ) t x k = polarFactor x * (((t ^ 2 : ℝ) : ℂ) * H t x k) := by
  obtain ⟨a, ha⟩ : ∃ a, (D.amp κ).lowOrder = a + 2 :=
    ⟨(D.amp κ).lowOrder - 2, by have := hD.lowOrder_ge κ hκ h1; omega⟩
  have hR := hD.radial_class κ hκ h1
  have hT := hD.polar_class κ hκ h1
  have dR := spline_diff hsm hR (by norm_num) (by norm_num)
  have dT := spline_diff hsm hT (by norm_num) (by norm_num)
  have eR := spline_tame hsm hsl hR (by norm_num) (by norm_num)
  have eT := spline_tame hsm hsl hT (by norm_num) (by norm_num)
  have tR := spline_tderiv_tame hsm hsl hsd hR (by norm_num) (by norm_num)
  have xT := spline_xderiv_tame hsm hsl hsd hT (by norm_num) (by norm_num)
  have hWq := weight_q_contDiff a (D.amp κ).highOrder
  set q : ℝ → ℂ := fun x => ((1 - x ^ 2 : ℝ) : ℂ) with hq
  set A : ℝ → ℝ → ℂ := fun t x => weightPoly a (D.amp κ).highOrder t * q x * (D.amp κ).radial.evalHalf t x with hA
  set B : ℝ → ℝ → ℂ := fun t x => weightPoly a (D.amp κ).highOrder t * q x * (D.amp κ).polar.evalHalf t x with hB
  set C : ℝ → ℝ → ℂ := fun t x => (Complex.I / (labelAzimuth P.azimuthOrder κ.label : ℂ)) *
    (((t * (1 - t) : ℝ) : ℂ) * deriv (fun t' => A t' x) t + ((2 * (1 - t) : ℝ) : ℂ) * A t x +
      Complex.I * (((κ.phaseIndex : ℝ) * phaseSlope P t : ℝ) : ℂ) * A t x + 2 * A t x -
      weightPoly a (D.amp κ).highOrder t * (3 * q x * ((-2 * x : ℝ) : ℂ) * (D.amp κ).polar.evalHalf t x +
        q x ^ 2 * deriv (fun x' => (D.amp κ).polar.evalHalf t x') x)) with hC
  have hAc : ∀ q0, TameAt (fun p : ℝ × ℝ => A p.1 p.2) q0 := fun q0 =>
    tame_mul (tame_of_contDiffAt (hWq.of_le (by norm_num)).contDiffAt) (eR q0)
  refine ⟨fun t x => ![A t x, B t x, C t x], ?_, ?_⟩
  · intro kk q0 hq0
    fin_cases kk
    · exact tame_congr (hAc q0) (Filter.Eventually.of_forall fun p => rfl)
    · exact tame_congr (tame_mul (tame_of_contDiffAt (hWq.of_le (by norm_num)).contDiffAt) (eT q0))
        (Filter.Eventually.of_forall fun p => rfl)
    · have hAt : TameAt (fun p : ℝ × ℝ => deriv (fun t' => A t' p.2) p.1) q0 :=
        tderiv_mul_tame (G := fun t x => weightPoly a (D.amp κ).highOrder t * q x) (F := fun t x => (D.amp κ).radial.evalHalf t x)
          hWq dR eR tR q0
      have hps : TameAt (fun p : ℝ × ℝ => Complex.I * (((κ.phaseIndex : ℝ) * phaseSlope P p.1 : ℝ) : ℂ)) q0 :=
        tame_of_contDiffAt (contDiffAt_const.mul (Complex.ofRealCLM.contDiff.contDiffAt.comp q0
          (contDiffAt_const.mul ((phaseSlope_contDiffAt hP hq0).comp q0 contDiffAt_fst))))
      have c1 : ContDiff ℝ 2 (fun p : ℝ × ℝ => ((p.1 * (1 - p.1) : ℝ) : ℂ)) :=
        Complex.ofRealCLM.contDiff.comp (contDiff_fst.mul (contDiff_const.sub contDiff_fst))
      have c2 : ContDiff ℝ 2 (fun p : ℝ × ℝ => ((2 * (1 - p.1) : ℝ) : ℂ)) :=
        Complex.ofRealCLM.contDiff.comp (contDiff_const.mul (contDiff_const.sub contDiff_fst))
      have c3 : ContDiff ℝ 2 (fun p : ℝ × ℝ => 3 * q p.2 * ((-2 * p.2 : ℝ) : ℂ)) :=
        (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp (contDiff_const.sub (contDiff_snd.pow 2)))).mul
          (Complex.ofRealCLM.contDiff.comp (contDiff_const.mul contDiff_snd))
      have c4 : ContDiff ℝ 2 (fun p : ℝ × ℝ => q p.2 ^ 2) :=
        (Complex.ofRealCLM.contDiff.comp (contDiff_const.sub (contDiff_snd.pow 2))).pow 2
      have c5 : ContDiff ℝ 2 (fun p : ℝ × ℝ => weightPoly a (D.amp κ).highOrder p.1) := by
        unfold weightPoly
        exact Complex.ofRealCLM.contDiff.comp ((contDiff_fst.pow a).mul ((contDiff_const.sub contDiff_fst).pow (D.amp κ).highOrder))
      have hall := tame_mul (tame_of_contDiffAt (contDiffAt_const (c := Complex.I / (labelAzimuth P.azimuthOrder κ.label : ℂ))))
        (tame_sub (tame_add (tame_add (tame_add (tame_mul (tame_of_contDiffAt c1.contDiffAt) hAt)
          (tame_mul (tame_of_contDiffAt c2.contDiffAt) (hAc q0))) (tame_mul hps (hAc q0)))
          (tame_mul (tame_of_contDiffAt (contDiffAt_const (c := (2 : ℂ)))) (hAc q0)))
          (tame_mul (tame_of_contDiffAt c5.contDiffAt) (tame_add (tame_mul (tame_of_contDiffAt c3.contDiffAt) (eT q0))
            (tame_mul (tame_of_contDiffAt c4.contDiffAt) (xT q0)))))
      exact tame_congr hall (Filter.Eventually.of_forall fun p => rfl)
  · have hdT : ∀ t x, HasDerivAt (fun x' => (D.amp κ).polar.evalHalf t x') (deriv (fun x' => (D.amp κ).polar.evalHalf t x') x) x := by
      intro t x
      have h2 : DifferentiableAt ℝ (fun x' : ℝ => (t, x')) x :=
        (differentiableAt_const _).prodMk differentiableAt_id
      exact ((dT _).comp x h2).hasDerivAt
    have hdA : ∀ t x, HasDerivAt (fun t' => A t' x) (deriv (fun t' => A t' x) t) t := by
      intro t x
      have h2 : DifferentiableAt ℝ (fun t' : ℝ => (t', x)) t :=
        differentiableAt_id.prodMk (differentiableAt_const _)
      have hAd : Differentiable ℝ (fun p : ℝ × ℝ => A p.1 p.2) :=
        (hWq.differentiable (by norm_num)).mul dR
      exact ((hAd _).comp t h2).hasDerivAt
    have hdq : ∀ x : ℝ, HasDerivAt q (((-2 * x : ℝ)) : ℂ) x := by
      intro x
      have := ((hasDerivAt_pow 2 x).const_sub 1).ofReal_comp
      convert this using 1
      push_cast
      ring
    have hdt2 : ∀ t : ℝ, HasDerivAt (fun t' : ℝ => ((t' ^ 2 : ℝ) : ℂ)) (((2 * t : ℝ)) : ℂ) t := by
      intro t
      have := (hasDerivAt_pow 2 t).ofReal_comp
      convert this using 1
      push_cast
      ring
    intro t x kk
    have eA : weightPoly (D.amp κ).lowOrder (D.amp κ).highOrder t * axisFactor x * (D.amp κ).radial.evalHalf t x =
        q x * (((t ^ 2 : ℝ) : ℂ) * A t x) := by
      simp only [hA, hq, ha, weightPoly_add_two, axisFactor]
      push_cast
      ring
    have eB : weightPoly (D.amp κ).lowOrder (D.amp κ).highOrder t * axisFactor x * (D.amp κ).polar.evalHalf t x =
        q x * (((t ^ 2 : ℝ) : ℂ) * B t x) := by
      simp only [hB, hq, ha, weightPoly_add_two, axisFactor]
      push_cast
      ring
    fin_cases kk
    · simp only [reducedComps, if_neg h1]
      show weightPoly (D.amp κ).lowOrder (D.amp κ).highOrder t * axisFactor x * (D.amp κ).radial.evalHalf t x =
        polarFactor x * (((t ^ 2 : ℝ) : ℂ) * A t x)
      exact eA
    · simp only [reducedComps, if_neg h1]
      show weightPoly (D.amp κ).lowOrder (D.amp κ).highOrder t * axisFactor x * (D.amp κ).polar.evalHalf t x =
        polarFactor x * (((t ^ 2 : ℝ) : ℂ) * B t x)
      exact eB
    · have hder1 : deriv (fun t' => weightPoly (D.amp κ).lowOrder (D.amp κ).highOrder t' * axisFactor x * (D.amp κ).radial.evalHalf t' x) t =
          q x * (((2 * t : ℝ) : ℂ) * A t x + ((t ^ 2 : ℝ) : ℂ) * deriv (fun t' => A t' x) t) := by
        have e1 : (fun t' => weightPoly (D.amp κ).lowOrder (D.amp κ).highOrder t' * axisFactor x * (D.amp κ).radial.evalHalf t' x) =
            fun t' => q x * (((t' ^ 2 : ℝ) : ℂ) * A t' x) := by
          funext t'
          simp only [hA, hq, ha, weightPoly_add_two, axisFactor]
          push_cast
          ring
        have hm : HasDerivAt (fun t' => ((t' ^ 2 : ℝ) : ℂ) * A t' x)
            (((2 * t : ℝ) : ℂ) * A t x + ((t ^ 2 : ℝ) : ℂ) * deriv (fun t' => A t' x) t) t :=
          (hdt2 t).mul (hdA t x)
        rw [e1, deriv_const_mul_field, hm.deriv]
      have hder2 : deriv (fun x' => polarFactor x' * (weightPoly (D.amp κ).lowOrder (D.amp κ).highOrder t * axisFactor x' *
          (D.amp κ).polar.evalHalf t x')) x =
          q x * (((t ^ 2 : ℝ) : ℂ) * (weightPoly a (D.amp κ).highOrder t * (3 * q x * ((-2 * x : ℝ) : ℂ) * (D.amp κ).polar.evalHalf t x +
            q x ^ 2 * deriv (fun x' => (D.amp κ).polar.evalHalf t x') x))) := by
        have e2 : (fun x' => polarFactor x' * (weightPoly (D.amp κ).lowOrder (D.amp κ).highOrder t * axisFactor x' *
            (D.amp κ).polar.evalHalf t x')) = fun x' => (((t ^ 2 : ℝ) : ℂ) * weightPoly a (D.amp κ).highOrder t) * (q x' ^ 3 * (D.amp κ).polar.evalHalf t x') := by
          funext x'
          simp only [hq, ha, weightPoly_add_two, axisFactor, polarFactor]
          push_cast
          ring
        have hh := (((hdq x).pow 3).mul (hdT t x)).const_mul (((t ^ 2 : ℝ) : ℂ) * weightPoly a (D.amp κ).highOrder t)
        have hh' : HasDerivAt (fun x' => (((t ^ 2 : ℝ) : ℂ) * weightPoly a (D.amp κ).highOrder t) *
            (q x' ^ 3 * (D.amp κ).polar.evalHalf t x'))
            ((((t ^ 2 : ℝ) : ℂ) * weightPoly a (D.amp κ).highOrder t) * (((3 : ℕ) : ℂ) * q x ^ (3 - 1) *
              ((-2 * x : ℝ) : ℂ) * (D.amp κ).polar.evalHalf t x +
              q x ^ 3 * deriv (fun x' => (D.amp κ).polar.evalHalf t x') x)) x := hh
        rw [e2, hh'.deriv]
        simp only [show (3 : ℕ) - 1 = 2 from rfl]
        push_cast
        ring
      simp only [reducedComps, if_neg h1, shiftedScale, radialScale, heightDeriv]
      try simp only [Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
      rw [hder1, hder2, eA]
      simp only [hC, polarFactor, hq]
      push_cast
      ring

private def planeOf (y : Space) : ℂ := (y 0 : ℂ) + (y 1 : ℂ) * Complex.I

private def planeMap (j : ℤ) (w : ℂ) : ℂ :=
  ((‖w‖ ^ 2 : ℝ) : ℂ) * Complex.exp (Complex.I * (((j : ℝ) * Complex.arg w : ℝ) : ℂ))

private theorem planeMap_scale (j : ℤ) {s : ℝ} (hs : 0 < s) (w : ℂ) :
    planeMap j ((s : ℂ) * w) = ((s ^ 2 : ℝ) : ℂ) * planeMap j w := by
  unfold planeMap
  rw [Complex.arg_real_mul w hs, norm_mul, Complex.norm_real, Real.norm_of_nonneg hs.le]
  push_cast
  ring

private theorem planeOf_contDiff : ContDiff ℝ ⊤ planeOf := by
  have h0 : ContDiff ℝ ⊤ (fun y : Space => ((y 0 : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (EuclideanSpace.proj (0 : Fin 3) : Space →L[ℝ] ℝ).contDiff
  have h1 : ContDiff ℝ ⊤ (fun y : Space => ((y 1 : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (EuclideanSpace.proj (1 : Fin 3) : Space →L[ℝ] ℝ).contDiff
  exact h0.add (h1.mul contDiff_const)

private theorem planeOf_smul (s : ℝ) (v : Space) : planeOf (s • v) = (s : ℂ) * planeOf v := by
  simp only [planeOf, PiLp.smul_apply, smul_eq_mul]
  push_cast
  ring

private theorem one_sub_heightRatio_sq (y : Space) (hy : y ≠ 0) :
    1 - heightRatio y ^ 2 = ‖planeOf y‖ ^ 2 / ‖y‖ ^ 2 := by
  have hn : ‖y‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.2 hy)
  have e1 : ‖y‖ ^ 2 = y 0 ^ 2 + y 1 ^ 2 + y 2 ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_three]
    simp [sq_abs]
  have e2 : ‖planeOf y‖ ^ 2 = y 0 ^ 2 + y 1 ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp [planeOf]
    ring
  unfold heightRatio
  rw [div_pow, e2]
  field_simp
  linarith

private def nearOriginProfile (P : ShapeParams) (κ : FieldKey) (σ : ℝ) (H : ℝ → ℝ → Fin 3 → ℂ)
    (p : ℝ × Space) (i : Fin 3) : ℂ :=
  ((((p.1 + P.chartLength) ^ 2)⁻¹ : ℝ) : ℂ) *
    Complex.exp (((2 * Real.pi * (labelTime κ.label : ℝ) * σ + (κ.phaseIndex : ℝ) * P.radialPhase (p.1 ^ 2) : ℝ) : ℂ) *
      Complex.I) *
    (H (p.1 / (p.1 + P.chartLength)) (p.2 2) 0 * ((p.2 i : ℝ) : ℂ) +
      H (p.1 / (p.1 + P.chartLength)) (p.2 2) 1 * ((![p.2 2 * p.2 0, p.2 2 * p.2 1, -(1 - p.2 2 ^ 2)] i : ℝ) : ℂ) +
      H (p.1 / (p.1 + P.chartLength)) (p.2 2) 2 * ((![-(p.2 1), p.2 0, 0] i : ℝ) : ℂ))

private theorem nearOriginProfile_tame {P : ShapeParams} (hP : IsShapeParams P) (κ : FieldKey) (σ : ℝ)
    (H : ℝ → ℝ → Fin 3 → ℂ) (hH : ∀ k : Fin 3, ∀ q0 : ℝ × ℝ, q0.1 < 1 → TameAt (fun p : ℝ × ℝ => H p.1 p.2 k) q0)
    (i : Fin 3) (p : ℝ × Space) (hp : 0 ≤ p.1) : TameAt (fun z => nearOriginProfile P κ σ H z i) p := by
  have hL := hP.chartLength_pos
  have hne : p.1 + P.chartLength ≠ 0 := by linarith
  have hr : ContDiffAt ℝ ⊤ (fun q : ℝ × Space => q.1) p := contDiffAt_fst
  have hτ : ContDiffAt ℝ ⊤ (fun q : ℝ × Space => q.1 / (q.1 + P.chartLength)) p :=
    hr.div (hr.add contDiffAt_const) hne
  have hτ1 : p.1 / (p.1 + P.chartLength) < 1 := by
    rw [div_lt_one (by linarith)]
    linarith
  have hinv : ContDiffAt ℝ ⊤ (fun q : ℝ × Space => ((q.1 + P.chartLength) ^ 2)⁻¹) p :=
    ((hr.add contDiffAt_const).pow 2).inv (pow_ne_zero 2 hne)
  obtain ⟨δ, hδ, hf⟩ := hP.phase.smooth
  have hs : p.1 ^ 2 ∈ Set.Ioi (-δ) := by
    rw [Set.mem_Ioi]
    nlinarith [sq_nonneg p.1]
  have h3 : ContDiffAt ℝ 3 P.radialPhase (p.1 ^ 2) := hf.contDiffAt (isOpen_Ioi.mem_nhds hs)
  have hph : ContDiffAt ℝ 3 (fun q : ℝ × Space => P.radialPhase (q.1 ^ 2)) p :=
    ContDiffAt.comp (g := P.radialPhase) (f := fun q : ℝ × Space => q.1 ^ 2) p h3 ((hr.of_le le_top).pow 2)
  have hE : TameAt (fun q : ℝ × Space => Complex.exp (((2 * Real.pi * (labelTime κ.label : ℝ) * σ +
      (κ.phaseIndex : ℝ) * P.radialPhase (q.1 ^ 2) : ℝ) : ℂ) * Complex.I)) p :=
    tame_of_contDiffAt ((Complex.contDiff_exp.contDiffAt.comp p ((Complex.ofRealCLM.contDiff.contDiffAt.comp p
      (contDiffAt_const.add (contDiffAt_const.mul hph))).mul contDiffAt_const)).of_le (by norm_num))
  have hu : ∀ j : Fin 3, ContDiffAt ℝ ⊤ (fun q : ℝ × Space => q.2 j) p := fun j =>
    ((EuclideanSpace.proj j : Space →L[ℝ] ℝ).contDiff.comp contDiff_snd).contDiffAt
  have hK : ∀ k : Fin 3, TameAt (fun q : ℝ × Space => H (q.1 / (q.1 + P.chartLength)) (q.2 2) k) p := fun k =>
    tame_comp (g := fun r : ℝ × ℝ => H r.1 r.2 k) (Φ := fun q : ℝ × Space => (q.1 / (q.1 + P.chartLength), q.2 2))
      (hH k _ hτ1) (tame_of_contDiffAt ((hτ.prodMk (hu 2)).of_le le_top))
  have hc : ∀ f : ℝ × Space → ℝ, ContDiffAt ℝ ⊤ f p → TameAt (fun q => (f q : ℂ)) p :=
    fun f hf => tame_of_contDiffAt ((Complex.ofRealCLM.contDiff.contDiffAt.comp p hf).of_le le_top)
  have hv1 : ContDiffAt ℝ ⊤ (fun q : ℝ × Space => ![q.2 2 * q.2 0, q.2 2 * q.2 1, -(1 - q.2 2 ^ 2)] i) p := by
    fin_cases i
    · simpa using (hu 2).mul (hu 0)
    · simpa using (hu 2).mul (hu 1)
    · simpa using (contDiffAt_const.sub ((hu 2).pow 2)).neg
  have hv2 : ContDiffAt ℝ ⊤ (fun q : ℝ × Space => ![-(q.2 1), q.2 0, 0] i) p := by
    fin_cases i
    · simpa using (hu 1).neg
    · simpa using hu 0
    · simpa using (contDiffAt_const : ContDiffAt ℝ ⊤ (fun _ : ℝ × Space => (0 : ℝ)) p)
  exact tame_mul (tame_mul (hc _ hinv) hE)
    (tame_add (tame_add (tame_mul (hK 0) (hc _ (hu i))) (tame_mul (hK 1) (hc _ hv1)))
      (tame_mul (hK 2) (hc _ hv2)))

private theorem keyPhase_factor {P : ShapeParams} (hP : IsShapeParams P) (κ : FieldKey) (σ : ℝ) (y : Space)
    (hy : y ≠ 0) (c : ℂ) :
    keyPhase P κ σ y * (polarFactor (heightRatio y) * (((chartCoord P y ^ 2 : ℝ) : ℂ) * c)) =
      planeMap (labelAzimuth P.azimuthOrder κ.label) (planeOf y) * ((((‖y‖ + P.chartLength) ^ 2)⁻¹ : ℝ) : ℂ) *
        Complex.exp (((2 * Real.pi * (labelTime κ.label : ℝ) * σ +
          (κ.phaseIndex : ℝ) * P.radialPhase (‖y‖ ^ 2) : ℝ) : ℂ) * Complex.I) * c := by
  have hn : ‖y‖ ≠ 0 := norm_ne_zero_iff.2 hy
  have hL : ‖y‖ + P.chartLength ≠ 0 := by have := hP.chartLength_pos; positivity
  have ea : keyPhase P κ σ y = Complex.exp (Complex.I *
      (((labelAzimuth P.azimuthOrder κ.label : ℝ) * Complex.arg (planeOf y) : ℝ) : ℂ)) *
      Complex.exp (((2 * Real.pi * (labelTime κ.label : ℝ) * σ +
        (κ.phaseIndex : ℝ) * P.radialPhase (‖y‖ ^ 2) : ℝ) : ℂ) * Complex.I) := by
    unfold keyPhase
    rw [← Complex.exp_add]
    congr 1
    simp only [pointAngle, planeOf]
    push_cast
    ring
  rw [ea, polarFactor, one_sub_heightRatio_sq y hy]
  unfold planeMap chartCoord
  have hn' : (‖y‖ : ℂ) ≠ 0 := by exact_mod_cast hn
  have hL' : ((‖y‖ : ℂ) + (P.chartLength : ℂ)) ≠ 0 := by exact_mod_cast hL
  push_cast
  field_simp

private theorem keyVector_near_eq {P : ShapeParams} (hP : IsShapeParams P) (κ : FieldKey) (A : KeyAmp) (σ : ℝ)
    (H : ℝ → ℝ → Fin 3 → ℂ)
    (hRK : ∀ t x k, reducedComps P κ A t x k = polarFactor x * (((t ^ 2 : ℝ) : ℂ) * H t x k))
    (y : Space) (hy : y ≠ 0) (i : Fin 3) :
    keyVector P κ A σ y i = planeMap (labelAzimuth P.azimuthOrder κ.label) (planeOf y) *
      nearOriginProfile P κ σ H (‖y‖, ‖y‖⁻¹ • y) i := by
  have hsm : ∀ j : Fin 3, (‖y‖⁻¹ • y) j = y j / ‖y‖ := by
    intro j
    rw [PiLp.smul_apply, smul_eq_mul, div_eq_inv_mul]
  have hph := fun c => keyPhase_factor hP κ σ y hy c
  simp only [keyVector, nearOriginProfile, hsm, hRK]
  have e2 : ‖y‖ / (‖y‖ + P.chartLength) = chartCoord P y := rfl
  have e3 : y 2 / ‖y‖ = heightRatio y := rfl
  rw [e2, e3]
  linear_combination (norm := skip)
    ((radialVec y i : ℂ)) * hph (H (chartCoord P y) (heightRatio y) 0) +
      ((polarVecQ y i : ℂ)) * hph (H (chartCoord P y) (heightRatio y) 1) +
      ((azimVecQ y i : ℂ)) * hph (H (chartCoord P y) (heightRatio y) 2)
  fin_cases i <;> simp [radialVec, polarVecQ, azimVecQ, qOf] <;> ring

private def scaledKey (P : ShapeParams) (κ : FieldKey) (σ : ℝ) (H : ℝ → ℝ → Fin 3 → ℂ) (p : ℝ × Space) :
    Fin 3 → ℂ :=
  fun i => planeMap (labelAzimuth P.azimuthOrder κ.label) (planeOf p.2) *
    nearOriginProfile P κ σ H (p.1 * ‖p.2‖, ‖p.2‖⁻¹ • p.2) i

private theorem scaleT_norm (s : ℝ) (hs : 0 < s) :
    ‖(0 : Space →L[ℝ] ℝ).prod (s⁻¹ • ContinuousLinearMap.id ℝ Space)‖ ≤ s⁻¹ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (inv_nonneg.2 hs.le) (fun v => ?_)
  rw [ContinuousLinearMap.prod_apply, Prod.norm_def]
  have ha : |s| = s := abs_of_pos hs
  simp [norm_smul, ha]
  positivity

private theorem scaled_hasFDerivAt {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {f : Space → G} {F : ℝ × Space → G}
    (hscale : ∀ s : ℝ, 0 < s → ∀ v : Space, v ≠ 0 → f (s • v) = (s ^ 2) • F (s, v))
    {s : ℝ} (hs : 0 < s) {w : Space} (hw : w ≠ 0) (hd : DifferentiableAt ℝ F (s, s⁻¹ • w)) :
    HasFDerivAt f ((s ^ 2) • (fderiv ℝ F (s, s⁻¹ • w)).comp
      ((0 : Space →L[ℝ] ℝ).prod (s⁻¹ • ContinuousLinearMap.id ℝ Space))) w := by
  have hT : HasFDerivAt (fun w' : Space => (s, s⁻¹ • w'))
      ((0 : Space →L[ℝ] ℝ).prod (s⁻¹ • ContinuousLinearMap.id ℝ Space)) w :=
    (hasFDerivAt_const s w).prodMk ((hasFDerivAt_id w).const_smul s⁻¹)
  have h1 := (hd.hasFDerivAt.comp w hT).const_smul (s ^ 2)
  refine h1.congr_of_eventuallyEq ?_
  filter_upwards [isOpen_ne.mem_nhds hw] with w' hw'
  have hv : s⁻¹ • w' ≠ 0 := smul_ne_zero (inv_ne_zero hs.ne') hw'
  have := hscale s hs (s⁻¹ • w') hv
  rw [smul_inv_smul₀ hs.ne'] at this
  rw [this]
  rfl

private theorem scaled_origin {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {f : Space → G} {F : ℝ × Space → G} {ρ : ℝ} (hρ : 0 < ρ) (hf0 : f 0 = 0)
    (hscale : ∀ s : ℝ, 0 < s → ∀ v : Space, v ≠ 0 → f (s • v) = (s ^ 2) • F (s, v))
    (hF : ∀ p ∈ Set.Icc 0 ρ ×ˢ (Metric.closedBall (0 : Space) 1 \ Metric.ball 0 (1 / 2)),
      ∃ U ∈ nhds p, (∀ q ∈ U, DifferentiableAt ℝ F q) ∧ ∃ K : NNReal, LipschitzOnWith K (fderiv ℝ F) U) :
    HasFDerivAt f (0 : Space →L[ℝ] G) 0 ∧ ∃ C : ℝ, (∀ y ∈ Metric.ball (0 : Space) ρ,
      DifferentiableAt ℝ f y ∧ ‖f y‖ ≤ C * ‖y‖ ^ 2 ∧ ‖fderiv ℝ f y‖ ≤ C * ‖y‖) ∧
      ∃ K : NNReal, LipschitzOnWith K (fderiv ℝ f) (Metric.ball 0 ρ) := by
  set Cs : Set (ℝ × Space) := Set.Icc 0 ρ ×ˢ (Metric.closedBall (0 : Space) 1 \ Metric.ball 0 (1 / 2)) with hCs
  have hCc : IsCompact Cs := isCompact_Icc.prod ((isCompact_closedBall _ _).diff Metric.isOpen_ball)
  have hdiff : ∀ p ∈ Cs, DifferentiableAt ℝ F p := fun p hp => by
    obtain ⟨U, hU, hd, -⟩ := hF p hp
    exact hd p (mem_of_mem_nhds hU)
  have hloc : LocallyLipschitzOn Cs (fderiv ℝ F) := by
    intro p hp
    obtain ⟨U, hU, -, K, hK⟩ := hF p hp
    exact ⟨K, U, mem_nhdsWithin_of_mem_nhds hU, hK⟩
  obtain ⟨L, hL⟩ := hloc.exists_lipschitzOnWith_of_compact hCc
  obtain ⟨M, hM⟩ := hCc.exists_bound_of_continuousOn hL.continuousOn
  obtain ⟨N, hN⟩ := hCc.exists_bound_of_continuousOn
    (fun p hp => (hdiff p hp).continuousAt.continuousWithinAt : ContinuousOn F Cs)
  have hM0 : 0 ≤ M := by
    have h := hM (0, EuclideanSpace.single 0 1) ⟨⟨le_rfl, hρ.le⟩, by
      simp [Metric.mem_closedBall, Metric.mem_ball]; norm_num⟩
    exact (norm_nonneg _).trans h
  have hN0 : 0 ≤ N := by
    have h := hN (0, EuclideanSpace.single 0 1) ⟨⟨le_rfl, hρ.le⟩, by
      simp [Metric.mem_closedBall, Metric.mem_ball]; norm_num⟩
    exact (norm_nonneg _).trans h
  have memC : ∀ s w, 0 < s → s ≤ ρ → 1 / 2 * s ≤ ‖w‖ → ‖w‖ ≤ s → (s, s⁻¹ • w) ∈ Cs := by
    intro s w hs hsρ h1 h2
    refine ⟨⟨hs.le, hsρ⟩, ?_, ?_⟩
    · rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hs)]
      rw [inv_mul_le_iff₀ hs]
      linarith
    · rw [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hs), not_lt]
      rw [le_inv_mul_iff₀ hs]
      linarith
  have hval : ∀ h : Space, ‖h‖ < ρ → ‖f h‖ ≤ N * ‖h‖ ^ 2 := by
    intro h hh
    by_cases h0 : h = 0
    · simp [h0, hf0]
    have hs : 0 < ‖h‖ := norm_pos_iff.2 h0
    have e := hscale ‖h‖ hs (‖h‖⁻¹ • h) (smul_ne_zero (inv_ne_zero hs.ne') h0)
    rw [smul_inv_smul₀ hs.ne'] at e
    rw [e, norm_smul, norm_pow, Real.norm_eq_abs, abs_of_pos hs, mul_comm]
    exact mul_le_mul_of_nonneg_right (hN _ (memC _ _ hs hh.le (by linarith) le_rfl)) (by positivity)
  have hd0 : HasFDerivAt f (0 : Space →L[ℝ] G) 0 := by
    rw [hasFDerivAt_iff_isLittleO_nhds_zero]
    have hbig : (fun h : Space => f (0 + h) - f 0 - (0 : Space →L[ℝ] G) h) =O[nhds 0] fun h => ‖h‖ ^ 2 := by
      refine Asymptotics.IsBigO.of_bound N ?_
      filter_upwards [Metric.ball_mem_nhds (0 : Space) hρ] with h hh
      rw [Metric.mem_ball, dist_zero_right] at hh
      simp only [zero_add, hf0, sub_zero, zero_apply, norm_pow, norm_norm]
      exact hval h hh
    exact hbig.trans_isLittleO (Asymptotics.isLittleO_norm_pow_id (by norm_num))
  have hat : ∀ s w, 0 < s → s ≤ ρ → 1 / 2 * s ≤ ‖w‖ → ‖w‖ ≤ s →
      fderiv ℝ f w = (s ^ 2) • (fderiv ℝ F (s, s⁻¹ • w)).comp
        ((0 : Space →L[ℝ] ℝ).prod (s⁻¹ • ContinuousLinearMap.id ℝ Space)) := by
    intro s w hs hsρ h1 h2
    have hw : w ≠ 0 := by
      intro h; rw [h, norm_zero] at h1; linarith
    exact (scaled_hasFDerivAt hscale hs hw (hdiff _ (memC s w hs hsρ h1 h2))).fderiv
  have hbound : ∀ w, ‖w‖ < ρ → ‖fderiv ℝ f w‖ ≤ M * ‖w‖ := by
    intro w hw
    by_cases h0 : w = 0
    · rw [h0, hd0.fderiv]; simp
    have hs : 0 < ‖w‖ := norm_pos_iff.2 h0
    rw [hat ‖w‖ w hs hw.le (by linarith) le_rfl, norm_smul, norm_pow, Real.norm_eq_abs, abs_of_pos hs]
    calc ‖w‖ ^ 2 * ‖(fderiv ℝ F (‖w‖, ‖w‖⁻¹ • w)).comp
          ((0 : Space →L[ℝ] ℝ).prod (‖w‖⁻¹ • ContinuousLinearMap.id ℝ Space))‖
        ≤ ‖w‖ ^ 2 * (M * ‖w‖⁻¹) := by
          gcongr
          refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
          exact mul_le_mul (hM _ (memC _ _ hs hw.le (by linarith) le_rfl)) (scaleT_norm _ hs) (norm_nonneg _) hM0
      _ = M * ‖w‖ := by field_simp
  have key : ∀ y z, ‖y‖ < ρ → ‖z‖ ≤ ‖y‖ → ‖fderiv ℝ f y - fderiv ℝ f z‖ ≤ (L + 4 * M) * ‖y - z‖ := by
    intro y z hy hzy
    by_cases hfar : ‖y‖ ≤ 2 * ‖y - z‖
    · calc ‖fderiv ℝ f y - fderiv ℝ f z‖ ≤ ‖fderiv ℝ f y‖ + ‖fderiv ℝ f z‖ := norm_sub_le _ _
        _ ≤ M * ‖y‖ + M * ‖z‖ := add_le_add (hbound y hy) (hbound z (lt_of_le_of_lt hzy hy))
        _ ≤ 4 * M * ‖y - z‖ := by nlinarith
        _ ≤ (L + 4 * M) * ‖y - z‖ := by gcongr; simp
    · push Not at hfar
      have hs : 0 < ‖y‖ := by have := norm_nonneg (y - z); linarith
      have hz1 : 1 / 2 * ‖y‖ ≤ ‖z‖ := by
        have := norm_sub_norm_le y z
        linarith
      rw [hat ‖y‖ y hs hy.le (by linarith) le_rfl, hat ‖y‖ z hs hy.le hz1 hzy, ← smul_sub,
        ← ContinuousLinearMap.sub_comp, norm_smul, norm_pow, Real.norm_eq_abs, abs_of_pos hs]
      have hyC := memC _ y hs hy.le (by linarith) le_rfl
      have hzC := memC _ z hs hy.le hz1 hzy
      have hLd := hL.dist_le_mul _ hyC _ hzC
      rw [dist_eq_norm, dist_eq_norm, Prod.mk_sub_mk, sub_self, Prod.norm_def, norm_zero, ← smul_sub,
        norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hs)] at hLd
      have hmax : max 0 (‖y‖⁻¹ * ‖y - z‖) = ‖y‖⁻¹ * ‖y - z‖ := max_eq_right (by positivity)
      rw [hmax] at hLd
      calc ‖y‖ ^ 2 * ‖(fderiv ℝ F (‖y‖, ‖y‖⁻¹ • y) - fderiv ℝ F (‖y‖, ‖y‖⁻¹ • z)).comp
            ((0 : Space →L[ℝ] ℝ).prod (‖y‖⁻¹ • ContinuousLinearMap.id ℝ Space))‖
          ≤ ‖y‖ ^ 2 * ((L * (‖y‖⁻¹ * ‖y - z‖)) * ‖y‖⁻¹) := by
            gcongr
            exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
              (mul_le_mul hLd (scaleT_norm _ hs) (norm_nonneg _) (by positivity))
        _ = L * ‖y - z‖ := by field_simp
        _ ≤ (L + 4 * M) * ‖y - z‖ := by gcongr; linarith
  refine ⟨hd0, max N M, fun y hy => ⟨?_, ?_, ?_⟩, Real.toNNReal (L + 4 * M),
    LipschitzOnWith.of_dist_le' fun y hy z hz => ?_⟩
  · rw [Metric.mem_ball, dist_zero_right] at hy
    by_cases h0 : y = 0
    · rw [h0]; exact hd0.differentiableAt
    have hs : 0 < ‖y‖ := norm_pos_iff.2 h0
    exact (scaled_hasFDerivAt hscale hs h0 (hdiff _ (memC _ y hs hy.le (by linarith) le_rfl))).differentiableAt
  · rw [Metric.mem_ball, dist_zero_right] at hy
    exact (hval y hy).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
  · rw [Metric.mem_ball, dist_zero_right] at hy
    exact (hbound y hy).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _))
  · rw [Metric.mem_ball, dist_zero_right] at hy hz
    rw [dist_eq_norm, dist_eq_norm]
    rcases le_total ‖z‖ ‖y‖ with h | h
    · exact key y z hy h
    · rw [← norm_neg, neg_sub, ← norm_neg (y - z), neg_sub]
      exact key z y hz h

theorem typeOneKey_origin_bounds (hsm : JoinedSplineSmooth) (hsl : JoinedSplineGradSlopeBound)
    (hsd : SplineDerivatives) (P : ShapeParams) (D : TimeFieldData) (κ : FieldKey) (σ : ℝ)
    (hP : IsShapeParams P) (hD : IsTimeFieldData D) (hκ : κ ∈ D.keys) (h1 : κ.label.1 ≠ 0) :
    HasFDerivAt (keyVector P κ (D.amp κ) σ) (0 : Space →L[ℝ] (Fin 3 → ℂ)) 0 ∧
      ∃ δ > 0, ∃ C : ℝ, ∃ L : NNReal, (∀ y ∈ Metric.closedBall (0 : Space) δ,
        DifferentiableAt ℝ (keyVector P κ (D.amp κ) σ) y ∧ ‖keyVector P κ (D.amp κ) σ y‖ ≤ C * ‖y‖ ^ 2 ∧
          ‖fderiv ℝ (keyVector P κ (D.amp κ) σ) y‖ ≤ C * ‖y‖) ∧
        LipschitzOnWith L (fderiv ℝ (keyVector P κ (D.amp κ) σ)) (Metric.closedBall 0 δ) := by
  obtain ⟨H, hH, hRK⟩ := typeOne_factor hsm hsl hsd hP hD hκ h1
  have hf0 : keyVector P κ (D.amp κ) σ 0 = 0 := by
    funext i
    have h0 : chartCoord P 0 = 0 := by simp [chartCoord]
    simp only [keyVector, hRK, h0]
    simp
  have hsc : ∀ s : ℝ, 0 < s → ∀ v : Space, v ≠ 0 →
      keyVector P κ (D.amp κ) σ (s • v) = (s ^ 2) • scaledKey P κ σ H (s, v) := by
    intro s hs v hv
    have hsv : s • v ≠ 0 := smul_ne_zero hs.ne' hv
    have hnorm : ‖s • v‖ = s * ‖v‖ := by rw [norm_smul, Real.norm_of_nonneg hs.le]
    have hdir : ‖s • v‖⁻¹ • (s • v) = ‖v‖⁻¹ • v := by
      rw [hnorm, smul_smul, mul_inv_rev, mul_assoc, inv_mul_cancel₀ hs.ne', mul_one]
    funext i
    rw [keyVector_near_eq hP κ (D.amp κ) σ H hRK _ hsv i, hdir, hnorm, planeOf_smul,
      planeMap_scale _ hs]
    simp only [scaledKey, Pi.smul_apply, Complex.real_smul]
    ring
  have htame : ∀ p : ℝ × Space, 0 ≤ p.1 → p.2 ≠ 0 → TameAt (scaledKey P κ σ H) p := by
    intro p hp1 hp2
    have hn' : ContDiffAt ℝ ⊤ (fun q : ℝ × Space => ‖q.2‖) p := (contDiffAt_norm ℝ hp2).comp p contDiffAt_snd
    have hΛ : ContDiffAt ℝ ⊤ (fun q : ℝ × Space => (q.1 * ‖q.2‖, ‖q.2‖⁻¹ • q.2)) p :=
      (contDiffAt_fst.mul hn').prodMk ((hn'.inv (norm_ne_zero_iff.2 hp2)).smul contDiffAt_snd)
    have hpl : ContDiffAt ℝ ⊤ (fun q : ℝ × Space => planeOf q.2) p :=
      planeOf_contDiff.contDiffAt.comp p contDiffAt_snd
    have hA : TameAt (fun q : ℝ × Space => planeMap (labelAzimuth P.azimuthOrder κ.label) (planeOf q.2)) p :=
      tame_comp (g := planeMap (labelAzimuth P.azimuthOrder κ.label)) (Φ := fun q : ℝ × Space => planeOf q.2)
        (tame_of_global ((planePhase_contDiff _).differentiable (by norm_num)) (planePhase_fderiv_localSlope _) _)
        (tame_of_contDiffAt (hpl.of_le le_top))
    refine tame_pi fun i => ?_
    exact tame_mul hA (tame_comp (g := fun z => nearOriginProfile P κ σ H z i)
      (Φ := fun q : ℝ × Space => (q.1 * ‖q.2‖, ‖q.2‖⁻¹ • q.2))
      (nearOriginProfile_tame hP κ σ H hH i _ (mul_nonneg hp1 (norm_nonneg _)))
      (tame_of_contDiffAt (hΛ.of_le le_top)))
  obtain ⟨hd0, C, hC, K, hK⟩ := scaled_origin (F := scaledKey P κ σ H) one_pos hf0 hsc
    (fun p hp => tame_region (htame p hp.1.1 (by
      intro h
      apply hp.2.2
      rw [h]
      exact Metric.mem_ball_self (by norm_num))))
  have hsub : Metric.closedBall (0 : Space) (1 / 2) ⊆ Metric.ball 0 1 :=
    Metric.closedBall_subset_ball (by norm_num)
  exact ⟨hd0, 1 / 2, by norm_num, C, K, fun y hy => hC y (hsub hy), hK.mono hsub⟩

theorem typeOneKey_origin (hsm : JoinedSplineSmooth) (hsl : JoinedSplineGradSlopeBound)
    (hsd : SplineDerivatives) (P : ShapeParams) (D : TimeFieldData) (κ : FieldKey) (σ : ℝ)
    (hP : IsShapeParams P) (hD : IsTimeFieldData D) (hκ : κ ∈ D.keys) (h1 : κ.label.1 ≠ 0) :
    DifferentiableAt ℝ (keyVector P κ (D.amp κ) σ) 0 ∧ ∃ δ > 0, ∃ L : NNReal,
      LipschitzOnWith L (fderiv ℝ (keyVector P κ (D.amp κ) σ)) (Metric.closedBall 0 δ) := by
  obtain ⟨hd0, δ, hδ, -, L, -, hL⟩ := typeOneKey_origin_bounds hsm hsl hsd P D κ σ hP hD hκ h1
  exact ⟨hd0.differentiableAt, δ, hδ, L, hL⟩

end GivenShape

end CertCell

end Breakdown
