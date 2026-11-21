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

namespace AtomSlopeFarInternal

open AtomAxisInternal

theorem dvd_sub_atFirst (P : MvPolynomial (Fin 2) ℂ) :
    (MvPolynomial.X 0 - 1 : MvPolynomial (Fin 2) ℂ) ∣ P - atFirst 1 P := by
  induction P using MvPolynomial.induction_on with
  | C a => simp [atFirst]
  | add p q hp hq =>
    have e : atFirst 1 (p + q) = atFirst 1 p + atFirst 1 q := by simp [atFirst, map_add]
    rw [e, show p + q - (atFirst 1 p + atFirst 1 q) = (p - atFirst 1 p) + (q - atFirst 1 q) by ring]
    exact dvd_add hp hq
  | mul_X p n hp =>
    have e : atFirst 1 (p * MvPolynomial.X n) =
        atFirst 1 p * (if n = 0 then MvPolynomial.C 1 else MvPolynomial.X 1) := by
      simp [atFirst, map_mul, MvPolynomial.bind₁_X_right]
    rw [e]
    fin_cases n
    · simp only [Fin.zero_eta, Fin.isValue, if_true, map_one]
      rw [show p * MvPolynomial.X 0 - atFirst 1 p * 1 =
        (p - atFirst 1 p) * MvPolynomial.X 0 + atFirst 1 p * (MvPolynomial.X 0 - 1) by ring]
      exact dvd_add (dvd_mul_of_dvd_left hp _) (dvd_mul_left _ _)
    · simp only [Fin.mk_one, Fin.isValue]
      rw [if_neg (by decide)]
      rw [show p * MvPolynomial.X 1 - atFirst 1 p * MvPolynomial.X 1 = (p - atFirst 1 p) * MvPolynomial.X 1 by ring]
      exact dvd_mul_of_dvd_left hp _

theorem factor_one (P : MvPolynomial (Fin 2) ℂ) (h : atFirst 1 P = 0) :
    ∃ Q, P = (1 - MvPolynomial.X 0) * Q := by
  obtain ⟨Q, hQ⟩ := dvd_sub_atFirst P
  rw [h, sub_zero] at hQ
  exact ⟨-Q, by rw [hQ]; ring⟩

theorem atFirst_one_sub_X0 : atFirst 1 (1 - MvPolynomial.X 0 : MvPolynomial (Fin 2) ℂ) = 0 := by
  simp [atFirst, MvPolynomial.bind₁_X_right]

theorem factor_two (P : MvPolynomial (Fin 2) ℂ) (h0 : atFirst 1 P = 0) (h1 : atFirst 1 (tDeriv 1 P) = 0) :
    ∃ Q, P = (1 - MvPolynomial.X 0) ^ 2 * Q := by
  obtain ⟨R, hR⟩ := factor_one P h0
  have hd : tDeriv 1 P = -R + (1 - MvPolynomial.X 0) * MvPolynomial.pderiv 0 R := by
    rw [hR]
    simp only [tDeriv, Function.iterate_one, Derivation.leibniz, smul_eq_mul, map_sub,
      MvPolynomial.pderiv_X_self, Derivation.map_one_eq_zero]
    ring
  have e : atFirst 1 (-R + (1 - MvPolynomial.X 0) * MvPolynomial.pderiv 0 R) = -atFirst 1 R := by
    simp [atFirst, map_add, map_mul, MvPolynomial.bind₁_X_right]
  rw [hd, e, neg_eq_zero] at h1
  obtain ⟨Q, hQ⟩ := factor_one R h1
  exact ⟨Q, by rw [hR, hQ]; ring⟩

open Classical in
def quot2 (P : MvPolynomial (Fin 2) ℂ) : MvPolynomial (Fin 2) ℂ :=
  if h : ∃ Q, P = (1 - MvPolynomial.X 0) ^ 2 * Q then h.choose else 0

theorem quot2_spec (P : MvPolynomial (Fin 2) ℂ) (h0 : atFirst 1 P = 0) (h1 : atFirst 1 (tDeriv 1 P) = 0) :
    P = (1 - MvPolynomial.X 0) ^ 2 * quot2 P := by
  have h := factor_two P h0 h1
  unfold quot2
  rw [dif_pos h]
  exact h.choose_spec

theorem sq_ne : ((1 - MvPolynomial.X 0) ^ 2 : MvPolynomial (Fin 2) ℂ) ≠ 0 := by
  intro h
  have := congrArg (MvPolynomial.eval (fun _ : Fin 2 => (0 : ℂ))) h
  simp at this

theorem xDeriv_mul_left (F Q : MvPolynomial (Fin 2) ℂ) (hF : MvPolynomial.pderiv 1 F = 0) (o : ℕ) :
    xDeriv o (F * Q) = F * xDeriv o Q := by
  induction o with
  | zero => simp [xDeriv]
  | succ o ih =>
    simp only [xDeriv, Function.iterate_succ_apply'] at ih ⊢
    rw [ih, Derivation.leibniz, hF]
    simp [smul_eq_mul]

theorem pderiv_sq : MvPolynomial.pderiv 1 ((1 - MvPolynomial.X 0) ^ 2 : MvPolynomial (Fin 2) ℂ) = 0 := by
  simp [MvPolynomial.pderiv_X]

theorem atSecond_sq_mul (c : ℂ) (Q : MvPolynomial (Fin 2) ℂ) :
    atSecond c ((1 - MvPolynomial.X 0) ^ 2 * Q) = (1 - MvPolynomial.X 0) ^ 2 * atSecond c Q := by
  simp [atSecond, map_mul, MvPolynomial.bind₁_X_right]

def lastRow (T : Spline) : Spline :=
  ⟨⟨[0, 1], T.mesh.xBreaks⟩, fun _ j => quot2 (T.piece (atomLastT T) j)⟩

def AtInfinity (T : Spline) : Prop :=
  ∀ j < cellCount T.mesh.xBreaks, atFirst 1 (T.piece (atomLastT T) j) = 0 ∧
    atFirst 1 (tDeriv 1 (T.piece (atomLastT T) j)) = 0

theorem lastRow_class {odd : Bool} {T : Spline} (hT : IsSplineClass 1 1 odd T) (hinf : AtInfinity T) :
    IsSplineClass 1 1 odd (lastRow T) := by
  have hm := hT.mesh
  have ht2 := length_two _ hm.t_first hm.t_last
  have hlast : atomLastT T < cellCount T.mesh.tBreaks := by unfold atomLastT cellCount; omega
  have spec : ∀ j < cellCount T.mesh.xBreaks,
      T.piece (atomLastT T) j = (1 - MvPolynomial.X 0) ^ 2 * quot2 (T.piece (atomLastT T) j) :=
    fun j hj => quot2_spec _ (hinf j hj).1 (hinf j hj).2
  refine ⟨⟨by simp [lastRow], hm.x_sorted, rfl, by simp [lastRow], hm.x_first, hm.x_last⟩, ?_, ?_, ?_⟩
  · intro i hi1 hi
    simp [lastRow, cellCount] at hi
    omega
  · intro j hj1 hj i _ o ho
    change j < cellCount T.mesh.xBreaks at hj
    have h := hT.x_joins j hj1 hj (atomLastT T) hlast o ho
    rw [spec (j - 1) (by omega), spec j hj, xDeriv_mul_left _ _ pderiv_sq, xDeriv_mul_left _ _ pderiv_sq,
      atSecond_sq_mul, atSecond_sq_mul] at h
    exact mul_left_cancel₀ sq_ne h
  · intro i _ o ho hev
    have hx2 := length_two _ hm.x_first hm.x_last
    have h := hT.parity (atomLastT T) hlast o ho hev
    rw [spec 0 (by unfold cellCount; omega), xDeriv_mul_left _ _ pderiv_sq, atSecond_sq_mul] at h
    exact (mul_eq_zero.1 h).resolve_left sq_ne

theorem lastRow_cell (u : ℝ) : cellIndex [0, 1] u = 0 := by
  simp [cellIndex]

theorem lastRow_eval {odd : Bool} {T : Spline} (hT : IsSplineClass 1 1 odd T) (hinf : AtInfinity T) (t x : ℝ)
    (ht : ∀ b ∈ (T.mesh.tBreaks.drop 1).dropLast, b ≤ t) :
    T.eval odd t x = (((1 - t) ^ 2 : ℝ) : ℂ) * (lastRow T).eval odd t x := by
  have hm := hT.mesh
  have hx2 := length_two _ hm.x_first hm.x_last
  have hci : cellIndex T.mesh.tBreaks t = atomLastT T := cellIndex_top _ _ ht
  have hxi := cellIndex_lt T.mesh.xBreaks |x| hx2
  unfold Spline.eval Spline.evalHalf
  rw [hci, quot2_spec _ (hinf _ hxi).1 (hinf _ hxi).2]
  simp only [lastRow, lastRow_cell, map_mul, map_pow, map_sub, map_one, MvPolynomial.eval_X]
  simp
  try ring

end AtomSlopeFarInternal

namespace AtomSlopeFarInternal

open AtomAxisInternal

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

theorem tame_global {f : E → F} (hd : ContDiff ℝ 1 f) (hl : LocallyLipschitz (fderiv ℝ f)) (y : E) :
    TameAt f y := by
  obtain ⟨K, t, ht, hK⟩ := hl y
  obtain ⟨r, hr, hsub⟩ := Metric.mem_nhds_iff.1 ht
  refine ⟨r, hr, fderiv ℝ f, K, K.2, fun z _ => (hd.differentiable (by norm_num) z).hasFDerivAt,
    fun z hz w hw => ?_⟩
  have := hK.dist_le_mul z (hsub hz) w (hsub hw)
  rwa [dist_eq_norm, dist_eq_norm] at this

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

theorem tame_region {f : E → F} {y : E} (h : TameAt f y) :
    ∃ U ∈ nhds y, (∀ q ∈ U, DifferentiableAt ℝ f q) ∧ ∃ K : NNReal, LipschitzOnWith K (fderiv ℝ f) U := by
  obtain ⟨r, hr, f', K, hK0, h1, h2⟩ := h
  refine ⟨Metric.ball y r, Metric.ball_mem_nhds y hr, fun z hz => (h1 z hz).differentiableAt, ⟨K, hK0⟩,
    LipschitzOnWith.of_dist_le_mul fun z hz w hw => ?_⟩
  rw [(h1 z hz).fderiv, (h1 w hw).fderiv, dist_eq_norm, dist_eq_norm]
  exact h2 z hz w hw

end Tame

def pmap (k : ℤ) (w : ℂ) : ℂ := ((‖w‖ ^ 2 : ℝ) : ℂ) * Complex.exp (Complex.I * (((k : ℝ) * Complex.arg w : ℝ) : ℂ))

theorem pmap_tame (k : ℤ) (w : ℂ) : TameAt (pmap k) w :=
  tame_global (planePhase_contDiff k) (planePhase_fderiv_localSlope k) w

theorem spline_tame {odd : Bool} {G : Spline} (hG : IsSplineClass 1 1 odd G) (q : ℝ × ℝ) :
    TameAt (fun p : ℝ × ℝ => G.eval odd p.1 p.2) q :=
  tame_global (spline_eval_contDiff G hG le_rfl le_rfl) (spline_eval_localSlope G hG le_rfl le_rfl) q

theorem atInf_of_atom {odd : Bool} {S : Spline} {j : ℕ} (hS : IsAtomSpline odd S j) : AtInfinity S :=
  fun k hk => hS.at_infinity k hk

theorem atInf_quot {odd : Bool} {S : Spline} {j : ℕ} (hS : IsAtomSpline odd S j) (hj : j ≠ 0) :
    AtInfinity (quotSpline S) := by
  have hm := hS.spline.mesh
  have ht2 := length_two _ hm.t_first hm.t_last
  have hx2 := length_two _ hm.x_first hm.x_last
  have hlastT : atomLastT S < cellCount S.mesh.tBreaks := by unfold atomLastT cellCount; omega
  have hlastX : atomLastX S < cellCount S.mesh.xBreaks := by unfold atomLastX cellCount; omega
  intro k _
  have hf := piece_factor hS hj (atomLastT S) hlastT
  obtain ⟨h0, h1⟩ := hS.at_infinity (atomLastX S) hlastX
  rw [hf, atFirst_mul, atFirst_one_sub] at h0
  rw [hf, tDeriv_mul_left _ _ pderiv_one_sub, atFirst_mul, atFirst_one_sub] at h1
  have q0 := (mul_eq_zero.1 h0).resolve_left one_sub_ne
  have q1 := (mul_eq_zero.1 h1).resolve_left one_sub_ne
  change atFirst 1 (MvPolynomial.X 1 * quotPiece S (atomLastT S)) = 0 ∧
    atFirst 1 (tDeriv 1 (MvPolynomial.X 1 * quotPiece S (atomLastT S))) = 0
  rw [tDeriv_mul_left _ _ pderiv_X_one, atFirst_mul, atFirst_mul, q0, q1]
  simp

theorem axis_half {odd : Bool} {S : Spline} {j : ℕ} (hS : IsAtomSpline odd S j) (hj : j ≠ 0) (t X : ℝ)
    (hX : 0 < X) (hall : ∀ b ∈ (S.mesh.xBreaks.drop 1).dropLast, b ≤ X) :
    (X : ℂ) * (lastRow S).evalHalf t X = (1 - (X : ℂ)) * (lastRow (quotSpline S)).eval true t X := by
  have hm := hS.spline.mesh
  have ht2 := length_two _ hm.t_first hm.t_last
  have hx2 := length_two _ hm.x_first hm.x_last
  have hlastT : atomLastT S < cellCount S.mesh.tBreaks := by unfold atomLastT cellCount; omega
  have hlastX : atomLastX S < cellCount S.mesh.xBreaks := by unfold atomLastX cellCount; omega
  have hci : cellIndex S.mesh.xBreaks X = atomLastX S := cellIndex_top _ _ hall
  have hinf := atInf_quot hS hj 0 (by simp [quotSpline, cellCount])
  have sp1 := quot2_spec _ (hS.at_infinity _ hlastX).1 (hS.at_infinity _ hlastX).2
  have sp2 := quot2_spec _ hinf.1 hinf.2
  have hf := piece_factor hS hj (atomLastT S) hlastT
  have key : MvPolynomial.X 1 * quot2 (S.piece (atomLastT S) (atomLastX S)) =
      (1 - MvPolynomial.X 1) * quot2 ((quotSpline S).piece (atomLastT (quotSpline S)) 0) := by
    apply mul_left_cancel₀ sq_ne
    have e2 : (quotSpline S).piece (atomLastT (quotSpline S)) 0 = MvPolynomial.X 1 * quotPiece S (atomLastT S) := rfl
    calc (1 - MvPolynomial.X 0) ^ 2 * (MvPolynomial.X 1 * quot2 (S.piece (atomLastT S) (atomLastX S)))
        = MvPolynomial.X 1 * ((1 - MvPolynomial.X 0) ^ 2 * quot2 (S.piece (atomLastT S) (atomLastX S))) := by ring
      _ = MvPolynomial.X 1 * S.piece (atomLastT S) (atomLastX S) := by rw [← sp1]
      _ = (1 - MvPolynomial.X 1) * (quotSpline S).piece (atomLastT (quotSpline S)) 0 := by rw [hf, e2]; ring
      _ = (1 - MvPolynomial.X 1) * ((1 - MvPolynomial.X 0) ^ 2 *
            quot2 ((quotSpline S).piece (atomLastT (quotSpline S)) 0)) := by rw [← sp2]
      _ = _ := by ring
  have hev := congrArg (MvPolynomial.eval ![(t : ℂ), (X : ℂ)]) key
  have hnx : ¬ X < 0 := not_lt.2 hX.le
  simp only [map_mul, map_sub, map_one, MvPolynomial.eval_X] at hev
  simp only [Spline.eval, Spline.evalHalf, lastRow, lastRow_cell, hnx, decide_false, Bool.and_false,
    abs_of_pos hX, hci]
  have c0 : cellIndex (quotSpline S).mesh.xBreaks X = 0 := lastRow_cell X
  simp only [c0]
  simpa using hev

end AtomSlopeFarInternal

namespace AtomSlopeFarInternal

open AtomAxisInternal

theorem sqrt_q (z : Space) (hz : z ≠ 0) : Real.sqrt (qOf z) = ‖planeW z‖ * ‖z‖⁻¹ := by
  have hn : 0 < ‖z‖ := norm_pos_iff.2 hz
  have hsq := norm_sq_split z
  have e2 : qOf z = (‖planeW z‖ * ‖z‖⁻¹) ^ 2 := by
    unfold qOf heightRatio
    field_simp
    linear_combination hsq
  rw [e2, Real.sqrt_sq (by positivity)]

def Yf (a : ℕ) (M : ℤ) (S : Spline) (p : ℝ × Space) : ℂ :=
  Complex.exp (Complex.I * (((M : ℝ) * angleOf p.2 : ℝ) : ℂ)) * ((Real.sqrt (qOf p.2) ^ a : ℝ) : ℂ) *
    (lastRow S).eval (decide (a = 0)) p.1 (heightRatio p.2)

theorem cd_norm {p0 : ℝ × Space} (h : p0.2 ≠ 0) : ContDiffAt ℝ 2 (fun p : ℝ × Space => ‖p.2‖) p0 :=
  (contDiffAt_norm ℝ h).comp p0 contDiffAt_snd

theorem cd_coord (i : Fin 3) (p0 : ℝ × Space) : ContDiffAt ℝ 2 (fun p : ℝ × Space => p.2 i) p0 :=
  ((EuclideanSpace.proj i : Space →L[ℝ] ℝ).contDiff.comp contDiff_snd).contDiffAt

theorem cd_height {p0 : ℝ × Space} (h : p0.2 ≠ 0) : ContDiffAt ℝ 2 (fun p : ℝ × Space => heightRatio p.2) p0 :=
  (cd_coord 2 p0).div (cd_norm h) (norm_ne_zero_iff.2 h)

theorem cd_plane (p0 : ℝ × Space) : ContDiffAt ℝ 2 (fun p : ℝ × Space => planeW p.2) p0 :=
  ((planeW_contDiff.of_le le_top).comp contDiff_snd).contDiffAt

theorem cd_ofReal {f : ℝ × Space → ℝ} {p0 : ℝ × Space} (h : ContDiffAt ℝ 2 f p0) :
    ContDiffAt ℝ 2 (fun p => (f p : ℂ)) p0 :=
  Complex.ofRealCLM.contDiff.contDiffAt.comp p0 h

theorem tame_spline_comp {odd : Bool} {G : Spline} (hG : IsSplineClass 1 1 odd G) {f g : ℝ × Space → ℝ}
    {p0 : ℝ × Space} (hf : ContDiffAt ℝ 2 f p0) (hg : ContDiffAt ℝ 2 g p0) :
    TameAt (fun p => G.eval odd (f p) (g p)) p0 :=
  tame_comp (g := fun q : ℝ × ℝ => G.eval odd q.1 q.2) (Φ := fun p => (f p, g p)) (spline_tame hG _)
    (tame_of_contDiffAt (hf.prodMk hg))

theorem ne_of_plane {z : Space} (hw : planeW z ≠ 0) : z ≠ 0 := by
  rintro rfl
  apply hw
  apply Complex.ext <;> simp [planeW]

theorem Y_off (a : ℕ) (M : ℤ) (S : Spline) (p : ℝ × Space) (hw : planeW p.2 ≠ 0) :
    Yf a M S p = pmap M (planeW p.2) * (((‖planeW p.2‖ ^ a * ((‖planeW p.2‖ ^ 2)⁻¹ * (‖p.2‖ ^ a)⁻¹)) : ℝ) : ℂ) *
      (lastRow S).eval (decide (a = 0)) p.1 (heightRatio p.2) := by
  have hz := ne_of_plane hw
  have hn : ((‖planeW p.2‖ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (norm_ne_zero_iff.2 hw)
  have hzn : ((‖p.2‖ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (norm_ne_zero_iff.2 hz)
  have ha : angleOf p.2 = Complex.arg (planeW p.2) := rfl
  unfold Yf pmap
  rw [sqrt_q p.2 hz, ha]
  push_cast
  rw [mul_pow, inv_pow]
  field_simp

theorem Y_tame_off {a : ℕ} {M : ℤ} {S : Spline} (hG : IsSplineClass 1 1 (decide (a = 0)) (lastRow S))
    (p0 : ℝ × Space) (hw : planeW p0.2 ≠ 0) : TameAt (Yf a M S) p0 := by
  have hz := ne_of_plane hw
  have hev : Yf a M S =ᶠ[𝓝 p0] fun p => pmap M (planeW p.2) *
      (((‖planeW p.2‖ ^ a * ((‖planeW p.2‖ ^ 2)⁻¹ * (‖p.2‖ ^ a)⁻¹)) : ℝ) : ℂ) *
      (lastRow S).eval (decide (a = 0)) p.1 (heightRatio p.2) := by
    have : ∀ᶠ p in 𝓝 p0, planeW p.2 ≠ 0 := (cd_plane p0).continuousAt.eventually_ne hw
    filter_upwards [this] with p hp
    exact Y_off a M S p hp
  refine tame_congr ?_ hev
  have hnw : ContDiffAt ℝ 2 (fun p : ℝ × Space => ‖planeW p.2‖) p0 := (contDiffAt_norm ℝ hw).comp p0 (cd_plane p0)
  have hr : ContDiffAt ℝ 2 (fun p : ℝ × Space => ‖planeW p.2‖ ^ a * ((‖planeW p.2‖ ^ 2)⁻¹ * (‖p.2‖ ^ a)⁻¹)) p0 :=
    (hnw.pow a).mul (((hnw.pow 2).inv (pow_ne_zero _ (norm_ne_zero_iff.2 hw))).mul
      (((cd_norm hz).pow a).inv (pow_ne_zero _ (norm_ne_zero_iff.2 hz))))
  exact tame_mul (tame_mul (tame_comp (g := pmap M) (Φ := fun p : ℝ × Space => planeW p.2) (pmap_tame M _)
    (tame_of_contDiffAt (cd_plane p0))) (tame_of_contDiffAt (cd_ofReal hr)))
    (tame_spline_comp hG contDiffAt_fst (cd_height hz))

theorem Y_plus (S : Spline) (p : ℝ × Space) (hz : p.2 ≠ 0) :
    Yf 1 1 S p = planeW p.2 * ((‖p.2‖⁻¹ : ℝ) : ℂ) * (lastRow S).eval (decide ((1 : ℕ) = 0)) p.1 (heightRatio p.2) := by
  unfold Yf
  rw [sqrt_q p.2 hz]
  have ha : angleOf p.2 = Complex.arg (planeW p.2) := rfl
  have e := Complex.norm_mul_exp_arg_mul_I (planeW p.2)
  have e2 : Complex.I * ((((1 : ℤ) : ℝ) * angleOf p.2 : ℝ) : ℂ) = (Complex.arg (planeW p.2) : ℂ) * Complex.I := by
    rw [ha]; push_cast; ring
  rw [e2]
  conv_rhs => rw [← e]
  push_cast
  ring

theorem Y_minus (S : Spline) (p : ℝ × Space) (hz : p.2 ≠ 0) :
    Yf 1 (-1) S p = Complex.conjCLE (planeW p.2) * ((‖p.2‖⁻¹ : ℝ) : ℂ) *
      (lastRow S).eval (decide ((1 : ℕ) = 0)) p.1 (heightRatio p.2) := by
  unfold Yf
  rw [sqrt_q p.2 hz, Complex.conjCLE_apply]
  have ha : angleOf p.2 = Complex.arg (planeW p.2) := rfl
  have e : (starRingEnd ℂ) (planeW p.2) =
      ((‖planeW p.2‖ : ℝ) : ℂ) * Complex.exp (-((Complex.arg (planeW p.2) : ℂ) * Complex.I)) := by
    conv_lhs => rw [← Complex.norm_mul_exp_arg_mul_I (planeW p.2)]
    rw [map_mul, Complex.conj_ofReal, ← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I,
      show (Complex.arg (planeW p.2) : ℂ) * -Complex.I = -((Complex.arg (planeW p.2) : ℂ) * Complex.I) by ring]
  have e2 : Complex.I * ((((-1 : ℤ) : ℝ) * angleOf p.2 : ℝ) : ℂ) = -((Complex.arg (planeW p.2) : ℂ) * Complex.I) := by
    rw [ha]; push_cast; ring
  rw [e2, e]
  push_cast
  ring

def Kf (a : ℕ) (sg : ℝ) (z : Space) : ℝ :=
  (‖z‖ ^ a)⁻¹ * (‖z‖ * (‖z‖ + sg * z 2))⁻¹ * (sg * heightRatio z)⁻¹

theorem Y_axis {a : ℕ} {M : ℤ} {S : Spline} {j : ℕ} (hS : IsAtomSpline (decide (a = 0)) S j) (hj : j ≠ 0)
    (sg : ℝ) (hs2 : sg = 1 ∨ sg = -1) (p : ℝ × Space) (hz : p.2 ≠ 0) (hx : 0 < sg * heightRatio p.2)
    (hall : ∀ b ∈ (S.mesh.xBreaks.drop 1).dropLast, b ≤ sg * heightRatio p.2) (hd : 0 < ‖p.2‖ + sg * p.2 2) :
    Yf a M S p = pmap (M - a) (planeW p.2) * planeW p.2 ^ a * ((Kf a sg p.2 : ℝ) : ℂ) *
      (if decide (a = 0) && decide (sg < 0) then (-1 : ℂ) else 1) *
      (lastRow (quotSpline S)).eval true p.1 (sg * heightRatio p.2) := by
  obtain ⟨t, z⟩ := p
  simp only at hz hx hall hd ⊢
  have hn : 0 < ‖z‖ := norm_pos_iff.2 hz
  have hsq := norm_sq_split z
  have hss : sg * sg = 1 := by rcases hs2 with h | h <;> rw [h] <;> norm_num
  have hev : (lastRow S).eval (decide (a = 0)) t (heightRatio z) =
      (if decide (a = 0) && decide (sg < 0) then (-1 : ℂ) else 1) * (lastRow S).evalHalf t (sg * heightRatio z) := by
    unfold Spline.eval
    rcases hs2 with rfl | rfl
    · have h1 : 0 < heightRatio z := by linarith
      have h2 : ¬ heightRatio z < 0 := not_lt.2 h1.le
      simp [h2, abs_of_pos h1]
    · have h1 : heightRatio z < 0 := by linarith
      simp [h1, abs_of_neg h1]
  have hhalf := axis_half hS hj t (sg * heightRatio z) hx hall
  have hne : ((sg * heightRatio z : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  have hEH : (lastRow S).evalHalf t (sg * heightRatio z) =
      (((1 - sg * heightRatio z) * (sg * heightRatio z)⁻¹ : ℝ) : ℂ) *
        (lastRow (quotSpline S)).eval true t (sg * heightRatio z) := by
    apply mul_left_cancel₀ hne
    rw [hhalf]
    have hne' : (sg : ℂ) * (heightRatio z : ℂ) ≠ 0 := by push_cast at hne; exact hne
    have hs0 : (sg : ℂ) ≠ 0 := left_ne_zero_of_mul hne'
    have hx0 : (heightRatio z : ℂ) ≠ 0 := right_ne_zero_of_mul hne'
    push_cast
    field_simp
  have hfac : 1 - sg * heightRatio z = ‖planeW z‖ ^ 2 * (‖z‖ * (‖z‖ + sg * z 2))⁻¹ := by
    have e1 : (1 - sg * heightRatio z) * (‖z‖ * (‖z‖ + sg * z 2)) = ‖z‖ ^ 2 - (sg * sg) * z 2 ^ 2 := by
      unfold heightRatio
      field_simp
      ring
    rw [← div_eq_mul_inv, eq_div_iff (mul_pos hn hd).ne', e1, hss, hsq]
    ring
  have hsqrt := sqrt_q z hz
  have hθ : angleOf z = Complex.arg (planeW z) := rfl
  have hexp : Complex.exp (Complex.I * (((M : ℝ) * angleOf z : ℝ) : ℂ)) =
      Complex.exp (Complex.I * ((((M - a : ℤ) : ℝ) * Complex.arg (planeW z) : ℝ) : ℂ)) *
        Complex.exp (Complex.I * (((a : ℝ) * Complex.arg (planeW z) : ℝ) : ℂ)) := by
    rw [← Complex.exp_add, hθ]
    congr 1
    push_cast
    ring
  have hwa : planeW z ^ a = ((‖planeW z‖ : ℝ) : ℂ) ^ a *
      Complex.exp (Complex.I * (((a : ℝ) * Complex.arg (planeW z) : ℝ) : ℂ)) := by
    conv_lhs => rw [← Complex.norm_mul_exp_arg_mul_I (planeW z)]
    rw [mul_pow, ← Complex.exp_nat_mul]
    congr 2
    push_cast
    ring
  unfold Yf pmap Kf
  simp only
  rw [hexp, hsqrt, hev, hEH, hfac, hwa]
  push_cast
  ring

theorem Y_tame_axis {a : ℕ} {M : ℤ} {S : Spline} {j : ℕ} (hS : IsAtomSpline (decide (a = 0)) S j) (hj : j ≠ 0)
    (p0 : ℝ × Space) (hy : p0.2 ≠ 0) (hw0 : planeW p0.2 = 0) : TameAt (Yf a M S) p0 := by
  set y := p0.2 with hydef
  set sg : ℝ := if 0 < y 2 then 1 else -1 with hsdef
  have hny : ‖y‖ ^ 2 = y 2 ^ 2 := by rw [norm_sq_split, hw0]; simp
  have hnpos : 0 < ‖y‖ := norm_pos_iff.2 hy
  have hsy : sg * y 2 = ‖y‖ := by
    have habs : ‖y‖ = |y 2| := by
      rw [← Real.sqrt_sq (norm_nonneg y), hny, Real.sqrt_sq_eq_abs]
    rw [habs]
    by_cases h : 0 < y 2
    · simp [hsdef, h, abs_of_pos h]
    · have h' : y 2 ≤ 0 := not_lt.1 h
      simp [hsdef, h, abs_of_nonpos h']
  have hs2 : sg = 1 ∨ sg = -1 := by by_cases h : 0 < y 2 <;> simp [hsdef, h]
  have hxy : sg * heightRatio y = 1 := by
    unfold heightRatio
    rw [← mul_div_assoc, hsy, div_self hnpos.ne']
  have hdy : ‖y‖ + sg * y 2 = 2 * ‖y‖ := by rw [hsy]; ring
  have chx : ContDiffAt ℝ 2 (fun p : ℝ × Space => sg * heightRatio p.2) p0 := contDiffAt_const.mul (cd_height hy)
  have chd : ContDiffAt ℝ 2 (fun p : ℝ × Space => ‖p.2‖ + sg * p.2 2) p0 :=
    (cd_norm hy).add (contDiffAt_const.mul (cd_coord 2 p0))
  have E1 : ∀ᶠ p in 𝓝 p0, p.2 ≠ 0 := continuousAt_snd.eventually_ne hy
  have E2 : ∀ᶠ p in 𝓝 p0, 0 < sg * heightRatio p.2 :=
    chx.continuousAt.eventually (lt_mem_nhds (by show 0 < sg * heightRatio y; rw [hxy]; norm_num))
  have E3 : ∀ᶠ p in 𝓝 p0, ∀ b ∈ ((S.mesh.xBreaks.drop 1).dropLast).toFinset, b ≤ sg * heightRatio p.2 := by
    rw [Filter.eventually_all_finset]
    intro b hb
    have hb1 := interior_lt_one _ hS.spline.mesh.x_sorted hS.spline.mesh.x_last b (List.mem_toFinset.1 hb)
    exact (chx.continuousAt.eventually (lt_mem_nhds (by show b < sg * heightRatio y; rw [hxy]; exact hb1))).mono
      fun p hp => hp.le
  have E4 : ∀ᶠ p in 𝓝 p0, 0 < ‖p.2‖ + sg * p.2 2 :=
    chd.continuousAt.eventually (lt_mem_nhds (by show 0 < ‖y‖ + sg * y 2; rw [hdy]; positivity))
  have heq : Yf a M S =ᶠ[𝓝 p0] fun p => pmap (M - a) (planeW p.2) * planeW p.2 ^ a * ((Kf a sg p.2 : ℝ) : ℂ) *
      (if decide (a = 0) && decide (sg < 0) then (-1 : ℂ) else 1) *
      (lastRow (quotSpline S)).eval true p.1 (sg * heightRatio p.2) := by
    filter_upwards [E1, E2, E3, E4] with p hz hx hall hd
    exact Y_axis hS hj sg hs2 p hz hx (fun b hb => hall b (List.mem_toFinset.2 hb)) hd
  refine tame_congr ?_ heq
  have hQ : IsSplineClass 1 1 true (lastRow (quotSpline S)) := lastRow_class (quotSpline_class hS hj) (atInf_quot hS hj)
  have hne2 : ‖y‖ * (‖y‖ + sg * y 2) ≠ 0 := by
    rw [hdy]
    exact mul_ne_zero hnpos.ne' (mul_ne_zero two_ne_zero hnpos.ne')
  have cK : ContDiffAt ℝ 2 (fun p : ℝ × Space => Kf a sg p.2) p0 :=
    ((((cd_norm hy).pow a).inv (pow_ne_zero _ hnpos.ne')).mul
      (((cd_norm hy).mul chd).inv hne2)).mul (chx.inv (by show sg * heightRatio y ≠ 0; rw [hxy]; norm_num))
  exact tame_mul (tame_mul (tame_mul (tame_mul (tame_comp (g := pmap (M - a)) (Φ := fun p : ℝ × Space => planeW p.2)
    (pmap_tame _ _) (tame_of_contDiffAt (cd_plane p0))) (tame_of_contDiffAt ((cd_plane p0).pow a)))
    (tame_of_contDiffAt (cd_ofReal cK))) (tame_of_contDiffAt contDiffAt_const))
    (tame_spline_comp hQ contDiffAt_fst chx)

theorem Y_tame {a : ℕ} {M : ℤ} {S : Spline} {j : ℕ} (ha : a ≤ 1) (hS : IsAtomSpline (decide (a = 0)) S j)
    (hM : j = 0 → M.natAbs = a) (p0 : ℝ × Space) (hz0 : p0.2 ≠ 0) : TameAt (Yf a M S) p0 := by
  have hG : IsSplineClass 1 1 (decide (a = 0)) (lastRow S) := lastRow_class hS.spline (atInf_of_atom hS)
  by_cases hw : planeW p0.2 = 0
  · by_cases hj : j = 0
    · have hMa := hM hj
      have E1 : ∀ᶠ p in 𝓝 p0, p.2 ≠ 0 := continuousAt_snd.eventually_ne hz0
      interval_cases a
      · have hM0 : M = 0 := Int.natAbs_eq_zero.1 hMa
        subst hM0
        have e : Yf 0 0 S = fun p => (lastRow S).eval (decide ((0 : ℕ) = 0)) p.1 (heightRatio p.2) := by
          funext p
          simp [Yf]
        rw [e]
        exact tame_spline_comp hG contDiffAt_fst (cd_height hz0)
      · have cn : ContDiffAt ℝ 2 (fun p : ℝ × Space => ‖p.2‖⁻¹) p0 := (cd_norm hz0).inv (norm_ne_zero_iff.2 hz0)
        rcases Int.natAbs_eq_iff.1 hMa with h | h
        · have hM1 : M = 1 := by rw [h]; rfl
          subst hM1
          refine tame_congr ?_ (E1.mono fun p hp => Y_plus S p hp)
          exact tame_mul (tame_mul (tame_of_contDiffAt (cd_plane p0)) (tame_of_contDiffAt (cd_ofReal cn)))
            (tame_spline_comp hG contDiffAt_fst (cd_height hz0))
        · have hM1 : M = -1 := by rw [h]; rfl
          subst hM1
          refine tame_congr ?_ (E1.mono fun p hp => Y_minus S p hp)
          exact tame_mul (tame_mul (tame_of_contDiffAt
            (Complex.conjCLE.contDiff.contDiffAt.comp p0 (cd_plane p0))) (tame_of_contDiffAt (cd_ofReal cn)))
            (tame_spline_comp hG contDiffAt_fst (cd_height hz0))
    · exact Y_tame_axis hS hj p0 hz0 hw
  · exact Y_tame_off hG p0 hw

end AtomSlopeFarInternal

namespace AtomSlopeFarInternal

open AtomAxisInternal

def tauF (P : ChartParams) (p : ℝ × Space) : ℝ := ‖p.2‖ / (‖p.2‖ + p.1 * P.L0)

def Ef (P : ChartParams) (j : ℕ) (β : ℝ) (p : ℝ × Space) : ℂ :=
  (((P.L0 / (‖p.2‖ + p.1 * P.L0)) ^ (2 * P.eps + 2) : ℝ) : ℂ) *
    Complex.exp (Complex.I * (((j : ℝ) * β * ((1 / 2) * Real.log (p.1 ^ 2 * P.rc ^ 2 + ‖p.2‖ ^ 2) - Real.log P.rc) : ℝ) : ℂ))

def Ff (P : ChartParams) (j a : ℕ) (M : ℤ) (β : ℝ) (S : Spline) (p : ℝ × Space) : ℂ :=
  Ef P j β p * Yf a M S (tauF P p, p.2)

theorem F_tame (P : ChartParams) (hP : IsChartParams P) {j a : ℕ} {M : ℤ} {β : ℝ} {S : Spline} (ha : a ≤ 1)
    (hS : IsAtomSpline (decide (a = 0)) S j) (hM : j = 0 → M.natAbs = a) (p0 : ℝ × Space) (hs : 0 ≤ p0.1)
    (hz : p0.2 ≠ 0) : TameAt (Ff P j a M β S) p0 := by
  have hn : 0 < ‖p0.2‖ := norm_pos_iff.2 hz
  have hL := hP.L0_pos
  have hden : 0 < ‖p0.2‖ + p0.1 * P.L0 := by positivity
  have cden : ContDiffAt ℝ 2 (fun p : ℝ × Space => ‖p.2‖ + p.1 * P.L0) p0 :=
    (cd_norm hz).add (contDiffAt_fst.mul contDiffAt_const)
  have cbase : ContDiffAt ℝ 2 (fun p : ℝ × Space => P.L0 / (‖p.2‖ + p.1 * P.L0)) p0 :=
    contDiffAt_const.div cden hden.ne'
  have cpow : ContDiffAt ℝ 2 (fun p : ℝ × Space => (P.L0 / (‖p.2‖ + p.1 * P.L0)) ^ (2 * P.eps + 2)) p0 :=
    cbase.rpow_const_of_ne (div_pos hL hden).ne'
  have hlogarg : 0 < p0.1 ^ 2 * P.rc ^ 2 + ‖p0.2‖ ^ 2 := by positivity
  have carg : ContDiffAt ℝ 2 (fun p : ℝ × Space => p.1 ^ 2 * P.rc ^ 2 + ‖p.2‖ ^ 2) p0 :=
    ((contDiffAt_fst.pow 2).mul contDiffAt_const).add ((contDiff_norm_sq ℝ).contDiffAt.comp p0 contDiffAt_snd)
  have clog : ContDiffAt ℝ 2 (fun p : ℝ × Space =>
      (j : ℝ) * β * ((1 / 2) * Real.log (p.1 ^ 2 * P.rc ^ 2 + ‖p.2‖ ^ 2) - Real.log P.rc)) p0 :=
    contDiffAt_const.mul ((contDiffAt_const.mul (carg.log hlogarg.ne')).sub contDiffAt_const)
  have cexp : ContDiffAt ℝ 2 (fun p : ℝ × Space => Complex.exp (Complex.I * (((j : ℝ) * β *
      ((1 / 2) * Real.log (p.1 ^ 2 * P.rc ^ 2 + ‖p.2‖ ^ 2) - Real.log P.rc) : ℝ) : ℂ))) p0 :=
    Complex.contDiff_exp.contDiffAt.comp p0 (contDiffAt_const.mul (cd_ofReal clog))
  have cE : ContDiffAt ℝ 2 (Ef P j β) p0 := (cd_ofReal cpow).mul cexp
  have cΦ : ContDiffAt ℝ 2 (fun p : ℝ × Space => (tauF P p, p.2)) p0 :=
    ((cd_norm hz).div cden hden.ne').prodMk contDiffAt_snd
  exact tame_mul (tame_of_contDiffAt cE) (tame_comp (g := Yf a M S) (Φ := fun p : ℝ × Space => (tauF P p, p.2))
    (Y_tame ha hS hM _ hz) (tame_of_contDiffAt cΦ))

theorem far_identity (P : ChartParams) (hP : IsChartParams P) (j a : ℕ) (M : ℤ) (β : ℝ) (S : Spline)
    (hS : IsAtomSpline (decide (a = 0)) S j) (s : ℝ) (hs : 0 < s) (z : Space) (hz : z ≠ 0)
    (ht : ∀ b ∈ (S.mesh.tBreaks.drop 1).dropLast, b ≤ tauF P (s, z)) :
    ((decayFactor P (s⁻¹ • z) : ℝ) : ℂ) * atomTerm P j a M β S (s⁻¹ • z) =
      (((s ^ (2 * P.eps + 2) : ℝ) : ℂ) * Complex.exp (-(Complex.I * (((j : ℝ) * β * Real.log s : ℝ) : ℂ)))) *
        Ff P j a M β S (s, z) := by
  have hn : 0 < ‖z‖ := norm_pos_iff.2 hz
  have hL := hP.L0_pos
  have hrc := hP.rc_pos
  have hden : 0 < ‖z‖ + s * P.L0 := by positivity
  have hny : ‖s⁻¹ • z‖ = s⁻¹ * ‖z‖ := by rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hs.le)]
  have hT : chartT P (s⁻¹ • z) = tauF P (s, z) := by
    unfold chartT tauF
    rw [hny]
    field_simp
  have hB : 0 < P.L0 / (‖z‖ + s * P.L0) := div_pos hL hden
  have hSy : chartS P (s⁻¹ • z) = s * (P.L0 / (‖z‖ + s * P.L0)) := by
    unfold chartS chartT
    rw [hny]
    field_simp
    ring
  have h1t : 1 - tauF P (s, z) = s * (P.L0 / (‖z‖ + s * P.L0)) := by
    unfold tauF
    field_simp
    ring
  have hH : heightRatio (s⁻¹ • z) = heightRatio z := by
    unfold heightRatio
    rw [hny]
    simp only [PiLp.smul_apply, smul_eq_mul]
    field_simp
  have hQ : qOf (s⁻¹ • z) = qOf z := by unfold qOf; rw [hH]
  have hA : angleOf (s⁻¹ • z) = angleOf z := by
    unfold angleOf
    have e : (⟨(s⁻¹ • z) 0, (s⁻¹ • z) 1⟩ : ℂ) = ((s⁻¹ : ℝ) : ℂ) * ⟨z 0, z 1⟩ := by
      apply Complex.ext <;> simp
    rw [e, Complex.arg_real_mul _ (inv_pos.2 hs)]
  have hLog : logPhase P (s⁻¹ • z) =
      (1 / 2) * Real.log (s ^ 2 * P.rc ^ 2 + ‖z‖ ^ 2) - Real.log P.rc - Real.log s := by
    unfold logPhase
    rw [hny]
    have e : 1 + (s⁻¹ * ‖z‖) ^ 2 / P.rc ^ 2 = (s ^ 2 * P.rc ^ 2 + ‖z‖ ^ 2) / (s * P.rc) ^ 2 := by
      field_simp
    rw [e, Real.log_div (by positivity) (by positivity), Real.log_pow, Real.log_mul hs.ne' hrc.ne']
    push_cast
    ring
  have hev := lastRow_eval hS.spline (atInf_of_atom hS) (chartT P (s⁻¹ • z)) (heightRatio (s⁻¹ • z))
    (by rw [hT]; exact ht)
  have hpow : (((s ^ (2 * P.eps + 2) : ℝ) : ℂ)) * (((P.L0 / (‖z‖ + s * P.L0)) ^ (2 * P.eps + 2) : ℝ) : ℂ) =
      (((s * (P.L0 / (‖z‖ + s * P.L0))) ^ (2 * P.eps) : ℝ) : ℂ) *
        ((((s * (P.L0 / (‖z‖ + s * P.L0))) ^ 2 : ℝ)) : ℂ) := by
    rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, ← Real.mul_rpow hs.le hB.le,
      Real.rpow_add (mul_pos hs hB), Real.rpow_two]
  have hexp : Complex.exp (Complex.I * (((j : ℝ) * β * ((1 / 2) * Real.log (s ^ 2 * P.rc ^ 2 + ‖z‖ ^ 2) -
      Real.log P.rc - Real.log s) + (M : ℝ) * angleOf z : ℝ) : ℂ)) =
      Complex.exp (Complex.I * (((j : ℝ) * β * ((1 / 2) * Real.log (s ^ 2 * P.rc ^ 2 + ‖z‖ ^ 2) -
        Real.log P.rc) : ℝ) : ℂ)) * Complex.exp (-(Complex.I * (((j : ℝ) * β * Real.log s : ℝ) : ℂ))) *
        Complex.exp (Complex.I * (((M : ℝ) * angleOf z : ℝ) : ℂ)) := by
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  unfold decayFactor atomTerm Ff Ef Yf
  dsimp only
  rw [hSy, hev, hT, hH, hQ, hA, hLog, h1t, hexp]
  linear_combination (-(Complex.exp (Complex.I * (((j : ℝ) * β * ((1 / 2) * Real.log (s ^ 2 * P.rc ^ 2 + ‖z‖ ^ 2) -
        Real.log P.rc) : ℝ) : ℂ)) * Complex.exp (-(Complex.I * (((j : ℝ) * β * Real.log s : ℝ) : ℂ))) *
        Complex.exp (Complex.I * (((M : ℝ) * angleOf z : ℝ) : ℂ)) * ((Real.sqrt (qOf z) ^ a : ℝ) : ℂ) *
        (lastRow S).eval (decide (a = 0)) (tauF P (s, z)) (heightRatio z))) * hpow

end AtomSlopeFarInternal


theorem atomScalar_fderiv_farScaled (P : ChartParams) (hP : IsChartParams P) (j a : ℕ) (M : ℤ) (β : ℝ) (S : Spline)
    (ha : a ≤ 1) (hS : IsAtomSpline (decide (a = 0)) S j) (hM : j = 0 → M.natAbs = a) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ W : ℝ × Space → (Space →L[ℝ] ℂ),
      LocallyLipschitzOn (Set.Ico 0 δ ×ˢ {z : Space | 1 / 4 < ‖z‖ ∧ ‖z‖ < 2}) W ∧
      ∀ s : ℝ, 0 < s → s < δ → ∃ c : ℂ, ‖c‖ ≤ s ^ 3 ∧
        ∀ z : Space, 1 / 4 < ‖z‖ → ‖z‖ < 2 → fderiv ℝ (fun y => ((decayFactor P y : ℝ) : ℂ) * atomTerm P j a M β S y) (s⁻¹ • z) = c • W (s, z) := by
  have hL := hP.L0_pos
  obtain ⟨δ0, hδ0, hδ⟩ : ∃ δ0 > 0, ∀ s : ℝ, |s| < δ0 →
      ∀ b ∈ ((S.mesh.tBreaks.drop 1).dropLast).toFinset, 4 * s * P.L0 < 1 - b := by
    have hev : ∀ᶠ s in 𝓝 (0 : ℝ), ∀ b ∈ ((S.mesh.tBreaks.drop 1).dropLast).toFinset, 4 * s * P.L0 < 1 - b := by
      rw [Filter.eventually_all_finset]
      intro b hb
      have hb1 := AtomAxisInternal.interior_lt_one _ hS.spline.mesh.t_sorted hS.spline.mesh.t_last b
        (List.mem_toFinset.1 hb)
      have hc : Continuous (fun s : ℝ => 4 * s * P.L0) := by fun_prop
      exact hc.continuousAt.eventually (gt_mem_nhds (by simp; linarith))
    obtain ⟨ε, hε, h⟩ := Metric.eventually_nhds_iff.1 hev
    exact ⟨ε, hε, fun s hs => h (by rwa [Real.dist_eq, sub_zero])⟩
  have hδpos : 0 < min δ0 1 := lt_min hδ0 one_pos
  have htb : ∀ s : ℝ, 0 ≤ s → s < min δ0 1 → ∀ z : Space, 1 / 4 < ‖z‖ →
      ∀ b ∈ (S.mesh.tBreaks.drop 1).dropLast, b ≤ AtomSlopeFarInternal.tauF P (s, z) := by
    intro s hs0 hsδ z hz b hb
    have h1 := hδ s (by rw [abs_of_nonneg hs0]; exact lt_of_lt_of_le hsδ (min_le_left _ _)) b
      (List.mem_toFinset.2 hb)
    have hb1 := AtomAxisInternal.interior_lt_one _ hS.spline.mesh.t_sorted hS.spline.mesh.t_last b hb
    have hz0 : 0 < ‖z‖ := by linarith
    unfold AtomSlopeFarInternal.tauF
    rw [le_div_iff₀ (by positivity)]
    nlinarith [mul_pos (sub_pos.2 hz) (sub_pos.2 hb1), mul_nonneg (sub_pos.2 hb1).le (mul_nonneg hs0 hL.le)]
  refine ⟨min δ0 1, hδpos, fun p => (fderiv ℝ (AtomSlopeFarInternal.Ff P j a M β S) p).comp (ContinuousLinearMap.inr ℝ ℝ Space), ?_, ?_⟩
  · intro p hp
    have hp0 : p.2 ≠ 0 := by
      intro h
      have := hp.2.1
      rw [h, norm_zero] at this
      linarith
    obtain ⟨U, hU, -, K, hK⟩ := AtomSlopeFarInternal.tame_region (AtomSlopeFarInternal.F_tame P hP (β := β) ha hS hM p hp.1.1 hp0)
    refine ⟨K, U, mem_nhdsWithin_of_mem_nhds hU, LipschitzOnWith.of_dist_le_mul fun q hq r hr => ?_⟩
    rw [dist_eq_norm, ← ContinuousLinearMap.sub_comp]
    have h1 := hK.dist_le_mul q hq r hr
    rw [dist_eq_norm] at h1
    have hinr : ‖ContinuousLinearMap.inr ℝ ℝ Space‖ ≤ 1 :=
      ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => by simp [Prod.norm_def]
    calc _ ≤ ‖fderiv ℝ (AtomSlopeFarInternal.Ff P j a M β S) q - fderiv ℝ (AtomSlopeFarInternal.Ff P j a M β S) r‖ * ‖ContinuousLinearMap.inr ℝ ℝ Space‖ :=
          ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ ‖fderiv ℝ (AtomSlopeFarInternal.Ff P j a M β S) q - fderiv ℝ (AtomSlopeFarInternal.Ff P j a M β S) r‖ * 1 :=
          mul_le_mul_of_nonneg_left hinr (norm_nonneg _)
      _ ≤ K * dist q r := by rw [mul_one]; exact h1
  · intro s hs hsδ
    have hs1 : s ≤ 1 := (lt_of_lt_of_le hsδ (min_le_right _ _)).le
    refine ⟨((s ^ (2 * P.eps + 3) : ℝ) : ℂ) * Complex.exp (-(Complex.I * (((j : ℝ) * β * Real.log s : ℝ) : ℂ))), ?_, ?_⟩
    · have hre : (-(Complex.I * (((j : ℝ) * β * Real.log s : ℝ) : ℂ))).re = 0 := by simp
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity), Complex.norm_exp, hre, Real.exp_zero,
        mul_one]
      have h3 : s ^ (2 * P.eps + 3) ≤ s ^ ((3 : ℕ) : ℝ) :=
        Real.rpow_le_rpow_of_exponent_ge hs hs1 (by have := hP.eps_pos; push_cast; linarith)
      rwa [Real.rpow_natCast] at h3
    · intro z hz1 hz2
      have hz : z ≠ 0 := by
        intro h
        rw [h, norm_zero] at hz1
        linarith
      set C0 : ℂ := ((s ^ (2 * P.eps + 2) : ℝ) : ℂ) * Complex.exp (-(Complex.I * (((j : ℝ) * β * Real.log s : ℝ) : ℂ)))
        with hC0
      have hloc : (fun y => ((decayFactor P y : ℝ) : ℂ) * atomTerm P j a M β S y) =ᶠ[𝓝 (s⁻¹ • z)]
          fun y => C0 * AtomSlopeFarInternal.Ff P j a M β S (s, s • y) := by
        have hc : ContinuousAt (fun y : Space => ‖s • y‖) (s⁻¹ • z) := by fun_prop
        have hev : ∀ᶠ y in 𝓝 (s⁻¹ • z), 1 / 4 < ‖s • y‖ :=
          hc.eventually (lt_mem_nhds (by show 1 / 4 < ‖s • s⁻¹ • z‖; rw [smul_inv_smul₀ hs.ne']; exact hz1))
        filter_upwards [hev] with y hy
        have hy0 : s • y ≠ 0 := by
          intro h
          rw [h, norm_zero] at hy
          linarith
        have e := AtomSlopeFarInternal.far_identity P hP j a M β S hS s hs (s • y) hy0 (htb s hs.le hsδ (s • y) hy)
        rw [inv_smul_smul₀ hs.ne'] at e
        exact e
      obtain ⟨U, hU, hdU, -⟩ := AtomSlopeFarInternal.tame_region (AtomSlopeFarInternal.F_tame P hP (β := β) ha hS hM (s, z) hs.le hz)
      have hdF : DifferentiableAt ℝ (AtomSlopeFarInternal.Ff P j a M β S) (s, z) := hdU _ (mem_of_mem_nhds hU)
      have hT : HasFDerivAt (fun y : Space => (s, s • y))
          ((0 : Space →L[ℝ] ℝ).prod (s • ContinuousLinearMap.id ℝ Space)) (s⁻¹ • z) :=
        (hasFDerivAt_const s _).prodMk ((hasFDerivAt_id _).const_smul s)
      have hcomp : HasFDerivAt (fun y : Space => AtomSlopeFarInternal.Ff P j a M β S (s, s • y))
          ((fderiv ℝ (AtomSlopeFarInternal.Ff P j a M β S) (s, z)).comp ((0 : Space →L[ℝ] ℝ).prod (s • ContinuousLinearMap.id ℝ Space)))
          (s⁻¹ • z) :=
        by
          have hg : HasFDerivAt (AtomSlopeFarInternal.Ff P j a M β S) (fderiv ℝ (AtomSlopeFarInternal.Ff P j a M β S) (s, z)) (s, s • (s⁻¹ • z)) := by
            rw [smul_inv_smul₀ hs.ne']
            exact hdF.hasFDerivAt
          exact hg.comp (s⁻¹ • z) hT
      have hfin := (hcomp.const_mul C0).congr_of_eventuallyEq hloc
      rw [hfin.fderiv]
      refine ContinuousLinearMap.ext fun v => ?_
      have e1 : ((0 : Space →L[ℝ] ℝ).prod (s • ContinuousLinearMap.id ℝ Space)) v = s • ((0 : ℝ), v) := by
        simp
      have hr3 : s ^ (2 * P.eps + 3) = s ^ (2 * P.eps + 2) * s := by
        rw [show 2 * P.eps + 3 = (2 * P.eps + 2) + 1 by ring, Real.rpow_add hs, Real.rpow_one]
      rw [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply, e1, map_smul,
        ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply, hC0, hr3,
        Complex.real_smul, smul_eq_mul, smul_eq_mul]
      push_cast
      ring

end GivenFields

end CellCert

end Breakdown
