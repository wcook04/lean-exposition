import Breakdown.FracCell.GivenAuxDefs
import Breakdown.FracCell.GivenAuxActuatorOpen
import Breakdown.FracCell.GivenAuxPinSmoothLocalLeaves
import Breakdown.FracCell.GivenAuxPinSmoothLocal

open scoped ContDiff ENNReal Topology
open MeasureTheory

noncomputable section

namespace Breakdown

namespace CellCert

namespace GivenFields

open SteadyCert
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

section TameOut

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

private theorem tame_of_local {f : E → F} {y : E}
    (h : ∃ U ∈ nhds y, (∀ q ∈ U, DifferentiableAt ℝ f q) ∧ ∃ K : NNReal, LipschitzOnWith K (fderiv ℝ f) U) :
    TameAt f y := by
  obtain ⟨U, hU, hd, K, hK⟩ := h
  obtain ⟨r, hr, hsub⟩ := Metric.mem_nhds_iff.1 hU
  refine ⟨r, hr, fderiv ℝ f, K, K.2, fun z hz => (hd z (hsub hz)).hasFDerivAt, fun z hz w hw => ?_⟩
  have := hK.dist_le_mul z (hsub hz) w (hsub hw)
  rwa [dist_eq_norm, dist_eq_norm] at this

private theorem tame_out {f : E → F} {y : E} (h : TameAt f y) :
    ∃ U ∈ nhds y, (∀ q ∈ U, DifferentiableAt ℝ f q) ∧ ∃ K : NNReal, LipschitzOnWith K (fderiv ℝ f) U := by
  obtain ⟨r, hr, f', K, hK0, h1, h2⟩ := h
  refine ⟨Metric.ball y r, Metric.ball_mem_nhds y hr, fun q hq => (h1 q hq).differentiableAt, ⟨K, hK0⟩,
    LipschitzOnWith.of_dist_le_mul fun z hz w hw => ?_⟩
  rw [(h1 z hz).fderiv, (h1 w hw).fderiv, dist_eq_norm, dist_eq_norm]
  exact h2 z hz w hw

end TameOut

private def nearEv (P : MvPolynomial (Fin 2) ℂ) (q : ℝ × ℝ) : ℂ := MvPolynomial.eval ![(q.1 : ℂ), (q.2 : ℂ)] P

private theorem near_eval_bind (v : Fin 2 → ℂ) (g : Fin 2 → MvPolynomial (Fin 2) ℂ) (Q : MvPolynomial (Fin 2) ℂ) :
    MvPolynomial.eval v (MvPolynomial.bind₁ g Q) = MvPolynomial.eval (fun i => MvPolynomial.eval v (g i)) Q := by
  induction Q using MvPolynomial.induction_on with
  | C a => simp
  | add p r hp hr => simp [hp, hr]
  | mul_X p i hp => simp [hp]

private theorem nearEv_atFirst (c : ℝ) (Q : MvPolynomial (Fin 2) ℂ) (q : ℝ × ℝ) :
    nearEv (atFirst (c : ℂ) Q) q = nearEv Q (c, q.2) := by
  unfold nearEv atFirst
  rw [near_eval_bind]
  refine congrArg (fun v => MvPolynomial.eval v Q) (funext fun i => ?_)
  fin_cases i <;> simp

private theorem near_mesh (l : List ℝ) (hs : l.Pairwise (· < ·)) (h0 : l.head? = some 0) (h1 : l.getLast? = some 1) :
    (∀ b ∈ (l.drop 1).dropLast, 0 < b) ∧ ((l.drop 1).dropLast).length + 1 = cellCount l := by
  refine ⟨?_, ?_⟩
  · intro b hb
    obtain ⟨r, rfl⟩ : ∃ r, l = 0 :: r := by
      cases l with
      | nil => simp at h0
      | cons a r => simp at h0; exact ⟨r, by rw [h0]⟩
    have hb' : b ∈ r := by simpa using List.mem_of_mem_dropLast hb
    exact List.rel_of_pairwise_cons hs hb'
  · have : 2 ≤ l.length := by
      match l, h0, h1 with
      | [], h0, _ => simp at h0
      | [a], h0, h1 => simp at h0 h1; linarith
      | a :: b :: r, _, _ => simp
    simp [cellCount]
    omega

private theorem near_pos_lower (L : List ℝ) (h : ∀ b ∈ L, 0 < b) : ∃ c > 0, ∀ b ∈ L, c ≤ b := by
  induction L with
  | nil => exact ⟨1, one_pos, by simp⟩
  | cons b L ih =>
    obtain ⟨c, hc, hcL⟩ := ih (fun x hx => h x (List.mem_cons_of_mem _ hx))
    refine ⟨min b c, lt_min (h b (by simp)) hc, ?_⟩
    intro x hx
    rcases List.mem_cons.1 hx with rfl | hx
    · exact min_le_left _ _
    · exact (min_le_right _ _).trans (hcL x hx)

private theorem near_atFirst_mul_X (c : ℂ) (p : MvPolynomial (Fin 2) ℂ) (i : Fin 2) :
    atFirst c (p * MvPolynomial.X i) =
      atFirst c p * (if i = 0 then MvPolynomial.C c else MvPolynomial.X 1) := by
  simp [atFirst]

private theorem near_sub_atFirst_dvd (R : MvPolynomial (Fin 2) ℂ) :
    MvPolynomial.X 0 ∣ R - atFirst 0 R := by
  induction R using MvPolynomial.induction_on with
  | C a => exact ⟨0, by simp [atFirst]⟩
  | add p r hp hr =>
    have e : p + r - atFirst 0 (p + r) = (p - atFirst 0 p) + (r - atFirst 0 r) := by
      simp only [atFirst, map_add]
      ring
    rw [e]
    exact dvd_add hp hr
  | mul_X p i hp =>
    obtain ⟨q, hq⟩ := hp
    rw [near_atFirst_mul_X]
    fin_cases i
    · exact ⟨p, by simp; ring⟩
    · refine ⟨q * MvPolynomial.X 1, ?_⟩
      have e : p * MvPolynomial.X 1 - atFirst 0 p * MvPolynomial.X 1 = (p - atFirst 0 p) * MvPolynomial.X 1 := by ring
      simp only [Fin.mk_one, one_ne_zero, if_false]
      rw [e, hq]
      ring

private theorem near_atSecond_X0_mul (c : ℂ) (q : MvPolynomial (Fin 2) ℂ) :
    atSecond c (MvPolynomial.X 0 * q) = MvPolynomial.X 0 * atSecond c q := by
  simp [atSecond]

private theorem near_xDeriv_X0_mul (o : ℕ) (q : MvPolynomial (Fin 2) ℂ) :
    xDeriv o (MvPolynomial.X 0 * q) = MvPolynomial.X 0 * xDeriv o q := by
  induction o generalizing q with
  | zero => rfl
  | succ o ih =>
    simp only [xDeriv, Function.iterate_succ_apply] at ih ⊢
    have : MvPolynomial.pderiv 1 (MvPolynomial.X 0 * q) = MvPolynomial.X 0 * MvPolynomial.pderiv 1 q := by
      rw [Derivation.leibniz, MvPolynomial.pderiv_X_of_ne (by decide)]
      simp
    rw [this, ih]

private theorem near_origin_split {odd : Bool} {S : Spline} {harm : ℕ} (hS : IsAtomSpline odd S harm) :
    ∃ T : Spline, IsSplineClass 1 1 odd T ∧ T.mesh.tBreaks = [0, 1] ∧ ∃ t1 > 0, (∀ t < t1, ∀ x : ℝ, S.eval odd t x = (t : ℂ) * T.eval odd t x) ∧
      (harm ≠ 0 → ∀ i < cellCount T.mesh.tBreaks, atSecond 1 (T.piece i (atomLastX T)) = 0) := by
  have hSc := hS.spline
  obtain ⟨pt, ct⟩ := near_mesh _ hSc.mesh.t_sorted hSc.mesh.t_first hSc.mesh.t_last
  obtain ⟨-, cx⟩ := near_mesh _ hSc.mesh.x_sorted hSc.mesh.x_first hSc.mesh.x_last
  obtain ⟨c, hc, hcL⟩ := near_pos_lower _ pt
  have hct : 0 < cellCount S.mesh.tBreaks := by omega
  have hQ : ∀ k, ∃ Q : MvPolynomial (Fin 2) ℂ, S.piece 0 k = atFirst 0 (S.piece 0 k) + MvPolynomial.X 0 * Q := by
    intro k
    obtain ⟨Q, hQ⟩ := near_sub_atFirst_dvd (S.piece 0 k)
    exact ⟨Q, by rw [← hQ]; ring⟩
  choose Q hQ using hQ
  have hQ' : ∀ k < cellCount S.mesh.xBreaks, S.piece 0 k = MvPolynomial.X 0 * Q k := by
    intro k hk
    have := hQ k
    rwa [hS.at_origin k hk, zero_add] at this
  have hi : ∀ t < c, cellIndex S.mesh.tBreaks t = 0 := by
    intro t ht
    unfold cellIndex
    rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
    intro y hy
    simpa using lt_of_lt_of_le ht (hcL y hy)
  have hxc : ∀ x : ℝ, cellIndex S.mesh.xBreaks x < cellCount S.mesh.xBreaks := by
    intro x
    unfold cellIndex
    have := List.length_filter_le (fun b => decide (b ≤ x)) ((S.mesh.xBreaks.drop 1).dropLast)
    omega
  have hT0 : ∀ t, cellIndex [0, 1] t = 0 := fun t => by simp [cellIndex]
  have hX : (MvPolynomial.X 0 : MvPolynomial (Fin 2) ℂ) ≠ 0 := MvPolynomial.X_ne_zero 0
  refine ⟨⟨⟨[0, 1], S.mesh.xBreaks⟩, fun _ k => Q k⟩, ?_, rfl, c, hc, ?_, ?_⟩
  · refine ⟨⟨by simp, hSc.mesh.x_sorted, by simp, by simp, hSc.mesh.x_first, hSc.mesh.x_last⟩, ?_, ?_, ?_⟩
    · intro i hi1 hi2
      simp [cellCount] at hi2
      omega
    · intro k hk1 hk2 i hi o ho
      have hk2' : k < cellCount S.mesh.xBreaks := hk2
      have h1 := hSc.x_joins k hk1 hk2' 0 hct o ho
      rw [hQ' (k - 1) (by omega), hQ' k hk2', near_xDeriv_X0_mul, near_xDeriv_X0_mul, near_atSecond_X0_mul,
        near_atSecond_X0_mul] at h1
      exact mul_left_cancel₀ hX h1
    · intro i hi o ho hpar
      have h1 := hSc.parity 0 hct o ho hpar
      rw [hQ' 0 (by omega), near_xDeriv_X0_mul, near_atSecond_X0_mul] at h1
      exact (mul_eq_zero.1 h1).resolve_left hX
  · intro t ht x
    simp only [Spline.eval, Spline.evalHalf, hi t ht]
    have e := hQ' (cellIndex S.mesh.xBreaks |x|) (hxc _)
    change _ * nearEv _ (t, |x|) = (t : ℂ) * (_ * nearEv _ (t, |x|))
    rw [e]
    have e2 : nearEv (MvPolynomial.X 0 * Q (cellIndex S.mesh.xBreaks |x|)) (t, |x|) =
        (t : ℂ) * nearEv (Q (cellIndex S.mesh.xBreaks |x|)) (t, |x|) := by
      simp [nearEv]
    rw [e2]
    ring
  · intro hh i hi
    have hlast : atomLastX S < cellCount S.mesh.xBreaks := by unfold atomLastX; omega
    have h1 := hS.at_axis hh 0 hct
    rw [hQ' _ hlast, near_atSecond_X0_mul] at h1
    exact (mul_eq_zero.1 h1).resolve_left hX

private def atomAngularProfile (a : ℕ) (M : ℤ) (T : Spline) (q : ℝ × Space) : ℂ :=
  Complex.exp (Complex.I * (((M : ℝ) * angleOf q.2 : ℝ) : ℂ)) * ((Real.sqrt (qOf q.2) ^ a : ℝ) : ℂ) *
    T.eval (decide (a = 0)) q.1 (heightRatio q.2)

private theorem ang_coord (i : Fin 3) : ContDiff ℝ ⊤ (fun y : Space => y i) :=
  (EuclideanSpace.proj i : Space →L[ℝ] ℝ).contDiff

private def angPlane (y : Space) : ℂ := ⟨y 0, y 1⟩

private theorem angPlane_contDiff : ContDiff ℝ ⊤ angPlane := by
  have e : angPlane = fun y => ((y 0 : ℝ) : ℂ) + ((y 1 : ℝ) : ℂ) * Complex.I := by
    funext y
    apply Complex.ext <;> simp [angPlane]
  rw [e]
  exact (Complex.ofRealCLM.contDiff.comp (ang_coord 0)).add
    ((Complex.ofRealCLM.contDiff.comp (ang_coord 1)).mul contDiff_const)

private theorem ang_exp_arg (w : ℂ) (hw : w ≠ 0) (k : ℤ) :
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

private theorem ang_zpow {f : ℝ × Space → ℂ} {y : ℝ × Space} (hf : ContDiffAt ℝ 2 f y) (hy : f y ≠ 0) (j : ℤ) :
    ContDiffAt ℝ 2 (fun z => f z ^ j) y := by
  cases j with
  | ofNat k => simpa using hf.pow k
  | negSucc k =>
    simp only [zpow_negSucc]
    exact (hf.pow (k + 1)).inv (pow_ne_zero _ hy)

private theorem ang_normsq (z : Space) : ‖z‖ ^ 2 = z 0 ^ 2 + z 1 ^ 2 + z 2 ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_three]
  simp [Real.norm_eq_abs, sq_abs]

private theorem ang_plane_normsq (z : Space) : ‖angPlane z‖ ^ 2 = z 0 ^ 2 + z 1 ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp [angPlane]
  ring

private theorem ang_sqrt (z : Space) (hz : z ≠ 0) : Real.sqrt (qOf z) = ‖angPlane z‖ / ‖z‖ := by
  have hn : 0 < ‖z‖ := norm_pos_iff.2 hz
  have hq : qOf z = (‖angPlane z‖ / ‖z‖) ^ 2 := by
    unfold qOf heightRatio
    rw [div_pow, div_pow, ang_plane_normsq, eq_div_iff (by positivity), sub_mul, one_mul,
      div_mul_cancel₀ _ (by positivity), ang_normsq]
    ring
  rw [hq, Real.sqrt_sq (by positivity)]

private theorem ang_height {p : ℝ × Space} (hz : p.2 ≠ 0) :
    ContDiffAt ℝ 2 (fun q : ℝ × Space => heightRatio q.2) p := by
  have h : ContDiffAt ℝ 2 heightRatio p.2 :=
    ((ang_coord 2).contDiffAt.of_le le_top).div (contDiffAt_norm ℝ hz) (norm_ne_zero_iff.2 hz)
  exact h.comp p contDiffAt_snd

private theorem ang_spline_tame (a : ℕ) (T : Spline) (hT : IsSplineClass 1 1 (decide (a = 0)) T)
    {p : ℝ × Space} (hz : p.2 ≠ 0) :
    TameAt (fun q : ℝ × Space => T.eval (decide (a = 0)) q.1 (heightRatio q.2)) p := by
  have hsp : TameAt (fun r : ℝ × ℝ => T.eval (decide (a = 0)) r.1 r.2) (p.1, heightRatio p.2) :=
    tame_of_global ((spline_eval_contDiff T hT le_rfl le_rfl).differentiable (by norm_num))
      (spline_eval_localSlope T hT le_rfl le_rfl) _
  have hΨ : TameAt (fun q : ℝ × Space => (q.1, heightRatio q.2)) p :=
    tame_of_contDiffAt (contDiffAt_fst.prodMk (ang_height hz))
  exact tame_comp (Φ := fun q : ℝ × Space => (q.1, heightRatio q.2))
    (g := fun r : ℝ × ℝ => T.eval (decide (a = 0)) r.1 r.2) hsp hΨ

private theorem ang_offAxis (a : ℕ) (M : ℤ) (T : Spline) (hT : IsSplineClass 1 1 (decide (a = 0)) T)
    (p : ℝ × Space) (hz : p.2 ≠ 0) (hw : angPlane p.2 ≠ 0) :
    TameAt (atomAngularProfile a M T) p := by
  have hwc : ContDiffAt ℝ 2 (fun q : ℝ × Space => angPlane q.2) p :=
    (angPlane_contDiff.contDiffAt.of_le le_top).comp p contDiffAt_snd
  have hwn : ContDiffAt ℝ 2 (fun q : ℝ × Space => ‖angPlane q.2‖) p := hwc.norm ℝ hw
  have hzn : ContDiffAt ℝ 2 (fun q : ℝ × Space => ‖q.2‖) p := contDiffAt_snd.norm ℝ hz
  have hu : ContDiffAt ℝ 2 (fun q : ℝ × Space => angPlane q.2 * ((‖angPlane q.2‖⁻¹ : ℝ) : ℂ)) p :=
    hwc.mul (Complex.ofRealCLM.contDiff.contDiffAt.comp p (hwn.inv (norm_ne_zero_iff.2 hw)))
  have hu0 : angPlane p.2 * ((‖angPlane p.2‖⁻¹ : ℝ) : ℂ) ≠ 0 :=
    mul_ne_zero hw (Complex.ofReal_ne_zero.2 (inv_ne_zero (norm_ne_zero_iff.2 hw)))
  have c1 := ang_zpow hu hu0 M
  have c2r : ContDiffAt ℝ 2 (fun q : ℝ × Space => (‖angPlane q.2‖ / ‖q.2‖) ^ a) p :=
    (hwn.div hzn (norm_ne_zero_iff.2 hz)).pow a
  have c2 : ContDiffAt ℝ 2 (fun q : ℝ × Space => (((‖angPlane q.2‖ / ‖q.2‖) ^ a : ℝ) : ℂ)) p :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp p c2r
  have t3 := ang_spline_tame a T hT hz
  have hall := tame_mul (tame_mul (tame_of_contDiffAt c1) (tame_of_contDiffAt c2)) t3
  refine tame_congr hall ?_
  have hev1 : ∀ᶠ q in nhds p, angPlane q.2 ≠ 0 :=
    ((angPlane_contDiff.continuous.comp continuous_snd).continuousAt (x := p)).eventually_ne hw
  have hev2 : ∀ᶠ q in nhds p, q.2 ≠ 0 := (continuous_snd.continuousAt (x := p)).eventually_ne hz
  filter_upwards [hev1, hev2] with q hq1 hq2
  unfold atomAngularProfile
  rw [ang_sqrt _ hq2]
  have e : angleOf q.2 = Complex.arg (angPlane q.2) := rfl
  rw [e, ang_exp_arg _ hq1]

private theorem ang_conj_identity (w : ℂ) :
    Complex.exp (Complex.I * (((-1 : ℤ) : ℝ) * Complex.arg w : ℝ)) * ((‖w‖ : ℝ) : ℂ) = (starRingEnd ℂ) w := by
  have h2 := Complex.norm_mul_exp_arg_mul_I w
  conv_rhs => rw [← h2]
  rw [map_mul, ← Complex.exp_conj, Complex.conj_ofReal]
  rw [mul_comm]
  congr 1
  congr 1
  push_cast
  rw [map_mul, Complex.conj_ofReal, Complex.conj_I]
  ring

private theorem ang_id_identity (w : ℂ) :
    Complex.exp (Complex.I * (((1 : ℤ) : ℝ) * Complex.arg w : ℝ)) * ((‖w‖ : ℝ) : ℂ) = w := by
  have h2 := Complex.norm_mul_exp_arg_mul_I w
  conv_rhs => rw [← h2]
  rw [mul_comm]
  congr 2
  push_cast
  ring

private theorem ang_harmonic (a : ℕ) (M : ℤ) (T : Spline) (hT : IsSplineClass 1 1 (decide (a = 0)) T)
    (hMa : M.natAbs = a) (ha : a ≤ 1) (p : ℝ × Space) (hz : p.2 ≠ 0) :
    TameAt (atomAngularProfile a M T) p := by
  have t3 := ang_spline_tame a T hT hz
  have hev2 : ∀ᶠ q in nhds p, q.2 ≠ 0 := (continuous_snd.continuousAt (x := p)).eventually_ne hz
  have hzn : ContDiffAt ℝ 2 (fun q : ℝ × Space => ‖q.2‖) p := contDiffAt_snd.norm ℝ hz
  have hinv : ContDiffAt ℝ 2 (fun q : ℝ × Space => ((‖q.2‖⁻¹ : ℝ) : ℂ)) p :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp p (hzn.inv (norm_ne_zero_iff.2 hz))
  have hwc : ContDiffAt ℝ 2 (fun q : ℝ × Space => angPlane q.2) p :=
    (angPlane_contDiff.contDiffAt.of_le le_top).comp p contDiffAt_snd
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 ha with rfl | rfl
  · have hM0 : M = 0 := Int.natAbs_eq_zero.1 hMa
    subst hM0
    refine tame_congr t3 (Filter.Eventually.of_forall fun q => ?_)
    simp [atomAngularProfile]
  · rcases Int.natAbs_eq M with hM | hM <;> rw [hMa] at hM <;> subst hM
    · have hall := tame_mul (tame_of_contDiffAt (hwc.mul hinv)) t3
      refine tame_congr hall ?_
      filter_upwards [hev2] with q hq2
      unfold atomAngularProfile
      rw [ang_sqrt _ hq2]
      have e : angleOf q.2 = Complex.arg (angPlane q.2) := rfl
      rw [e]
      have h := ang_id_identity (angPlane q.2)
      conv_rhs => rw [← h]
      push_cast
      ring
    · have hcc : ContDiffAt ℝ 2 (fun q : ℝ × Space => (starRingEnd ℂ) (angPlane q.2)) p :=
        (Complex.conjCLE.toContinuousLinearMap.contDiff.contDiffAt).comp p hwc
      have hall := tame_mul (tame_of_contDiffAt (hcc.mul hinv)) t3
      refine tame_congr hall ?_
      filter_upwards [hev2] with q hq2
      unfold atomAngularProfile
      rw [ang_sqrt _ hq2]
      have e : angleOf q.2 = Complex.arg (angPlane q.2) := rfl
      rw [e]
      have h := ang_conj_identity (angPlane q.2)
      conv_rhs => rw [← h]
      push_cast
      ring

private theorem near_sub_atSecond_dvd (R : MvPolynomial (Fin 2) ℂ) :
    MvPolynomial.X 1 - MvPolynomial.C 1 ∣ R - atSecond 1 R := by
  induction R using MvPolynomial.induction_on with
  | C a => exact ⟨0, by simp [atSecond]⟩
  | add p r hp hr =>
    have e : p + r - atSecond 1 (p + r) = (p - atSecond 1 p) + (r - atSecond 1 r) := by
      simp only [atSecond, map_add]
      ring
    rw [e]
    exact dvd_add hp hr
  | mul_X p i hp =>
    obtain ⟨q, hq⟩ := hp
    have e : atSecond 1 (p * MvPolynomial.X i) =
        atSecond 1 p * (if i = 1 then MvPolynomial.C 1 else MvPolynomial.X 0) := by
      simp [atSecond]
    rw [e]
    fin_cases i
    · refine ⟨q * MvPolynomial.X 0, ?_⟩
      have e2 : p * MvPolynomial.X 0 - atSecond 1 p * MvPolynomial.X 0 = (p - atSecond 1 p) * MvPolynomial.X 0 := by ring
      simp only [Fin.zero_eta, zero_ne_one, if_false]
      rw [e2, hq]
      ring
    · refine ⟨p + q, ?_⟩
      simp only [Fin.mk_one, if_true]
      have e3 : p * MvPolynomial.X 1 - atSecond 1 p * MvPolynomial.C 1 =
          p * (MvPolynomial.X 1 - MvPolynomial.C 1) + (p - atSecond 1 p) := by
        simp only [map_one, mul_one]
        ring
      rw [e3, hq]
      ring

private theorem nearEv_contDiff (R : MvPolynomial (Fin 2) ℂ) : ContDiff ℝ ⊤ (nearEv R) := by
  induction R using MvPolynomial.induction_on with
  | C a =>
    have e : nearEv (MvPolynomial.C a) = fun _ => a := by funext q; simp [nearEv]
    rw [e]; exact contDiff_const
  | add p r hp hr =>
    have e : nearEv (p + r) = fun q => nearEv p q + nearEv r q := by funext q; simp [nearEv]
    rw [e]; exact hp.add hr
  | mul_X p i hp =>
    fin_cases i
    · have e : nearEv (p * MvPolynomial.X 0) = fun q => nearEv p q * ((q.1 : ℝ) : ℂ) := by
        funext q; simp [nearEv]
      show ContDiff ℝ ⊤ (nearEv (p * MvPolynomial.X 0))
      rw [e]; exact hp.mul (Complex.ofRealCLM.contDiff.comp contDiff_fst)
    · have e : nearEv (p * MvPolynomial.X 1) = fun q => nearEv p q * ((q.2 : ℝ) : ℂ) := by
        funext q; simp [nearEv]
      show ContDiff ℝ ⊤ (nearEv (p * MvPolynomial.X 1))
      rw [e]; exact hp.mul (Complex.ofRealCLM.contDiff.comp contDiff_snd)

private theorem near_upper_gap (l : List ℝ) (hs : l.Pairwise (· < ·)) (h1 : l.getLast? = some 1) :
    ∃ c < 1, ∀ b ∈ (l.drop 1).dropLast, b ≤ c := by
  have hlt : ∀ b ∈ (l.drop 1).dropLast, b < 1 := by
    intro b hb
    have hb' : b ∈ l.dropLast := by
      rw [List.dropLast_drop_eq_drop_dropLast] at hb
      exact List.mem_of_mem_drop hb
    have hne : l ≠ [] := by rintro rfl; simp at h1
    have hl : l.getLast hne = 1 := by
      rw [List.getLast?_eq_some_getLast hne] at h1
      exact Option.some_injective _ h1
    have e := List.dropLast_append_getLast hne
    have hp := hs
    rw [← e] at hp
    have := (List.pairwise_append.1 hp).2.2 b hb' (l.getLast hne) (by simp)
    rwa [hl] at this
  generalize (l.drop 1).dropLast = L at hlt ⊢
  induction L with
  | nil => exact ⟨0, by norm_num, by simp⟩
  | cons b L ih =>
    obtain ⟨c, hc, hcL⟩ := ih (fun x hx => hlt x (List.mem_cons_of_mem _ hx))
    refine ⟨max b c, max_lt (hlt b (by simp)) hc, ?_⟩
    intro x hx
    rcases List.mem_cons.1 hx with rfl | hx
    · exact le_max_left _ _
    · exact (hcL x hx).trans (le_max_right _ _)

private def planeMapN (k : ℤ) (w : ℂ) : ℂ :=
  ((‖w‖ ^ 2 : ℝ) : ℂ) * Complex.exp (Complex.I * (((k : ℝ) * Complex.arg w : ℝ) : ℂ))

private theorem planeMapN_tame (k : ℤ) (w : ℂ) : TameAt (planeMapN k) w :=
  tame_of_global ((planePhase_contDiff k).differentiable (by norm_num)) (planePhase_fderiv_localSlope k) w

private theorem axis_core (a : ℕ) (M : ℤ) (T : Spline) (Φ : ℂ → ℂ) (hΦt : ∀ w, TameAt Φ w)
    (hΦe : ∀ w, Φ w = ((‖w‖ ^ (2 + a) : ℝ) : ℂ) * Complex.exp (Complex.I * (((M : ℝ) * Complex.arg w : ℝ) : ℂ)))
    (hT : IsSplineClass 1 1 (decide (a = 0)) T) (hT1 : T.mesh.tBreaks = [0, 1])
    (hax : ∀ i < cellCount T.mesh.tBreaks, atSecond 1 (T.piece i (atomLastX T)) = 0)
    (p : ℝ × Space) (hz : p.2 ≠ 0) (hw : angPlane p.2 = 0) :
    TameAt (atomAngularProfile a M T) p := by
  obtain ⟨R, hR⟩ := near_sub_atSecond_dvd (T.piece 0 (atomLastX T))
  rw [hax 0 (by rw [hT1]; decide), sub_zero] at hR
  obtain ⟨c, hc1, hcB⟩ := near_upper_gap _ hT.mesh.x_sorted hT.mesh.x_last
  obtain ⟨-, hlen⟩ := near_mesh _ hT.mesh.x_sorted hT.mesh.x_first hT.mesh.x_last
  have hcell : ∀ y, c < y → cellIndex T.mesh.xBreaks y = atomLastX T := by
    intro y hy
    unfold cellIndex atomLastX
    rw [List.filter_eq_self.2 (fun b hb => by simpa using (hcB b hb).trans hy.le)]
    omega
  have heval : ∀ t x : ℝ, c < |x| → T.eval (decide (a = 0)) t x =
      (if decide (a = 0) && decide (x < 0) then -1 else 1) * (((|x| - 1 : ℝ) : ℂ) * nearEv R (t, |x|)) := by
    intro t x hx
    unfold Spline.eval Spline.evalHalf
    rw [hT1, hcell _ hx]
    have h0 : cellIndex [0, 1] t = 0 := by simp [cellIndex]
    rw [h0, hR]
    simp [nearEv]
  set z0 := p.2 with hz0
  have hw0 : z0 0 = 0 := by simpa [angPlane] using congrArg Complex.re hw
  have hw1 : z0 1 = 0 := by simpa [angPlane] using congrArg Complex.im hw
  have hn0 : 0 < ‖z0‖ := norm_pos_iff.2 hz
  have hnsq : ‖z0‖ ^ 2 = z0 2 ^ 2 := by rw [ang_normsq, hw0, hw1]; ring
  set σ : ℝ := if 0 < z0 2 then 1 else -1 with hσ
  have hσ2 : σ * σ = 1 := by rw [hσ]; split_ifs <;> norm_num
  have hσc : 0 < σ * z0 2 := by
    have hc0 : z0 2 ≠ 0 := by
      intro h
      rw [h] at hnsq
      have : ‖z0‖ = 0 := by nlinarith
      exact hn0.ne' this
    rw [hσ]
    split_ifs with h
    · linarith
    · have : z0 2 < 0 := lt_of_le_of_ne (not_lt.1 h) hc0
      linarith
  have hσn : σ * z0 2 = ‖z0‖ := by
    have h1 : (σ * z0 2) ^ 2 = ‖z0‖ ^ 2 := by rw [hnsq]; nlinarith [hσ2]
    nlinarith [hn0, hσc]
  have hxcont : ContinuousAt (fun q : ℝ × Space => σ * heightRatio q.2) p :=
    (contDiffAt_const.mul (ang_height hz)).continuousAt
  have hx0 : σ * heightRatio p.2 = 1 := by
    show σ * (z0 2 / ‖z0‖) = 1
    rw [← mul_div_assoc, hσn, div_self hn0.ne']
  have hcm : max c 0 < 1 := max_lt hc1 (by norm_num)
  have hev1 : ∀ᶠ q in nhds p, max c 0 < σ * heightRatio q.2 :=
    hxcont.eventually (lt_mem_nhds (by show max c 0 < σ * heightRatio p.2; rw [hx0]; exact hcm))
  have hev2 : ∀ᶠ q in nhds p, q.2 ≠ 0 := (continuous_snd.continuousAt (x := p)).eventually_ne hz
  have hzn : ContDiffAt ℝ 2 (fun q : ℝ × Space => ‖q.2‖) p := contDiffAt_snd.norm ℝ hz
  have hz2 : ContDiffAt ℝ 2 (fun q : ℝ × Space => q.2 2) p :=
    ((ang_coord 2).contDiffAt.of_le le_top).comp p contDiffAt_snd
  have hden : ContDiffAt ℝ 2 (fun q : ℝ × Space => ‖q.2‖ ^ a * ‖q.2‖ * (‖q.2‖ + σ * q.2 2)) p :=
    ((hzn.pow a).mul hzn).mul (hzn.add (contDiffAt_const.mul hz2))
  have hden0 : ‖p.2‖ ^ a * ‖p.2‖ * (‖p.2‖ + σ * p.2 2) ≠ 0 := by
    have : 0 < ‖p.2‖ + σ * p.2 2 := by rw [← hz0]; linarith
    positivity
  have c3 : ContDiffAt ℝ 2 (fun q : ℝ × Space =>
      (((‖q.2‖ ^ a * ‖q.2‖ * (‖q.2‖ + σ * q.2 2))⁻¹ : ℝ) : ℂ)) p :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp p (hden.inv hden0)
  have c4 : ContDiffAt ℝ 2 (fun q : ℝ × Space => nearEv R (q.1, σ * heightRatio q.2)) p :=
    ((nearEv_contDiff R).contDiffAt.of_le le_top).comp p (contDiffAt_fst.prodMk (contDiffAt_const.mul (ang_height hz)))
  have hwc : TameAt (fun q : ℝ × Space => angPlane q.2) p :=
    tame_of_contDiffAt ((angPlane_contDiff.contDiffAt.of_le le_top).comp p contDiffAt_snd)
  have t1 := tame_comp (Φ := fun q : ℝ × Space => angPlane q.2) (g := Φ) (hΦt _) hwc
  set sg : ℂ := if decide (a = 0) && decide (σ < 0) then -1 else 1 with hsg
  have hall := tame_mul (tame_mul (tame_mul (tame_of_contDiffAt (contDiffAt_const (c := -sg))) t1)
    (tame_of_contDiffAt c3)) (tame_of_contDiffAt c4)
  refine tame_congr hall ?_
  filter_upwards [hev1, hev2] with q hq1 hq2
  set z := q.2 with hzq
  have hzpos : 0 < ‖z‖ := norm_pos_iff.2 hq2
  have hxpos : 0 < σ * heightRatio z := lt_of_le_of_lt (le_max_right _ _) hq1
  have habs : |heightRatio z| = σ * heightRatio z := by
    rw [hσ] at hxpos ⊢
    split_ifs at hxpos ⊢ with h
    · rw [one_mul] at hxpos ⊢; exact abs_of_pos hxpos
    · have : heightRatio z < 0 := by linarith
      rw [abs_of_neg this]; ring
  have hneg : decide (heightRatio z < 0) = decide (σ < 0) := by
    rw [hσ] at hxpos ⊢
    split_ifs at hxpos ⊢ with h
    · have : ¬ heightRatio z < 0 := by linarith
      simp [this]
    · have : heightRatio z < 0 := by linarith
      simp [this]
  have hgap : c < |heightRatio z| := by rw [habs]; exact lt_of_le_of_lt (le_max_left _ _) hq1
  have hσz : σ * heightRatio z = σ * z 2 / ‖z‖ := by unfold heightRatio; ring
  have hwn : ‖angPlane z‖ ^ 2 = ‖z‖ ^ 2 - z 2 ^ 2 := by rw [ang_plane_normsq, ang_normsq]; ring
  have hposd : 0 < ‖z‖ + σ * z 2 := by
    have : 0 < σ * z 2 / ‖z‖ := by rw [← hσz]; exact hxpos
    have : 0 < σ * z 2 := by
      by_contra hh
      push Not at hh
      have := div_nonpos_of_nonpos_of_nonneg hh hzpos.le
      linarith
    linarith
  have hkey : σ * heightRatio z - 1 = -(‖angPlane z‖ ^ 2) / (‖z‖ * (‖z‖ + σ * z 2)) := by
    rw [hσz, hwn, eq_div_iff (by positivity)]
    field_simp
    have : σ ^ 2 = 1 := by nlinarith [hσ2]
    nlinarith [this]
  unfold atomAngularProfile
  rw [heval _ _ hgap, habs, hneg, ← hsg, hkey, ang_sqrt _ hq2, hΦe]
  have e : angleOf z = Complex.arg (angPlane z) := rfl
  rw [e]
  have hzC : (‖z‖ : ℂ) ≠ 0 := by exact_mod_cast hzpos.ne'
  have hAC : ((‖z‖ + σ * z 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hposd.ne'
  push_cast at hAC ⊢
  field_simp
  have hpz : (‖z‖ : ℂ) ^ a * ((‖z‖ : ℂ))⁻¹ ^ a = 1 := by rw [inv_pow, mul_inv_cancel₀ (pow_ne_zero _ hzC)]
  linear_combination (-((‖angPlane z‖ : ℂ) ^ 2 * (‖angPlane z‖ : ℂ) ^ a * sg * nearEv R (q.1, σ * heightRatio z))) * hpz

private theorem ang_axis (a : ℕ) (ha : a ≤ 1) (M : ℤ) (T : Spline) (hT : IsSplineClass 1 1 (decide (a = 0)) T)
    (hT1 : T.mesh.tBreaks = [0, 1])
    (hax : ∀ i < cellCount T.mesh.tBreaks, atSecond 1 (T.piece i (atomLastX T)) = 0)
    (p : ℝ × Space) (hz : p.2 ≠ 0) (hw : angPlane p.2 = 0) :
    TameAt (atomAngularProfile a M T) p := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 ha with rfl | rfl
  · refine axis_core 0 M T (planeMapN M) (planeMapN_tame M) (fun w => ?_) hT hT1 hax p hz hw
    simp [planeMapN]
  · refine axis_core 1 M T (fun w => planeMapN (M - 1) w * w)
      (fun w => tame_mul (planeMapN_tame (M - 1) w) (tame_of_contDiffAt (contDiffAt_id (x := w))))
      (fun w => ?_) hT hT1 hax p hz hw
    unfold planeMapN
    have h2 := Complex.norm_mul_exp_arg_mul_I w
    have h3 : Complex.exp (Complex.I * ((((M - 1 : ℤ) : ℝ) * Complex.arg w : ℝ) : ℂ)) *
        Complex.exp ((Complex.arg w : ℂ) * Complex.I) =
        Complex.exp (Complex.I * ((((M : ℤ) : ℝ) * Complex.arg w : ℝ) : ℂ)) := by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    conv_lhs => arg 2; rw [← h2]
    rw [← h3]
    push_cast
    ring

private theorem ang_tame (a : ℕ) (ha : a ≤ 1) (M : ℤ) (T : Spline)
    (hT : IsSplineClass 1 1 (decide (a = 0)) T) (hT1 : T.mesh.tBreaks = [0, 1])
    (hax : (∀ i < cellCount T.mesh.tBreaks, atSecond 1 (T.piece i (atomLastX T)) = 0) ∨ M.natAbs = a)
    (p : ℝ × Space) (hz : p.2 ≠ 0) :
    TameAt (atomAngularProfile a M T) p := by
  rcases hax with hax | hMa
  · by_cases hw : angPlane p.2 = 0
    · exact ang_axis a ha M T hT hT1 hax p hz hw
    · exact ang_offAxis a M T hT p hz hw
  · exact ang_harmonic a M T hT hMa ha p hz

private def nearT (P : ChartParams) (q : ℝ × Space) : ℝ := q.1 * ‖q.2‖ / (q.1 * ‖q.2‖ + P.L0)

private def nearProfile (P : ChartParams) (j a : ℕ) (M : ℤ) (β : ℝ) (T : Spline) (q : ℝ × Space) : ℂ :=
  ((((1 - nearT P q) ^ (2 * P.eps) : ℝ) : ℂ) *
    Complex.exp (Complex.I * (((j : ℝ) * β * ((1 / 2) * Real.log (1 + (q.1 * ‖q.2‖) ^ 2 / P.rc ^ 2)) : ℝ) : ℂ)) *
    ((‖q.2‖ / (q.1 * ‖q.2‖ + P.L0) : ℝ) : ℂ)) * atomAngularProfile a M T (nearT P q, q.2)

private theorem near_exp_add (x y : ℝ) :
    Complex.exp (Complex.I * ((x + y : ℝ) : ℂ)) = Complex.exp (Complex.I * (x : ℂ)) * Complex.exp (Complex.I * (y : ℂ)) := by
  push_cast
  rw [mul_add, Complex.exp_add]

private theorem near_identity (P : ChartParams) (j a : ℕ) (M : ℤ) (β : ℝ) (S T : Spline) {t1 : ℝ}
    (hsplit : ∀ t < t1, ∀ x : ℝ, S.eval (decide (a = 0)) t x = (t : ℂ) * T.eval (decide (a = 0)) t x)
    {s : ℝ} (hs : 0 < s) (z : Space) (ht : nearT P (s, z) < t1) :
    ((decayFactor P (s • z) : ℝ) : ℂ) * atomTerm P j a M β S (s • z) = (s : ℂ) * nearProfile P j a M β T (s, z) := by
  have hn : ‖s • z‖ = s * ‖z‖ := by rw [norm_smul, Real.norm_of_nonneg hs.le]
  have hT : chartT P (s • z) = nearT P (s, z) := by unfold chartT nearT; rw [hn]
  have hD : decayFactor P (s • z) = (1 - nearT P (s, z)) ^ (2 * P.eps) := by
    unfold decayFactor chartS; rw [hT]
  have hL : logPhase P (s • z) = (1 / 2) * Real.log (1 + (s * ‖z‖) ^ 2 / P.rc ^ 2) := by
    unfold logPhase; rw [hn]
  have hA : angleOf (s • z) = angleOf z := by
    unfold angleOf
    have e : (⟨(s • z) 0, (s • z) 1⟩ : ℂ) = (s : ℂ) * ⟨z 0, z 1⟩ := by
      apply Complex.ext <;> simp
    rw [e, Complex.arg_real_mul _ hs]
  have hH : heightRatio (s • z) = heightRatio z := by
    unfold heightRatio
    rw [hn]
    simp only [PiLp.smul_apply, smul_eq_mul]
    rw [mul_div_mul_left _ _ hs.ne']
  have hQ : qOf (s • z) = qOf z := by unfold qOf; rw [hH]
  have hτ : nearT P (s, z) = s * (‖z‖ / (s * ‖z‖ + P.L0)) := by
    unfold nearT; rw [mul_div_assoc]
  unfold atomTerm nearProfile atomAngularProfile
  rw [hD, hL, hA, hQ, hH, hT, hsplit _ ht, near_exp_add, hτ]
  simp only
  push_cast
  ring

private theorem near_tame (P : ChartParams) (hP : IsChartParams P) (j a : ℕ) (ha : a ≤ 1) (M : ℤ) (β : ℝ)
    (T : Spline) (hT : IsSplineClass 1 1 (decide (a = 0)) T) (hT1 : T.mesh.tBreaks = [0, 1])
    (hax : (∀ i < cellCount T.mesh.tBreaks, atSecond 1 (T.piece i (atomLastX T)) = 0) ∨ M.natAbs = a)
    (p : ℝ × Space) (hz : p.2 ≠ 0) (hden : 0 < p.1 * ‖p.2‖ + P.L0) :
    TameAt (nearProfile P j a M β T) p := by
  have hn : ContDiffAt ℝ 2 (fun q : ℝ × Space => ‖q.2‖) p := contDiffAt_snd.norm ℝ hz
  have hs : ContDiffAt ℝ 2 (fun q : ℝ × Space => q.1) p := contDiffAt_fst
  have hA : ContDiffAt ℝ 2 (fun q : ℝ × Space => q.1 * ‖q.2‖) p := hs.mul hn
  have hD : ContDiffAt ℝ 2 (fun q : ℝ × Space => q.1 * ‖q.2‖ + P.L0) p := hA.add contDiffAt_const
  have hτ : ContDiffAt ℝ 2 (nearT P) p := hA.div hD hden.ne'
  have h1τ : 0 < 1 - nearT P p := by
    have : nearT P p < 1 := by
      unfold nearT
      rw [div_lt_one hden]
      linarith [hP.L0_pos]
    linarith
  have c1 : ContDiffAt ℝ 2 (fun q => (1 - nearT P q) ^ (2 * P.eps)) p :=
    (contDiffAt_const.sub hτ).rpow_const_of_ne h1τ.ne'
  have hLin : ContDiffAt ℝ 2 (fun q : ℝ × Space => 1 + (q.1 * ‖q.2‖) ^ 2 / P.rc ^ 2) p :=
    contDiffAt_const.add ((hA.pow 2).div_const _)
  have hLpos : 0 < 1 + (p.1 * ‖p.2‖) ^ 2 / P.rc ^ 2 := by positivity
  have c2r : ContDiffAt ℝ 2 (fun q : ℝ × Space => (j : ℝ) * β * ((1 / 2) * Real.log (1 + (q.1 * ‖q.2‖) ^ 2 / P.rc ^ 2))) p :=
    contDiffAt_const.mul (contDiffAt_const.mul (hLin.log hLpos.ne'))
  have c2 : ContDiffAt ℝ 2 (fun q : ℝ × Space =>
      Complex.exp (Complex.I * (((j : ℝ) * β * ((1 / 2) * Real.log (1 + (q.1 * ‖q.2‖) ^ 2 / P.rc ^ 2)) : ℝ) : ℂ))) p :=
    (Complex.contDiff_exp.contDiffAt.comp p (contDiffAt_const.mul (Complex.ofRealCLM.contDiff.contDiffAt.comp p c2r)))
  have c3r : ContDiffAt ℝ 2 (fun q : ℝ × Space => ‖q.2‖ / (q.1 * ‖q.2‖ + P.L0)) p := hn.div hD hden.ne'
  have t1 : TameAt (fun q : ℝ × Space => (((1 - nearT P q) ^ (2 * P.eps) : ℝ) : ℂ)) p :=
    tame_of_contDiffAt (Complex.ofRealCLM.contDiff.contDiffAt.comp p c1)
  have t2 := tame_of_contDiffAt c2
  have t3 : TameAt (fun q : ℝ × Space => ((‖q.2‖ / (q.1 * ‖q.2‖ + P.L0) : ℝ) : ℂ)) p :=
    tame_of_contDiffAt (Complex.ofRealCLM.contDiff.contDiffAt.comp p c3r)
  have hΦ : TameAt (fun q : ℝ × Space => (nearT P q, q.2)) p := tame_of_contDiffAt (hτ.prodMk contDiffAt_snd)
  have hg : TameAt (atomAngularProfile a M T) (nearT P p, p.2) :=
    ang_tame a ha M T hT hT1 hax _ hz
  have t4 := tame_comp (Φ := fun q : ℝ × Space => (nearT P q, q.2)) (g := atomAngularProfile a M T) hg hΦ
  exact tame_congr (tame_mul (tame_mul (tame_mul t1 t2) t3) t4) (Filter.Eventually.of_forall fun q => rfl)

private theorem nearGlue_comp_le (L : ℝ × Space →L[ℝ] ℂ) :
    ‖L.comp (ContinuousLinearMap.inr ℝ ℝ Space)‖ ≤ ‖L‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun v => ?_
  have h := L.le_opNorm ((0 : ℝ), v)
  simpa [Prod.norm_def] using h

private theorem nearGlue {u : Space → ℂ} {F : ℝ × Space → ℂ} {δ : ℝ}
    (hu : ∀ s : ℝ, 0 < s → s < δ → ∀ z : Space, 1 / 4 < ‖z‖ → ‖z‖ < 2 → u (s • z) = (s : ℂ) * F (s, z))
    (hF : ∀ p ∈ Set.Ico 0 δ ×ˢ {z : Space | 1 / 4 < ‖z‖ ∧ ‖z‖ < 2}, ∃ U ∈ nhds p,
        (∀ q ∈ U, DifferentiableAt ℝ F q) ∧ ∃ K : NNReal, LipschitzOnWith K (fderiv ℝ F) U) :
    ∃ V : ℝ × Space → (Space →L[ℝ] ℂ),
      LocallyLipschitzOn (Set.Ico 0 δ ×ˢ {z : Space | 1 / 4 < ‖z‖ ∧ ‖z‖ < 2}) V ∧
      ∀ s : ℝ, 0 < s → s < δ → ∀ z : Space, 1 / 4 < ‖z‖ → ‖z‖ < 2 → fderiv ℝ u (s • z) = V (s, z) := by
  refine ⟨fun p => (fderiv ℝ F p).comp (ContinuousLinearMap.inr ℝ ℝ Space), ?_, ?_⟩
  · intro p hp
    obtain ⟨U, hU, -, K, hK⟩ := hF p hp
    refine ⟨K, U, mem_nhdsWithin_of_mem_nhds hU, LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_⟩
    rw [dist_eq_norm, ← ContinuousLinearMap.sub_comp]
    refine (nearGlue_comp_le _).trans ?_
    rw [← dist_eq_norm]
    exact hK.dist_le_mul x hx y hy
  · intro s hs hsδ z hz1 hz2
    obtain ⟨U, hU, hd, -⟩ := hF (s, z) ⟨⟨hs.le, hsδ⟩, hz1, hz2⟩
    have hdF : DifferentiableAt ℝ F (s, z) := hd _ (mem_of_mem_nhds hU)
    have hs0 : s ≠ 0 := hs.ne'
    have hopen : IsOpen {z : Space | 1 / 4 < ‖z‖ ∧ ‖z‖ < 2} :=
      (isOpen_lt continuous_const continuous_norm).inter (isOpen_lt continuous_norm continuous_const)
    have hcont : Continuous (fun y : Space => s⁻¹ • y) := continuous_const_smul _
    have hmem : s⁻¹ • (s • z) ∈ {z : Space | 1 / 4 < ‖z‖ ∧ ‖z‖ < 2} := by
      rw [inv_smul_smul₀ hs0]; exact ⟨hz1, hz2⟩
    have hev : u =ᶠ[nhds (s • z)] fun y => (s : ℂ) * F (s, s⁻¹ • y) := by
      filter_upwards [hcont.continuousAt.preimage_mem_nhds (hopen.mem_nhds hmem)] with y hy
      have := hu s hs hsδ (s⁻¹ • y) hy.1 hy.2
      rwa [smul_inv_smul₀ hs0] at this
    rw [hev.fderiv_eq]
    have hin : HasFDerivAt (fun y : Space => (s, s⁻¹ • y))
        ((0 : Space →L[ℝ] ℝ).prod (s⁻¹ • ContinuousLinearMap.id ℝ Space)) (s • z) :=
      (hasFDerivAt_const s (s • z)).prodMk ((hasFDerivAt_id (s • z)).const_smul s⁻¹)
    have hF' : HasFDerivAt F (fderiv ℝ F (s, z)) (s, s⁻¹ • (s • z)) := by
      rw [inv_smul_smul₀ hs0]; exact hdF.hasFDerivAt
    have hall : HasFDerivAt (fun y : Space => (s : ℂ) * F (s, s⁻¹ • y))
        ((s : ℂ) • (fderiv ℝ F (s, z)).comp ((0 : Space →L[ℝ] ℝ).prod (s⁻¹ • ContinuousLinearMap.id ℝ Space))) (s • z) :=
      (hF'.comp (s • z) hin).const_mul (s : ℂ)
    rw [hall.fderiv]
    ext v
    have e : ((0 : Space →L[ℝ] ℝ).prod (s⁻¹ • ContinuousLinearMap.id ℝ Space)) v = s⁻¹ • ((0 : ℝ), v) := by
      ext <;> simp
    simp only [FunLike.coe_smul, Pi.smul_apply, ContinuousLinearMap.comp_apply, e, map_smul,
      ContinuousLinearMap.inr_apply, Complex.real_smul, smul_eq_mul]
    push_cast
    rw [← mul_assoc, mul_inv_cancel₀ (by exact_mod_cast hs0), one_mul]

private theorem atomScalar_nearProfile (P : ChartParams) (hP : IsChartParams P) (j a : ℕ) (M : ℤ) (β : ℝ) (S : Spline)
    (ha : a ≤ 1) (hS : IsAtomSpline (decide (a = 0)) S j) (hM : j = 0 → M.natAbs = a) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ F : ℝ × Space → ℂ,
      (∀ s : ℝ, 0 < s → s < δ → ∀ z : Space, 1 / 4 < ‖z‖ → ‖z‖ < 2 →
        ((decayFactor P (s • z) : ℝ) : ℂ) * atomTerm P j a M β S (s • z) = (s : ℂ) * F (s, z)) ∧
      ∀ p ∈ Set.Ico 0 δ ×ˢ {z : Space | 1 / 4 < ‖z‖ ∧ ‖z‖ < 2}, ∃ U ∈ nhds p,
        (∀ q ∈ U, DifferentiableAt ℝ F q) ∧ ∃ K : NNReal, LipschitzOnWith K (fderiv ℝ F) U := by
  obtain ⟨T, hT, hT1, t1, ht1, hsplit, hTax⟩ := near_origin_split hS
  have hL0 := hP.L0_pos
  have hax : (∀ i < cellCount T.mesh.tBreaks, atSecond 1 (T.piece i (atomLastX T)) = 0) ∨ M.natAbs = a := by
    by_cases hj : j = 0
    · exact Or.inr (hM hj)
    · exact Or.inl (hTax hj)
  refine ⟨t1 * P.L0 / 2, by positivity, nearProfile P j a M β T, ?_, ?_⟩
  · intro s hs hsδ z hz1 hz2
    refine near_identity P j a M β S T hsplit hs z ?_
    unfold nearT
    have hden : 0 < s * ‖z‖ + P.L0 := by positivity
    rw [div_lt_iff₀ hden]
    have h1 : s * ‖z‖ < 2 * s := by nlinarith
    have h2 : 0 ≤ t1 * (s * ‖z‖) := by positivity
    nlinarith
  · intro p hp
    obtain ⟨⟨hp0, -⟩, hz1, -⟩ := hp
    have hz : p.2 ≠ 0 := by
      intro h
      rw [h, norm_zero] at hz1
      norm_num at hz1
    have hden : 0 < p.1 * ‖p.2‖ + P.L0 := by positivity
    exact tame_out (near_tame P hP j a ha M β T hT hT1 hax p hz hden)

theorem atomScalar_fderiv_nearScaled (P : ChartParams) (hP : IsChartParams P) (j a : ℕ) (M : ℤ) (β : ℝ) (S : Spline)
    (ha : a ≤ 1) (hS : IsAtomSpline (decide (a = 0)) S j) (hM : j = 0 → M.natAbs = a) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ V : ℝ × Space → (Space →L[ℝ] ℂ),
      LocallyLipschitzOn (Set.Ico 0 δ ×ˢ {z : Space | 1 / 4 < ‖z‖ ∧ ‖z‖ < 2}) V ∧
      ∀ s : ℝ, 0 < s → s < δ → ∀ z : Space, 1 / 4 < ‖z‖ → ‖z‖ < 2 → fderiv ℝ (fun y => ((decayFactor P y : ℝ) : ℂ) * atomTerm P j a M β S y) (s • z) = V (s, z) := by
  obtain ⟨δ, hδ, F, hu, hF⟩ := atomScalar_nearProfile P hP j a M β S ha hS hM
  obtain ⟨V, hV1, hV2⟩ := nearGlue (u := fun y => ((decayFactor P y : ℝ) : ℂ) * atomTerm P j a M β S y) hu hF
  exact ⟨δ, hδ, V, hV1, hV2⟩

end GivenFields

end CellCert

end Breakdown
