import Breakdown.CertCell.ShapeStatements

open scoped ContDiff

noncomputable section

namespace Breakdown

namespace CertCell

namespace GivenShape

namespace Internal

namespace TypeTwoNear

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

theorem tame_of_slope {f : E → F} (hd : Differentiable ℝ f)
    (hl : ∀ R : ℝ, ∃ L : NNReal, LipschitzOnWith L (fderiv ℝ f) (Metric.closedBall 0 R)) (y : E) :
    TameAt f y := by
  obtain ⟨L, hL⟩ := hl (‖y‖ + 1)
  have hsub : Metric.ball y 1 ⊆ Metric.closedBall 0 (‖y‖ + 1) := by
    intro z hz
    rw [Metric.mem_ball, dist_eq_norm] at hz
    rw [Metric.mem_closedBall, dist_zero_right]
    have := norm_le_norm_add_norm_sub' z y
    linarith
  refine ⟨1, one_pos, fderiv ℝ f, L, L.2, fun z _ => (hd z).hasFDerivAt, fun z hz w hw => ?_⟩
  have := hL.dist_le_mul z (hsub hz) w (hsub hw)
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

theorem tame_add {f g : E → F} {y : E} (hf : TameAt f y) (hg : TameAt g y) :
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

theorem tame_clm {f : E → F} {y : E} (L : F →L[ℝ] G) (hf : TameAt f y) :
    TameAt (fun z => L (f z)) y := by
  obtain ⟨r, hr, f', K, hK0, h1, h2⟩ := hf
  refine ⟨r, hr, fun z => L.comp (f' z), ‖L‖ * K, by positivity,
    fun z hz => L.hasFDerivAt.comp z (h1 z hz), fun z hz w hw => ?_⟩
  rw [← ContinuousLinearMap.comp_sub]
  calc _ ≤ ‖L‖ * ‖f' z - f' w‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖L‖ * (K * ‖z - w‖) := mul_le_mul_of_nonneg_left (h2 z hz w hw) (norm_nonneg _)
    _ = ‖L‖ * K * ‖z - w‖ := by ring

theorem tame_comp {Φ : E → F} {g : F → G} {y : E} (hg : TameAt g (Φ y)) (hΦ : TameAt Φ y) :
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

theorem tame_mul {c d : E → ℂ} {y : E} (hc : TameAt c y) (hd : TameAt d y) :
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

theorem tame_neg {f : E → F} {y : E} (hf : TameAt f y) : TameAt (fun z => -f z) y :=
  tame_congr (tame_clm (-(ContinuousLinearMap.id ℝ F)) hf) (Filter.Eventually.of_forall fun z => by simp)

theorem tame_sub {f g : E → F} {y : E} (hf : TameAt f y) (hg : TameAt g y) :
    TameAt (fun z => f z - g z) y :=
  tame_congr (tame_add hf (tame_neg hg)) (Filter.Eventually.of_forall fun z => by simp [sub_eq_add_neg])

theorem tame_region {f : E → F} {y : E} (h : TameAt f y) :
    ∃ U ∈ nhds y, (∀ q ∈ U, DifferentiableAt ℝ f q) ∧ ∃ K : NNReal, LipschitzOnWith K (fderiv ℝ f) U := by
  obtain ⟨r, hr, f', K, hK0, h1, h2⟩ := h
  refine ⟨Metric.ball y r, Metric.ball_mem_nhds y hr, fun z hz => (h1 z hz).differentiableAt, ⟨K, hK0⟩,
    LipschitzOnWith.of_dist_le_mul fun z hz w hw => ?_⟩
  rw [(h1 z hz).fderiv, (h1 w hw).fderiv, dist_eq_norm, dist_eq_norm]
  exact h2 z hz w hw

theorem tame_pi {f : E → (Fin 3 → ℂ)} {y : E} (h : ∀ i, TameAt (fun z => f z i) y) : TameAt f y := by
  have e : ∀ z, f z = ∑ i : Fin 3, ContinuousLinearMap.single ℝ (fun _ : Fin 3 => ℂ) i (f z i) := by
    intro z
    funext j
    simp [Finset.sum_apply, Pi.single_apply]
  have h3 := tame_add (tame_add (tame_clm (ContinuousLinearMap.single ℝ (fun _ : Fin 3 => ℂ) 0) (h 0))
    (tame_clm (ContinuousLinearMap.single ℝ (fun _ : Fin 3 => ℂ) 1) (h 1)))
    (tame_clm (ContinuousLinearMap.single ℝ (fun _ : Fin 3 => ℂ) 2) (h 2))
  refine tame_congr h3 (Filter.Eventually.of_forall fun z => ?_)
  rw [e z, Fin.sum_univ_three]

end Tame

theorem scale_norm_le (s : ℝ) (hs : 0 < s) :
    ‖(0 : Space →L[ℝ] ℝ).prod (s⁻¹ • ContinuousLinearMap.id ℝ Space)‖ ≤ s⁻¹ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (inv_nonneg.2 hs.le) (fun v => ?_)
  rw [ContinuousLinearMap.prod_apply, Prod.norm_def]
  have ha : |s| = s := abs_of_pos hs
  simp [norm_smul, ha]
  positivity

theorem scaled_hasFDerivAt {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
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

theorem scaled_fderiv_slope {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {f : Space → G} {F : ℝ × Space → G} {ρ : ℝ} (hρ : 0 < ρ) (hf0 : f 0 = 0)
    (hscale : ∀ s : ℝ, 0 < s → ∀ v : Space, v ≠ 0 → f (s • v) = (s ^ 2) • F (s, v))
    (hF : ∀ p ∈ Set.Icc 0 ρ ×ˢ (Metric.closedBall (0 : Space) 1 \ Metric.ball 0 (1 / 2)),
      ∃ U ∈ nhds p, (∀ q ∈ U, DifferentiableAt ℝ F q) ∧ ∃ K : NNReal, LipschitzOnWith K (fderiv ℝ F) U) :
    (∀ y ∈ Metric.ball (0 : Space) ρ, DifferentiableAt ℝ f y) ∧
      ∃ K : NNReal, LipschitzOnWith K (fderiv ℝ f) (Metric.ball 0 ρ) := by
  set C : Set (ℝ × Space) := Set.Icc 0 ρ ×ˢ (Metric.closedBall (0 : Space) 1 \ Metric.ball 0 (1 / 2)) with hC
  have hCc : IsCompact C := isCompact_Icc.prod ((isCompact_closedBall _ _).diff Metric.isOpen_ball)
  have hdiff : ∀ p ∈ C, DifferentiableAt ℝ F p := fun p hp => by
    obtain ⟨U, hU, hd, -⟩ := hF p hp
    exact hd p (mem_of_mem_nhds hU)
  have hloc : LocallyLipschitzOn C (fderiv ℝ F) := by
    intro p hp
    obtain ⟨U, hU, -, K, hK⟩ := hF p hp
    exact ⟨K, U, mem_nhdsWithin_of_mem_nhds hU, hK⟩
  obtain ⟨L, hL⟩ := hloc.exists_lipschitzOnWith_of_compact hCc
  obtain ⟨M, hM⟩ := hCc.exists_bound_of_continuousOn hL.continuousOn
  obtain ⟨N, hN⟩ := hCc.exists_bound_of_continuousOn
    (fun p hp => (hdiff p hp).continuousAt.continuousWithinAt : ContinuousOn F C)
  have hM0 : 0 ≤ M := by
    have h := hM (0, EuclideanSpace.single 0 1)
      ⟨⟨le_rfl, hρ.le⟩, by simp [Metric.mem_closedBall, Metric.mem_ball]; norm_num⟩
    exact (norm_nonneg _).trans h
  have memC : ∀ s w, 0 < s → s ≤ ρ → 1 / 2 * s ≤ ‖w‖ → ‖w‖ ≤ s → (s, s⁻¹ • w) ∈ C := by
    intro s w hs hsρ h1 h2
    refine ⟨⟨hs.le, hsρ⟩, ?_, ?_⟩
    · rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hs)]
      rw [inv_mul_le_iff₀ hs]
      linarith
    · rw [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hs), not_lt]
      rw [le_inv_mul_iff₀ hs]
      linarith
  have hd0 : HasFDerivAt f (0 : Space →L[ℝ] G) 0 := by
    rw [hasFDerivAt_iff_isLittleO_nhds_zero]
    have hbig : (fun h : Space => f (0 + h) - f 0 - (0 : Space →L[ℝ] G) h) =O[nhds 0] fun h => ‖h‖ ^ 2 := by
      refine Asymptotics.IsBigO.of_bound N ?_
      filter_upwards [Metric.ball_mem_nhds (0 : Space) hρ] with h hh
      rw [Metric.mem_ball, dist_zero_right] at hh
      simp only [zero_add, hf0, sub_zero, zero_apply, norm_pow, norm_norm]
      by_cases h0 : h = 0
      · simp [h0, hf0]
      have hs : 0 < ‖h‖ := norm_pos_iff.2 h0
      have e := hscale ‖h‖ hs (‖h‖⁻¹ • h) (smul_ne_zero (inv_ne_zero hs.ne') h0)
      rw [smul_inv_smul₀ hs.ne'] at e
      rw [e, norm_smul, norm_pow, Real.norm_eq_abs, abs_of_pos hs, mul_comm]
      exact mul_le_mul_of_nonneg_right (hN _ (memC _ _ hs hh.le (by linarith) le_rfl)) (by positivity)
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
          exact mul_le_mul (hM _ (memC _ _ hs hw.le (by linarith) le_rfl)) (scale_norm_le _ hs) (norm_nonneg _) hM0
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
              (mul_le_mul hLd (scale_norm_le _ hs) (norm_nonneg _) (by positivity))
        _ = L * ‖y - z‖ := by field_simp
        _ ≤ (L + 4 * M) * ‖y - z‖ := by gcongr; linarith
  refine ⟨fun y hy => ?_, Real.toNNReal (L + 4 * M), LipschitzOnWith.of_dist_le' fun y hy z hz => ?_⟩
  · rw [Metric.mem_ball, dist_zero_right] at hy
    by_cases h0 : y = 0
    · rw [h0]; exact hd0.differentiableAt
    have hs : 0 < ‖y‖ := norm_pos_iff.2 h0
    exact (scaled_hasFDerivAt hscale hs h0 (hdiff _ (memC _ y hs hy.le (by linarith) le_rfl))).differentiableAt
  · rw [Metric.mem_ball, dist_zero_right] at hy hz
    rw [dist_eq_norm, dist_eq_norm]
    rcases le_total ‖z‖ ‖y‖ with h | h
    · exact key y z hy h
    · rw [← norm_neg, neg_sub, ← norm_neg (y - z), neg_sub]
      exact key z y hz h

end TypeTwoNear

end Internal

end GivenShape

end CertCell

end Breakdown
