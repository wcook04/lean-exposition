import Breakdown.FracCell.GivenChartDefs

open scoped ContDiff

noncomputable section

namespace Breakdown

namespace FarDecayInternal

variable {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

def FarDecay (f : Space → F) (a : ℝ) : Prop :=
  ∃ R C : ℝ, 2 ≤ R ∧ 0 ≤ C ∧ ∀ y : Space, R ≤ ‖y‖ →
    (∀ z ∈ Metric.ball y 1, DifferentiableAt ℝ f z ∧ ‖f z‖ ≤ C * ‖y‖ ^ (-a) ∧
      ‖fderiv ℝ f z‖ ≤ C * ‖y‖ ^ (-(a + 1))) ∧
    ∀ z ∈ Metric.ball y 1, ∀ w ∈ Metric.ball y 1,
      ‖fderiv ℝ f z - fderiv ℝ f w‖ ≤ C * ‖y‖ ^ (-(a + 2)) * ‖z - w‖

theorem rpow_pair {r : ℝ} (hr : 0 < r) (u v w : ℝ) (h : u + v = w) : r ^ (-u) * r ^ (-v) = r ^ (-w) := by
  rw [← Real.rpow_add hr, ← h]
  congr 1
  ring

theorem rpow_anti {r : ℝ} (hr : 1 ≤ r) {a b : ℝ} (h : b ≤ a) : r ^ (-a) ≤ r ^ (-b) :=
  Real.rpow_le_rpow_of_exponent_le hr (by linarith)

theorem FarDecay.mono {f : Space → F} {a b : ℝ} (hf : FarDecay f a) (h : b ≤ a) : FarDecay f b := by
  obtain ⟨R, C, hR, hC, hf⟩ := hf
  refine ⟨R, C, hR, hC, fun y hy => ?_⟩
  have h1 : 1 ≤ ‖y‖ := by linarith
  obtain ⟨h1f, h2f⟩ := hf y hy
  refine ⟨fun z hz => ⟨(h1f z hz).1, (h1f z hz).2.1.trans (mul_le_mul_of_nonneg_left (rpow_anti h1 h) hC),
    (h1f z hz).2.2.trans (mul_le_mul_of_nonneg_left (rpow_anti h1 (by linarith)) hC)⟩, fun z hz w hw => ?_⟩
  exact (h2f z hz w hw).trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (rpow_anti h1 (by linarith)) hC) (norm_nonneg _))

theorem FarDecay.add {f g : Space → F} {a : ℝ} (hf : FarDecay f a) (hg : FarDecay g a) :
    FarDecay (fun y => f y + g y) a := by
  obtain ⟨R1, C1, hR1, hC1, hf⟩ := hf
  obtain ⟨R2, C2, hR2, hC2, hg⟩ := hg
  refine ⟨max R1 R2, C1 + C2, le_max_of_le_left hR1, add_nonneg hC1 hC2, fun y hy => ?_⟩
  obtain ⟨f1, f2⟩ := hf y ((le_max_left _ _).trans hy)
  obtain ⟨g1, g2⟩ := hg y ((le_max_right _ _).trans hy)
  have hd : ∀ z ∈ Metric.ball y 1, fderiv ℝ (fun y => f y + g y) z = fderiv ℝ f z + fderiv ℝ g z :=
    fun z hz => fderiv_add (f1 z hz).1 (g1 z hz).1
  refine ⟨fun z hz => ⟨(f1 z hz).1.add (g1 z hz).1, ?_, ?_⟩, fun z hz w hw => ?_⟩
  · calc ‖f z + g z‖ ≤ ‖f z‖ + ‖g z‖ := norm_add_le _ _
      _ ≤ C1 * ‖y‖ ^ (-a) + C2 * ‖y‖ ^ (-a) := add_le_add (f1 z hz).2.1 (g1 z hz).2.1
      _ = (C1 + C2) * ‖y‖ ^ (-a) := by ring
  · rw [hd z hz]
    calc ‖fderiv ℝ f z + fderiv ℝ g z‖ ≤ ‖fderiv ℝ f z‖ + ‖fderiv ℝ g z‖ := norm_add_le _ _
      _ ≤ C1 * ‖y‖ ^ (-(a + 1)) + C2 * ‖y‖ ^ (-(a + 1)) := add_le_add (f1 z hz).2.2 (g1 z hz).2.2
      _ = (C1 + C2) * ‖y‖ ^ (-(a + 1)) := by ring
  · rw [hd z hz, hd w hw]
    calc ‖fderiv ℝ f z + fderiv ℝ g z - (fderiv ℝ f w + fderiv ℝ g w)‖
        = ‖(fderiv ℝ f z - fderiv ℝ f w) + (fderiv ℝ g z - fderiv ℝ g w)‖ := by congr 1; abel
      _ ≤ ‖fderiv ℝ f z - fderiv ℝ f w‖ + ‖fderiv ℝ g z - fderiv ℝ g w‖ := norm_add_le _ _
      _ ≤ C1 * ‖y‖ ^ (-(a + 2)) * ‖z - w‖ + C2 * ‖y‖ ^ (-(a + 2)) * ‖z - w‖ :=
          add_le_add (f2 z hz w hw) (g2 z hz w hw)
      _ = (C1 + C2) * ‖y‖ ^ (-(a + 2)) * ‖z - w‖ := by ring

theorem FarDecay.clm {f : Space → F} {a : ℝ} (L : F →L[ℝ] G) (hf : FarDecay f a) :
    FarDecay (fun y => L (f y)) a := by
  obtain ⟨R, C, hR, hC, hf⟩ := hf
  refine ⟨R, ‖L‖ * C, hR, mul_nonneg (norm_nonneg _) hC, fun y hy => ?_⟩
  obtain ⟨f1, f2⟩ := hf y hy
  have hd : ∀ z ∈ Metric.ball y 1, fderiv ℝ (fun y => L (f y)) z = L.comp (fderiv ℝ f z) :=
    fun z hz => (L.hasFDerivAt.comp z (f1 z hz).1.hasFDerivAt).fderiv
  refine ⟨fun z hz => ⟨(L.differentiableAt.comp z (f1 z hz).1), ?_, ?_⟩, fun z hz w hw => ?_⟩
  · calc ‖L (f z)‖ ≤ ‖L‖ * ‖f z‖ := L.le_opNorm _
      _ ≤ ‖L‖ * (C * ‖y‖ ^ (-a)) := mul_le_mul_of_nonneg_left (f1 z hz).2.1 (norm_nonneg _)
      _ = ‖L‖ * C * ‖y‖ ^ (-a) := by ring
  · rw [hd z hz]
    calc ‖L.comp (fderiv ℝ f z)‖ ≤ ‖L‖ * ‖fderiv ℝ f z‖ := L.opNorm_comp_le _
      _ ≤ ‖L‖ * (C * ‖y‖ ^ (-(a + 1))) := mul_le_mul_of_nonneg_left (f1 z hz).2.2 (norm_nonneg _)
      _ = ‖L‖ * C * ‖y‖ ^ (-(a + 1)) := by ring
  · rw [hd z hz, hd w hw, ← L.comp_sub]
    calc ‖L.comp (fderiv ℝ f z - fderiv ℝ f w)‖ ≤ ‖L‖ * ‖fderiv ℝ f z - fderiv ℝ f w‖ := L.opNorm_comp_le _
      _ ≤ ‖L‖ * (C * ‖y‖ ^ (-(a + 2)) * ‖z - w‖) := mul_le_mul_of_nonneg_left (f2 z hz w hw) (norm_nonneg _)
      _ = ‖L‖ * C * ‖y‖ ^ (-(a + 2)) * ‖z - w‖ := by ring

theorem FarDecay.mul {f g : Space → ℂ} {a b : ℝ} (hf : FarDecay f a) (hg : FarDecay g b) :
    FarDecay (fun y => f y * g y) (a + b) := by
  obtain ⟨R1, C1, hR1, hC1, hf⟩ := hf
  obtain ⟨R2, C2, hR2, hC2, hg⟩ := hg
  have hCC : 0 ≤ C1 * C2 := mul_nonneg hC1 hC2
  refine ⟨max R1 R2, 4 * (C1 * C2), le_max_of_le_left hR1, by linarith, fun y hy => ?_⟩
  obtain ⟨f1, f2⟩ := hf y ((le_max_left _ _).trans hy)
  obtain ⟨g1, g2⟩ := hg y ((le_max_right _ _).trans hy)
  have hr : 0 < ‖y‖ := by linarith [le_max_left R1 R2]
  have pw : ∀ u : ℝ, 0 ≤ ‖y‖ ^ u := fun u => Real.rpow_nonneg (norm_nonneg y) u
  have hd : ∀ z ∈ Metric.ball y 1, fderiv ℝ (fun y => f y * g y) z = f z • fderiv ℝ g z + g z • fderiv ℝ f z :=
    fun z hz => ((f1 z hz).1.hasFDerivAt.mul (g1 z hz).1.hasFDerivAt).fderiv
  have lf : ∀ z ∈ Metric.ball y 1, ∀ w ∈ Metric.ball y 1, ‖f z - f w‖ ≤ C1 * ‖y‖ ^ (-(a + 1)) * ‖z - w‖ :=
    fun z hz w hw => (convex_ball y 1).norm_image_sub_le_of_norm_fderiv_le (fun x hx => (f1 x hx).1)
      (fun x hx => (f1 x hx).2.2) hw hz
  have lg : ∀ z ∈ Metric.ball y 1, ∀ w ∈ Metric.ball y 1, ‖g z - g w‖ ≤ C2 * ‖y‖ ^ (-(b + 1)) * ‖z - w‖ :=
    fun z hz w hw => (convex_ball y 1).norm_image_sub_le_of_norm_fderiv_le (fun x hx => (g1 x hx).1)
      (fun x hx => (g1 x hx).2.2) hw hz
  refine ⟨fun z hz => ⟨(f1 z hz).1.mul (g1 z hz).1, ?_, ?_⟩, fun z hz w hw => ?_⟩
  · rw [norm_mul]
    calc ‖f z‖ * ‖g z‖ ≤ (C1 * ‖y‖ ^ (-a)) * (C2 * ‖y‖ ^ (-b)) :=
          mul_le_mul (f1 z hz).2.1 (g1 z hz).2.1 (norm_nonneg _) (mul_nonneg hC1 (pw _))
      _ = C1 * C2 * (‖y‖ ^ (-a) * ‖y‖ ^ (-b)) := by ring
      _ = C1 * C2 * ‖y‖ ^ (-(a + b)) := by rw [rpow_pair hr a b _ rfl]
      _ ≤ 4 * (C1 * C2) * ‖y‖ ^ (-(a + b)) := by nlinarith [pw (-(a + b))]
  · rw [hd z hz]
    have t1 : ‖f z • fderiv ℝ g z‖ ≤ C1 * C2 * ‖y‖ ^ (-(a + b + 1)) := by
      rw [norm_smul, ← rpow_pair hr a (b + 1) _ (by ring)]
      calc ‖f z‖ * ‖fderiv ℝ g z‖ ≤ (C1 * ‖y‖ ^ (-a)) * (C2 * ‖y‖ ^ (-(b + 1))) :=
            mul_le_mul (f1 z hz).2.1 (g1 z hz).2.2 (norm_nonneg _) (mul_nonneg hC1 (pw _))
        _ = _ := by ring
    have t2 : ‖g z • fderiv ℝ f z‖ ≤ C1 * C2 * ‖y‖ ^ (-(a + b + 1)) := by
      rw [norm_smul, ← rpow_pair hr b (a + 1) _ (by ring)]
      calc ‖g z‖ * ‖fderiv ℝ f z‖ ≤ (C2 * ‖y‖ ^ (-b)) * (C1 * ‖y‖ ^ (-(a + 1))) :=
            mul_le_mul (g1 z hz).2.1 (f1 z hz).2.2 (norm_nonneg _) (mul_nonneg hC2 (pw _))
        _ = _ := by ring
    calc _ ≤ ‖f z • fderiv ℝ g z‖ + ‖g z • fderiv ℝ f z‖ := norm_add_le _ _
      _ ≤ C1 * C2 * ‖y‖ ^ (-(a + b + 1)) + C1 * C2 * ‖y‖ ^ (-(a + b + 1)) := add_le_add t1 t2
      _ ≤ 4 * (C1 * C2) * ‖y‖ ^ (-(a + b + 1)) := by nlinarith [pw (-(a + b + 1))]
  · rw [hd z hz, hd w hw]
    have hzw := norm_nonneg (z - w)
    have e : f z • fderiv ℝ g z + g z • fderiv ℝ f z - (f w • fderiv ℝ g w + g w • fderiv ℝ f w) =
        ((f z - f w) • fderiv ℝ g z + f w • (fderiv ℝ g z - fderiv ℝ g w)) +
          ((g z - g w) • fderiv ℝ f z + g w • (fderiv ℝ f z - fderiv ℝ f w)) := by
      simp only [sub_smul, smul_sub]
      abel
    have t1 : ‖(f z - f w) • fderiv ℝ g z‖ ≤ C1 * C2 * ‖y‖ ^ (-(a + b + 2)) * ‖z - w‖ := by
      rw [norm_smul, ← rpow_pair hr (a + 1) (b + 1) _ (by ring)]
      calc ‖f z - f w‖ * ‖fderiv ℝ g z‖ ≤ (C1 * ‖y‖ ^ (-(a + 1)) * ‖z - w‖) * (C2 * ‖y‖ ^ (-(b + 1))) :=
            mul_le_mul (lf z hz w hw) (g1 z hz).2.2 (norm_nonneg _) (mul_nonneg (mul_nonneg hC1 (pw _)) hzw)
        _ = _ := by ring
    have t2 : ‖f w • (fderiv ℝ g z - fderiv ℝ g w)‖ ≤ C1 * C2 * ‖y‖ ^ (-(a + b + 2)) * ‖z - w‖ := by
      rw [norm_smul, ← rpow_pair hr a (b + 2) _ (by ring)]
      calc ‖f w‖ * ‖fderiv ℝ g z - fderiv ℝ g w‖ ≤ (C1 * ‖y‖ ^ (-a)) * (C2 * ‖y‖ ^ (-(b + 2)) * ‖z - w‖) :=
            mul_le_mul (f1 w hw).2.1 (g2 z hz w hw) (norm_nonneg _) (mul_nonneg hC1 (pw _))
        _ = _ := by ring
    have t3 : ‖(g z - g w) • fderiv ℝ f z‖ ≤ C1 * C2 * ‖y‖ ^ (-(a + b + 2)) * ‖z - w‖ := by
      rw [norm_smul, ← rpow_pair hr (b + 1) (a + 1) _ (by ring)]
      calc ‖g z - g w‖ * ‖fderiv ℝ f z‖ ≤ (C2 * ‖y‖ ^ (-(b + 1)) * ‖z - w‖) * (C1 * ‖y‖ ^ (-(a + 1))) :=
            mul_le_mul (lg z hz w hw) (f1 z hz).2.2 (norm_nonneg _) (mul_nonneg (mul_nonneg hC2 (pw _)) hzw)
        _ = _ := by ring
    have t4 : ‖g w • (fderiv ℝ f z - fderiv ℝ f w)‖ ≤ C1 * C2 * ‖y‖ ^ (-(a + b + 2)) * ‖z - w‖ := by
      rw [norm_smul, ← rpow_pair hr b (a + 2) _ (by ring)]
      calc ‖g w‖ * ‖fderiv ℝ f z - fderiv ℝ f w‖ ≤ (C2 * ‖y‖ ^ (-b)) * (C1 * ‖y‖ ^ (-(a + 2)) * ‖z - w‖) :=
            mul_le_mul (g1 w hw).2.1 (f2 z hz w hw) (norm_nonneg _) (mul_nonneg hC2 (pw _))
        _ = _ := by ring
    rw [e]
    calc _ ≤ (‖(f z - f w) • fderiv ℝ g z‖ + ‖f w • (fderiv ℝ g z - fderiv ℝ g w)‖) +
          (‖(g z - g w) • fderiv ℝ f z‖ + ‖g w • (fderiv ℝ f z - fderiv ℝ f w)‖) :=
          (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) (norm_add_le _ _))
      _ ≤ _ := by linarith

theorem FarDecay.bounds {f : Space → F} {a : ℝ} (hf : FarDecay f a) :
    ∃ R C : ℝ, ∀ y : Space, R ≤ ‖y‖ →
      ‖f y‖ ≤ C * ‖y‖ ^ (-a) ∧ ‖fderiv ℝ f y‖ ≤ C * ‖y‖ ^ (-(a + 1)) ∧
        LipschitzOnWith (Real.toNNReal (C * ‖y‖ ^ (-(a + 2)))) (fderiv ℝ f) (Metric.ball y 1) := by
  obtain ⟨R, C, hR, hC, hf⟩ := hf
  refine ⟨R, C, fun y hy => ?_⟩
  obtain ⟨f1, f2⟩ := hf y hy
  have hy1 : y ∈ Metric.ball y 1 := Metric.mem_ball_self one_pos
  refine ⟨(f1 y hy1).2.1, (f1 y hy1).2.2, LipschitzOnWith.of_dist_le_mul fun z hz w hw => ?_⟩
  rw [Real.coe_toNNReal _ (mul_nonneg hC (Real.rpow_nonneg (norm_nonneg y) _)), dist_eq_norm, dist_eq_norm]
  exact f2 z hz w hw

theorem FarDecay.ofReal {f : Space → ℝ} {a : ℝ} (h : FarDecay f a) : FarDecay (fun y => (f y : ℂ)) a := by
  have h' := h.clm Complex.ofRealCLM
  have e : (fun y => Complex.ofRealCLM (f y)) = fun y => (f y : ℂ) := funext fun y => Complex.ofRealCLM_apply _
  rw [e] at h'
  exact h'

theorem FarDecay.re {f : Space → ℂ} {a : ℝ} (h : FarDecay f a) : FarDecay (fun y => (f y).re) a := by
  have h' := h.clm Complex.reCLM
  have e : (fun y => Complex.reCLM (f y)) = fun y => (f y).re := funext fun y => Complex.reCLM_apply _
  rw [e] at h'
  exact h'

theorem FarDecay.rmul {f g : Space → ℝ} {a b : ℝ} (hf : FarDecay f a) (hg : FarDecay g b) :
    FarDecay (fun y => f y * g y) (a + b) := by
  have h := (hf.ofReal.mul hg.ofReal).re
  have e : (fun y => ((f y : ℂ) * (g y : ℂ)).re) = fun y => f y * g y := funext fun y => by simp
  rw [e] at h
  exact h

theorem FarDecay.neg {f : Space → F} {a : ℝ} (h : FarDecay f a) : FarDecay (fun y => -f y) a := by
  have h' := h.clm (-ContinuousLinearMap.id ℝ F)
  have e : (fun y => (-ContinuousLinearMap.id ℝ F) (f y)) = fun y => -f y := funext fun y => by simp
  rw [e] at h'
  exact h'

theorem FarDecay.const (c : F) : FarDecay (fun _ : Space => c) 0 := by
  refine ⟨2, ‖c‖, le_rfl, norm_nonneg _, fun y _ => ⟨fun z _ => ⟨differentiableAt_const c, ?_, ?_⟩, fun z _ w _ => ?_⟩⟩
  · rw [neg_zero, Real.rpow_zero, mul_one]
  · rw [(hasFDerivAt_const c z).fderiv, norm_zero]
    positivity
  · rw [(hasFDerivAt_const c z).fderiv, (hasFDerivAt_const c w).fderiv, sub_self, norm_zero]
    positivity

theorem ball_norm_le {y z : Space} (hz : z ∈ Metric.ball y 1) : ‖z‖ ≤ ‖y‖ + 1 := by
  rw [Metric.mem_ball, dist_eq_norm] at hz
  linarith [norm_sub_norm_le z y]

theorem ball_norm_ge {y z : Space} (hz : z ∈ Metric.ball y 1) : ‖y‖ - 1 ≤ ‖z‖ := by
  rw [Metric.mem_ball, dist_eq_norm] at hz
  have := norm_sub_norm_le y z
  rw [norm_sub_rev] at this
  linarith

theorem FarDecay.ident : FarDecay (fun y : Space => y) (-1) := by
  refine ⟨2, 2, le_rfl, by norm_num, fun y hy => ⟨fun z hz => ⟨differentiableAt_id, ?_, ?_⟩, fun z _ w _ => ?_⟩⟩
  · rw [neg_neg, Real.rpow_one]
    linarith [ball_norm_le hz]
  · have e : -((-1 : ℝ) + 1) = 0 := by norm_num
    rw [e, Real.rpow_zero, fderiv_id']
    linarith [ContinuousLinearMap.norm_id_le (E := Space) (𝕜 := ℝ)]
  · rw [fderiv_id', fderiv_id', sub_self, norm_zero]
    positivity

theorem pow_bound {c C ρ u : ℝ} (hc : 0 < c) (hρ : 0 < ρ) (h1 : c * ρ ≤ u) (h2 : u ≤ C * ρ) (q : ℝ) :
    u ^ q ≤ (c ^ q + C ^ q) * ρ ^ q := by
  have hθ0 : c ≤ u / ρ := by rw [le_div_iff₀ hρ]; exact h1
  have hθ1 : u / ρ ≤ C := by rw [div_le_iff₀ hρ]; exact h2
  have hθ : 0 < u / ρ := lt_of_lt_of_le hc hθ0
  have e : u = (u / ρ) * ρ := by field_simp
  rw [e, Real.mul_rpow hθ.le hρ.le]
  refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg hρ.le q)
  have hcq := Real.rpow_nonneg hc.le q
  have hCq := Real.rpow_nonneg (hc.le.trans (hθ0.trans hθ1)) q
  rcases le_total 0 q with hq | hq
  · have := Real.rpow_le_rpow hθ.le hθ1 hq
    linarith
  · have := Real.rpow_le_rpow_of_nonpos hc hθ0 hq
    linarith

theorem rpow_weight {r : ℝ} (hr : 0 < r) (a q : ℝ) : (r ^ (-a)) ^ q = r ^ (-(a * q)) := by
  rw [← Real.rpow_mul hr.le]
  congr 1
  ring

theorem FarDecay.rpow {g : Space → ℝ} {a : ℝ} (hg : FarDecay g a) {R0 c : ℝ} (hc : 0 < c)
    (hlow : ∀ y : Space, R0 ≤ ‖y‖ → ∀ z ∈ Metric.ball y 1, c * ‖y‖ ^ (-a) ≤ g z) (p : ℝ) :
    FarDecay (fun z => g z ^ p) (a * p) := by
  obtain ⟨R, C, hR, hC, hg⟩ := hg
  set K0 := c ^ p + C ^ p with hK0
  set K1 := |p| * (c ^ (p - 1) + C ^ (p - 1)) * C with hK1
  set K2 := |p| * (|p - 1| * (c ^ (p - 1 - 1) + C ^ (p - 1 - 1)) * C) * C with hK2
  have q0 : ∀ q : ℝ, 0 ≤ c ^ q + C ^ q := fun q => add_nonneg (Real.rpow_nonneg hc.le q) (Real.rpow_nonneg hC q)
  have hK0n : 0 ≤ K0 := q0 p
  have hK1n : 0 ≤ K1 := mul_nonneg (mul_nonneg (abs_nonneg _) (q0 _)) hC
  have hK2n : 0 ≤ K2 := mul_nonneg (mul_nonneg (abs_nonneg _) (mul_nonneg (mul_nonneg (abs_nonneg _) (q0 _)) hC)) hC
  refine ⟨max R R0, K0 + K1 + K2 + K1, le_max_of_le_left hR, by linarith, fun y hy => ?_⟩
  obtain ⟨g1, g2⟩ := hg y ((le_max_left _ _).trans hy)
  have hr : 0 < ‖y‖ := by linarith [le_max_left R R0]
  have hρ : 0 < ‖y‖ ^ (-a) := Real.rpow_pos_of_pos hr _
  have pw : ∀ u : ℝ, 0 ≤ ‖y‖ ^ u := fun u => Real.rpow_nonneg (norm_nonneg y) u
  have lo : ∀ z ∈ Metric.ball y 1, c * ‖y‖ ^ (-a) ≤ g z := hlow y ((le_max_right _ _).trans hy)
  have gpos : ∀ z ∈ Metric.ball y 1, 0 < g z := fun z hz => lt_of_lt_of_le (mul_pos hc hρ) (lo z hz)
  have gq : ∀ z ∈ Metric.ball y 1, ∀ q : ℝ, g z ^ q ≤ (c ^ q + C ^ q) * ‖y‖ ^ (-(a * q)) := by
    intro z hz q
    rw [← rpow_weight hr]
    have hu := (g1 z hz).2.1
    rw [Real.norm_eq_abs] at hu
    exact pow_bound hc hρ (lo z hz) ((le_abs_self _).trans hu) q
  have gqn : ∀ z ∈ Metric.ball y 1, ∀ q : ℝ, 0 ≤ g z ^ q := fun z hz q => Real.rpow_nonneg (gpos z hz).le q
  have hd : ∀ z ∈ Metric.ball y 1, ∀ q : ℝ,
      HasFDerivAt (fun z => g z ^ q) ((q * g z ^ (q - 1)) • fderiv ℝ g z) z := fun z hz q =>
    (Real.hasDerivAt_rpow_const (Or.inl (gpos z hz).ne')).comp_hasFDerivAt z (g1 z hz).1.hasFDerivAt
  have dn : ∀ z ∈ Metric.ball y 1, ∀ q : ℝ, ‖(q * g z ^ (q - 1)) • fderiv ℝ g z‖ ≤
      |q| * (c ^ (q - 1) + C ^ (q - 1)) * C * ‖y‖ ^ (-(a * q + 1)) := by
    intro z hz q
    rw [norm_smul, Real.norm_eq_abs, abs_mul, abs_of_nonneg (gqn z hz _)]
    have h1 := gq z hz (q - 1)
    have h2 := (g1 z hz).2.2
    have e : ‖y‖ ^ (-(a * (q - 1))) * ‖y‖ ^ (-(a + 1)) = ‖y‖ ^ (-(a * q + 1)) := rpow_pair hr _ _ _ (by ring)
    calc |q| * g z ^ (q - 1) * ‖fderiv ℝ g z‖
        ≤ |q| * ((c ^ (q - 1) + C ^ (q - 1)) * ‖y‖ ^ (-(a * (q - 1)))) * (C * ‖y‖ ^ (-(a + 1))) :=
          mul_le_mul (mul_le_mul_of_nonneg_left h1 (abs_nonneg q)) h2 (norm_nonneg _)
            (mul_nonneg (abs_nonneg q) (mul_nonneg (q0 _) (pw _)))
      _ = |q| * (c ^ (q - 1) + C ^ (q - 1)) * C * (‖y‖ ^ (-(a * (q - 1))) * ‖y‖ ^ (-(a + 1))) := by ring
      _ = _ := by rw [e]
  have hfd : ∀ z ∈ Metric.ball y 1, fderiv ℝ (fun z => g z ^ p) z = (p * g z ^ (p - 1)) • fderiv ℝ g z :=
    fun z hz => (hd z hz p).fderiv
  refine ⟨fun z hz => ⟨(hd z hz p).differentiableAt, ?_, ?_⟩, fun z hz w hw => ?_⟩
  · show ‖g z ^ p‖ ≤ _
    rw [Real.norm_eq_abs, abs_of_nonneg (gqn z hz p)]
    exact (gq z hz p).trans (mul_le_mul_of_nonneg_right (by linarith) (pw _))
  · rw [hfd z hz]
    exact (dn z hz p).trans (mul_le_mul_of_nonneg_right (by linarith) (pw _))
  · rw [hfd z hz, hfd w hw]
    have hzw := norm_nonneg (z - w)
    have hm : ‖g z ^ (p - 1) - g w ^ (p - 1)‖ ≤
        (|p - 1| * (c ^ (p - 1 - 1) + C ^ (p - 1 - 1)) * C * ‖y‖ ^ (-(a * (p - 1) + 1))) * ‖z - w‖ := by
      have := (convex_ball y 1).norm_image_sub_le_of_norm_hasFDerivWithin_le
        (f := fun z => g z ^ (p - 1)) (fun x hx => (hd x hx (p - 1)).hasFDerivWithinAt)
        (fun x hx => dn x hx (p - 1)) hw hz
      exact this
    have e : (p * g z ^ (p - 1)) • fderiv ℝ g z - (p * g w ^ (p - 1)) • fderiv ℝ g w =
        (p * (g z ^ (p - 1) - g w ^ (p - 1))) • fderiv ℝ g z + (p * g w ^ (p - 1)) • (fderiv ℝ g z - fderiv ℝ g w) := by
      simp only [mul_sub, sub_smul, smul_sub]
      abel
    have t1 : ‖(p * (g z ^ (p - 1) - g w ^ (p - 1))) • fderiv ℝ g z‖ ≤ K2 * ‖y‖ ^ (-(a * p + 2)) * ‖z - w‖ := by
      rw [norm_smul, norm_mul, Real.norm_eq_abs]
      have e2 : ‖y‖ ^ (-(a * (p - 1) + 1)) * ‖y‖ ^ (-(a + 1)) = ‖y‖ ^ (-(a * p + 2)) := rpow_pair hr _ _ _ (by ring)
      calc |p| * ‖g z ^ (p - 1) - g w ^ (p - 1)‖ * ‖fderiv ℝ g z‖
          ≤ |p| * ((|p - 1| * (c ^ (p - 1 - 1) + C ^ (p - 1 - 1)) * C * ‖y‖ ^ (-(a * (p - 1) + 1))) * ‖z - w‖) *
              (C * ‖y‖ ^ (-(a + 1))) :=
            mul_le_mul (mul_le_mul_of_nonneg_left hm (abs_nonneg p)) (g1 z hz).2.2 (norm_nonneg _)
              (mul_nonneg (abs_nonneg p) (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (abs_nonneg _) (q0 _)) hC)
                (pw _)) hzw))
        _ = K2 * (‖y‖ ^ (-(a * (p - 1) + 1)) * ‖y‖ ^ (-(a + 1))) * ‖z - w‖ := by rw [hK2]; ring
        _ = _ := by rw [e2]
    have t2 : ‖(p * g w ^ (p - 1)) • (fderiv ℝ g z - fderiv ℝ g w)‖ ≤ K1 * ‖y‖ ^ (-(a * p + 2)) * ‖z - w‖ := by
      rw [norm_smul, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (gqn w hw _)]
      have e2 : ‖y‖ ^ (-(a * (p - 1))) * ‖y‖ ^ (-(a + 2)) = ‖y‖ ^ (-(a * p + 2)) := rpow_pair hr _ _ _ (by ring)
      calc |p| * g w ^ (p - 1) * ‖fderiv ℝ g z - fderiv ℝ g w‖
          ≤ |p| * ((c ^ (p - 1) + C ^ (p - 1)) * ‖y‖ ^ (-(a * (p - 1)))) * (C * ‖y‖ ^ (-(a + 2)) * ‖z - w‖) :=
            mul_le_mul (mul_le_mul_of_nonneg_left (gq w hw _) (abs_nonneg p)) (g2 z hz w hw) (norm_nonneg _)
              (mul_nonneg (abs_nonneg p) (mul_nonneg (q0 _) (pw _)))
        _ = K1 * (‖y‖ ^ (-(a * (p - 1))) * ‖y‖ ^ (-(a + 2))) * ‖z - w‖ := by rw [hK1]; ring
        _ = _ := by rw [e2]
    rw [e]
    have hX := pw (-(a * p + 2))
    calc _ ≤ _ := norm_add_le _ _
      _ ≤ K2 * ‖y‖ ^ (-(a * p + 2)) * ‖z - w‖ + K1 * ‖y‖ ^ (-(a * p + 2)) * ‖z - w‖ := add_le_add t1 t2
      _ ≤ (K0 + K1 + K2 + K1) * ‖y‖ ^ (-(a * p + 2)) * ‖z - w‖ := by
          have := mul_nonneg hX hzw
          nlinarith

theorem FarDecay.prodMk {f g : Space → ℝ} {a : ℝ} (hf : FarDecay f a) (hg : FarDecay g a) :
    FarDecay (fun y => (f y, g y)) a := by
  obtain ⟨R1, C1, hR1, hC1, hf⟩ := hf
  obtain ⟨R2, C2, hR2, hC2, hg⟩ := hg
  refine ⟨max R1 R2, C1 + C2, le_max_of_le_left hR1, add_nonneg hC1 hC2, fun y hy => ?_⟩
  obtain ⟨f1, f2⟩ := hf y ((le_max_left _ _).trans hy)
  obtain ⟨g1, g2⟩ := hg y ((le_max_right _ _).trans hy)
  have pw : ∀ u : ℝ, 0 ≤ ‖y‖ ^ u := fun u => Real.rpow_nonneg (norm_nonneg y) u
  have hd : ∀ z ∈ Metric.ball y 1, fderiv ℝ (fun y => (f y, g y)) z = (fderiv ℝ f z).prod (fderiv ℝ g z) :=
    fun z hz => ((f1 z hz).1.hasFDerivAt.prodMk (g1 z hz).1.hasFDerivAt).fderiv
  refine ⟨fun z hz => ⟨(f1 z hz).1.prodMk (g1 z hz).1, ?_, ?_⟩, fun z hz w hw => ?_⟩
  · refine norm_prod_le_iff.2 ⟨(f1 z hz).2.1.trans ?_, (g1 z hz).2.1.trans ?_⟩ <;>
      exact mul_le_mul_of_nonneg_right (by linarith) (pw _)
  · rw [hd z hz, ContinuousLinearMap.opNorm_prod]
    refine norm_prod_le_iff.2 ⟨(f1 z hz).2.2.trans ?_, (g1 z hz).2.2.trans ?_⟩ <;>
      exact mul_le_mul_of_nonneg_right (by linarith) (pw _)
  · rw [hd z hz, hd w hw]
    have e : (fderiv ℝ f z).prod (fderiv ℝ g z) - (fderiv ℝ f w).prod (fderiv ℝ g w) =
        (fderiv ℝ f z - fderiv ℝ f w).prod (fderiv ℝ g z - fderiv ℝ g w) := by
      ext v <;> simp
    rw [e, ContinuousLinearMap.opNorm_prod]
    have hzw := norm_nonneg (z - w)
    refine norm_prod_le_iff.2 ⟨(f2 z hz w hw).trans ?_, (g2 z hz w hw).trans ?_⟩ <;>
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith) (pw _)) hzw

theorem FarDecay.comp_compact {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Φ : Space → E} (hΦ : FarDecay Φ 0) {K : Set E} (hK : IsCompact K)
    (hΦK : ∀ z : Space, 1 ≤ ‖z‖ → Φ z ∈ K) {G : E → F} (hG : Differentiable ℝ G)
    (hGl : LocallyLipschitz (fderiv ℝ G)) : FarDecay (fun y => G (Φ y)) 0 := by
  obtain ⟨R, C, hR, hC, hΦ⟩ := hΦ
  obtain ⟨L, hL⟩ := hGl.locallyLipschitzOn.exists_lipschitzOnWith_of_compact hK
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn hG.continuous.continuousOn
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn hGl.continuous.continuousOn
  have hB0 : 0 ≤ max B 0 := le_max_right _ _
  have hM0 : 0 ≤ max M 0 := le_max_right _ _
  have hL0 : 0 ≤ (L : ℝ) := L.2
  have hMC : 0 ≤ max M 0 * C := mul_nonneg hM0 hC
  have hLCC : 0 ≤ (L : ℝ) * C * C := mul_nonneg (mul_nonneg hL0 hC) hC
  refine ⟨R, max B 0 + max M 0 * C + ((L : ℝ) * C * C + max M 0 * C), hR, by linarith, fun y hy => ?_⟩
  obtain ⟨p1, p2⟩ := hΦ y hy
  have hr : 0 < ‖y‖ := by linarith
  have pw : ∀ u : ℝ, 0 ≤ ‖y‖ ^ u := fun u => Real.rpow_nonneg (norm_nonneg y) u
  have inK : ∀ z ∈ Metric.ball y 1, Φ z ∈ K := fun z hz => hΦK z (by linarith [ball_norm_ge hz])
  have hd : ∀ z ∈ Metric.ball y 1, fderiv ℝ (fun y => G (Φ y)) z = (fderiv ℝ G (Φ z)).comp (fderiv ℝ Φ z) :=
    fun z hz => ((hG (Φ z)).hasFDerivAt.comp z (p1 z hz).1.hasFDerivAt).fderiv
  have lΦ : ∀ z ∈ Metric.ball y 1, ∀ w ∈ Metric.ball y 1, ‖Φ z - Φ w‖ ≤ C * ‖y‖ ^ (-(0 + 1 : ℝ)) * ‖z - w‖ :=
    fun z hz w hw => (convex_ball y 1).norm_image_sub_le_of_norm_fderiv_le (fun x hx => (p1 x hx).1)
      (fun x hx => (p1 x hx).2.2) hw hz
  have Mb : ∀ z ∈ Metric.ball y 1, ‖fderiv ℝ G (Φ z)‖ ≤ max M 0 := fun z hz => (hM _ (inK z hz)).trans (le_max_left _ _)
  refine ⟨fun z hz => ⟨(hG (Φ z)).comp z (p1 z hz).1, ?_, ?_⟩, fun z hz w hw => ?_⟩
  · rw [neg_zero, Real.rpow_zero, mul_one]
    have := (hB _ (inK z hz)).trans (le_max_left B 0)
    linarith
  · rw [hd z hz]
    calc _ ≤ ‖fderiv ℝ G (Φ z)‖ * ‖fderiv ℝ Φ z‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ max M 0 * (C * ‖y‖ ^ (-(0 + 1 : ℝ))) := mul_le_mul (Mb z hz) (p1 z hz).2.2 (norm_nonneg _) hM0
      _ ≤ _ := by
          rw [← mul_assoc]
          exact mul_le_mul_of_nonneg_right (by linarith) (pw _)
  · rw [hd z hz, hd w hw]
    have hzw := norm_nonneg (z - w)
    have e : (fderiv ℝ G (Φ z)).comp (fderiv ℝ Φ z) - (fderiv ℝ G (Φ w)).comp (fderiv ℝ Φ w) =
        (fderiv ℝ G (Φ z) - fderiv ℝ G (Φ w)).comp (fderiv ℝ Φ z) +
          (fderiv ℝ G (Φ w)).comp (fderiv ℝ Φ z - fderiv ℝ Φ w) := by
      rw [ContinuousLinearMap.sub_comp, ContinuousLinearMap.comp_sub]
      abel
    have hLz : ‖fderiv ℝ G (Φ z) - fderiv ℝ G (Φ w)‖ ≤ L * (C * ‖y‖ ^ (-(0 + 1 : ℝ)) * ‖z - w‖) := by
      have := hL.dist_le_mul (Φ z) (inK z hz) (Φ w) (inK w hw)
      rw [dist_eq_norm, dist_eq_norm] at this
      exact this.trans (mul_le_mul_of_nonneg_left (lΦ z hz w hw) hL0)
    have e2 : ‖y‖ ^ (-(0 + 1 : ℝ)) * ‖y‖ ^ (-(0 + 1 : ℝ)) = ‖y‖ ^ (-(0 + 2 : ℝ)) := rpow_pair hr _ _ _ (by ring)
    have t1 : ‖(fderiv ℝ G (Φ z) - fderiv ℝ G (Φ w)).comp (fderiv ℝ Φ z)‖ ≤
        (L : ℝ) * C * C * ‖y‖ ^ (-(0 + 2 : ℝ)) * ‖z - w‖ := by
      calc _ ≤ ‖fderiv ℝ G (Φ z) - fderiv ℝ G (Φ w)‖ * ‖fderiv ℝ Φ z‖ := ContinuousLinearMap.opNorm_comp_le _ _
        _ ≤ (L * (C * ‖y‖ ^ (-(0 + 1 : ℝ)) * ‖z - w‖)) * (C * ‖y‖ ^ (-(0 + 1 : ℝ))) :=
            mul_le_mul hLz (p1 z hz).2.2 (norm_nonneg _) (mul_nonneg hL0 (mul_nonneg (mul_nonneg hC (pw _)) hzw))
        _ = (L : ℝ) * C * C * (‖y‖ ^ (-(0 + 1 : ℝ)) * ‖y‖ ^ (-(0 + 1 : ℝ))) * ‖z - w‖ := by ring
        _ = _ := by rw [e2]
    have t2 : ‖(fderiv ℝ G (Φ w)).comp (fderiv ℝ Φ z - fderiv ℝ Φ w)‖ ≤
        max M 0 * C * ‖y‖ ^ (-(0 + 2 : ℝ)) * ‖z - w‖ := by
      calc _ ≤ ‖fderiv ℝ G (Φ w)‖ * ‖fderiv ℝ Φ z - fderiv ℝ Φ w‖ := ContinuousLinearMap.opNorm_comp_le _ _
        _ ≤ max M 0 * (C * ‖y‖ ^ (-(0 + 2 : ℝ)) * ‖z - w‖) := mul_le_mul (Mb w hw) (p2 z hz w hw) (norm_nonneg _) hM0
        _ = _ := by ring
    rw [e]
    have hX := mul_nonneg (pw (-(0 + 2 : ℝ))) hzw
    calc _ ≤ _ := norm_add_le _ _
      _ ≤ (L : ℝ) * C * C * ‖y‖ ^ (-(0 + 2 : ℝ)) * ‖z - w‖ + max M 0 * C * ‖y‖ ^ (-(0 + 2 : ℝ)) * ‖z - w‖ :=
          add_le_add t1 t2
      _ ≤ _ := by nlinarith

theorem FarDecay.comp_slope {Φ : Space → ℝ} {R C : ℝ} (hR : 2 ≤ R) (hC : 0 ≤ C)
    (hΦ : ∀ y : Space, R ≤ ‖y‖ →
      (∀ z ∈ Metric.ball y 1, DifferentiableAt ℝ Φ z ∧ ‖fderiv ℝ Φ z‖ ≤ C * ‖y‖ ^ (-(0 + 1 : ℝ))) ∧
      ∀ z ∈ Metric.ball y 1, ∀ w ∈ Metric.ball y 1,
        ‖fderiv ℝ Φ z - fderiv ℝ Φ w‖ ≤ C * ‖y‖ ^ (-(0 + 2 : ℝ)) * ‖z - w‖)
    {G : ℝ → F} {B M L : ℝ} (hG : Differentiable ℝ G) (hB : ∀ u, ‖G u‖ ≤ B) (hM : ∀ u, ‖fderiv ℝ G u‖ ≤ M)
    (hL : ∀ u v, ‖fderiv ℝ G u - fderiv ℝ G v‖ ≤ L * ‖u - v‖) (hL0 : 0 ≤ L) :
    FarDecay (fun y => G (Φ y)) 0 := by
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  have hMC : 0 ≤ M * C := mul_nonneg hM0 hC
  have hLCC : 0 ≤ L * C * C := mul_nonneg (mul_nonneg hL0 hC) hC
  refine ⟨R, B + M * C + (L * C * C + M * C), hR, by linarith, fun y hy => ?_⟩
  obtain ⟨p1, p2⟩ := hΦ y hy
  have hr : 0 < ‖y‖ := by linarith
  have pw : ∀ u : ℝ, 0 ≤ ‖y‖ ^ u := fun u => Real.rpow_nonneg (norm_nonneg y) u
  have hd : ∀ z ∈ Metric.ball y 1, fderiv ℝ (fun y => G (Φ y)) z = (fderiv ℝ G (Φ z)).comp (fderiv ℝ Φ z) :=
    fun z hz => ((hG (Φ z)).hasFDerivAt.comp z (p1 z hz).1.hasFDerivAt).fderiv
  have lΦ : ∀ z ∈ Metric.ball y 1, ∀ w ∈ Metric.ball y 1, ‖Φ z - Φ w‖ ≤ C * ‖y‖ ^ (-(0 + 1 : ℝ)) * ‖z - w‖ :=
    fun z hz w hw => (convex_ball y 1).norm_image_sub_le_of_norm_fderiv_le (fun x hx => (p1 x hx).1)
      (fun x hx => (p1 x hx).2) hw hz
  refine ⟨fun z hz => ⟨(hG (Φ z)).comp z (p1 z hz).1, ?_, ?_⟩, fun z hz w hw => ?_⟩
  · rw [neg_zero, Real.rpow_zero, mul_one]
    have := hB (Φ z)
    linarith
  · rw [hd z hz]
    calc _ ≤ ‖fderiv ℝ G (Φ z)‖ * ‖fderiv ℝ Φ z‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ M * (C * ‖y‖ ^ (-(0 + 1 : ℝ))) := mul_le_mul (hM _) (p1 z hz).2 (norm_nonneg _) hM0
      _ ≤ _ := by
          rw [← mul_assoc]
          exact mul_le_mul_of_nonneg_right (by linarith) (pw _)
  · rw [hd z hz, hd w hw]
    have hzw := norm_nonneg (z - w)
    have e : (fderiv ℝ G (Φ z)).comp (fderiv ℝ Φ z) - (fderiv ℝ G (Φ w)).comp (fderiv ℝ Φ w) =
        (fderiv ℝ G (Φ z) - fderiv ℝ G (Φ w)).comp (fderiv ℝ Φ z) +
          (fderiv ℝ G (Φ w)).comp (fderiv ℝ Φ z - fderiv ℝ Φ w) := by
      rw [ContinuousLinearMap.sub_comp, ContinuousLinearMap.comp_sub]
      abel
    have hLz : ‖fderiv ℝ G (Φ z) - fderiv ℝ G (Φ w)‖ ≤ L * (C * ‖y‖ ^ (-(0 + 1 : ℝ)) * ‖z - w‖) :=
      (hL _ _).trans (mul_le_mul_of_nonneg_left (lΦ z hz w hw) hL0)
    have e2 : ‖y‖ ^ (-(0 + 1 : ℝ)) * ‖y‖ ^ (-(0 + 1 : ℝ)) = ‖y‖ ^ (-(0 + 2 : ℝ)) := rpow_pair hr _ _ _ (by ring)
    have t1 : ‖(fderiv ℝ G (Φ z) - fderiv ℝ G (Φ w)).comp (fderiv ℝ Φ z)‖ ≤
        L * C * C * ‖y‖ ^ (-(0 + 2 : ℝ)) * ‖z - w‖ := by
      calc _ ≤ ‖fderiv ℝ G (Φ z) - fderiv ℝ G (Φ w)‖ * ‖fderiv ℝ Φ z‖ := ContinuousLinearMap.opNorm_comp_le _ _
        _ ≤ (L * (C * ‖y‖ ^ (-(0 + 1 : ℝ)) * ‖z - w‖)) * (C * ‖y‖ ^ (-(0 + 1 : ℝ))) :=
            mul_le_mul hLz (p1 z hz).2 (norm_nonneg _) (mul_nonneg hL0 (mul_nonneg (mul_nonneg hC (pw _)) hzw))
        _ = L * C * C * (‖y‖ ^ (-(0 + 1 : ℝ)) * ‖y‖ ^ (-(0 + 1 : ℝ))) * ‖z - w‖ := by ring
        _ = _ := by rw [e2]
    have t2 : ‖(fderiv ℝ G (Φ w)).comp (fderiv ℝ Φ z - fderiv ℝ Φ w)‖ ≤
        M * C * ‖y‖ ^ (-(0 + 2 : ℝ)) * ‖z - w‖ := by
      calc _ ≤ ‖fderiv ℝ G (Φ w)‖ * ‖fderiv ℝ Φ z - fderiv ℝ Φ w‖ := ContinuousLinearMap.opNorm_comp_le _ _
        _ ≤ M * (C * ‖y‖ ^ (-(0 + 2 : ℝ)) * ‖z - w‖) := mul_le_mul (hM _) (p2 z hz w hw) (norm_nonneg _) hM0
        _ = _ := by ring
    rw [e]
    have hX := mul_nonneg (pw (-(0 + 2 : ℝ))) hzw
    calc _ ≤ _ := norm_add_le _ _
      _ ≤ L * C * C * ‖y‖ ^ (-(0 + 2 : ℝ)) * ‖z - w‖ + M * C * ‖y‖ ^ (-(0 + 2 : ℝ)) * ‖z - w‖ := add_le_add t1 t2
      _ ≤ _ := by nlinarith

theorem FarDecay.log_slope {g : Space → ℝ} {a : ℝ} (hg : FarDecay g a) {R0 c : ℝ} (hc : 0 < c)
    (hlow : ∀ y : Space, R0 ≤ ‖y‖ → ∀ z ∈ Metric.ball y 1, c * ‖y‖ ^ (-a) ≤ g z) :
    ∃ R C : ℝ, 2 ≤ R ∧ 0 ≤ C ∧ ∀ y : Space, R ≤ ‖y‖ →
      (∀ z ∈ Metric.ball y 1, DifferentiableAt ℝ (fun z => Real.log (g z)) z ∧
        ‖fderiv ℝ (fun z => Real.log (g z)) z‖ ≤ C * ‖y‖ ^ (-(0 + 1 : ℝ))) ∧
      ∀ z ∈ Metric.ball y 1, ∀ w ∈ Metric.ball y 1,
        ‖fderiv ℝ (fun z => Real.log (g z)) z - fderiv ℝ (fun z => Real.log (g z)) w‖ ≤
          C * ‖y‖ ^ (-(0 + 2 : ℝ)) * ‖z - w‖ := by
  have hh := hg.rpow hc hlow (-1)
  obtain ⟨R1, C1, hR1, hC1, hg'⟩ := hg
  obtain ⟨R2, C2, hR2, hC2, hh'⟩ := hh
  have hCC : 0 ≤ C1 * C2 := mul_nonneg hC1 hC2
  refine ⟨max (max R1 R2) R0, 2 * (C1 * C2), le_max_of_le_left (le_max_of_le_left hR1), by linarith, fun y hy => ?_⟩
  have hy1 : R1 ≤ ‖y‖ := (le_max_left _ _).trans ((le_max_left _ _).trans hy)
  have hy2 : R2 ≤ ‖y‖ := (le_max_right _ _).trans ((le_max_left _ _).trans hy)
  have hy0 : R0 ≤ ‖y‖ := (le_max_right _ _).trans hy
  obtain ⟨g1, g2⟩ := hg' y hy1
  obtain ⟨h1, h2⟩ := hh' y hy2
  have hr : 0 < ‖y‖ := by linarith
  have pw : ∀ u : ℝ, 0 ≤ ‖y‖ ^ u := fun u => Real.rpow_nonneg (norm_nonneg y) u
  have gpos : ∀ z ∈ Metric.ball y 1, 0 < g z := fun z hz =>
    lt_of_lt_of_le (mul_pos hc (Real.rpow_pos_of_pos hr _)) (hlow y hy0 z hz)
  have hinv : ∀ z ∈ Metric.ball y 1, g z ^ (-1 : ℝ) = (g z)⁻¹ := fun z _ => Real.rpow_neg_one _
  have hd : ∀ z ∈ Metric.ball y 1, fderiv ℝ (fun z => Real.log (g z)) z = (g z ^ (-1 : ℝ)) • fderiv ℝ g z := by
    intro z hz
    rw [hinv z hz]
    have := ((Real.hasDerivAt_log (gpos z hz).ne').comp_hasFDerivAt z (g1 z hz).1.hasFDerivAt).fderiv
    exact this
  have lh : ∀ z ∈ Metric.ball y 1, ∀ w ∈ Metric.ball y 1,
      ‖g z ^ (-1 : ℝ) - g w ^ (-1 : ℝ)‖ ≤ C2 * ‖y‖ ^ (-(a * -1 + 1)) * ‖z - w‖ :=
    fun z hz w hw => (convex_ball y 1).norm_image_sub_le_of_norm_fderiv_le
      (f := fun z => g z ^ (-1 : ℝ)) (fun x hx => (h1 x hx).1) (fun x hx => (h1 x hx).2.2) hw hz
  refine ⟨fun z hz => ⟨((Real.hasDerivAt_log (gpos z hz).ne').comp_hasFDerivAt z
      (g1 z hz).1.hasFDerivAt).differentiableAt, ?_⟩, fun z hz w hw => ?_⟩
  · rw [hd z hz, norm_smul]
    have e : ‖y‖ ^ (-(a * -1)) * ‖y‖ ^ (-(a + 1)) = ‖y‖ ^ (-(0 + 1 : ℝ)) := rpow_pair hr _ _ _ (by ring)
    calc ‖g z ^ (-1 : ℝ)‖ * ‖fderiv ℝ g z‖ ≤ (C2 * ‖y‖ ^ (-(a * -1))) * (C1 * ‖y‖ ^ (-(a + 1))) :=
          mul_le_mul (h1 z hz).2.1 (g1 z hz).2.2 (norm_nonneg _) (mul_nonneg hC2 (pw _))
      _ = C1 * C2 * (‖y‖ ^ (-(a * -1)) * ‖y‖ ^ (-(a + 1))) := by ring
      _ = C1 * C2 * ‖y‖ ^ (-(0 + 1 : ℝ)) := by rw [e]
      _ ≤ _ := by nlinarith [pw (-(0 + 1 : ℝ))]
  · rw [hd z hz, hd w hw]
    have hzw := norm_nonneg (z - w)
    have e : (g z ^ (-1 : ℝ)) • fderiv ℝ g z - (g w ^ (-1 : ℝ)) • fderiv ℝ g w =
        (g z ^ (-1 : ℝ) - g w ^ (-1 : ℝ)) • fderiv ℝ g z + (g w ^ (-1 : ℝ)) • (fderiv ℝ g z - fderiv ℝ g w) := by
      simp only [sub_smul, smul_sub]
      abel
    have t1 : ‖(g z ^ (-1 : ℝ) - g w ^ (-1 : ℝ)) • fderiv ℝ g z‖ ≤ C1 * C2 * ‖y‖ ^ (-(0 + 2 : ℝ)) * ‖z - w‖ := by
      rw [norm_smul, ← rpow_pair hr (a * -1 + 1) (a + 1) _ (by ring)]
      calc _ ≤ (C2 * ‖y‖ ^ (-(a * -1 + 1)) * ‖z - w‖) * (C1 * ‖y‖ ^ (-(a + 1))) :=
            mul_le_mul (lh z hz w hw) (g1 z hz).2.2 (norm_nonneg _) (mul_nonneg (mul_nonneg hC2 (pw _)) hzw)
        _ = _ := by ring
    have t2 : ‖(g w ^ (-1 : ℝ)) • (fderiv ℝ g z - fderiv ℝ g w)‖ ≤ C1 * C2 * ‖y‖ ^ (-(0 + 2 : ℝ)) * ‖z - w‖ := by
      rw [norm_smul, ← rpow_pair hr (a * -1) (a + 2) _ (by ring)]
      calc _ ≤ (C2 * ‖y‖ ^ (-(a * -1))) * (C1 * ‖y‖ ^ (-(a + 2)) * ‖z - w‖) :=
            mul_le_mul (h1 w hw).2.1 (g2 z hz w hw) (norm_nonneg _) (mul_nonneg hC2 (pw _))
        _ = _ := by ring
    rw [e]
    calc _ ≤ _ := norm_add_le _ _
      _ ≤ _ := add_le_add t1 t2
      _ = _ := by ring

end FarDecayInternal

end Breakdown
