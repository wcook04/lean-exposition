import Breakdown.FracCell.GivenProfileFarModeSplit

open scoped ContDiff

noncomputable section

namespace Breakdown

namespace FracCellInternal

open CellCert.GivenFields

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

private def SlopeBoundOn (f : Space → E) (K : ℝ) (s : Set Space) : Prop :=
  ∀ z ∈ s, ∀ w ∈ s, ‖f z - f w‖ ≤ K * ‖z - w‖

private def BallData (f : Space → E) (y : Space) (v d l : ℝ) : Prop :=
  (∀ z ∈ Metric.ball y 1, DifferentiableAt ℝ f z ∧ ‖f z‖ ≤ v ∧ ‖fderiv ℝ f z‖ ≤ d) ∧
    SlopeBoundOn (fderiv ℝ f) l (Metric.ball y 1)

private theorem slopeBoundOn_of_fderiv {f : Space → E} {y : Space} {r K : ℝ}
    (hd : ∀ z ∈ Metric.ball y r, DifferentiableAt ℝ f z) (hb : ∀ z ∈ Metric.ball y r, ‖fderiv ℝ f z‖ ≤ K) :
    SlopeBoundOn f K (Metric.ball y r) := fun z hz w hw =>
  (convex_ball y r).norm_image_sub_le_of_norm_fderiv_le hd hb hw hz

private theorem slopeBoundOn_congr {f g : Space → E} {K : ℝ} {s : Set Space} (h : SlopeBoundOn g K s)
    (he : ∀ z ∈ s, f z = g z) : SlopeBoundOn f K s := fun z hz w hw => by
  rw [he z hz, he w hw]; exact h z hz w hw

private theorem slopeBoundOn_mono {f : Space → E} {K K' : ℝ} {s : Set Space} (h : SlopeBoundOn f K s) (hK : K ≤ K') :
    SlopeBoundOn f K' s := fun z hz w hw => (h z hz w hw).trans (mul_le_mul_of_nonneg_right hK (norm_nonneg _))

private theorem slopeBoundOn_add {f g : Space → E} {K1 K2 : ℝ} {s : Set Space} (hf : SlopeBoundOn f K1 s) (hg : SlopeBoundOn g K2 s) :
    SlopeBoundOn (fun z => f z + g z) (K1 + K2) s := fun z hz w hw => by
  have e : f z + g z - (f w + g w) = (f z - f w) + (g z - g w) := by abel
  rw [e]
  calc _ ≤ ‖f z - f w‖ + ‖g z - g w‖ := norm_add_le _ _
    _ ≤ K1 * ‖z - w‖ + K2 * ‖z - w‖ := add_le_add (hf z hz w hw) (hg z hz w hw)
    _ = (K1 + K2) * ‖z - w‖ := by ring

private theorem slopeBoundOn_smul {φ : Space → ℝ} {L : Space → E} {k1 k2 v1 v2 : ℝ} {s : Set Space}
    (hφ : SlopeBoundOn φ k1 s) (hL : SlopeBoundOn L k2 s) (bφ : ∀ z ∈ s, ‖φ z‖ ≤ v1) (bL : ∀ z ∈ s, ‖L z‖ ≤ v2) :
    SlopeBoundOn (fun z => φ z • L z) (k1 * v2 + v1 * k2) s := fun z hz w hw => by
  have e : φ z • L z - φ w • L w = (φ z - φ w) • L z + φ w • (L z - L w) := by
    rw [sub_smul, smul_sub]; abel
  rw [e]
  have h1 : ‖(φ z - φ w) • L z‖ ≤ k1 * ‖z - w‖ * v2 := by
    rw [norm_smul]
    exact mul_le_mul (hφ z hz w hw) (bL z hz) (norm_nonneg _) ((norm_nonneg _).trans (hφ z hz w hw))
  have h2 : ‖φ w • (L z - L w)‖ ≤ v1 * (k2 * ‖z - w‖) := by
    rw [norm_smul]
    exact mul_le_mul (bφ w hw) (hL z hz w hw) (norm_nonneg _) ((norm_nonneg _).trans (bφ w hw))
  calc _ ≤ ‖(φ z - φ w) • L z‖ + ‖φ w • (L z - L w)‖ := norm_add_le _ _
    _ ≤ k1 * ‖z - w‖ * v2 + v1 * (k2 * ‖z - w‖) := add_le_add h1 h2
    _ = (k1 * v2 + v1 * k2) * ‖z - w‖ := by ring

private theorem slopeBoundOn_smulRight {c : Space → (Space →L[ℝ] ℝ)} {v : Space → Space} {k1 k2 v1 v2 : ℝ}
    {s : Set Space} (hc : SlopeBoundOn c k1 s) (hv : SlopeBoundOn v k2 s) (bc : ∀ z ∈ s, ‖c z‖ ≤ v1)
    (bv : ∀ z ∈ s, ‖v z‖ ≤ v2) :
    SlopeBoundOn (fun z => (c z).smulRight (v z)) (k1 * v2 + v1 * k2) s := fun z hz w hw => by
  have e : (c z).smulRight (v z) - (c w).smulRight (v w) =
      (c z - c w).smulRight (v z) + (c w).smulRight (v z - v w) := by
    ext1 x
    simp only [ContinuousLinearMap.coe_sub', ContinuousLinearMap.coe_add', Pi.sub_apply, Pi.add_apply,
      ContinuousLinearMap.smulRight_apply, sub_smul, smul_sub]
    abel
  rw [e]
  have h1 : ‖(c z - c w).smulRight (v z)‖ ≤ k1 * ‖z - w‖ * v2 := by
    rw [ContinuousLinearMap.norm_smulRight_apply]
    exact mul_le_mul (hc z hz w hw) (bv z hz) (norm_nonneg _) ((norm_nonneg _).trans (hc z hz w hw))
  have h2 : ‖(c w).smulRight (v z - v w)‖ ≤ v1 * (k2 * ‖z - w‖) := by
    rw [ContinuousLinearMap.norm_smulRight_apply]
    exact mul_le_mul (bc w hw) (hv z hz w hw) (norm_nonneg _) ((norm_nonneg _).trans (bc w hw))
  calc _ ≤ ‖(c z - c w).smulRight (v z)‖ + ‖(c w).smulRight (v z - v w)‖ := norm_add_le _ _
    _ ≤ k1 * ‖z - w‖ * v2 + v1 * (k2 * ‖z - w‖) := add_le_add h1 h2
    _ = (k1 * v2 + v1 * k2) * ‖z - w‖ := by ring

private theorem ballData_mono {f : Space → E} {y : Space} {v d l v' d' l' : ℝ} (h : BallData f y v d l)
    (hv : v ≤ v') (hd : d ≤ d') (hl : l ≤ l') : BallData f y v' d' l' :=
  ⟨fun z hz => ⟨(h.1 z hz).1, (h.1 z hz).2.1.trans hv, (h.1 z hz).2.2.trans hd⟩, slopeBoundOn_mono h.2 hl⟩

private theorem ballData_add {f g : Space → E} {y : Space} {v1 d1 l1 v2 d2 l2 : ℝ}
    (hf : BallData f y v1 d1 l1) (hg : BallData g y v2 d2 l2) :
    BallData (fun z => f z + g z) y (v1 + v2) (d1 + d2) (l1 + l2) := by
  have hD : ∀ z ∈ Metric.ball y 1, fderiv ℝ (fun z => f z + g z) z = fderiv ℝ f z + fderiv ℝ g z :=
    fun z hz => ((hf.1 z hz).1.hasFDerivAt.add (hg.1 z hz).1.hasFDerivAt).fderiv
  refine ⟨fun z hz => ⟨(hf.1 z hz).1.add (hg.1 z hz).1, (norm_add_le _ _).trans
    (add_le_add (hf.1 z hz).2.1 (hg.1 z hz).2.1), ?_⟩, slopeBoundOn_congr (slopeBoundOn_add hf.2 hg.2) hD⟩
  rw [hD z hz]
  exact (norm_add_le _ _).trans (add_le_add (hf.1 z hz).2.2 (hg.1 z hz).2.2)

private theorem ballData_zero (y : Space) : BallData (fun _ : Space => (0 : E)) y 0 0 0 := by
  refine ⟨fun z _ => ⟨differentiableAt_const _, by simp, by simp⟩, fun z _ w _ => by simp⟩

private theorem ballData_sum {ι : Type*} (u : Finset ι) (f : ι → Space → E) (y : Space) (v d l : ι → ℝ)
    (h : ∀ j ∈ u, BallData (f j) y (v j) (d j) (l j)) :
    BallData (fun z => ∑ j ∈ u, f j z) y (∑ j ∈ u, v j) (∑ j ∈ u, d j) (∑ j ∈ u, l j) := by
  classical
  induction u using Finset.induction_on with
  | empty => simpa using ballData_zero (E := E) y
  | insert a u ha ih =>
    simp only [Finset.sum_insert ha]
    exact ballData_add (h a (Finset.mem_insert_self a u)) (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

private theorem ballData_smul {g : Space → ℝ} {A : Space → Space} {y : Space} {v1 d1 l1 v2 d2 l2 : ℝ}
    (hg : BallData g y v1 d1 l1) (hA : BallData A y v2 d2 l2) :
    BallData (fun z => g z • A z) y (v1 * v2) (v1 * d2 + d1 * v2) ((d1 * d2 + v1 * l2) + (l1 * v2 + d1 * d2)) := by
  have hD : ∀ z ∈ Metric.ball y 1, fderiv ℝ (fun z => g z • A z) z =
      g z • fderiv ℝ A z + (fderiv ℝ g z).smulRight (A z) :=
    fun z hz => ((hg.1 z hz).1.hasFDerivAt.smul (hA.1 z hz).1.hasFDerivAt).fderiv
  have hgL : SlopeBoundOn g d1 (Metric.ball y 1) :=
    slopeBoundOn_of_fderiv (fun z hz => (hg.1 z hz).1) (fun z hz => (hg.1 z hz).2.2)
  have hAL : SlopeBoundOn A d2 (Metric.ball y 1) :=
    slopeBoundOn_of_fderiv (fun z hz => (hA.1 z hz).1) (fun z hz => (hA.1 z hz).2.2)
  refine ⟨fun z hz => ⟨(hg.1 z hz).1.smul (hA.1 z hz).1, ?_, ?_⟩, ?_⟩
  · rw [norm_smul]
    exact mul_le_mul (hg.1 z hz).2.1 (hA.1 z hz).2.1 (norm_nonneg _) ((norm_nonneg _).trans (hg.1 z hz).2.1)
  · rw [hD z hz]
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [norm_smul]
      exact mul_le_mul (hg.1 z hz).2.1 (hA.1 z hz).2.2 (norm_nonneg _) ((norm_nonneg _).trans (hg.1 z hz).2.1)
    · rw [ContinuousLinearMap.norm_smulRight_apply]
      exact mul_le_mul (hg.1 z hz).2.2 (hA.1 z hz).2.1 (norm_nonneg _) ((norm_nonneg _).trans (hg.1 z hz).2.2)
  · refine slopeBoundOn_congr (slopeBoundOn_add (slopeBoundOn_smul hgL hA.2 (fun z hz => (hg.1 z hz).2.1) (fun z hz => (hA.1 z hz).2.2))
      (slopeBoundOn_smulRight hg.2 hAL (fun z hz => (hg.1 z hz).2.2) (fun z hz => (hA.1 z hz).2.1))) hD

private theorem hom_fderiv {A : Space → E} (hhom : ∀ s : ℝ, 0 < s → ∀ y, A (s • y) = A y) {s : ℝ} (hs : 0 < s)
    {z : Space} (hd : DifferentiableAt ℝ A (s⁻¹ • z)) :
    fderiv ℝ A z = s⁻¹ • fderiv ℝ A (s⁻¹ • z) := by
  have h : HasFDerivAt (fun w => A (s⁻¹ • w))
      ((fderiv ℝ A (s⁻¹ • z)).comp (s⁻¹ • ContinuousLinearMap.id ℝ Space)) z :=
    hd.hasFDerivAt.comp z ((hasFDerivAt_id z).const_smul s⁻¹)
  have h2 : HasFDerivAt A ((fderiv ℝ A (s⁻¹ • z)).comp (s⁻¹ • ContinuousLinearMap.id ℝ Space)) z :=
    h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun w => (hhom s⁻¹ (inv_pos.2 hs) w).symm)
  rw [h2.fderiv]
  ext1 v
  simp

private theorem hom_ball {A : Space → E} (hhom : ∀ s : ℝ, 0 < s → ∀ y, A (s • y) = A y)
    (hd : ∀ y : Space, y ≠ 0 → DifferentiableAt ℝ A y)
    (hl : LocallyLipschitzOn {y : Space | y ≠ 0} (fderiv ℝ A)) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ y : Space, 2 ≤ ‖y‖ → BallData A y M (M * ‖y‖⁻¹) (M * ‖y‖⁻¹ ^ 2) := by
  set K : Set Space := {w | 1 / 2 ≤ ‖w‖ ∧ ‖w‖ ≤ 2} with hKdef
  have hKc : IsCompact K := (isCompact_closedBall (0 : Space) 2).of_isClosed_subset
    ((isClosed_le continuous_const continuous_norm).inter (isClosed_le continuous_norm continuous_const))
    (fun w hw => by simpa [Metric.mem_closedBall, dist_zero_right] using hw.2)
  have hK0 : ∀ w ∈ K, w ≠ 0 := fun w hw h => by
    have := hw.1
    rw [h, norm_zero] at this
    linarith
  obtain ⟨L, hL⟩ := (hl.mono (fun w hw => hK0 w hw)).exists_lipschitzOnWith_of_compact hKc
  obtain ⟨M1, hM1⟩ := hKc.exists_bound_of_continuousOn (f := A)
    (fun w hw => (hd w (hK0 w hw)).continuousAt.continuousWithinAt)
  obtain ⟨M2, hM2⟩ := hKc.exists_bound_of_continuousOn hL.continuousOn
  have hL0 : (0 : ℝ) ≤ L := L.2
  refine ⟨|M1| + |M2| + L, by positivity, fun y hy => ?_⟩
  set Y := ‖y‖ with hY
  have hY0 : 0 < Y := by linarith
  have hmem : ∀ z ∈ Metric.ball y 1, Y⁻¹ • z ∈ K ∧ z ≠ 0 := by
    intro z hz
    have h1 : ‖z - y‖ < 1 := by rwa [Metric.mem_ball, dist_eq_norm] at hz
    have h2 : Y - 1 < ‖z‖ := by
      have := norm_sub_norm_le y z
      rw [norm_sub_rev] at this
      linarith
    have h3 : ‖z‖ < Y + 1 := by
      have := norm_sub_norm_le z y
      linarith
    have hn : ‖Y⁻¹ • z‖ = ‖z‖ / Y := by
      rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hY0]
      ring
    refine ⟨⟨?_, ?_⟩, fun h => by rw [h, norm_zero] at h2; linarith⟩
    · rw [hn, le_div_iff₀ hY0]; linarith
    · rw [hn, div_le_iff₀ hY0]; linarith
  have hval : ∀ z, A z = A (Y⁻¹ • z) := fun z => (hhom Y⁻¹ (inv_pos.2 hY0) z).symm
  have hder : ∀ z ∈ Metric.ball y 1, fderiv ℝ A z = Y⁻¹ • fderiv ℝ A (Y⁻¹ • z) := fun z hz =>
    hom_fderiv hhom hY0 (hd _ (hK0 _ (hmem z hz).1))
  refine ⟨fun z hz => ⟨hd z (hmem z hz).2, ?_, ?_⟩, fun z hz w hw => ?_⟩
  · rw [hval z]
    exact (hM1 _ (hmem z hz).1).trans (by linarith [le_abs_self M1, abs_nonneg M2])
  · rw [hder z hz, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hY0]
    have := hM2 _ (hmem z hz).1
    calc Y⁻¹ * ‖fderiv ℝ A (Y⁻¹ • z)‖ ≤ Y⁻¹ * (|M1| + |M2| + L) :=
          mul_le_mul_of_nonneg_left (by linarith [le_abs_self M2, abs_nonneg M1]) (inv_nonneg.2 hY0.le)
      _ = _ := by ring
  · rw [hder z hz, hder w hw, ← smul_sub, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hY0]
    have h1 := hL.dist_le_mul _ (hmem z hz).1 _ (hmem w hw).1
    rw [dist_eq_norm, dist_eq_norm, ← smul_sub, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hY0] at h1
    calc Y⁻¹ * ‖fderiv ℝ A (Y⁻¹ • z) - fderiv ℝ A (Y⁻¹ • w)‖ ≤ Y⁻¹ * (L * (Y⁻¹ * ‖z - w‖)) :=
          mul_le_mul_of_nonneg_left h1 (inv_nonneg.2 hY0.le)
      _ ≤ Y⁻¹ * ((|M1| + |M2| + L) * (Y⁻¹ * ‖z - w‖)) := by
          have : (0 : ℝ) ≤ Y⁻¹ * ‖z - w‖ := by positivity
          have : (L : ℝ) ≤ |M1| + |M2| + L := by linarith [abs_nonneg M1, abs_nonneg M2]
          gcongr
      _ = (|M1| + |M2| + L) * Y⁻¹ ^ 2 * ‖z - w‖ := by ring

private theorem norm_hasFDerivAt {z : Space} (hz : z ≠ 0) :
    HasFDerivAt (fun x : Space => ‖x‖) (‖z‖⁻¹ • innerSL ℝ z) z := by
  have hz' : 0 < ‖z‖ := norm_pos_iff.2 hz
  have h2 := (hasStrictFDerivAt_norm_sq z).hasFDerivAt
  have hpos : 0 < ‖z‖ ^ 2 := by positivity
  have hs := (Real.hasDerivAt_sqrt hpos.ne').comp_hasFDerivAt z h2
  have e1 : (Real.sqrt ∘ fun x : Space => ‖x‖ ^ 2) = fun x => ‖x‖ :=
    funext fun x => by simp [Real.sqrt_sq (norm_nonneg x)]
  have e2 : (1 / (2 * Real.sqrt (‖z‖ ^ 2))) • (2 • innerSL ℝ z) = ‖z‖⁻¹ • innerSL ℝ z := by
    rw [Real.sqrt_sq (norm_nonneg z)]
    ext1 v
    simp only [ContinuousLinearMap.smul_apply, innerSL_apply_apply, smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat]
    field_simp
  rw [e1, e2] at hs
  exact hs

private theorem normMap_norm {z : Space} (hz : z ≠ 0) : ‖‖z‖⁻¹ • innerSL ℝ z‖ = 1 := by
  rw [norm_smul, innerSL_apply_norm, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.2 hz)]

private theorem unit_sub_le {z w : Space} (hz : z ≠ 0) (hw : w ≠ 0) :
    ‖‖z‖⁻¹ • z - ‖w‖⁻¹ • w‖ ≤ 2 * ‖z - w‖ / ‖z‖ := by
  have hz' : 0 < ‖z‖ := norm_pos_iff.2 hz
  have hw' : 0 < ‖w‖ := norm_pos_iff.2 hw
  have e : ‖z‖⁻¹ • z - ‖w‖⁻¹ • w = ‖z‖⁻¹ • ((z - w) + (‖w‖ - ‖z‖) • (‖w‖⁻¹ • w)) := by
    rw [smul_add, smul_smul, smul_smul, smul_sub]
    have : ‖z‖⁻¹ * (‖w‖ - ‖z‖) * ‖w‖⁻¹ = ‖z‖⁻¹ - ‖w‖⁻¹ := by
      field_simp
    rw [this, sub_smul]
    abel
  rw [e, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hz']
  have h1 : ‖(z - w) + (‖w‖ - ‖z‖) • (‖w‖⁻¹ • w)‖ ≤ 2 * ‖z - w‖ := by
    refine (norm_add_le _ _).trans ?_
    have hu : ‖‖w‖⁻¹ • w‖ = 1 := by rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hw'.ne']
    rw [norm_smul, hu, mul_one, Real.norm_eq_abs]
    have := abs_norm_sub_norm_le w z
    rw [norm_sub_rev w z] at this
    linarith
  rw [div_eq_inv_mul]
  exact mul_le_mul_of_nonneg_left h1 (inv_nonneg.2 hz'.le)

private theorem rpow_step {Y : ℝ} (hY : 0 < Y) (b : ℝ) : Y ^ (-b) * Y⁻¹ = Y ^ (-(b + 1)) := by
  rw [← Real.rpow_neg_one, ← Real.rpow_add hY]
  ring_nf

private theorem rpow_half {Y Z b : ℝ} (hY : 0 < Y) (hZ : Y / 2 ≤ Z) (hb : 0 ≤ b) :
    Z ^ (-b) ≤ (2 : ℝ) ^ b * Y ^ (-b) := by
  have h1 : Z ^ (-b) ≤ (Y / 2) ^ (-b) := Real.rpow_le_rpow_of_nonpos (by positivity) hZ (by linarith)
  have h2 : (Y / 2) ^ (-b) = (2 : ℝ) ^ b * Y ^ (-b) := by
    rw [Real.div_rpow hY.le (by norm_num), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2) b, div_inv_eq_mul]
    ring
  linarith

private theorem radial_ball {ρ : ℝ → ℝ} {R0 C a : ℝ} (hR0 : 0 < R0) (ha : 0 ≤ a)
    (hρ : ContDiffOn ℝ 2 ρ (Set.Ioi R0))
    (hb : ∀ r : ℝ, R0 < r → |ρ r| ≤ C * r ^ (-a) ∧ |deriv ρ r| ≤ C * r ^ (-(a + 1)) ∧
      |deriv (deriv ρ) r| ≤ C * r ^ (-(a + 2))) :
    ∃ K R : ℝ, 0 ≤ K ∧ 2 ≤ R ∧ ∀ y : Space, R ≤ ‖y‖ →
      BallData (fun z => ρ ‖z‖) y (K * ‖y‖ ^ (-a)) (K * ‖y‖ ^ (-(a + 1))) (K * ‖y‖ ^ (-(a + 2))) := by
  have h1 : ∀ r, R0 < r → HasDerivAt ρ (deriv ρ r) r := fun r hr =>
    (((hρ.differentiableOn (by norm_num)) r hr).differentiableAt (Ioi_mem_nhds hr)).hasDerivAt
  have hρ2 : ContDiffOn ℝ (1 + 1) ρ (Set.Ioi R0) := by
    have e : ((1 : WithTop ℕ∞) + 1) = 2 := by norm_num
    rw [e]; exact hρ
  have hρ' : ContDiffOn ℝ 1 (deriv ρ) (Set.Ioi R0) :=
    ((contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioi).1 hρ2).2.2
  have h2 : ∀ r, R0 < r → HasDerivAt (deriv ρ) (deriv (deriv ρ) r) r := fun r hr =>
    (((hρ'.differentiableOn (by norm_num)) r hr).differentiableAt (Ioi_mem_nhds hr)).hasDerivAt
  set T : ℝ := (2 : ℝ) ^ (a + 2) with hT
  have hT0 : 0 ≤ T := by positivity
  refine ⟨5 * |C| * T, 2 * R0 + 2, by positivity, by linarith, fun y hy => ?_⟩
  set Y := ‖y‖ with hY
  have hY0 : 0 < Y := by linarith
  have hz : ∀ z ∈ Metric.ball y 1, Y / 2 ≤ ‖z‖ ∧ R0 < ‖z‖ ∧ z ≠ 0 := by
    intro z hz
    have h1 : ‖z - y‖ < 1 := by rwa [Metric.mem_ball, dist_eq_norm] at hz
    have h2 : Y - 1 < ‖z‖ := by
      have := norm_sub_norm_le y z
      rw [norm_sub_rev] at this
      linarith
    refine ⟨by linarith, by linarith, fun h => ?_⟩
    rw [h, norm_zero] at h2
    linarith
  have hpow : ∀ z ∈ Metric.ball y 1, ∀ b : ℝ, 0 ≤ b → b ≤ a + 2 → ‖z‖ ^ (-b) ≤ T * Y ^ (-b) := by
    intro z hz' b hb0 hb1
    refine (rpow_half hY0 (hz z hz').1 hb0).trans ?_
    have : (2 : ℝ) ^ b ≤ T := Real.rpow_le_rpow_of_exponent_le (by norm_num) hb1
    gcongr
  have hbnd : ∀ z ∈ Metric.ball y 1, ∀ (u : ℝ) (b : ℝ), 0 ≤ b → b ≤ a + 2 → |u| ≤ C * ‖z‖ ^ (-b) →
      |u| ≤ |C| * T * Y ^ (-b) := by
    intro z hz' u b hb0 hb1 hu
    have hzp : 0 ≤ ‖z‖ ^ (-b) := Real.rpow_nonneg (norm_nonneg _) _
    calc |u| ≤ C * ‖z‖ ^ (-b) := hu
      _ ≤ |C| * ‖z‖ ^ (-b) := mul_le_mul_of_nonneg_right (le_abs_self C) hzp
      _ ≤ |C| * (T * Y ^ (-b)) := mul_le_mul_of_nonneg_left (hpow z hz' b hb0 hb1) (abs_nonneg C)
      _ = |C| * T * Y ^ (-b) := by ring
  have hg : ∀ z ∈ Metric.ball y 1, HasFDerivAt (fun x : Space => ρ ‖x‖)
      (deriv ρ ‖z‖ • (‖z‖⁻¹ • innerSL ℝ z)) z := fun z hz' =>
    (h1 _ (hz z hz').2.1).comp_hasFDerivAt z (norm_hasFDerivAt (hz z hz').2.2)
  have hg' : ∀ z ∈ Metric.ball y 1, HasFDerivAt (fun x : Space => deriv ρ ‖x‖)
      (deriv (deriv ρ) ‖z‖ • (‖z‖⁻¹ • innerSL ℝ z)) z := fun z hz' =>
    (h2 _ (hz z hz').2.1).comp_hasFDerivAt z (norm_hasFDerivAt (hz z hz').2.2)
  have hNslope : SlopeBoundOn (fun z : Space => ‖z‖⁻¹ • innerSL ℝ z) (4 * Y⁻¹) (Metric.ball y 1) := by
    intro z hz' w hw'
    have key : ‖z‖⁻¹ • innerSL ℝ z - ‖w‖⁻¹ • innerSL ℝ w = innerSL ℝ (‖z‖⁻¹ • z - ‖w‖⁻¹ • w) := by
      ext1 v
      simp [inner_sub_left, real_inner_smul_left]
    rw [key, innerSL_apply_norm]
    have hzz := hz z hz'
    refine (unit_sub_le hzz.2.2 (hz w hw').2.2).trans ?_
    have hn : 0 ≤ 2 * ‖z - w‖ := by positivity
    calc 2 * ‖z - w‖ / ‖z‖ ≤ 2 * ‖z - w‖ / (Y / 2) := div_le_div_of_nonneg_left hn (by positivity) hzz.1
      _ = 4 * Y⁻¹ * ‖z - w‖ := by field_simp; ring
  have hw0 : 0 ≤ Y ^ (-a) := Real.rpow_nonneg hY0.le _
  have hw1 : 0 ≤ Y ^ (-(a + 1)) := Real.rpow_nonneg hY0.le _
  have hw2 : 0 ≤ Y ^ (-(a + 2)) := Real.rpow_nonneg hY0.le _
  have hCT : 0 ≤ |C| * T := by positivity
  have hφ : SlopeBoundOn (fun z : Space => deriv ρ ‖z‖) (|C| * T * Y ^ (-(a + 2))) (Metric.ball y 1) := by
    refine slopeBoundOn_of_fderiv (fun z hz' => (hg' z hz').differentiableAt) (fun z hz' => ?_)
    rw [(hg' z hz').fderiv, norm_smul, normMap_norm (hz z hz').2.2, mul_one, Real.norm_eq_abs]
    exact hbnd z hz' _ _ (by linarith) le_rfl (hb _ (hz z hz').2.1).2.2
  have hφb : ∀ z ∈ Metric.ball y 1, ‖deriv ρ ‖z‖‖ ≤ |C| * T * Y ^ (-(a + 1)) := fun z hz' => by
    rw [Real.norm_eq_abs]
    exact hbnd z hz' _ _ (by linarith) (by linarith) (hb _ (hz z hz').2.1).2.1
  have hNb : ∀ z ∈ Metric.ball y 1, ‖‖z‖⁻¹ • innerSL ℝ z‖ ≤ 1 := fun z hz' =>
    (normMap_norm (hz z hz').2.2).le
  refine ⟨fun z hz' => ⟨(hg z hz').differentiableAt, ?_, ?_⟩, ?_⟩
  · rw [Real.norm_eq_abs]
    refine (hbnd z hz' _ _ ha (by linarith) (hb _ (hz z hz').2.1).1).trans ?_
    have : |C| * T * Y ^ (-a) ≤ 5 * |C| * T * Y ^ (-a) := by nlinarith
    linarith
  · rw [(hg z hz').fderiv, norm_smul, normMap_norm (hz z hz').2.2, mul_one]
    refine (hφb z hz').trans ?_
    nlinarith
  · have hL := slopeBoundOn_smul hφ hNslope hφb hNb
    refine slopeBoundOn_mono (slopeBoundOn_congr hL fun z hz' => (hg z hz').fderiv) ?_
    have e : Y ^ (-(a + 1)) * Y⁻¹ = Y ^ (-(a + 2)) := by
      rw [rpow_step hY0]; ring_nf
    calc |C| * T * Y ^ (-(a + 2)) * 1 + |C| * T * Y ^ (-(a + 1)) * (4 * Y⁻¹)
        = 5 * (|C| * T) * (Y ^ (-(a + 1)) * Y⁻¹) - 0 + 0 - 0 + 0 - 0 + 0 + (|C| * T * Y ^ (-(a + 2)) - |C| * T * (Y ^ (-(a + 1)) * Y⁻¹)) := by ring
      _ = 5 * |C| * T * Y ^ (-(a + 2)) := by rw [e]; ring
      _ ≤ 5 * |C| * T * Y ^ (-(a + 2)) := le_rfl

private theorem far_of_split {a : ℝ} (ha : 0 ≤ a) {N : ℕ} (ρ : Fin N → ℝ → ℝ) (A : Fin N → Space → Space)
    (f : Space → Space) {R0 C : ℝ} (hR0 : 0 < R0)
    (heq : ∀ y : Space, R0 < ‖y‖ → f y = ∑ j, ρ j ‖y‖ • A j y)
    (hρ : ∀ j, ContDiffOn ℝ 2 (ρ j) (Set.Ioi R0))
    (hb : ∀ j, ∀ r : ℝ, R0 < r → |ρ j r| ≤ C * r ^ (-a) ∧ |deriv (ρ j) r| ≤ C * r ^ (-(a + 1)) ∧
      |deriv (deriv (ρ j)) r| ≤ C * r ^ (-(a + 2)))
    (hhom : ∀ j, ∀ s : ℝ, 0 < s → ∀ y : Space, A j (s • y) = A j y)
    (hAd : ∀ j, ∀ y : Space, y ≠ 0 → DifferentiableAt ℝ (A j) y)
    (hAl : ∀ j, LocallyLipschitzOn {y : Space | y ≠ 0} (fderiv ℝ (A j))) :
    ∃ R C' : ℝ, ∀ y : Space, R ≤ ‖y‖ →
      ‖f y‖ ≤ C' * ‖y‖ ^ (-a) ∧ ‖fderiv ℝ f y‖ ≤ C' * ‖y‖ ^ (-(a + 1)) ∧
        LipschitzOnWith (Real.toNNReal (C' * ‖y‖ ^ (-(a + 2)))) (fderiv ℝ f) (Metric.ball y 1) := by
  choose K R hK0 hR2 hK using fun j => radial_ball hR0 ha (hρ j) (hb j)
  choose M hM0 hM using fun j => hom_ball (hhom j) (hAd j) (hAl j)
  set R1 : ℝ := 2 + 2 * R0 + ∑ j, |R j| with hR1
  set Q : ℝ := ∑ j, 4 * K j * M j with hQ
  refine ⟨R1, Q, fun y hy => ?_⟩
  set Y := ‖y‖ with hY
  have hsum0 : 0 ≤ ∑ j, |R j| := Finset.sum_nonneg fun j _ => abs_nonneg _
  have hY0 : 0 < Y := by linarith
  have hRj : ∀ j, R j ≤ Y := fun j => by
    have h3 : |R j| ≤ ∑ i, |R i| := Finset.single_le_sum (f := fun i => |R i|) (fun i _ => abs_nonneg _) (Finset.mem_univ j)
    have := le_abs_self (R j)
    linarith
  have h2Y : 2 ≤ Y := by linarith
  have hw0 : 0 ≤ Y ^ (-a) := Real.rpow_nonneg hY0.le _
  have hw1 : 0 ≤ Y ^ (-(a + 1)) := Real.rpow_nonneg hY0.le _
  have hw2 : 0 ≤ Y ^ (-(a + 2)) := Real.rpow_nonneg hY0.le _
  have e01 : Y ^ (-a) * Y⁻¹ = Y ^ (-(a + 1)) := rpow_step hY0 a
  have e12 : Y ^ (-(a + 1)) * Y⁻¹ = Y ^ (-(a + 2)) := by rw [rpow_step hY0]; ring_nf
  have e02 : Y ^ (-a) * Y⁻¹ ^ 2 = Y ^ (-(a + 2)) := by rw [pow_two, ← mul_assoc, e01, e12]
  have hterm : ∀ j, BallData (fun z => ρ j ‖z‖ • A j z) y (4 * K j * M j * Y ^ (-a))
      (4 * K j * M j * Y ^ (-(a + 1))) (4 * K j * M j * Y ^ (-(a + 2))) := by
    intro j
    have hp := ballData_smul (hK j y (hRj j)) (hM j y h2Y)
    have hKM : 0 ≤ K j * M j := mul_nonneg (hK0 j) (hM0 j)
    refine ballData_mono hp ?_ ?_ ?_
    · have : 0 ≤ K j * M j * Y ^ (-a) := mul_nonneg hKM hw0
      nlinarith
    · have e : K j * Y ^ (-a) * (M j * Y⁻¹) + K j * Y ^ (-(a + 1)) * M j =
          2 * (K j * M j * Y ^ (-(a + 1))) := by linear_combination (K j * M j) * e01
      have : 0 ≤ K j * M j * Y ^ (-(a + 1)) := mul_nonneg hKM hw1
      rw [e]; nlinarith
    · have e : K j * Y ^ (-(a + 1)) * (M j * Y⁻¹) + K j * Y ^ (-a) * (M j * Y⁻¹ ^ 2) +
          (K j * Y ^ (-(a + 2)) * M j + K j * Y ^ (-(a + 1)) * (M j * Y⁻¹)) =
          4 * (K j * M j * Y ^ (-(a + 2))) := by
        linear_combination (K j * M j) * (2 * e12 + e02)
      rw [e]; nlinarith
  have hS := ballData_sum Finset.univ (fun j z => ρ j ‖z‖ • A j z) y _ _ _ fun j _ => hterm j
  simp only [← Finset.sum_mul] at hS
  have hball : ∀ z ∈ Metric.ball y 1, R0 < ‖z‖ := fun z hz => by
    have h1 : ‖z - y‖ < 1 := by rwa [Metric.mem_ball, dist_eq_norm] at hz
    have := norm_sub_norm_le y z
    rw [norm_sub_rev] at this
    linarith
  have hfd : ∀ z ∈ Metric.ball y 1, fderiv ℝ f z = fderiv ℝ (fun z => ∑ j, ρ j ‖z‖ • A j z) z := by
    intro z hz
    refine Filter.EventuallyEq.fderiv_eq ?_
    filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds (hball z hz)] with w hw
    exact heq w hw
  have hy1 : y ∈ Metric.ball y 1 := Metric.mem_ball_self one_pos
  refine ⟨?_, ?_, ?_⟩
  · rw [heq y (hball y hy1)]
    exact (hS.1 y hy1).2.1
  · rw [hfd y hy1]
    exact (hS.1 y hy1).2.2
  · refine LipschitzOnWith.of_dist_le_mul fun z hz w hw => ?_
    rw [dist_eq_norm, dist_eq_norm, hfd z hz, hfd w hw]
    exact (hS.2 z hz w hw).trans (mul_le_mul_of_nonneg_right (Real.le_coe_toNNReal _) (norm_nonneg _))

theorem modeFieldOf_far_bounds_order (P : ChartParams) (hP : IsChartParams P) (e : ℕ) (D : FieldData)
    (hD : IsFieldData P e D) (c : ℝ) (n : ℤ) (hn : n ∈ D.modes) :
    ∃ R C : ℝ, ∀ y : Space, R ≤ ‖y‖ →
      ‖modeFieldOf P D c n y‖ ≤ C * ‖y‖ ^ (-((e : ℝ) + P.eps)) ∧
        ‖fderiv ℝ (modeFieldOf P D c n) y‖ ≤ C * ‖y‖ ^ (-((e : ℝ) + P.eps + 1)) ∧
          LipschitzOnWith (Real.toNNReal (C * ‖y‖ ^ (-((e : ℝ) + P.eps + 2))))
            (fderiv ℝ (modeFieldOf P D c n)) (Metric.ball y 1) := by
  obtain ⟨N, ρ, A, R0, C, hR0, heq, hρ, hb, hhom, hAd, hAl⟩ := modeFieldOf_radial_split P hP e D hD c n hn
  have ha : (0 : ℝ) ≤ (e : ℝ) + P.eps := by
    have := hP.eps_pos
    positivity
  exact far_of_split ha ρ A (modeFieldOf P D c n) hR0 heq hρ hb hhom hAd hAl

private theorem rpow_weaken {C r b b' : ℝ} (hr : 1 ≤ r) (hb : b' ≤ b) : C * r ^ (-b) ≤ |C| * r ^ (-b') :=
  (mul_le_mul_of_nonneg_right (le_abs_self C) (Real.rpow_nonneg (by linarith) _)).trans
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hr (by linarith)) (abs_nonneg C))

theorem modeFieldOf_far_bounds_three (P : ChartParams) (hP : IsChartParams P) (D : FieldData)
    (hD : IsFieldData P 3 D) (β : ℝ) (n : ℤ) (hn : n ∈ D.modes) :
    ∃ R C : ℝ, ∀ y : Space, R ≤ ‖y‖ →
      ‖modeFieldOf P D β n y‖ ≤ C * ‖y‖ ^ (-(3 : ℝ)) ∧
        ‖fderiv ℝ (modeFieldOf P D β n) y‖ ≤ C * ‖y‖ ^ (-(4 : ℝ)) ∧
          LipschitzOnWith (Real.toNNReal (C * ‖y‖ ^ (-(5 : ℝ)))) (fderiv ℝ (modeFieldOf P D β n))
            (Metric.ball y 1) := by
  obtain ⟨R, C, h⟩ := modeFieldOf_far_bounds_order P hP 3 D hD β n hn
  have he := hP.eps_pos
  refine ⟨max R 1, |C|, fun y hy => ?_⟩
  obtain ⟨h1, h2, h3⟩ := h y ((le_max_left _ _).trans hy)
  have hr : 1 ≤ ‖y‖ := (le_max_right _ _).trans hy
  refine ⟨h1.trans (rpow_weaken hr (by push_cast; linarith)),
    h2.trans (rpow_weaken hr (by push_cast; linarith)), h3.weaken ?_⟩
  exact Real.toNNReal_le_toNNReal (rpow_weaken hr (by push_cast; linarith))

theorem modeFieldOf_far_bounds (P : ChartParams) (hP : IsChartParams P) (D : FieldData)
    (hD : IsFieldData P 1 D) (c : ℝ) (n : ℤ) (hn : n ∈ D.modes) :
    ∃ R C : ℝ, ∀ y : Space, R ≤ ‖y‖ →
      ‖modeFieldOf P D c n y‖ ≤ C * ‖y‖ ^ (-(1 + P.eps)) ∧
        ‖fderiv ℝ (modeFieldOf P D c n) y‖ ≤ C * ‖y‖ ^ (-(2 + P.eps)) ∧
          LipschitzOnWith (Real.toNNReal (C * ‖y‖ ^ (-(3 + P.eps))))
            (fderiv ℝ (modeFieldOf P D c n)) (Metric.ball y 1) := by
  obtain ⟨R, C, h⟩ := modeFieldOf_far_bounds_order P hP 1 D hD c n hn
  refine ⟨R, C, fun y hy => ?_⟩
  obtain ⟨h1, h2, h3⟩ := h y hy
  have e0 : ((1 : ℕ) : ℝ) + P.eps = 1 + P.eps := by norm_num
  have e1 : ((1 : ℕ) : ℝ) + P.eps + 1 = 2 + P.eps := by norm_num; ring
  have e2 : ((1 : ℕ) : ℝ) + P.eps + 2 = 3 + P.eps := by norm_num; ring
  rw [e0] at h1
  rw [e1] at h2
  rw [e2] at h3
  exact ⟨h1, h2, h3⟩

end FracCellInternal

end Breakdown
