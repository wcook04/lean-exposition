import Breakdown.CertCell.ShapeTypeTwoDecayBall

open scoped ContDiff

noncomputable section

namespace Breakdown

namespace CertCell

namespace GivenShape

namespace Internal

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem norm_hasFDerivAt_of_ne {z : Space} (hz : z ≠ 0) :
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
    simp only [smul_apply, innerSL_apply_apply, smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat]
    field_simp
  rw [e1, e2] at hs
  exact hs

theorem norm_unitMap {z : Space} (hz : z ≠ 0) : ‖‖z‖⁻¹ • innerSL ℝ z‖ = 1 := by
  rw [norm_smul, innerSL_apply_norm, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.2 hz)]

theorem unit_diff_le {z w : Space} (hz : z ≠ 0) (hw : w ≠ 0) :
    ‖‖z‖⁻¹ • z - ‖w‖⁻¹ • w‖ ≤ 2 * ‖z - w‖ / ‖z‖ := by
  have hz' : 0 < ‖z‖ := norm_pos_iff.2 hz
  have hw' : 0 < ‖w‖ := norm_pos_iff.2 hw
  have e : ‖z‖⁻¹ • z - ‖w‖⁻¹ • w = ‖z‖⁻¹ • ((z - w) + (‖w‖ - ‖z‖) • (‖w‖⁻¹ • w)) := by
    rw [smul_add, smul_smul, smul_smul, smul_sub]
    have : ‖z‖⁻¹ * (‖w‖ - ‖z‖) * ‖w‖⁻¹ = ‖z‖⁻¹ - ‖w‖⁻¹ := by field_simp
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

theorem farBound_radial {ρ ρ1 ρ2 : ℝ → E} {a : ℕ} {R0 C : ℝ} (hR0 : 1 ≤ R0) (hC : 0 ≤ C)
    (h1 : ∀ s, R0 ≤ s → HasDerivAt ρ (ρ1 s) s) (h2 : ∀ s, R0 ≤ s → HasDerivAt ρ1 (ρ2 s) s)
    (hb : ∀ s, R0 ≤ s → ‖ρ s‖ ≤ C / s ^ a ∧ ‖ρ1 s‖ ≤ C / s ^ (a + 1) ∧ ‖ρ2 s‖ ≤ C / s ^ (a + 2)) :
    FarBound (fun z => ρ ‖z‖) a := by
  refine ⟨3 * (2 ^ (a + 2) * C), 2 * R0 + 2, by positivity, by linarith, fun y hy => ?_⟩
  have hr0 : 0 < ‖y‖ := by linarith
  have hz : ∀ z ∈ Metric.ball y 1, R0 ≤ ‖z‖ ∧ ‖y‖ / 2 ≤ ‖z‖ ∧ z ≠ 0 := by
    intro z hz
    have := (ball_norm_near hz).1
    refine ⟨by linarith, by linarith, fun h => ?_⟩
    rw [h, norm_zero] at this
    linarith
  have hg : ∀ z ∈ Metric.ball y 1, HasFDerivAt (fun x : Space => ρ ‖x‖)
      ((‖z‖⁻¹ • innerSL ℝ z).smulRight (ρ1 ‖z‖)) z := by
    intro z hz'
    exact ((h1 _ (hz z hz').1).hasFDerivAt.comp z (norm_hasFDerivAt_of_ne (hz z hz').2.2)).congr_fderiv
      (by ext1 v; simp [smul_smul])
  have hg' : ∀ z ∈ Metric.ball y 1, HasFDerivAt (fun x : Space => ρ1 ‖x‖)
      ((‖z‖⁻¹ • innerSL ℝ z).smulRight (ρ2 ‖z‖)) z := by
    intro z hz'
    exact ((h2 _ (hz z hz').1).hasFDerivAt.comp z (norm_hasFDerivAt_of_ne (hz z hz').2.2)).congr_fderiv
      (by ext1 v; simp [smul_smul])
  have kb : ∀ z ∈ Metric.ball y 1, ∀ (k : ℕ) (u : E), ‖u‖ ≤ C / ‖z‖ ^ k → ‖u‖ ≤ 2 ^ k * C / ‖y‖ ^ k :=
    fun z hz' k u hu => hu.trans (pow_div_le_of_half k hr0 (hz z hz').2.1 hC)
  have p0 : 0 ≤ C / ‖y‖ ^ (a + 2) := by positivity
  have hρ1 : ∀ z ∈ Metric.ball y 1, ‖ρ1 ‖z‖‖ ≤ 2 ^ (a + 1) * C / ‖y‖ ^ (a + 1) := fun z hz' =>
    kb z hz' _ _ (hb _ (hz z hz').1).2.1
  have hD : ∀ z ∈ Metric.ball y 1, fderiv ℝ (fun x : Space => ρ ‖x‖) z =
      ContinuousLinearMap.smulRightL ℝ Space E (‖z‖⁻¹ • innerSL ℝ z) (ρ1 ‖z‖) := fun z hz' => (hg z hz').fderiv
  refine ⟨fun z hz' => (hg z hz').differentiableAt, fun z hz' => ?_, fun z hz' => ?_, ?_⟩
  · refine (kb z hz' _ _ (hb _ (hz z hz').1).1).trans ?_
    rw [div_le_div_iff_of_pos_right (by positivity)]
    have h3 : (2 : ℝ) ^ a * C ≤ 2 ^ (a + 2) * C :=
      mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) (by omega)) hC
    have h4 : 0 ≤ (2 : ℝ) ^ (a + 2) * C := by positivity
    linarith
  · rw [(hg z hz').fderiv, ContinuousLinearMap.norm_smulRight_apply, norm_unitMap (hz z hz').2.2, one_mul]
    refine (hρ1 z hz').trans ?_
    rw [div_le_div_iff_of_pos_right (by positivity)]
    have h3 : (2 : ℝ) ^ (a + 1) * C ≤ 2 ^ (a + 2) * C :=
      mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) (by omega)) hC
    have h4 : 0 ≤ (2 : ℝ) ^ (a + 2) * C := by positivity
    linarith
  · have hB : ∀ (u : Space →L[ℝ] ℝ) (v : E), ‖ContinuousLinearMap.smulRightL ℝ Space E u v‖ ≤ ‖u‖ * ‖v‖ :=
      fun u v => (ContinuousLinearMap.norm_smulRight_apply u v).le
    have sN : SlopeOn (fun z : Space => ‖z‖⁻¹ • innerSL ℝ z) (4 / ‖y‖) (Metric.ball y 1) := by
      intro z hz' w hw'
      have key : ‖z‖⁻¹ • innerSL ℝ z - ‖w‖⁻¹ • innerSL ℝ w = innerSL ℝ (‖z‖⁻¹ • z - ‖w‖⁻¹ • w) := by
        ext1 v
        simp
      rw [key, innerSL_apply_norm]
      refine (unit_diff_le (hz z hz').2.2 (hz w hw').2.2).trans ?_
      have hn : 0 ≤ 2 * ‖z - w‖ := by positivity
      calc 2 * ‖z - w‖ / ‖z‖ ≤ 2 * ‖z - w‖ / (‖y‖ / 2) :=
            div_le_div_of_nonneg_left hn (by positivity) (hz z hz').2.1
        _ = 4 / ‖y‖ * ‖z - w‖ := by field_simp; ring
    have s1 : SlopeOn (fun z : Space => ρ1 ‖z‖) (2 ^ (a + 2) * C / ‖y‖ ^ (a + 2)) (Metric.ball y 1) := by
      refine slopeOn_of_fderiv (fun z hz' => (hg' z hz').differentiableAt) fun z hz' => ?_
      rw [(hg' z hz').fderiv, ContinuousLinearMap.norm_smulRight_apply, norm_unitMap (hz z hz').2.2, one_mul]
      exact kb z hz' _ _ (hb _ (hz z hz').1).2.2
    have s := SlopeOn.bilin (ContinuousLinearMap.smulRightL ℝ Space E) hB sN s1
      (fun z hz' => (norm_unitMap (hz z hz').2.2).le) hρ1
    refine (s.congr hD).mono (le_of_eq ?_)
    field_simp
    ring

theorem homog_fderiv {A : Space → E} (hhom : ∀ s : ℝ, 0 < s → ∀ y, A (s • y) = A y) {s : ℝ} (hs : 0 < s)
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

theorem farBound_homog {A : Space → E} (hhom : ∀ s : ℝ, 0 < s → ∀ y, A (s • y) = A y)
    (hA : ∀ y : Space, y ≠ 0 → ContDiffAt ℝ 2 A y) : FarBound A 0 := by
  set K : Set Space := {w | 1 / 2 ≤ ‖w‖ ∧ ‖w‖ ≤ 2} with hKdef
  have hKc : IsCompact K := (isCompact_closedBall (0 : Space) 2).of_isClosed_subset
    ((isClosed_le continuous_const continuous_norm).inter (isClosed_le continuous_norm continuous_const))
    (fun w hw => by simpa [Metric.mem_closedBall, dist_zero_right] using hw.2)
  have hK0 : ∀ w ∈ K, w ≠ 0 := fun w hw h => by
    have := hw.1
    rw [h, norm_zero] at this
    linarith
  have hd : ∀ y : Space, y ≠ 0 → DifferentiableAt ℝ A y := fun y hy =>
    (hA y hy).differentiableAt (by norm_num)
  have hloc : LocallyLipschitzOn K (fderiv ℝ A) := by
    intro w hw
    obtain ⟨L, t, ht, hL⟩ := ((hA w (hK0 w hw)).fderiv_right (m := 1) (by norm_num)).exists_lipschitzOnWith
    exact ⟨L, t, mem_nhdsWithin_of_mem_nhds ht, hL⟩
  obtain ⟨L, hL⟩ := hloc.exists_lipschitzOnWith_of_compact hKc
  obtain ⟨M1, hStrain⟩ := hKc.exists_bound_of_continuousOn (f := A)
    (fun w hw => (hd w (hK0 w hw)).continuousAt.continuousWithinAt)
  obtain ⟨M2, hM2⟩ := hKc.exists_bound_of_continuousOn hL.continuousOn
  have hL0 : (0 : ℝ) ≤ L := L.2
  refine ⟨|M1| + |M2| + L, 2, by positivity, le_rfl, fun y hy => ?_⟩
  set Y := ‖y‖ with hY
  have hY0 : 0 < Y := by linarith
  have hmem : ∀ z ∈ Metric.ball y 1, Y⁻¹ • z ∈ K ∧ z ≠ 0 := by
    intro z hz
    obtain ⟨h2, h3⟩ := ball_norm_near hz
    have hn : ‖Y⁻¹ • z‖ = ‖z‖ / Y := by
      rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hY0]
      ring
    refine ⟨⟨?_, ?_⟩, fun h => by rw [h, norm_zero] at h2; linarith⟩
    · rw [hn, le_div_iff₀ hY0]; linarith
    · rw [hn, div_le_iff₀ hY0]; linarith
  have hval : ∀ z, A z = A (Y⁻¹ • z) := fun z => (hhom Y⁻¹ (inv_pos.2 hY0) z).symm
  have hder : ∀ z ∈ Metric.ball y 1, fderiv ℝ A z = Y⁻¹ • fderiv ℝ A (Y⁻¹ • z) := fun z hz =>
    homog_fderiv hhom hY0 (hd _ (hK0 _ (hmem z hz).1))
  refine ⟨fun z hz => hd z (hmem z hz).2, fun z hz => ?_, fun z hz => ?_, fun z hz w hw => ?_⟩
  · rw [hval z, pow_zero, div_one]
    exact (hStrain _ (hmem z hz).1).trans (by linarith [le_abs_self M1, abs_nonneg M2])
  · rw [hder z hz, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hY0, zero_add, pow_one]
    have := hM2 _ (hmem z hz).1
    rw [inv_mul_eq_div]
    exact div_le_div_of_nonneg_right (by linarith [le_abs_self M2, abs_nonneg M1]) hY0.le
  · rw [hder z hz, hder w hw, ← smul_sub, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hY0]
    have h1 := hL.dist_le_mul _ (hmem z hz).1 _ (hmem w hw).1
    rw [dist_eq_norm, dist_eq_norm, ← smul_sub, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hY0] at h1
    calc Y⁻¹ * ‖fderiv ℝ A (Y⁻¹ • z) - fderiv ℝ A (Y⁻¹ • w)‖ ≤ Y⁻¹ * (L * (Y⁻¹ * ‖z - w‖)) :=
          mul_le_mul_of_nonneg_left h1 (inv_nonneg.2 hY0.le)
      _ ≤ Y⁻¹ * ((|M1| + |M2| + L) * (Y⁻¹ * ‖z - w‖)) := by
          have : (0 : ℝ) ≤ Y⁻¹ * ‖z - w‖ := by positivity
          have : (L : ℝ) ≤ |M1| + |M2| + L := by linarith [abs_nonneg M1, abs_nonneg M2]
          gcongr
      _ = (|M1| + |M2| + L) / Y ^ (0 + 2) * ‖z - w‖ := by rw [zero_add]; field_simp

theorem FarBound.comp_unitBall {Φ : Space → ℝ × ℝ} (hΦ : FarBound Φ 0) (hK : ∀ z, ‖Φ z‖ ≤ 1) {g : ℝ × ℝ → F}
    (hg : ContDiff ℝ 1 g) (hg2 : ∃ L : NNReal, LipschitzOnWith L (fderiv ℝ g) (Metric.closedBall 0 1)) :
    FarBound (fun z => g (Φ z)) 0 := by
  obtain ⟨M, R, hM, hR, h⟩ := hΦ
  obtain ⟨L, hL⟩ := hg2
  have hKc : IsCompact (Metric.closedBall (0 : ℝ × ℝ) 1) := isCompact_closedBall 0 1
  obtain ⟨c0, hc0⟩ := hKc.exists_bound_of_continuousOn hg.continuous.continuousOn
  obtain ⟨c1, hc1⟩ := hKc.exists_bound_of_continuousOn (hg.continuous_fderiv one_ne_zero).continuousOn
  have hL0 : (0 : ℝ) ≤ L := L.2
  refine ⟨|c0| + |c1| * M + L * M * M, R, by positivity, hR, fun y hy => ?_⟩
  have hr : 1 ≤ ‖y‖ := by linarith
  have hb := h y hy
  simp only [pow_zero, div_one, zero_add, pow_one] at hb ⊢
  have hmem : ∀ z ∈ Metric.ball y 1, Φ z ∈ Metric.closedBall (0 : ℝ × ℝ) 1 := fun z _ => by
    rw [Metric.mem_closedBall, dist_zero_right]
    exact hK z
  have hc := hb.comp (K := Metric.closedBall (0 : ℝ × ℝ) 1) hmem
    (fun u _ => (hg.differentiable one_ne_zero u)) (fun u hu => (hc0 u hu).trans (le_abs_self c0))
    (fun u hu => (hc1 u hu).trans (le_abs_self c1)) hL0 (fun u hu u' hu' => by
      have := hL.dist_le_mul u hu u' hu'
      rwa [dist_eq_norm, dist_eq_norm] at this)
  refine hc.mono ?_ ?_ ?_
  · have : 0 ≤ |c1| * M + L * M * M := by positivity
    linarith
  · rw [mul_div_assoc']
    refine div_le_div_of_nonneg_right ?_ (by positivity)
    have : 0 ≤ |c0| + L * M * M := by positivity
    linarith
  · have hy2 : 0 < ‖y‖ := by linarith
    have e : L * (M / ‖y‖) * (M / ‖y‖) + |c1| * (M / ‖y‖ ^ 2) = (L * M * M + |c1| * M) / ‖y‖ ^ 2 := by
      field_simp
    rw [e]
    refine div_le_div_of_nonneg_right ?_ (by positivity)
    have : 0 ≤ |c0| := abs_nonneg _
    linarith

theorem unitBall_of_contDiff_two {g : ℝ × ℝ → F} (hg : ContDiff ℝ 2 g) :
    ContDiff ℝ 1 g ∧ ∃ L : NNReal, LipschitzOnWith L (fderiv ℝ g) (Metric.closedBall 0 1) :=
  ⟨hg.of_le (by norm_num), ((hg.fderiv_right (m := 1) (by norm_num)).locallyLipschitz.locallyLipschitzOn).exists_lipschitzOnWith_of_compact
    (isCompact_closedBall 0 1)⟩

end Internal

end GivenShape

end CertCell

end Breakdown
