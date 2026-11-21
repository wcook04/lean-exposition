import Breakdown.CertCell.LocalFieldDefs2
import Breakdown.CertCell.LocalModeIntegrable
import Breakdown.FracCell.ModeHeightAxis

open MeasureTheory Set Real

noncomputable section

namespace Breakdown.CertCell.LocalField

open SteadyCert CellCert CellCert.Assembly CellCert.CellAnalysis CellCert.CellFormula
open Breakdown.FracInternal.ModeHeightAxis Breakdown.CellCert.CellAnalysis.LowEntry.Internal

namespace Internal

private def thirdPhaseKernel (m : ℕ) (n : ℤ) (a b c : Fin 3) (θ : ℝ)
    (T : Space →L[ℝ] Space →L[ℝ] Space) : ℂ :=
  Complex.exp (-((azimuth m n * θ : ℝ) : ℂ) * Complex.I) * (frameThird θ T a b c : ℂ)

private theorem thirdPhaseKernel_continuous (m : ℕ) (n : ℤ) (a b c : Fin 3) :
    Continuous (fun q : ℝ × (Space →L[ℝ] Space →L[ℝ] Space) => thirdPhaseKernel m n a b c q.1 q.2) := by
  unfold thirdPhaseKernel frameThird frameUnit
  exact (phase_cont m n).mul (Complex.continuous_ofReal.comp
    (((continuous_snd.clm_apply ((unit_cont c).comp continuous_fst)).clm_apply
      ((unit_cont b).comp continuous_fst)).inner ((unit_cont a).comp continuous_fst)))

private theorem thirdPhaseKernel_norm_le (m : ℕ) (n : ℤ) (a b c : Fin 3) (θ : ℝ)
    (T : Space →L[ℝ] Space →L[ℝ] Space) : ‖thirdPhaseKernel m n a b c θ T‖ ≤ ‖T‖ := by
  rw [thirdPhaseKernel, norm_mul, phase_norm, one_mul, Complex.norm_real, Real.norm_eq_abs]
  unfold frameThird frameUnit
  refine (inner_unit_bound θ _ a).trans ((T.le_opNorm₂ _ _).trans ?_)
  calc ‖T‖ * ‖![radialUnit θ, angularUnit θ, axialUnit] c‖ * ‖![radialUnit θ, angularUnit θ, axialUnit] b‖
      ≤ ‖T‖ * 1 * 1 := by gcongr <;> exact unit_norm θ _
    _ = ‖T‖ := by ring

private theorem modeThird_eq_kernel (m : ℕ) (n : ℤ) (H : Space → (Space →L[ℝ] Space →L[ℝ] Space))
    (a b c : Fin 3) (p : ℝ × ℝ) : modeThird m n H a b c p =
      (1 / (2 * π) : ℂ) * ∫ θ in Ioo (-π) π, thirdPhaseKernel m n a b c θ (H (cylPoint p.1 θ p.2)) := by
  unfold modeThird
  rw [per_interval]
  · rfl
  · intro θ
    simp only [phase_per, cylPoint_per, frameThird, frameUnit, radialUnit, angularUnit,
      Real.cos_add_two_pi, Real.sin_add_two_pi]

private theorem bilinear_norm_le_entries (T : Space →L[ℝ] Space →L[ℝ] Space) :
    ‖T‖ ≤ ∑ i : Fin 3, ∑ j : Fin 3, ‖T (unitVector i) (unitVector j)‖ := by
  refine ContinuousLinearMap.opNorm_le_bound₂ T (by positivity) fun x y => ?_
  have hx : x = ∑ i, x i • unitVector i := by
    simpa [unitVector] using ((EuclideanSpace.basisFun (Fin 3) ℝ).sum_repr x).symm
  have hy : y = ∑ j, y j • unitVector j := by
    simpa [unitVector] using ((EuclideanSpace.basisFun (Fin 3) ℝ).sum_repr y).symm
  have hT : T x y = ∑ i, ∑ j, (x i * y j) • T (unitVector i) (unitVector j) := by
    conv_lhs => rw [hx, hy]
    simp only [map_sum, map_smul, FunLike.coe_sum, FunLike.coe_smul, Finset.sum_apply, Pi.smul_apply,
      Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [mul_comm]
  rw [hT, Finset.sum_mul, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [Finset.sum_mul, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [norm_smul, Real.norm_eq_abs, abs_mul]
  have hxi : |x i| ≤ ‖x‖ := by simpa [Real.norm_eq_abs] using PiLp.norm_apply_le x i
  have hyj : |y j| ≤ ‖y‖ := by simpa [Real.norm_eq_abs] using PiLp.norm_apply_le y j
  have h0 := norm_nonneg (T (unitVector i) (unitVector j))
  calc |x i| * |y j| * ‖T (unitVector i) (unitVector j)‖
      ≤ ‖x‖ * ‖y‖ * ‖T (unitVector i) (unitVector j)‖ := by gcongr
    _ = ‖T (unitVector i) (unitVector j)‖ * ‖x‖ * ‖y‖ := by ring

private theorem second_locallyIntegrable {v : Space → Space} {G : Space → (Space →L[ℝ] Space)}
    {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)} (hs : IsLocalSecondOrderField v G H) :
    LocallyIntegrable H volume := by
  have hsum : MemLp (fun y => ∑ i : Fin 3, ∑ j : Fin 3, ‖H y (unitVector i) (unitVector j)‖) 2 volume :=
    memLp_finsetSum _ fun i _ => memLp_finsetSum _ fun j _ =>
      (second_memLp hs.measurable_second hs.second_two i j).norm
  refine (hsum.locallyIntegrable (by norm_num)).mono hs.measurable_second
    (Filter.Eventually.of_forall fun y => ?_)
  refine (bilinear_norm_le_entries (H y)).trans (le_of_eq ?_)
  rw [Real.norm_of_nonneg (by positivity)]

private theorem weighted_third_integrableOn {v : Space → Space} {G : Space → (Space →L[ℝ] Space)}
    {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)} (hs : IsLocalSecondOrderField v G H)
    (m : ℕ) (n : ℤ) (a b c : Fin 3) (R Z : ℝ) :
    IntegrableOn (fun p : ℝ × ℝ => (p.1 : ℂ) * modeThird m n H a b c p) (Icc 0 R ×ˢ Icc (-Z) Z) := by
  have hint := (weighted_int R Z (second_locallyIntegrable hs) (thirdPhaseKernel m n a b c)
    (thirdPhaseKernel_continuous m n a b c) (thirdPhaseKernel_norm_le m n a b c)).const_mul
      (1 / (2 * π) : ℂ)
  refine IntegrableOn.congr_fun hint (fun p _ => ?_) (measurableSet_Icc.prod measurableSet_Icc)
  rw [modeThird_eq_kernel m n H a b c p]
  ring

private theorem real_coef_mul {s : Set (ℝ × ℝ)} (hs : IsCompact s) {f : ℝ × ℝ → ℂ} (hf : IntegrableOn f s)
    {g : ℝ × ℝ → ℝ} (hg : Continuous g) : IntegrableOn (fun p => ((g p : ℝ) : ℂ) * f p) s :=
  IntegrableOn.continuousOn_mul (Complex.continuous_ofReal.comp hg).continuousOn hf hs

private theorem rect_subset_strip (K : CellBox) (hK : IsCellBox K) :
    K.rect ⊆ Icc 0 K.r₂ ×ˢ Icc (-K.z₂) K.z₂ := by
  intro p hp
  simp only [CellBox.rect, mem_prod, mem_Icc] at hp
  exact ⟨⟨hK.r_order.1.trans hp.1.1, hp.1.2⟩, ⟨by linarith [hp.2.1, hK.z_order.1, hK.z_order.2], hp.2.2⟩⟩

private theorem Icc_min_max_reflect {u w l : ℝ} (huw : u < w) (hl : l = u ∨ l = w) :
    Icc (min l (u + w - l)) (max l (u + w - l)) = Icc u w := by
  rcases hl with h | h <;> rw [h]
  · rw [show u + w - u = w by ring, min_eq_left huw.le, max_eq_right huw.le]
  · rw [show u + w - w = u by ring, min_eq_right huw.le, max_eq_left huw.le]

private theorem radial_side_pair {K : CellBox} {V G0 T : ℝ × ℝ → ℂ}
    (hV : IntegrableOn V K.rect) (hG0 : IntegrableOn G0 K.rect) (lv ot : ℝ)
    (hset : Icc (min lv ot) (max lv ot) = Icc K.r₁ K.r₂)
    (hT : IntegrableOn (fun p : ℝ × ℝ => (((p.1 - ot) / (lv - ot) : ℝ) : ℂ) * T p) K.rect) :
    IntegrableOn (fun p : ℝ × ℝ => (((1 / (lv - ot) : ℝ)) : ℂ) * V p
        + (((p.1 - ot) / (lv - ot) : ℝ) : ℂ) * G0 p) (Icc (min lv ot) (max lv ot) ×ˢ Icc K.z₁ K.z₂) ∧
      IntegrableOn (fun p : ℝ × ℝ => (((1 / (lv - ot) : ℝ)) : ℂ) * G0 p
        + (((p.1 - ot) / (lv - ot) : ℝ) : ℂ) * T p) (Icc (min lv ot) (max lv ot) ×ˢ Icc K.z₁ K.z₂) := by
  rw [hset]
  have hc := rect_compact K
  exact ⟨(real_coef_mul hc hV (g := fun _ => 1 / (lv - ot)) continuous_const).add
      (real_coef_mul hc hG0 (g := fun p => (p.1 - ot) / (lv - ot)) (by fun_prop)),
    (real_coef_mul hc hG0 (g := fun _ => 1 / (lv - ot)) continuous_const).add hT⟩

private theorem height_side_pair {K : CellBox} {V G2 T : ℝ × ℝ → ℂ}
    (hV : IntegrableOn V K.rect) (hG2 : IntegrableOn G2 K.rect)
    (hT : IntegrableOn (fun p : ℝ × ℝ => (p.1 : ℂ) * T p) K.rect) (lv ot : ℝ)
    (hset : Icc (min lv ot) (max lv ot) = Icc K.z₁ K.z₂) :
    IntegrableOn (fun p : ℝ × ℝ => ((((1 / (lv - ot) : ℝ)) : ℂ) * V p
        + (((p.2 - ot) / (lv - ot) : ℝ) : ℂ) * G2 p) * ((1 : ℝ) : ℂ))
        (Icc K.r₁ K.r₂ ×ˢ Icc (min lv ot) (max lv ot)) ∧
      IntegrableOn (fun p : ℝ × ℝ => ((((1 / (lv - ot) : ℝ)) : ℂ) * G2 p
        + (((p.2 - ot) / (lv - ot) : ℝ) : ℂ) * T p) * ((p.1 : ℝ) : ℂ))
        (Icc K.r₁ K.r₂ ×ˢ Icc (min lv ot) (max lv ot)) := by
  rw [hset]
  have hc := rect_compact K
  refine ⟨?_, ?_⟩
  · have h := (real_coef_mul hc hV (g := fun _ => 1 / (lv - ot)) continuous_const).add
      (real_coef_mul hc hG2 (g := fun p => (p.2 - ot) / (lv - ot)) (by fun_prop))
    refine h.congr_fun (fun p _ => ?_) (rect_meas K)
    simp only [Pi.add_apply, Complex.ofReal_one, mul_one]
  · have h := (real_coef_mul hc hG2 (g := fun p => 1 / (lv - ot) * p.1) (by fun_prop)).add
      (real_coef_mul hc hT (g := fun p => (p.2 - ot) / (lv - ot)) (by fun_prop))
    refine h.congr_fun (fun p _ => ?_) (rect_meas K)
    simp only [Pi.add_apply]
    push_cast
    ring

end Internal

open Breakdown.CertCell.LocalField.Internal in
theorem localSideStripIntegrable : LocalSideStripIntegrableStatement := by
  intro k N c K S B L hL x hx n e a he
  have hbox := hL.box_eq
  subst hbox
  have hs := hx.1
  have hK : IsCellBox L.box := hL.box_valid
  have hsub := rect_subset_strip L.box hK
  have hc : IsCompact L.box.rect := rect_compact L.box
  have hV : IntegrableOn (L.velMode n x a) L.box.rect :=
    (localModeRectIntegrable c L.box S B L hL x hx n a 0).1
  have hG0 : IntegrableOn (L.gradModeOf n x a 0) L.box.rect :=
    (localModeRectIntegrable c L.box S B L hL x hx n a 0).2
  have hG2 : IntegrableOn (L.gradModeOf n x a 2) L.box.rect :=
    (localModeRectIntegrable c L.box S B L hL x hx n a 2).2
  have hT : ∀ b c : Fin 3,
      IntegrableOn (fun p : ℝ × ℝ => (p.1 : ℂ) * L.secondModeOf n x a b c p) L.box.rect :=
    fun b c => (weighted_third_integrableOn hs L.order n a b c L.box.r₂ L.box.z₂).mono_set hsub
  have hTu : L.box.r₁ ≠ 0 → ∀ b c : Fin 3, IntegrableOn (L.secondModeOf n x a b c) L.box.rect := by
    intro h0 b c
    have hpos : 0 < L.box.r₁ := lt_of_le_of_ne hK.r_order.1 (Ne.symm h0)
    have hne : ∀ p ∈ L.box.rect, p.1 ≠ 0 := fun p hp => ne_of_gt (lt_of_lt_of_le hpos hp.1.1)
    have hco : ContinuousOn (fun p : ℝ × ℝ => ((1 / p.1 : ℝ) : ℂ)) L.box.rect :=
      Complex.continuous_ofReal.comp_continuousOn (continuousOn_const.div continuous_fst.continuousOn hne)
    refine (IntegrableOn.continuousOn_mul hco (hT b c) hc).congr_fun (fun p hp => ?_) (rect_meas _)
    dsimp only
    rw [← mul_assoc, ← Complex.ofReal_mul, one_div_mul_cancel (hne p hp), Complex.ofReal_one, one_mul]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have hot : L.sideOther e = L.box.r₁ + L.box.r₂ - L.sideLevel e := by
      rw [CellLayout.sideOther, if_pos h]
    have hl : (L.sideLevel e = L.box.r₁ ∧ e.val = 0) ∨ (L.sideLevel e = L.box.r₂ ∧ e.val = 1) := by
      unfold CellLayout.sideLevel
      rcases (by omega : e.val = 0 ∨ e.val = 1) with h' | h' <;> simp [h']
    rw [hot]
    refine radial_side_pair hV hG0 (L.sideLevel e) _
      (Icc_min_max_reflect hK.r_order.2 (hl.imp And.left And.left)) ?_
    by_cases h0 : L.box.r₁ = 0
    · have hl2 : L.sideLevel e = L.box.r₂ := by
        rcases hl with hl | hl
        · exact absurd h0 (he hl.2)
        · exact hl.1
      refine IntegrableOn.congr_fun ((hT 0 0).const_mul (((1 / L.box.r₂ : ℝ)) : ℂ)) (fun p _ => ?_)
        (rect_meas _)
      rw [hl2, h0]
      simp only [zero_add, sub_self, sub_zero]
      push_cast
      ring
    · exact real_coef_mul hc (hTu h0 0 0) (by fun_prop)
  · have h2 : ¬ e.val < 2 := by omega
    have hot : L.sideOther e = L.box.z₁ + L.box.z₂ - L.sideLevel e := by
      rw [CellLayout.sideOther, if_neg h2]
    have hl : L.sideLevel e = L.box.z₁ ∨ L.sideLevel e = L.box.z₂ := by
      unfold CellLayout.sideLevel
      rcases (by omega : e.val = 2 ∨ e.val = 3) with h' | h' <;> simp [h']
    rw [hot]
    exact height_side_pair hV hG2 (hT 2 2) (L.sideLevel e) _ (Icc_min_max_reflect hK.z_order.2 hl)

end Breakdown.CertCell.LocalField
