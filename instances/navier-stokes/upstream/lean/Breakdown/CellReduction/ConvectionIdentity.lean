import Breakdown.CellReduction.MatrixFacts
import Breakdown.CellReduction.ConvectionSmooth

open scoped ContDiff ENNReal Topology
open MeasureTheory Filter

noncomputable section

namespace Breakdown

namespace CertReduction

namespace Internal

theorem lintegral_ofReal_mul_le {x z : Space → ℝ} (hx : AEMeasurable x) (hz : AEMeasurable z)
    (hx0 : ∀ y, 0 ≤ x y) (hz0 : ∀ y, 0 ≤ z y) :
    (∫⁻ y, ENNReal.ofReal (x y * z y)) ≤
      (∫⁻ y, ENNReal.ofReal (x y ^ 2)) ^ (1 / (2 : ℝ)) *
        (∫⁻ y, ENNReal.ofReal (z y ^ 2)) ^ (1 / (2 : ℝ)) := by
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq volume Real.HolderConjugate.two_two
    hx.ennreal_ofReal hz.ennreal_ofReal
  simp only [Pi.mul_apply] at h
  have ex : (∫⁻ y, ENNReal.ofReal (x y) ^ (2 : ℝ)) = ∫⁻ y, ENNReal.ofReal (x y ^ 2) :=
    lintegral_congr (fun y => by rw [ENNReal.rpow_two, ENNReal.ofReal_pow (hx0 y)])
  have ez : (∫⁻ y, ENNReal.ofReal (z y) ^ (2 : ℝ)) = ∫⁻ y, ENNReal.ofReal (z y ^ 2) :=
    lintegral_congr (fun y => by rw [ENNReal.rpow_two, ENNReal.ofReal_pow (hz0 y)])
  rw [ex, ez] at h
  calc (∫⁻ y, ENNReal.ofReal (x y * z y))
      = ∫⁻ y, ENNReal.ofReal (x y) * ENNReal.ofReal (z y) :=
        lintegral_congr (fun y => ENNReal.ofReal_mul (hx0 y))
    _ ≤ _ := h

theorem lintegral_ofReal_mul_lt_top {x z : Space → ℝ} (hx : AEMeasurable x) (hz : AEMeasurable z)
    (hx0 : ∀ y, 0 ≤ x y) (hz0 : ∀ y, 0 ≤ z y)
    (hxf : (∫⁻ y, ENNReal.ofReal (x y ^ 2)) < ⊤) (hzf : (∫⁻ y, ENNReal.ofReal (z y ^ 2)) < ⊤) :
    (∫⁻ y, ENNReal.ofReal (x y * z y)) < ⊤ := by
  refine (lintegral_ofReal_mul_le hx hz hx0 hz0).trans_lt (ENNReal.mul_lt_top ?_ ?_)
  · exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) hxf.ne
  · exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) hzf.ne

theorem tendsto_lintegral_ofReal_mul {x z : ℕ → Space → ℝ} (hx : ∀ n, AEMeasurable (x n))
    (hz : ∀ n, AEMeasurable (z n)) (hx0 : ∀ n y, 0 ≤ x n y) (hz0 : ∀ n y, 0 ≤ z n y)
    (hxl : Tendsto (fun n => ∫⁻ y, ENNReal.ofReal (x n y ^ 2)) atTop (𝓝 0))
    {K : ℝ≥0∞} (hK : K ≠ ⊤) (hzb : ∀ᶠ n in atTop, (∫⁻ y, ENNReal.ofReal (z n y ^ 2)) ≤ K) :
    Tendsto (fun n => ∫⁻ y, ENNReal.ofReal (x n y * z n y)) atTop (𝓝 0) := by
  have h2 : Tendsto (fun n => (∫⁻ y, ENNReal.ofReal (x n y ^ 2)) ^ (1 / (2 : ℝ))) atTop (𝓝 0) := by
    have h3 := ((ENNReal.continuous_rpow_const (y := 1 / (2 : ℝ))).tendsto 0).comp hxl
    rw [ENNReal.zero_rpow_of_pos (by norm_num)] at h3
    exact h3
  have hK2 : K ^ (1 / (2 : ℝ)) ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg (by norm_num) hK
  have h1 := ENNReal.Tendsto.mul_const h2 (Or.inr hK2)
  rw [zero_mul] at h1
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h1
    (Eventually.of_forall fun n => bot_le) ?_
  filter_upwards [hzb] with n hn
  refine (lintegral_ofReal_mul_le (hx n) (hz n) (hx0 n) (hz0 n)).trans ?_
  gcongr

theorem eventually_lintegral_le_one {f : ℕ → ℝ≥0∞} (hf : Tendsto f atTop (𝓝 0)) :
    ∀ᶠ n in atTop, f n ≤ 1 :=
  (tendsto_order.1 hf).2 1 (by norm_num) |>.mono fun _ h => h.le

theorem tendsto_integral_of_lintegral {F : ℕ → Space → ℝ} {f : Space → ℝ}
    (hFm : ∀ n, AEStronglyMeasurable (F n)) (hf : Integrable f)
    (hF : Tendsto (fun n => ∫⁻ y, ‖F n y - f y‖ₑ) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ y, F n y) atTop (𝓝 (∫ y, f y)) := by
  refine tendsto_integral_of_L1 f hf.aestronglyMeasurable ?_ hF
  filter_upwards [eventually_lintegral_le_one hF] with n hn
  have hd : Integrable (fun y => F n y - f y) :=
    ⟨(hFm n).sub hf.aestronglyMeasurable, lt_of_le_of_lt hn ENNReal.one_lt_top⟩
  have he : (fun y => F n y - f y) + f = F n := by
    funext y
    simp
  rw [← he]
  exact hd.add hf

theorem integrable_of_bound {f x z : Space → ℝ} {K : ℝ} (hfm : AEStronglyMeasurable f)
    (hx : AEMeasurable x) (hz : AEMeasurable z) (hx0 : ∀ y, 0 ≤ x y) (hz0 : ∀ y, 0 ≤ z y)
    (hxf : (∫⁻ y, ENNReal.ofReal (x y ^ 2)) < ⊤) (hzf : (∫⁻ y, ENNReal.ofReal (z y ^ 2)) < ⊤)
    (hb : ∀ y, ‖f y‖ ≤ K * (x y * z y)) : Integrable f := by
  refine ⟨hfm, ?_⟩
  unfold HasFiniteIntegral
  calc (∫⁻ y, ‖f y‖ₑ) ≤ ∫⁻ y, ENNReal.ofReal K * ENNReal.ofReal (x y * z y) := by
        refine lintegral_mono (fun y => ?_)
        rw [← ofReal_norm, ← ENNReal.ofReal_mul' (mul_nonneg (hx0 y) (hz0 y))]
        exact ENNReal.ofReal_le_ofReal (hb y)
    _ = ENNReal.ofReal K * ∫⁻ y, ENNReal.ofReal (x y * z y) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top
        (lintegral_ofReal_mul_lt_top hx hz hx0 hz0 hxf hzf)


theorem enorm_le_three {v x1 x2 x3 c : ℝ} (hc : 0 ≤ c) (h : ‖v‖ ≤ c * x1 + c * x2 + c * x3) :
    ‖v‖ₑ ≤ ENNReal.ofReal c * ENNReal.ofReal x1 + ENNReal.ofReal c * ENNReal.ofReal x2 +
      ENNReal.ofReal c * ENNReal.ofReal x3 := by
  rw [← ofReal_norm]
  calc ENNReal.ofReal ‖v‖ ≤ ENNReal.ofReal (c * x1 + c * x2 + c * x3) := ENNReal.ofReal_le_ofReal h
    _ ≤ ENNReal.ofReal (c * x1 + c * x2) + ENNReal.ofReal (c * x3) := ENNReal.ofReal_add_le
    _ ≤ ENNReal.ofReal (c * x1) + ENNReal.ofReal (c * x2) + ENNReal.ofReal (c * x3) :=
        add_le_add_left ENNReal.ofReal_add_le _
    _ = _ := by rw [ENNReal.ofReal_mul hc, ENNReal.ofReal_mul hc, ENNReal.ofReal_mul hc]

theorem tendsto_lintegral_three {X Y Z : ℕ → Space → ℝ} {c : ℝ} (hX : ∀ n, AEMeasurable (X n))
    (hY : ∀ n, AEMeasurable (Y n))
    (hXl : Tendsto (fun n => ∫⁻ y, ENNReal.ofReal (X n y)) atTop (𝓝 0))
    (hYl : Tendsto (fun n => ∫⁻ y, ENNReal.ofReal (Y n y)) atTop (𝓝 0))
    (hZl : Tendsto (fun n => ∫⁻ y, ENNReal.ofReal (Z n y)) atTop (𝓝 0)) :
    Tendsto (fun n => ∫⁻ y, ENNReal.ofReal c * ENNReal.ofReal (X n y) +
      ENNReal.ofReal c * ENNReal.ofReal (Y n y) + ENNReal.ofReal c * ENNReal.ofReal (Z n y))
      atTop (𝓝 0) := by
  have e : ∀ n, (∫⁻ y, ENNReal.ofReal c * ENNReal.ofReal (X n y) +
      ENNReal.ofReal c * ENNReal.ofReal (Y n y) + ENNReal.ofReal c * ENNReal.ofReal (Z n y)) =
      ENNReal.ofReal c * (∫⁻ y, ENNReal.ofReal (X n y)) +
        ENNReal.ofReal c * (∫⁻ y, ENNReal.ofReal (Y n y)) +
        ENNReal.ofReal c * (∫⁻ y, ENNReal.ofReal (Z n y)) := by
    intro n
    have m1 : AEMeasurable (fun y => ENNReal.ofReal c * ENNReal.ofReal (X n y) +
        ENNReal.ofReal c * ENNReal.ofReal (Y n y)) :=
      ((hX n).ennreal_ofReal.const_mul _).add ((hY n).ennreal_ofReal.const_mul _)
    have m2 : AEMeasurable (fun y => ENNReal.ofReal c * ENNReal.ofReal (X n y)) :=
      (hX n).ennreal_ofReal.const_mul _
    have e1 := lintegral_add_left' m1 (fun y => ENNReal.ofReal c * ENNReal.ofReal (Z n y))
    have e2 := lintegral_add_left' m2 (fun y => ENNReal.ofReal c * ENNReal.ofReal (Y n y))
    rw [e1, e2, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  simp only [e]
  have hc : ENNReal.ofReal c ≠ ⊤ := ENNReal.ofReal_ne_top
  have h := ((ENNReal.Tendsto.const_mul hXl (Or.inr hc)).add
    (ENNReal.Tendsto.const_mul hYl (Or.inr hc))).add (ENNReal.Tendsto.const_mul hZl (Or.inr hc))
  simpa using h

theorem convection_diff_bound (A G' : Space →L[ℝ] Space) (D T' V : Space) {C : ℝ} (hV : ‖V‖ ≤ C) :
    ‖inner ℝ (A V) (-D) - inner ℝ (G' V) (-T')‖ ≤
      C * (‖A - G'‖ * ‖D - T'‖) + C * (‖A - G'‖ * ‖T'‖) + C * (‖D - T'‖ * ‖G'‖) := by
  have hC : 0 ≤ C := (norm_nonneg _).trans hV
  have e : inner ℝ (A V) (-D) - inner ℝ (G' V) (-T') =
      inner ℝ ((A - G') V) (-D) + inner ℝ (G' V) (T' - D) := by
    simp only [sub_apply, inner_sub_left, inner_neg_right, inner_sub_right]
    ring
  have h1 : ‖(A - G') V‖ ≤ ‖A - G'‖ * C :=
    ((A - G').le_opNorm V).trans (mul_le_mul_of_nonneg_left hV (norm_nonneg _))
  have h2 : ‖G' V‖ ≤ ‖G'‖ * C := (G'.le_opNorm V).trans (mul_le_mul_of_nonneg_left hV (norm_nonneg _))
  have h3 : ‖-D‖ ≤ ‖D - T'‖ + ‖T'‖ := by
    rw [norm_neg]
    calc ‖D‖ = ‖(D - T') + T'‖ := by rw [sub_add_cancel]
      _ ≤ _ := norm_add_le _ _
  have h4 : ‖T' - D‖ = ‖D - T'‖ := norm_sub_rev _ _
  rw [e, Real.norm_eq_abs]
  calc |inner ℝ ((A - G') V) (-D) + inner ℝ (G' V) (T' - D)|
      ≤ |inner ℝ ((A - G') V) (-D)| + |inner ℝ (G' V) (T' - D)| := abs_add_le _ _
    _ ≤ ‖(A - G') V‖ * ‖-D‖ + ‖G' V‖ * ‖T' - D‖ :=
        add_le_add (abs_real_inner_le_norm _ _) (abs_real_inner_le_norm _ _)
    _ ≤ (‖A - G'‖ * C) * (‖D - T'‖ + ‖T'‖) + (‖G'‖ * C) * ‖D - T'‖ := by
        rw [h4]
        exact add_le_add (mul_le_mul h1 h3 (norm_nonneg _) (mul_nonneg (norm_nonneg _) hC))
          (mul_le_mul_of_nonneg_right h2 (norm_nonneg _))
    _ = _ := by ring

theorem strain_diff_bound (A G' B : Space →L[ℝ] Space) {C : ℝ} (hB : ‖B‖ ≤ C) :
    ‖(∑ i : Fin 3, inner ℝ (B (ContinuousLinearMap.adjoint A (unitVector i)))
        (ContinuousLinearMap.adjoint A (unitVector i))) -
      ∑ i : Fin 3, inner ℝ (B (ContinuousLinearMap.adjoint G' (unitVector i)))
        (ContinuousLinearMap.adjoint G' (unitVector i))‖ ≤
      3 * C * (‖A - G'‖ * ‖A - G'‖) + 3 * C * (‖A - G'‖ * ‖G'‖) + 3 * C * (‖A - G'‖ * ‖G'‖) := by
  have hC : 0 ≤ C := (norm_nonneg _).trans hB
  have hadj : ∀ (K : Space →L[ℝ] Space) (i : Fin 3),
      ‖ContinuousLinearMap.adjoint K (unitVector i)‖ ≤ ‖K‖ := by
    intro K i
    calc _ ≤ ‖ContinuousLinearMap.adjoint K‖ * ‖unitVector i‖ := ContinuousLinearMap.le_opNorm _ _
      _ = ‖K‖ := by rw [LinearIsometryEquiv.norm_map]; simp [unitVector]
  have hBx : ∀ x : Space, ‖B x‖ ≤ C * ‖x‖ := fun x =>
    (B.le_opNorm x).trans (mul_le_mul_of_nonneg_right hB (norm_nonneg _))
  have hterm : ∀ i : Fin 3,
      ‖inner ℝ (B (ContinuousLinearMap.adjoint A (unitVector i))) (ContinuousLinearMap.adjoint A (unitVector i)) -
        inner ℝ (B (ContinuousLinearMap.adjoint G' (unitVector i)))
          (ContinuousLinearMap.adjoint G' (unitVector i))‖ ≤
        C * (‖A - G'‖ * ‖A - G'‖) + C * (‖A - G'‖ * ‖G'‖) + C * (‖A - G'‖ * ‖G'‖) := by
    intro i
    have hpq : ContinuousLinearMap.adjoint A (unitVector i) - ContinuousLinearMap.adjoint G' (unitVector i) =
        ContinuousLinearMap.adjoint (A - G') (unitVector i) := by
      rw [map_sub, sub_apply]
    generalize hp : ContinuousLinearMap.adjoint A (unitVector i) = p at hpq ⊢
    generalize hq : ContinuousLinearMap.adjoint G' (unitVector i) = q at hpq ⊢
    have h1 : ‖p - q‖ ≤ ‖A - G'‖ := by rw [hpq]; exact hadj _ i
    have h2 : ‖q‖ ≤ ‖G'‖ := by rw [← hq]; exact hadj _ i
    have hp' : ‖p‖ ≤ ‖p - q‖ + ‖q‖ := by
      calc ‖p‖ = ‖(p - q) + q‖ := by rw [sub_add_cancel]
        _ ≤ _ := norm_add_le _ _
    have e : inner ℝ (B p) p - inner ℝ (B q) q = inner ℝ (B (p - q)) p + inner ℝ (B q) (p - q) := by
      simp only [map_sub, inner_sub_left, inner_sub_right]
      ring
    rw [e, Real.norm_eq_abs]
    calc |inner ℝ (B (p - q)) p + inner ℝ (B q) (p - q)|
        ≤ |inner ℝ (B (p - q)) p| + |inner ℝ (B q) (p - q)| := abs_add_le _ _
      _ ≤ ‖B (p - q)‖ * ‖p‖ + ‖B q‖ * ‖p - q‖ :=
          add_le_add (abs_real_inner_le_norm _ _) (abs_real_inner_le_norm _ _)
      _ ≤ (C * ‖p - q‖) * (‖p - q‖ + ‖q‖) + (C * ‖q‖) * ‖p - q‖ :=
          add_le_add (mul_le_mul (hBx _) hp' (norm_nonneg _) (mul_nonneg hC (norm_nonneg _)))
            (mul_le_mul_of_nonneg_right (hBx _) (norm_nonneg _))
      _ ≤ (C * ‖A - G'‖) * (‖A - G'‖ + ‖G'‖) + (C * ‖G'‖) * ‖A - G'‖ :=
          add_le_add (mul_le_mul (mul_le_mul_of_nonneg_left h1 hC) (add_le_add h1 h2)
              (add_nonneg (norm_nonneg _) (norm_nonneg _)) (mul_nonneg hC (norm_nonneg _)))
            (mul_le_mul (mul_le_mul_of_nonneg_left h2 hC) h1 (norm_nonneg _)
              (mul_nonneg hC (norm_nonneg _)))
      _ = _ := by ring
  rw [← Finset.sum_sub_distrib]
  refine (norm_sum_le _ _).trans ((Finset.sum_le_sum fun i _ => hterm i).trans (le_of_eq ?_))
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  push_cast
  ring

theorem aestronglyMeasurable_apply {f : Space → (Space →L[ℝ] Space)} {v : Space → Space}
    (hf : AEStronglyMeasurable f) (hv : AEStronglyMeasurable v) :
    AEStronglyMeasurable (fun y => f y (v y)) :=
  (continuous_fst.clm_apply continuous_snd).comp_aestronglyMeasurable (hf.prodMk hv)

theorem aestronglyMeasurable_pairing {A : Space → (Space →L[ℝ] Space)} {D V : Space → Space}
    (hA : AEStronglyMeasurable A) (hD : AEStronglyMeasurable D) (hV : AEStronglyMeasurable V) :
    AEStronglyMeasurable (fun y => inner ℝ (A y (V y)) (-D y)) :=
  (continuous_fst.inner continuous_snd.neg).comp_aestronglyMeasurable
    ((aestronglyMeasurable_apply hA hV).prodMk hD)

theorem aestronglyMeasurable_strain {A B : Space → (Space →L[ℝ] Space)}
    (hA : AEStronglyMeasurable A) (hB : AEStronglyMeasurable B) :
    AEStronglyMeasurable (fun y => ∑ i : Fin 3, inner ℝ (B y (ContinuousLinearMap.adjoint (A y) (unitVector i)))
      (ContinuousLinearMap.adjoint (A y) (unitVector i))) := by
  have hadj : Continuous (fun K : Space →L[ℝ] Space => ContinuousLinearMap.adjoint K) :=
    ContinuousLinearMap.adjoint.continuous
  have hi : ∀ i : Fin 3, AEStronglyMeasurable (fun y => ContinuousLinearMap.adjoint (A y) (unitVector i)) :=
    fun i => aestronglyMeasurable_apply (hadj.comp_aestronglyMeasurable hA) aestronglyMeasurable_const
  have hj : ∀ i : Fin 3, AEStronglyMeasurable (fun y => inner ℝ (B y (ContinuousLinearMap.adjoint (A y) (unitVector i)))
      (ContinuousLinearMap.adjoint (A y) (unitVector i))) := fun i =>
    (continuous_fst.inner continuous_snd).comp_aestronglyMeasurable
      ((aestronglyMeasurable_apply hB (hi i)).prodMk (hi i))
  have e : (fun y => ∑ i : Fin 3, inner ℝ (B y (ContinuousLinearMap.adjoint (A y) (unitVector i)))
      (ContinuousLinearMap.adjoint (A y) (unitVector i))) = fun y =>
      inner ℝ (B y (ContinuousLinearMap.adjoint (A y) (unitVector 0))) (ContinuousLinearMap.adjoint (A y) (unitVector 0)) +
      inner ℝ (B y (ContinuousLinearMap.adjoint (A y) (unitVector 1))) (ContinuousLinearMap.adjoint (A y) (unitVector 1)) +
      inner ℝ (B y (ContinuousLinearMap.adjoint (A y) (unitVector 2))) (ContinuousLinearMap.adjoint (A y) (unitVector 2)) := by
    funext y
    exact Fin.sum_univ_three _
  rw [e]
  exact ((hj 0).add (hj 1)).add (hj 2)

end Internal

open Internal in
theorem convectionIdentityHolds_of
    (hsmooth : ∀ (W u : Space → Space) (C : ℝ), ContDiff ℝ 1 W → (∀ y, ‖W y‖ ≤ C) →
      (∀ y, ‖fderiv ℝ W y‖ ≤ C) → (∀ y, divergenceAt W y = 0) → ContDiff ℝ ∞ u →
      HasCompactSupport u →
      (∫ y, inner ℝ (fderiv ℝ u y (W y)) (-sumSecondPartialsAt u y)) =
        ∫ y, ∑ i : Fin 3, inner ℝ (fderiv ℝ W y (ContinuousLinearMap.adjoint (fderiv ℝ u y) (unitVector i)))
          (ContinuousLinearMap.adjoint (fderiv ℝ u y) (unitVector i)))
    (happrox : ∀ (Γ : Set Symmetry) (w : Space → Space) (G : Space → (Space →L[ℝ] Space))
      (H : Space → (Space →L[ℝ] Space →L[ℝ] Space)), IsProfileField Γ w G H →
      ∃ u : ℕ → Space → Space, (∀ n, ContDiff ℝ ∞ (u n) ∧ HasCompactSupport (u n)) ∧
        Tendsto (fun n => ∫⁻ y, ENNReal.ofReal (matSq (fderiv ℝ (u n) y - G y))) atTop (𝓝 0) ∧
        Tendsto (fun n => ∫⁻ y, ENNReal.ofReal (‖sumSecondPartialsAt (u n) y - secondDerivTrace (H y)‖ ^ 2))
          atTop (𝓝 0)) :
    ConvectionIdentityHolds := by
  intro Γ W w G H C hW hWb hDW hdiv hP
  obtain ⟨u, hu, hA, hD⟩ := happrox Γ w G H hP
  have hC : 0 ≤ C := (norm_nonneg _).trans (hWb 0)
  have hGm : AEStronglyMeasurable G := hP.weak_gradient.2.1.aestronglyMeasurable
  have hTm : AEStronglyMeasurable (fun y => secondDerivTrace (H y)) := by
    have e : (fun y => secondDerivTrace (H y)) = fun y =>
        (H y).flip (unitVector 0) (unitVector 0) + (H y).flip (unitVector 1) (unitVector 1) +
          (H y).flip (unitVector 2) (unitVector 2) := by
      funext y
      simp [secondDerivTrace, Fin.sum_univ_three]
    rw [e]
    exact ((aestronglyMeasurable_apply (hP.weak_secondDeriv 0).2.1.aestronglyMeasurable
      aestronglyMeasurable_const).add (aestronglyMeasurable_apply
        (hP.weak_secondDeriv 1).2.1.aestronglyMeasurable aestronglyMeasurable_const)).add
      (aestronglyMeasurable_apply (hP.weak_secondDeriv 2).2.1.aestronglyMeasurable
        aestronglyMeasurable_const)
  have hWm : AEStronglyMeasurable W := hW.continuous.aestronglyMeasurable
  have hDWm : AEStronglyMeasurable (fderiv ℝ W) := (hW.continuous_fderiv one_ne_zero).aestronglyMeasurable
  have hAm : ∀ n, AEStronglyMeasurable (fderiv ℝ (u n)) := fun n =>
    ((hu n).1.continuous_fderiv (by simp)).aestronglyMeasurable
  have hLm : ∀ n, AEStronglyMeasurable (fun y => sumSecondPartialsAt (u n) y) := by
    intro n
    have h2 : Continuous (iteratedFDeriv ℝ 2 (u n)) := (hu n).1.continuous_iteratedFDeriv (by norm_cast)
    have hc : Continuous (fun y => ∑ i : Fin 3, iteratedFDeriv ℝ 2 (u n) y ![unitVector i, unitVector i]) :=
      continuous_finsetSum _ fun i _ => (continuous_eval_const _).comp h2
    exact hc.aestronglyMeasurable
  have ham : ∀ n, AEMeasurable (fun y => ‖fderiv ℝ (u n) y - G y‖) := fun n =>
    ((hAm n).sub hGm).norm.aemeasurable
  have hdm : ∀ n, AEMeasurable (fun y => ‖sumSecondPartialsAt (u n) y - secondDerivTrace (H y)‖) := fun n =>
    ((hLm n).sub hTm).norm.aemeasurable
  have hgm : AEMeasurable (fun y => ‖G y‖) := hGm.norm.aemeasurable
  have htm : AEMeasurable (fun y => ‖secondDerivTrace (H y)‖) := hTm.norm.aemeasurable
  have hal : Tendsto (fun n => ∫⁻ y, ENNReal.ofReal (‖fderiv ℝ (u n) y - G y‖ ^ 2)) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hA (fun n => bot_le)
      (fun n => lintegral_mono fun y => ENNReal.ofReal_le_ofReal (operatorSquareBound _))
  have hgf : (∫⁻ y, ENNReal.ofReal (‖G y‖ ^ 2)) < ⊤ :=
    lt_of_le_of_lt (lintegral_mono fun y => ENNReal.ofReal_le_ofReal (operatorSquareBound _))
      hP.gradient_finite
  have htf : (∫⁻ y, ENNReal.ofReal (‖secondDerivTrace (H y)‖ ^ 2)) < ⊤ := hP.sumSecondPartials_finite
  have ha1 := eventually_lintegral_le_one hal
  have hd1 := eventually_lintegral_le_one hD
  have hLf : Integrable (fun y => inner ℝ (G y (W y)) (-secondDerivTrace (H y))) := by
    refine integrable_of_bound (aestronglyMeasurable_pairing hGm hTm hWm) hgm htm
      (fun y => norm_nonneg _) (fun y => norm_nonneg _) hgf htf (K := C) (fun y => ?_)
    have h := convection_diff_bound (G y) 0 (secondDerivTrace (H y)) 0 (W y) (hWb y)
    simpa using h
  have hRf : Integrable (fun y => ∑ i : Fin 3, inner ℝ (fderiv ℝ W y
      (ContinuousLinearMap.adjoint (G y) (unitVector i))) (ContinuousLinearMap.adjoint (G y) (unitVector i))) := by
    refine integrable_of_bound (aestronglyMeasurable_strain hGm hDWm) hgm hgm
      (fun y => norm_nonneg _) (fun y => norm_nonneg _) hgf hgf (K := 3 * C) (fun y => ?_)
    have h := strain_diff_bound (G y) 0 (fderiv ℝ W y) (hDW y)
    simpa using h
  have hLc : Tendsto (fun n => ∫ y, inner ℝ (fderiv ℝ (u n) y (W y)) (-sumSecondPartialsAt (u n) y)) atTop
      (𝓝 (∫ y, inner ℝ (G y (W y)) (-secondDerivTrace (H y)))) := by
    refine tendsto_integral_of_lintegral (fun n => aestronglyMeasurable_pairing (hAm n) (hLm n) hWm) hLf ?_
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (tendsto_lintegral_three (c := C) (fun n => (ham n).mul (hdm n)) (fun n => (ham n).mul htm)
        (tendsto_lintegral_ofReal_mul ham hdm (fun n y => norm_nonneg _) (fun n y => norm_nonneg _) hal
          ENNReal.one_ne_top hd1)
        (tendsto_lintegral_ofReal_mul (z := fun _ => fun y => ‖secondDerivTrace (H y)‖) ham (fun _ => htm)
          (fun n y => norm_nonneg _) (fun n y => norm_nonneg _) hal htf.ne
          (Eventually.of_forall fun n => le_rfl))
        (tendsto_lintegral_ofReal_mul (z := fun _ => fun y => ‖G y‖) hdm (fun _ => hgm)
          (fun n y => norm_nonneg _) (fun n y => norm_nonneg _) hD hgf.ne
          (Eventually.of_forall fun n => le_rfl)))
      (fun n => bot_le) (fun n => lintegral_mono fun y => ?_)
    exact enorm_le_three hC (convection_diff_bound _ _ _ _ _ (hWb y))
  have hRc : Tendsto (fun n => ∫ y, ∑ i : Fin 3, inner ℝ (fderiv ℝ W y
      (ContinuousLinearMap.adjoint (fderiv ℝ (u n) y) (unitVector i)))
        (ContinuousLinearMap.adjoint (fderiv ℝ (u n) y) (unitVector i))) atTop
      (𝓝 (∫ y, ∑ i : Fin 3, inner ℝ (fderiv ℝ W y
      (ContinuousLinearMap.adjoint (G y) (unitVector i))) (ContinuousLinearMap.adjoint (G y) (unitVector i)))) := by
    refine tendsto_integral_of_lintegral (fun n => aestronglyMeasurable_strain (hAm n) hDWm) hRf ?_
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (tendsto_lintegral_three (c := 3 * C) (fun n => (ham n).mul (ham n)) (fun n => (ham n).mul hgm)
        (tendsto_lintegral_ofReal_mul ham ham (fun n y => norm_nonneg _) (fun n y => norm_nonneg _) hal
          ENNReal.one_ne_top ha1)
        (tendsto_lintegral_ofReal_mul (z := fun _ => fun y => ‖G y‖) ham (fun _ => hgm)
          (fun n y => norm_nonneg _) (fun n y => norm_nonneg _) hal hgf.ne
          (Eventually.of_forall fun n => le_rfl))
        (tendsto_lintegral_ofReal_mul (z := fun _ => fun y => ‖G y‖) ham (fun _ => hgm)
          (fun n y => norm_nonneg _) (fun n y => norm_nonneg _) hal hgf.ne
          (Eventually.of_forall fun n => le_rfl)))
      (fun n => bot_le) (fun n => lintegral_mono fun y => ?_)
    exact enorm_le_three (by positivity) (strain_diff_bound _ _ _ (hDW y))
  have heq : ∀ n, (∫ y, inner ℝ (fderiv ℝ (u n) y (W y)) (-sumSecondPartialsAt (u n) y)) =
      ∫ y, ∑ i : Fin 3, inner ℝ (fderiv ℝ W y
        (ContinuousLinearMap.adjoint (fderiv ℝ (u n) y) (unitVector i)))
          (ContinuousLinearMap.adjoint (fderiv ℝ (u n) y) (unitVector i)) := fun n =>
    hsmooth W (u n) C hW hWb hDW hdiv (hu n).1 (hu n).2
  exact tendsto_nhds_unique hLc (hRc.congr fun n => (heq n).symm)

theorem convectionIdentityHolds_of_approx
    (happrox : ∀ (Γ : Set Symmetry) (w : Space → Space) (G : Space → (Space →L[ℝ] Space))
      (H : Space → (Space →L[ℝ] Space →L[ℝ] Space)), IsProfileField Γ w G H →
      ∃ u : ℕ → Space → Space, (∀ n, ContDiff ℝ ∞ (u n) ∧ HasCompactSupport (u n)) ∧
        Tendsto (fun n => ∫⁻ y, ENNReal.ofReal (matSq (fderiv ℝ (u n) y - G y))) atTop (𝓝 0) ∧
        Tendsto (fun n => ∫⁻ y, ENNReal.ofReal (‖sumSecondPartialsAt (u n) y - secondDerivTrace (H y)‖ ^ 2))
          atTop (𝓝 0)) :
    ConvectionIdentityHolds :=
  convectionIdentityHolds_of convectionIdentitySmooth happrox

end CertReduction

end Breakdown
