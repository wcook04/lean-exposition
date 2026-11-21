import Breakdown.Frac.StSpace
import Breakdown.Uniqueness.EnergyDefs
import Breakdown.Uniqueness.FundSolDecay
import Breakdown.Uniqueness.CutoffBounds

open scoped ContDiff ENNReal Topology
open MeasureTheory Set Real Filter

noncomputable section

namespace Breakdown

private lemma contDiff_divergence_field {ψ : Space → Space} (hψ : ContDiff ℝ ∞ ψ) :
    ContDiff ℝ ∞ (divergenceAt ψ) := by
  have hd : ContDiff ℝ ∞ (fderiv ℝ ψ) := hψ.fderiv_right (m := ∞) le_rfl
  have e : divergenceAt ψ = fun x => ∑ i : Fin 3,
      (EuclideanSpace.proj i : Space →L[ℝ] ℝ) (fderiv ℝ ψ x (unitVector i)) := by
    funext x; simp [divergenceAt]
  rw [e]
  exact ContDiff.sum fun i _ => (EuclideanSpace.proj i : Space →L[ℝ] ℝ).contDiff.comp
    (hd.clm_apply contDiff_const)

private lemma hasCompactSupport_divergence_field {ψ : Space → Space} (hc : HasCompactSupport ψ) :
    HasCompactSupport (divergenceAt ψ) := by
  show HasCompactSupport
    ((fun A : Space →L[ℝ] Space => ∑ i : Fin 3, A (unitVector i) i) ∘ fderiv ℝ ψ)
  exact (hc.fderiv (𝕜 := ℝ)).comp_left (by simp)

private lemma fderiv_slice_eq_fderivWithin {T : ℝ} {f : ℝ → Space → ℝ}
    (hf : ContDiffOn ℝ ∞ (fun z : ℝ × Space => f z.1 z.2) (Icc 0 T ×ˢ univ)) {τ : ℝ}
    (hτ : τ ∈ Icc 0 T) (x w : Space) :
    fderiv ℝ (f τ) x w =
      fderivWithin ℝ (fun z : ℝ × Space => f z.1 z.2) (Icc 0 T ×ˢ univ) (τ, x) (0, w) := by
  have hd : DifferentiableWithinAt ℝ (fun z : ℝ × Space => f z.1 z.2) (Icc 0 T ×ˢ univ) (τ, x) :=
    (hf.differentiableOn (by simp)) _ ⟨hτ, mem_univ _⟩
  have hg : HasFDerivWithinAt (fun y : Space => (τ, y)) (ContinuousLinearMap.inr ℝ ℝ Space)
      univ x := (hasFDerivAt_prodMk_right τ x).hasFDerivWithinAt
  have h := hd.hasFDerivWithinAt.comp x hg (fun y _ => ⟨hτ, mem_univ y⟩)
  rw [hasFDerivWithinAt_univ] at h
  have e : f τ = (fun z : ℝ × Space => f z.1 z.2) ∘ fun y : Space => (τ, y) := rfl
  rw [e, h.fderiv]
  simp

private lemma continuousOn_integral_inner_gradient {T : ℝ} (hT : 0 < T) {q : ℝ → Space → ℝ}
    (hq : ContDiffOn ℝ ∞ (fun z : ℝ × Space => q z.1 z.2) (Icc 0 T ×ˢ univ))
    {ϕ : Space → Space} (hϕ : Continuous ϕ) (hc : HasCompactSupport ϕ) :
    ContinuousOn (fun t => ∫ x, inner ℝ (gradientAt (q t) x) (ϕ x)) (Icc 0 T) := by
  have hs : UniqueDiffOn ℝ (Icc 0 T ×ˢ (univ : Set Space)) :=
    (uniqueDiffOn_Icc hT).prod uniqueDiffOn_univ
  have hD := hq.continuousOn_fderivWithin hs (by simp)
  have h1 : ContinuousOn (fun z : ℝ × Space => ∑ i : Fin 3,
      fderivWithin ℝ (fun z : ℝ × Space => q z.1 z.2) (Icc 0 T ×ˢ univ) z (0, unitVector i) •
        unitVector i) (Icc 0 T ×ˢ univ) :=
    continuousOn_finsetSum _ fun i _ => (hD.clm_apply continuousOn_const).smul continuousOn_const
  have hG : ContinuousOn (fun z : ℝ × Space => gradientAt (q z.1) z.2) (Icc 0 T ×ˢ univ) := by
    refine h1.congr fun z hz => ?_
    simp only [gradientAt]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [fderiv_slice_eq_fderivWithin hq hz.1]
  refine continuousOn_integral_of_compact_support (f := fun t x => inner ℝ (gradientAt (q t) x) (ϕ x))
    hc.isCompact (hG.inner (hϕ.comp continuous_snd).continuousOn) ?_
  intro t x _ hx
  simp [image_eq_zero_of_notMem_tsupport hx]

private def quadraticStress (v : ℝ → Space → Space) (θ : Space → ℝ) (t : ℝ) (x : Space) : ℝ :=
  ∑ i, ∑ j, v t x i * v t x j * FundSol.secondPartial θ i j x

private lemma abs_quadratic_form_le (a : Space) (m : Fin 3 → Fin 3 → ℝ) {K : ℝ}
    (hm : ∀ i j, |m i j| ≤ K) : |∑ i, ∑ j, a i * a j * m i j| ≤ 9 * K * ‖a‖ ^ 2 := by
  have ha : ∀ i, |a i| ≤ ‖a‖ := fun i => by
    rw [← Real.norm_eq_abs]; exact PiLp.norm_apply_le a i
  have ht : ∀ i j, |a i * a j * m i j| ≤ K * ‖a‖ ^ 2 := fun i j => by
    rw [abs_mul, abs_mul]
    calc |a i| * |a j| * |m i j| ≤ ‖a‖ * ‖a‖ * K := by
          gcongr
          · exact ha i
          · exact ha j
          · exact hm i j
      _ = K * ‖a‖ ^ 2 := by ring
  calc |∑ i, ∑ j, a i * a j * m i j| ≤ ∑ i, ∑ j, |a i * a j * m i j| :=
        (Finset.abs_sum_le_sum_abs _ _).trans
          (Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ _i : Fin 3, ∑ _j : Fin 3, K * ‖a‖ ^ 2 :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ht i j
    _ = 9 * K * ‖a‖ ^ 2 := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        norm_num
        ring

private lemma abs_secondPartial_le_decay {θ : Space → ℝ} {C : ℝ}
    (hC : ∀ x, ‖iteratedFDeriv ℝ 2 θ x‖ ≤ C * (1 + ‖x‖)⁻¹ ^ (2 + 1)) (i j : Fin 3) (x : Space) :
    |FundSol.secondPartial θ i j x| ≤ |C| * (1 + ‖x‖)⁻¹ := by
  have h1 : |FundSol.secondPartial θ i j x| ≤ ‖iteratedFDeriv ℝ 2 θ x‖ := by
    unfold FundSol.secondPartial
    rw [← Real.norm_eq_abs]
    refine (ContinuousMultilinearMap.le_opNorm _ _).trans ?_
    simp [unitVector, Fin.prod_univ_two]
  have h0 : 0 ≤ (1 + ‖x‖)⁻¹ := by positivity
  have h01 : (1 + ‖x‖)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith [norm_nonneg x])
  have h3 : (1 + ‖x‖)⁻¹ ^ (2 + 1) ≤ (1 + ‖x‖)⁻¹ := pow_le_of_le_one h0 h01 (by norm_num)
  calc |FundSol.secondPartial θ i j x| ≤ C * (1 + ‖x‖)⁻¹ ^ (2 + 1) := h1.trans (hC x)
    _ ≤ |C| * (1 + ‖x‖)⁻¹ ^ (2 + 1) := mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)
    _ ≤ |C| * (1 + ‖x‖)⁻¹ := mul_le_mul_of_nonneg_left h3 (abs_nonneg C)

private lemma continuous_secondPartial_of_smooth {θ : Space → ℝ} (hθ : ContDiff ℝ ∞ θ)
    (i j : Fin 3) : Continuous (FundSol.secondPartial θ i j) := by
  unfold FundSol.secondPartial
  exact (hθ.continuous_iteratedFDeriv (WithTop.coe_le_coe.mpr le_top)).eval_const _

private lemma continuousOn_stressPairing_self {T : ℝ} {v : ℝ → Space → Space}
    (hv : ContinuousOn (fun z : ℝ × Space => v z.1 z.2) (Icc 0 T ×ˢ univ))
    {A : ℝ} (hA : ∀ t ∈ Icc 0 T, ∫⁻ x, ENNReal.ofReal (‖v t x‖ ^ 2) ≤ ENNReal.ofReal A)
    {θ : Space → ℝ} (hθ : ContDiff ℝ ∞ θ) {C : ℝ}
    (hC : ∀ x, ‖iteratedFDeriv ℝ 2 θ x‖ ≤ C * (1 + ‖x‖)⁻¹ ^ (2 + 1)) :
    ContinuousOn (fun t => stressPairing (v t) (v t) θ) (Icc 0 T) := by
  have hsec := continuous_secondPartial_of_smooth hθ
  have hsecb := abs_secondPartial_le_decay hC
  have hM : ∀ i j x, |FundSol.secondPartial θ i j x| ≤ |C| := fun i j x => by
    have h01 : (1 + ‖x‖)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith [norm_nonneg x])
    exact (hsecb i j x).trans (by
      calc |C| * (1 + ‖x‖)⁻¹ ≤ |C| * 1 := mul_le_mul_of_nonneg_left h01 (abs_nonneg C)
        _ = |C| := mul_one _)
  have hvi : ∀ i, ContinuousOn (fun z : ℝ × Space => v z.1 z.2 i) (Icc 0 T ×ˢ univ) := fun i =>
    (EuclideanSpace.proj i : Space →L[ℝ] ℝ).continuous.comp_continuousOn hv
  have hH : ContinuousOn (fun z : ℝ × Space => quadraticStress v θ z.1 z.2) (Icc 0 T ×ˢ univ) := by
    unfold quadraticStress
    exact continuousOn_finsetSum _ fun i _ => continuousOn_finsetSum _ fun j _ =>
      ((hvi i).mul (hvi j)).mul ((hsec i j).comp continuous_snd).continuousOn
  have hslice : ∀ t ∈ Icc 0 T, Continuous (v t) := fun t ht =>
    hv.comp_continuous (continuous_const.prodMk continuous_id) fun x => ⟨ht, mem_univ x⟩
  have hHt : ∀ t ∈ Icc 0 T, Continuous (quadraticStress v θ t) := fun t ht =>
    hH.comp_continuous (continuous_const.prodMk continuous_id) fun x => ⟨ht, mem_univ x⟩
  have hsq : ∀ t ∈ Icc 0 T, Integrable (fun x => ‖v t x‖ ^ 2) := fun t ht =>
    ⟨((hslice t ht).norm.pow 2).aestronglyMeasurable,
      (hasFiniteIntegral_iff_ofReal (ae_of_all _ fun x => by positivity)).2
        ((hA t ht).trans_lt ENNReal.ofReal_lt_top)⟩
  have hsqle : ∀ t ∈ Icc 0 T, ∫ x, ‖v t x‖ ^ 2 ≤ max A 0 := fun t ht => by
    calc ∫ x, ‖v t x‖ ^ 2 = (∫⁻ x, ENNReal.ofReal (‖v t x‖ ^ 2)).toReal :=
          integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun x => by positivity)
            ((hslice t ht).norm.pow 2).aestronglyMeasurable
      _ ≤ (ENNReal.ofReal A).toReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hA t ht)
      _ = max A 0 := ENNReal.toReal_ofReal'
  have hHint : ∀ t ∈ Icc 0 T, Integrable (quadraticStress v θ t) := fun t ht =>
    ((hsq t ht).const_mul (9 * |C|)).mono' (hHt t ht).aestronglyMeasurable
      (ae_of_all _ fun x => by
        rw [Real.norm_eq_abs]
        exact abs_quadratic_form_le (v t x) (fun i j => FundSol.secondPartial θ i j x)
          (fun i j => hM i j x))
  have hcut : ∀ n : ℕ, ∀ t ∈ Icc 0 T,
      Integrable (fun x => radialCutoff ((n : ℝ) + 1) x * quadraticStress v θ t x) :=
    fun n t ht => ((contDiff_radialCutoff (by positivity)).continuous.mul
      (hHt t ht)).integrable_of_hasCompactSupport
        ((hasCompactSupport_radialCutoff (by positivity)).mul_right)
  have htail : ∀ n : ℕ, ∀ t ∈ Icc 0 T, ∀ x,
      |quadraticStress v θ t x - radialCutoff ((n : ℝ) + 1) x * quadraticStress v θ t x| ≤
        9 * (|C| * ((n : ℝ) + 2)⁻¹) * ‖v t x‖ ^ 2 := by
    intro n t _ x
    have hr : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    by_cases hx : ‖x‖ ≤ (n : ℝ) + 1
    · rw [radialCutoff_eq_one hr hx, one_mul, sub_self, abs_zero]
      positivity
    · replace hx := not_le.1 hx
      have hb : |quadraticStress v θ t x| ≤ 9 * (|C| * ((n : ℝ) + 2)⁻¹) * ‖v t x‖ ^ 2 := by
        refine abs_quadratic_form_le (v t x) (fun i j => FundSol.secondPartial θ i j x)
          (fun i j => (hsecb i j x).trans ?_)
        exact mul_le_mul_of_nonneg_left (inv_anti₀ (by positivity) (by linarith))
          (abs_nonneg C)
      have h0 := radialCutoff_nonneg ((n : ℝ) + 1) x
      have h1 := radialCutoff_le_one ((n : ℝ) + 1) x
      have hχ : |1 - radialCutoff ((n : ℝ) + 1) x| ≤ 1 := abs_le.2 ⟨by linarith, by linarith⟩
      rw [← one_sub_mul, abs_mul]
      calc |1 - radialCutoff ((n : ℝ) + 1) x| * |quadraticStress v θ t x|
          ≤ 1 * (9 * (|C| * ((n : ℝ) + 2)⁻¹) * ‖v t x‖ ^ 2) :=
            mul_le_mul hχ hb (abs_nonneg _) zero_le_one
        _ = _ := one_mul _
  have hGn : ∀ n : ℕ, ContinuousOn
      (fun t => ∫ x, radialCutoff ((n : ℝ) + 1) x * quadraticStress v θ t x) (Icc 0 T) := by
    intro n
    have hr : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    refine continuousOn_integral_of_compact_support
      (f := fun t x => radialCutoff ((n : ℝ) + 1) x * quadraticStress v θ t x)
      (hasCompactSupport_radialCutoff hr).isCompact
      (((contDiff_radialCutoff hr).continuous.comp continuous_snd).continuousOn.mul hH) ?_
    intro t x _ hx
    simp [image_eq_zero_of_notMem_tsupport hx]
  have hU : TendstoUniformlyOn
      (fun (n : ℕ) t => ∫ x, radialCutoff ((n : ℝ) + 1) x * quadraticStress v θ t x)
      (fun t => ∫ x, quadraticStress v θ t x) atTop (Icc 0 T) := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := exists_nat_gt (9 * |C| * max A 0 / ε)
    refine eventually_atTop.2 ⟨N, fun n hn t ht => ?_⟩
    have hn' : (N : ℝ) ≤ n := Nat.cast_le.2 hn
    have h2 : (0 : ℝ) < (n : ℝ) + 2 := by positivity
    rw [div_lt_iff₀ hε] at hN
    have hK : 0 ≤ 9 * |C| * max A 0 := by positivity
    rw [Real.dist_eq, ← integral_sub (hHint t ht) (hcut n t ht)]
    calc |∫ x, (quadraticStress v θ t x - radialCutoff ((n : ℝ) + 1) x * quadraticStress v θ t x)|
        ≤ ∫ x, 9 * (|C| * ((n : ℝ) + 2)⁻¹) * ‖v t x‖ ^ 2 := by
          rw [← Real.norm_eq_abs]
          exact norm_integral_le_of_norm_le ((hsq t ht).const_mul _)
            (ae_of_all _ fun x => by rw [Real.norm_eq_abs]; exact htail n t ht x)
      _ = 9 * (|C| * ((n : ℝ) + 2)⁻¹) * ∫ x, ‖v t x‖ ^ 2 := integral_const_mul _ _
      _ ≤ 9 * (|C| * ((n : ℝ) + 2)⁻¹) * max A 0 :=
          mul_le_mul_of_nonneg_left (hsqle t ht) (by positivity)
      _ = (9 * |C| * max A 0) / ((n : ℝ) + 2) := by ring
      _ < ε := by
          rw [div_lt_iff₀ h2]
          nlinarith [mul_le_mul_of_nonneg_left hn' hε.le]
  show ContinuousOn (fun t => ∫ x, quadraticStress v θ t x) (Icc 0 T)
  exact hU.continuousOn (Frequently.of_forall hGn)

theorem forcedPressureContinuity : ForcedPressureContinuityStatement := by
  intro T v q F hv hE ϕ hϕ hc
  rcases le_or_gt T 0 with hT | hT
  · refine Set.Subsingleton.continuousOn ?_ _
    intro a ha b hb
    have h1 : a = 0 := le_antisymm (ha.2.trans hT) ha.1
    have h2 : b = 0 := le_antisymm (hb.2.trans hT) hb.1
    rw [h1, h2]
  have hdiv := contDiff_divergence_field hϕ
  have hdivc := hasCompactSupport_divergence_field hc
  have hθ : ContDiff ℝ ∞ (FundSol.potential (divergenceAt ϕ)) :=
    FundSol.contDiff_potential hdiv hdivc
  obtain ⟨C, hC⟩ := FundSol.potential_decay hdiv hdivc
  obtain ⟨A, hA⟩ := hE
  exact (continuousOn_integral_inner_gradient hT hv.smooth_pressure hϕ.continuous hc).sub
    (continuousOn_stressPairing_self hv.smooth_velocity.continuousOn hA hθ
      (fun x => hC 2 (by norm_num) x))

end Breakdown
