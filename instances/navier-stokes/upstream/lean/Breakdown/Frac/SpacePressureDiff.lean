import Breakdown.Frac.StSpace
import Breakdown.Uniqueness.FundSolDecay
import Breakdown.Uniqueness.CutoffBounds

open scoped ContDiff ENNReal
open MeasureTheory Set Real

noncomputable section

namespace Breakdown

private theorem slice_contDiff_of_contDiffOn {T : ℝ} {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f : ℝ → Space → E}
    (hf : ContDiffOn ℝ ∞ (fun z : ℝ × Space => f z.1 z.2) (Icc 0 T ×ˢ univ)) {t : ℝ}
    (ht : t ∈ Icc 0 T) : ContDiff ℝ ∞ (f t) := by
  have hpair : ContDiff ℝ ∞ (fun x : Space => (t, x)) := contDiff_const.prodMk contDiff_id
  exact hf.comp_contDiff hpair (fun x => mk_mem_prod ht (mem_univ x))

private def pairStress (a b : Space → Space) (θ : Space → ℝ) (x : Space) : ℝ :=
  ∑ i, ∑ j, a x i * b x j * FundSol.secondPartial θ i j x

private lemma contDiff_divergenceAt_field {ψ : Space → Space} (hψ : ContDiff ℝ ∞ ψ) :
    ContDiff ℝ ∞ (divergenceAt ψ) := by
  have hd : ContDiff ℝ ∞ (fderiv ℝ ψ) := hψ.fderiv_right (m := ∞) le_rfl
  have e : divergenceAt ψ = fun x => ∑ i : Fin 3,
      (EuclideanSpace.proj i : Space →L[ℝ] ℝ) (fderiv ℝ ψ x (unitVector i)) := by
    funext x
    simp [divergenceAt]
  rw [e]
  exact ContDiff.sum fun i _ => (EuclideanSpace.proj i : Space →L[ℝ] ℝ).contDiff.comp
    (hd.clm_apply contDiff_const)

private lemma hasCompactSupport_divergenceAt_field {ψ : Space → Space}
    (hc : HasCompactSupport ψ) : HasCompactSupport (divergenceAt ψ) := by
  show HasCompactSupport
    ((fun A : Space →L[ℝ] Space => ∑ i : Fin 3, A (unitVector i) i) ∘ fderiv ℝ ψ)
  exact (hc.fderiv (𝕜 := ℝ)).comp_left (by simp)

private lemma continuous_gradientAt_field {f : Space → ℝ} (hf : ContDiff ℝ ∞ f) :
    Continuous (gradientAt f) := by
  have hd : Continuous (fderiv ℝ f) := hf.continuous_fderiv (by simp)
  show Continuous (fun x => ∑ i : Fin 3, fderiv ℝ f x (unitVector i) • unitVector i)
  exact continuous_finsetSum _ fun i _ => (hd.clm_apply continuous_const).smul continuous_const

private lemma integrable_inner_gradientAt {f : Space → ℝ} (hf : ContDiff ℝ ∞ f)
    {ϕ : Space → Space} (hϕ : Continuous ϕ) (hc : HasCompactSupport ϕ) :
    Integrable (fun x => inner ℝ (gradientAt f x) (ϕ x)) := by
  refine ((continuous_gradientAt_field hf).inner hϕ).integrable_of_hasCompactSupport ?_
  refine hc.mono fun x hx => ?_
  rw [Function.mem_support] at hx ⊢
  intro h
  apply hx
  simp [h]

private lemma abs_secondPartial_potential_le {g : Space → ℝ} (hg : ContDiff ℝ ∞ g)
    (hc : HasCompactSupport g) :
    ∃ K : ℝ, ∀ i j x, |FundSol.secondPartial (FundSol.potential g) i j x| ≤ K := by
  obtain ⟨C, hC⟩ := FundSol.potential_decay hg hc
  refine ⟨|C|, fun i j x => ?_⟩
  have h1 : |FundSol.secondPartial (FundSol.potential g) i j x| ≤
      ‖iteratedFDeriv ℝ 2 (FundSol.potential g) x‖ := by
    unfold FundSol.secondPartial
    rw [← Real.norm_eq_abs]
    refine (ContinuousMultilinearMap.le_opNorm _ _).trans ?_
    simp [unitVector, Fin.prod_univ_two]
  have h2 := hC 2 (by norm_num) x
  have h0 : 0 ≤ (1 + ‖x‖)⁻¹ := by positivity
  have h01 : (1 + ‖x‖)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith [norm_nonneg x])
  have h3 : (1 + ‖x‖)⁻¹ ^ (2 + 1) ≤ 1 := pow_le_one₀ h0 h01
  calc |FundSol.secondPartial (FundSol.potential g) i j x|
      ≤ C * (1 + ‖x‖)⁻¹ ^ (2 + 1) := h1.trans h2
    _ ≤ |C| * (1 + ‖x‖)⁻¹ ^ (2 + 1) :=
        mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)
    _ ≤ |C| * 1 := mul_le_mul_of_nonneg_left h3 (abs_nonneg C)
    _ = |C| := mul_one _

private lemma integrable_sq_of_lintegral_le {a : Space → Space} (ha : Continuous a) {A : ℝ}
    (hA : ∫⁻ x, ENNReal.ofReal (‖a x‖ ^ 2) ≤ ENNReal.ofReal A) :
    Integrable (fun x => ‖a x‖ ^ 2) :=
  ⟨(ha.norm.pow 2).aestronglyMeasurable,
    (hasFiniteIntegral_iff_ofReal (ae_of_all _ fun x => by positivity)).2
      (hA.trans_lt ENNReal.ofReal_lt_top)⟩

private lemma integrable_sq_sub_field {a b : Space → Space} (ha : Continuous a) (hb : Continuous b)
    (ha2 : Integrable (fun x => ‖a x‖ ^ 2)) (hb2 : Integrable (fun x => ‖b x‖ ^ 2)) :
    Integrable (fun x => ‖(a - b) x‖ ^ 2) := by
  have hs : Integrable (fun x => ‖a x‖ ^ 2 + ‖b x‖ ^ 2) := ha2.add hb2
  refine (hs.const_mul 2).mono' ((ha.sub hb).norm.pow 2).aestronglyMeasurable
    (ae_of_all _ fun x => ?_)
  show ‖‖a x - b x‖ ^ 2‖ ≤ 2 * (‖a x‖ ^ 2 + ‖b x‖ ^ 2)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have h := norm_sub_le (a x) (b x)
  have h2 : ‖a x - b x‖ ^ 2 ≤ (‖a x‖ + ‖b x‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h 2
  nlinarith [sq_nonneg (‖a x‖ - ‖b x‖)]

private lemma integrable_pairStress {a b : Space → Space} {θ : Space → ℝ}
    (ha : Continuous a) (hb : Continuous b)
    (ha2 : Integrable (fun x => ‖a x‖ ^ 2)) (hb2 : Integrable (fun x => ‖b x‖ ^ 2))
    (hm : ∀ i j, Continuous (FundSol.secondPartial θ i j)) {K : ℝ}
    (hK : ∀ i j x, |FundSol.secondPartial θ i j x| ≤ K) :
    Integrable (pairStress a b θ) := by
  have hcont : Continuous (pairStress a b θ) := by
    unfold pairStress
    refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_
    exact (((EuclideanSpace.proj i : Space →L[ℝ] ℝ).continuous.comp ha).mul
      ((EuclideanSpace.proj j : Space →L[ℝ] ℝ).continuous.comp hb)).mul (hm i j)
  have hs : Integrable (fun x => ‖a x‖ ^ 2 + ‖b x‖ ^ 2) := ha2.add hb2
  refine (hs.const_mul (9 * K)).mono' hcont.aestronglyMeasurable (ae_of_all _ fun x => ?_)
  show ‖pairStress a b θ x‖ ≤ 9 * K * (‖a x‖ ^ 2 + ‖b x‖ ^ 2)
  rw [Real.norm_eq_abs]
  unfold pairStress
  have hai : ∀ i, |a x i| ≤ ‖a x‖ := fun i => by
    rw [← Real.norm_eq_abs]
    exact PiLp.norm_apply_le (a x) i
  have hbj : ∀ j, |b x j| ≤ ‖b x‖ := fun j => by
    rw [← Real.norm_eq_abs]
    exact PiLp.norm_apply_le (b x) j
  have hab : ‖a x‖ * ‖b x‖ ≤ ‖a x‖ ^ 2 + ‖b x‖ ^ 2 := by
    nlinarith [norm_nonneg (a x), norm_nonneg (b x)]
  have ht : ∀ i j, |a x i * b x j * FundSol.secondPartial θ i j x| ≤
      K * (‖a x‖ ^ 2 + ‖b x‖ ^ 2) := fun i j => by
    have hK0 : 0 ≤ K := (abs_nonneg _).trans (hK i j x)
    rw [abs_mul, abs_mul]
    calc |a x i| * |b x j| * |FundSol.secondPartial θ i j x| ≤ ‖a x‖ * ‖b x‖ * K := by
          gcongr
          · exact hai i
          · exact hbj j
          · exact hK i j x
      _ ≤ (‖a x‖ ^ 2 + ‖b x‖ ^ 2) * K := mul_le_mul_of_nonneg_right hab hK0
      _ = K * (‖a x‖ ^ 2 + ‖b x‖ ^ 2) := by ring
  calc |∑ i, ∑ j, a x i * b x j * FundSol.secondPartial θ i j x|
      ≤ ∑ i, ∑ j, |a x i * b x j * FundSol.secondPartial θ i j x| :=
        (Finset.abs_sum_le_sum_abs _ _).trans
          (Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ _i : Fin 3, ∑ _j : Fin 3, K * (‖a x‖ ^ 2 + ‖b x‖ ^ 2) :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ht i j
    _ = 9 * K * (‖a x‖ ^ 2 + ‖b x‖ ^ 2) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

private lemma pairStress_self_sub (a b : Space → Space) (θ : Space → ℝ) (x : Space) :
    pairStress a a θ x - pairStress b b θ x =
      pairStress (a - b) (a - b) θ x + pairStress b (a - b) θ x +
        pairStress (a - b) b θ x := by
  unfold pairStress
  simp only [Pi.sub_apply, PiLp.sub_apply, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

private lemma stressPairing_self_sub {a b : Space → Space} {θ : Space → ℝ}
    (ha : Continuous a) (hb : Continuous b)
    (ha2 : Integrable (fun x => ‖a x‖ ^ 2)) (hb2 : Integrable (fun x => ‖b x‖ ^ 2))
    (hm : ∀ i j, Continuous (FundSol.secondPartial θ i j)) {K : ℝ}
    (hK : ∀ i j x, |FundSol.secondPartial θ i j x| ≤ K) :
    stressPairing a a θ - stressPairing b b θ =
      stressPairing (a - b) (a - b) θ + stressPairing b (a - b) θ + stressPairing (a - b) b θ := by
  have hd : Continuous (a - b) := ha.sub hb
  have hd2 : Integrable (fun x => ‖(a - b) x‖ ^ 2) := integrable_sq_sub_field ha hb ha2 hb2
  have iaa := integrable_pairStress ha ha ha2 ha2 hm hK
  have ibb := integrable_pairStress hb hb hb2 hb2 hm hK
  have idd := integrable_pairStress hd hd hd2 hd2 hm hK
  have ibd := integrable_pairStress hb hd hb2 hd2 hm hK
  have idb := integrable_pairStress hd hb hd2 hb2 hm hK
  show (∫ x, pairStress a a θ x) - (∫ x, pairStress b b θ x) =
    (∫ x, pairStress (a - b) (a - b) θ x) + (∫ x, pairStress b (a - b) θ x) +
      (∫ x, pairStress (a - b) b θ x)
  rw [← integral_sub iaa ibb, ← integral_add idd ibd, ← integral_add (f := fun x => pairStress (a - b) (a - b) θ x + pairStress b (a - b) θ x)
    (idd.add ibd) idb]
  exact integral_congr_ae (ae_of_all _ fun x => pairStress_self_sub a b θ x)

theorem forcedPressureDifference_of (h1 : ForcedPressureIdentityStatement) :
    ForcedPressureDifferenceStatement := by
  intro T u v p q F G hu hv hEu hEv r hr t ht
  have hti : t ∈ Icc 0 T := Ioo_subset_Icc_self ht
  have hvc : ContDiff ℝ ∞ (v t) := slice_contDiff_of_contDiffOn hv.smooth_velocity hti
  have huc : ContDiff ℝ ∞ (u t) := slice_contDiff_of_contDiffOn hu.smooth_velocity hti
  have hqc : ContDiff ℝ ∞ (q t) := slice_contDiff_of_contDiffOn hv.smooth_pressure hti
  have hpc : ContDiff ℝ ∞ (p t) := slice_contDiff_of_contDiffOn hu.smooth_pressure hti
  have hϕ : ContDiff ℝ ∞ (fun x => cutoffPow r x • (v t x - u t x)) :=
    ((contDiff_radialCutoff hr).pow 4).smul (hvc.sub huc)
  have hϕc : HasCompactSupport (fun x => cutoffPow r x • (v t x - u t x)) :=
    HasCompactSupport.intro (isCompact_closedBall (0 : Space) (2 * r)) fun x hx => by
      have h2 : 2 * r ≤ ‖x‖ := by
        simp only [Metric.mem_closedBall, dist_zero_right, not_le] at hx
        exact hx.le
      simp [cutoffPow, radialCutoff_eq_zero hr h2]
  have hdiv : divergenceAt (fun x => cutoffPow r x • (v t x - u t x)) =
      cutoffSource r (v t - u t) := rfl
  have hq0 := h1 T v q G hv hEv t ht _ hϕ hϕc
  have hp0 := h1 T u p F hu hEu t ht _ hϕ hϕc
  unfold pressureDefect at hq0 hp0
  rw [sub_eq_zero, hdiv] at hq0 hp0
  have hIq := integrable_inner_gradientAt hqc hϕ.continuous hϕc
  have hIp := integrable_inner_gradientAt hpc hϕ.continuous hϕc
  have hL : (∫ x, inner ℝ (gradientAt (q t) x - gradientAt (p t) x)
        (cutoffPow r x • (v t x - u t x))) =
      (∫ x, inner ℝ (gradientAt (q t) x) (cutoffPow r x • (v t x - u t x))) -
        ∫ x, inner ℝ (gradientAt (p t) x) (cutoffPow r x • (v t x - u t x)) := by
    rw [← integral_sub hIq hIp]
    exact integral_congr_ae (ae_of_all _ fun x => inner_sub_left _ _ _)
  rw [hL, hq0, hp0]
  have hsc : ContDiff ℝ ∞ (cutoffSource r (v t - u t)) := contDiff_divergenceAt_field hϕ
  have hscc : HasCompactSupport (cutoffSource r (v t - u t)) :=
    hasCompactSupport_divergenceAt_field hϕc
  have hθ := FundSol.contDiff_potential hsc hscc
  obtain ⟨K, hK⟩ := abs_secondPartial_potential_le hsc hscc
  have hm : ∀ i j, Continuous
      (FundSol.secondPartial (FundSol.potential (cutoffSource r (v t - u t))) i j) := fun i j => by
    unfold FundSol.secondPartial
    exact (hθ.continuous_iteratedFDeriv (m := 2) (by norm_cast)).eval_const _
  obtain ⟨Av, hAv⟩ := hEv
  obtain ⟨Au, hAu⟩ := hEu
  exact stressPairing_self_sub hvc.continuous huc.continuous
    (integrable_sq_of_lintegral_le hvc.continuous (hAv t hti))
    (integrable_sq_of_lintegral_le huc.continuous (hAu t hti)) hm hK

end Breakdown
