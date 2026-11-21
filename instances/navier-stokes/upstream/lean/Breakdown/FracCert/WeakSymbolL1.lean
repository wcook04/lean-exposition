import Breakdown.FracCert.StWeakRegular
import Breakdown.Uniqueness.RegEmbed
import Breakdown.Uniqueness.RegIdentifyAuxDivFree
import Breakdown.FreqTr.Realization
import Breakdown.Frac.OpIntegrable

open MeasureTheory Set Real Filter Metric
open scoped ENNReal ContDiff FourierTransform Topology

noncomputable section

namespace Breakdown.FracCert.MomentsInternal

open Breakdown.Freq Breakdown.SmoothFlow Breakdown.SmoothFlow.Internal.RegIdentifyDivFree
  Breakdown.SmoothFlow.Internal.RegEmbed

theorem aesm_symbolX (x : X) : AEStronglyMeasurable (symbolX x) volume := by
  unfold symbolX
  exact (by fun_prop : Measurable fun ξ : Space => ((2 * π * ‖ξ‖)⁻¹ : ℝ)).aestronglyMeasurable.smul
    (Lp.aestronglyMeasurable _)

theorem symbolX_zero (x : X) : symbolX x 0 = 0 := by simp [symbolX]

theorem integrable_weight_sq {f : Space → CSpace} (hm : AEStronglyMeasurable f volume) {k : ℕ}
    (hk : homNormSq k f < ⊤) : Integrable (fun ξ => ‖ξ‖ ^ (2 * k) * ‖f ξ‖ ^ 2) := by
  refine ⟨(by fun_prop : Continuous fun ξ : Space => ‖ξ‖ ^ (2 * k)).aestronglyMeasurable.mul
    (hm.norm.pow 2), ?_⟩
  unfold HasFiniteIntegral
  refine lt_of_le_of_lt (le_of_eq ?_) hk
  unfold homNormSq
  refine lintegral_congr fun ξ => ?_
  rw [Real.enorm_eq_ofReal (by positivity), ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm, ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]

theorem le_half_inv_add (t c : ℝ) (ht : 0 < t) : c ≤ (t⁻¹ + t * c ^ 2) / 2 := by
  have e : t⁻¹ * t = 1 := inv_mul_cancel₀ ht.ne'
  have h : t⁻¹ + t * c ^ 2 - 2 * c = t⁻¹ * (t * c - 1) ^ 2 := by
    linear_combination (2 * c - t * c ^ 2) * e
  have : 0 ≤ t⁻¹ * (t * c - 1) ^ 2 := by positivity
  linarith

theorem weighted_moment {f : Space → CSpace} (hm : AEStronglyMeasurable f volume) (h0 : f 0 = 0)
    (hf : ∀ k : ℕ, 1 ≤ k → homNormSq k f < ⊤) (j : ℕ) :
    Integrable (fun ξ => (1 + ‖ξ‖) ^ j * ‖f ξ‖) := by
  have hmeas : AEStronglyMeasurable (fun ξ => (1 + ‖ξ‖) ^ j * ‖f ξ‖) volume :=
    (by fun_prop : Continuous fun ξ : Space => (1 + ‖ξ‖) ^ j).aestronglyMeasurable.mul hm.norm
  have i1 := integrable_weight_sq hm (hf 1 le_rfl)
  have i2 := integrable_weight_sq hm (hf (j + 2) (by omega))
  have hin : IntegrableOn (fun ξ => (1 + ‖ξ‖) ^ j * ‖f ξ‖) (ball (0 : Space) 1) := by
    have hb := FracInternal.integrableOn_ball_norm_rpow (s := -2) (by norm_num)
    have hg : IntegrableOn (fun ξ : Space =>
        2 ^ j * ((‖ξ‖ ^ (-2 : ℝ) + ‖ξ‖ ^ (2 * 1) * ‖f ξ‖ ^ 2) / 2)) (ball 0 1) :=
      ((hb.add i1.integrableOn).div_const 2).const_mul _
    refine hg.mono' hmeas.restrict (ae_restrict_of_forall_mem measurableSet_ball fun ξ hξ => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have hr1 : ‖ξ‖ < 1 := by simpa using hξ
    have hj : (1 + ‖ξ‖) ^ j ≤ 2 ^ j := pow_le_pow_left₀ (by positivity) (by linarith) j
    rcases eq_or_ne ξ 0 with rfl | hne
    · simp only [h0, norm_zero, mul_zero]
      positivity
    have hr : 0 < ‖ξ‖ := norm_pos_iff.2 hne
    have key := le_half_inv_add (‖ξ‖ ^ 2) ‖f ξ‖ (by positivity)
    have e : ‖ξ‖ ^ (-2 : ℝ) = (‖ξ‖ ^ 2)⁻¹ := by
      rw [show (-2 : ℝ) = -((2 : ℕ) : ℝ) by norm_num, Real.rpow_neg hr.le, Real.rpow_natCast]
    rw [e, show 2 * 1 = 2 from rfl]
    calc (1 + ‖ξ‖) ^ j * ‖f ξ‖ ≤ 2 ^ j * ‖f ξ‖ := mul_le_mul_of_nonneg_right hj (norm_nonneg _)
      _ ≤ _ := mul_le_mul_of_nonneg_left key (by positivity)
  have hout : IntegrableOn (fun ξ => (1 + ‖ξ‖) ^ j * ‖f ξ‖) (ball (0 : Space) 1)ᶜ := by
    have hb := FracInternal.integrableOn_compl_ball_norm_rpow (s := -4) (by norm_num)
    have hg : IntegrableOn (fun ξ : Space =>
        2 ^ j * ((‖ξ‖ ^ (-4 : ℝ) + ‖ξ‖ ^ (2 * (j + 2)) * ‖f ξ‖ ^ 2) / 2)) (ball 0 1)ᶜ :=
      ((hb.add i2.integrableOn).div_const 2).const_mul _
    refine hg.mono' hmeas.restrict
      (ae_restrict_of_forall_mem measurableSet_ball.compl fun ξ hξ => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have hr1 : 1 ≤ ‖ξ‖ := by simpa using hξ
    have hr : 0 < ‖ξ‖ := by linarith
    have hj : (1 + ‖ξ‖) ^ j ≤ 2 ^ j * ‖ξ‖ ^ j := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ (by positivity) (by linarith) j
    have key := le_half_inv_add (‖ξ‖ ^ 4) (‖ξ‖ ^ j * ‖f ξ‖) (by positivity)
    have e : ‖ξ‖ ^ (-4 : ℝ) = (‖ξ‖ ^ 4)⁻¹ := by
      rw [show (-4 : ℝ) = -((4 : ℕ) : ℝ) by norm_num, Real.rpow_neg hr.le, Real.rpow_natCast]
    have e2 : ‖ξ‖ ^ (2 * (j + 2)) * ‖f ξ‖ ^ 2 = ‖ξ‖ ^ 4 * (‖ξ‖ ^ j * ‖f ξ‖) ^ 2 := by ring
    rw [e, e2]
    calc (1 + ‖ξ‖) ^ j * ‖f ξ‖ ≤ 2 ^ j * ‖ξ‖ ^ j * ‖f ξ‖ :=
          mul_le_mul_of_nonneg_right hj (norm_nonneg _)
      _ = 2 ^ j * (‖ξ‖ ^ j * ‖f ξ‖) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left key (by positivity)
  have := hin.union hout
  rwa [union_compl_self, integrableOn_univ] at this

def evenPart (f : Space → CSpace) (ξ : Space) : CSpace := (1 / 2 : ℝ) • (f ξ + conjVec (f (-ξ)))

def solRep (f : Space → CSpace) (ξ : Space) : CSpace := divFreeC ξ (evenPart f ξ)

theorem solRep_solenoidal (f : Space → CSpace) : IsSolenoidalSymbol (solRep f) := by
  intro ξ
  constructor
  · rcases eq_or_ne ξ 0 with rfl | hξ
    · simp
    · rw [← inner_freqVec_eq]
      exact inner_freqVec_divFreeC hξ _
  · have hk : evenPart f (-ξ) = conjVec (evenPart f ξ) := by
      simp only [evenPart, neg_neg, map_smul, map_add, conjVec_conjVec]
      rw [add_comm]
    have h2 := congrArg conjVec (conjVec_divFreeC_neg ξ (evenPart f ξ))
    rw [conjVec_conjVec] at h2
    simp only [solRep, hk, h2]

theorem solRep_ae (x : X) : solRep (symbolX x) =ᵐ[volume] symbolX x := by
  have hx := (Internal.H1Consistency.mem_sig_iff (x : L2C)).1 x.2
  have hr := Internal.H1Consistency.reflConj_ae fieldOpRealized_holds (x : L2C)
  rw [hx.1] at hr
  have hl := Internal.H1Consistency.longitudinal_ae fieldOpRealized_holds (x : L2C)
  rw [hx.2] at hl
  filter_upwards [hr, hl, Lp.coeFn_zero CSpace 2 (volume : Measure Space)] with ξ a b c
  have e1 : evenPart (symbolX x) ξ = symbolX x ξ := by
    simp only [evenPart, symbolX, norm_neg, map_smul]
    rw [← a]
    module
  have e2 : divFreeC ξ (symbolX x ξ) = symbolX x ξ := by
    rw [divFreeC_eq_sub, symbolX, map_smul, ← b, c, Pi.zero_apply, smul_zero, sub_zero]
  show divFreeC ξ (evenPart _ ξ) = _
  rw [e1, e2]


def cutSet (n : ℕ) : Set Space := {ξ | 1 / ((n : ℝ) + 1) < ‖ξ‖}

theorem measurableSet_cutSet (n : ℕ) : MeasurableSet (cutSet n) :=
  measurableSet_lt measurable_const measurable_norm

theorem eventually_mem_cutSet {ξ : Space} (hξ : ξ ≠ 0) : ∀ᶠ n in atTop, ξ ∈ cutSet n :=
  tendsto_one_div_add_atTop_nhds_zero_nat.eventually (gt_mem_nhds (norm_pos_iff.2 hξ))

def cutRep (f : Space → CSpace) (n : ℕ) : Space → CSpace := (cutSet n).indicator (solRep f)

theorem cutRep_solenoidal (f : Space → CSpace) (n : ℕ) : IsSolenoidalSymbol (cutRep f n) := by
  intro ξ
  by_cases h : ξ ∈ cutSet n
  · have h' : -ξ ∈ cutSet n := by simpa [cutSet] using h
    simp only [cutRep, indicator_of_mem h, indicator_of_mem h']
    exact solRep_solenoidal f ξ
  · have h' : -ξ ∉ cutSet n := by simpa [cutSet] using h
    simp [cutRep, h, h']

theorem aesm_solRep (x : X) : AEStronglyMeasurable (solRep (symbolX x)) volume :=
  (aesm_symbolX x).congr (solRep_ae x).symm

theorem aesm_cutRep (x : X) (n : ℕ) : AEStronglyMeasurable (cutRep (symbolX x) n) volume :=
  (aesm_solRep x).indicator (measurableSet_cutSet n)

theorem weight_le_of_mem {n m : ℕ} {ξ : Space} (h : ξ ∈ cutSet n) :
    hsWeight m ξ ≤ (((n : ℝ) + 1) ^ 2 + 1) ^ m * ((n : ℝ) + 1) ^ 2 * ‖ξ‖ ^ (2 * (m + 1)) := by
  have ha : 0 < (n : ℝ) + 1 := by positivity
  have hr : 1 / ((n : ℝ) + 1) < ‖ξ‖ := h
  have h0 : 1 < ‖ξ‖ * ((n : ℝ) + 1) := (div_lt_iff₀ ha).1 hr
  have h1 : 1 ≤ ((n : ℝ) + 1) ^ 2 * ‖ξ‖ ^ 2 := by nlinarith
  have h2 : 1 + ‖ξ‖ ^ 2 ≤ (((n : ℝ) + 1) ^ 2 + 1) * ‖ξ‖ ^ 2 := by nlinarith
  unfold hsWeight
  calc (1 + ‖ξ‖ ^ 2) ^ m ≤ ((((n : ℝ) + 1) ^ 2 + 1) * ‖ξ‖ ^ 2) ^ m :=
        pow_le_pow_left₀ (by positivity) h2 m
    _ = (((n : ℝ) + 1) ^ 2 + 1) ^ m * ‖ξ‖ ^ (2 * m) * 1 := by rw [mul_pow, ← pow_mul, mul_one]
    _ ≤ (((n : ℝ) + 1) ^ 2 + 1) ^ m * ‖ξ‖ ^ (2 * m) * (((n : ℝ) + 1) ^ 2 * ‖ξ‖ ^ 2) := by gcongr
    _ = _ := by ring

theorem homNormSq_solRep (x : X) (k : ℕ) : homNormSq k (solRep (symbolX x)) = homNormSq k (symbolX x) := by
  unfold homNormSq
  refine lintegral_congr_ae ?_
  filter_upwards [solRep_ae x] with ξ h
  rw [h]

theorem hsNormSq_cutRep (x : X) (hx : HasAllMoments x) (n m : ℕ) :
    hsNormSq m (cutRep (symbolX x) n) < ⊤ := by
  have hk : homNormSq (m + 1) (solRep (symbolX x)) < ⊤ := by
    rw [homNormSq_solRep]
    exact hx (m + 1) (by omega)
  calc hsNormSq m (cutRep (symbolX x) n) ≤ ∫⁻ ξ, ENNReal.ofReal
        ((((n : ℝ) + 1) ^ 2 + 1) ^ m * ((n : ℝ) + 1) ^ 2) *
        (ENNReal.ofReal (‖ξ‖ ^ (2 * (m + 1))) * ‖solRep (symbolX x) ξ‖ₑ ^ 2) := by
        refine lintegral_mono fun ξ => ?_
        by_cases h : ξ ∈ cutSet n
        · rw [cutRep, indicator_of_mem h, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
          gcongr ?_ * _
          exact ENNReal.ofReal_le_ofReal (weight_le_of_mem h)
        · simp [cutRep, h]
    _ = ENNReal.ofReal ((((n : ℝ) + 1) ^ 2 + 1) ^ m * ((n : ℝ) + 1) ^ 2) *
          homNormSq (m + 1) (solRep (symbolX x)) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hk

theorem embed_cut (x : X) (hx : HasAllMoments x) (n : ℕ) :
    ((embedX (physField (cutRep (symbolX x) n)) : X) : Space → CSpace) =ᵐ[volume]
      (cutSet n).indicator ((x : L2C) : Space → CSpace) := by
  filter_upwards [coe_embedX_physField fieldOpRealized_holds (aesm_cutRep x n)
      (cutRep_solenoidal _ n) (hsNormSq_cutRep x hx n), solRep_ae x,
      Internal.H1Consistency.ae_ne_zero] with ξ a b c
  rw [a]
  by_cases h : ξ ∈ cutSet n
  · rw [cutRep, indicator_of_mem h, indicator_of_mem h, b, symbolX, Complex.coe_smul, smul_smul,
      mul_inv_cancel₀ (mul_ne_zero (mul_ne_zero two_ne_zero pi_ne_zero) (norm_ne_zero_iff.2 c)),
      one_smul]
  · simp [cutRep, h]

theorem tendsto_embed_cut (x : X) (hx : HasAllMoments x) :
    Tendsto (fun n => embedX (physField (cutRep (symbolX x) n))) atTop (𝓝 x) := by
  refine tendsto_subtype_rng.2 ?_
  rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm']
  have e : ∀ n : ℕ, eLpNorm (⇑((embedX (physField (cutRep (symbolX x) n)) : X) : L2C) - ⇑(x : L2C))
      2 volume = (∫⁻ ξ, ‖(cutSet n)ᶜ.indicator ((x : L2C) : Space → CSpace) ξ‖ₑ ^ (2 : ℝ)) ^
        (1 / (2 : ℝ)) := by
    intro n
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top]
    simp only [ENNReal.toReal_ofNat]
    congr 1
    refine lintegral_congr_ae ?_
    filter_upwards [embed_cut x hx n] with ξ a
    rw [Pi.sub_apply, a]
    by_cases h : ξ ∈ cutSet n <;> simp [h]
  simp_rw [e]
  have hfin : ∫⁻ ξ, ‖((x : L2C) : Space → CSpace) ξ‖ₑ ^ (2 : ℝ) ≠ ⊤ := by
    have := (Lp.memLp (x : L2C)).eLpNorm_lt_top
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top] at this
    simp only [ENNReal.toReal_ofNat] at this
    exact ((ENNReal.rpow_lt_top_iff_of_pos (by norm_num)).1 this).ne
  have hlim : Tendsto (fun n : ℕ => ∫⁻ ξ, ‖(cutSet n)ᶜ.indicator ((x : L2C) : Space → CSpace) ξ‖ₑ ^
      (2 : ℝ)) atTop (𝓝 0) := by
    have := tendsto_lintegral_of_dominated_convergence'
      (F := fun (n : ℕ) ξ => ‖(cutSet n)ᶜ.indicator ((x : L2C) : Space → CSpace) ξ‖ₑ ^ (2 : ℝ))
      (f := fun _ => 0) (fun ξ => ‖((x : L2C) : Space → CSpace) ξ‖ₑ ^ (2 : ℝ))
      (fun n => (((Lp.aestronglyMeasurable (x : L2C)).indicator
        (measurableSet_cutSet n).compl).enorm.pow_const _))
      (fun n => ae_of_all _ fun ξ => ENNReal.rpow_le_rpow (enorm_indicator_le_enorm_self _ _) (by norm_num))
      hfin ?_
    · simpa using this
    · filter_upwards [Internal.H1Consistency.ae_ne_zero] with ξ hξ
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_mem_cutSet hξ] with n hn
      simp [hn]
  have := ((ENNReal.continuous_rpow_const (y := 1 / (2 : ℝ))).tendsto 0).comp hlim
  rwa [ENNReal.zero_rpow_of_pos (by norm_num)] at this


theorem integrable_symbolX (x : X) (hx : HasAllMoments x) : Integrable (symbolX x) := by
  have h := weighted_moment (aesm_symbolX x) (symbolX_zero x) hx 0
  simp only [pow_zero, one_mul] at h
  exact (integrable_norm_iff (aesm_symbolX x)).1 h

theorem physField_solRep (x : X) (y : Space) :
    physField (solRep (symbolX x)) y = physField (symbolX x) y := by
  unfold physField
  congr 1
  rw [Real.fourierInv_eq, Real.fourierInv_eq]
  refine integral_congr_ae ?_
  filter_upwards [solRep_ae x] with ξ h
  rw [h]

theorem tendsto_phys_cut (x : X) (hx : HasAllMoments x) (y : Space) :
    Tendsto (fun n => physField (cutRep (symbolX x) n) y) atTop (𝓝 (physField (symbolX x) y)) := by
  rw [← physField_solRep]
  unfold physField
  refine (realVec.continuous.tendsto _).comp ?_
  simp only [Real.fourierInv_eq]
  have hi : Integrable (solRep (symbolX x)) :=
    (integrable_symbolX x hx).congr (solRep_ae x).symm
  refine tendsto_integral_of_dominated_convergence (fun ξ => ‖solRep (symbolX x) ξ‖)
    (fun n => ?_) hi.norm (fun n => ae_of_all _ fun ξ => ?_) ?_
  · exact (Real.continuous_fourierChar.comp (continuous_id.inner continuous_const)).aestronglyMeasurable.smul
      (aesm_cutRep x n)
  · rw [Circle.norm_smul]
    exact norm_indicator_le_norm_self _ _
  · filter_upwards [Internal.H1Consistency.ae_ne_zero] with ξ hξ
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_mem_cutSet hξ] with n hn
    simp [cutRep, hn]

theorem velocity_ae (x : X) (hx : HasAllMoments x) :
    (velocity x : Space → Space) =ᵐ[volume] physField (symbolX x) := by
  have hv : Tendsto (fun n => velocity (embedX (physField (cutRep (symbolX x) n)))) atTop
      (𝓝 (velocity x)) :=
    (velocity.continuous.tendsto x).comp (tendsto_embed_cut x hx)
  obtain ⟨ns, hmono, hns⟩ := (tendstoInMeasure_of_tendsto_Lp hv).exists_seq_tendsto_ae
  have hH : ∀ n, ((velocity (embedX (physField (cutRep (symbolX x) n))) : L6R) : Space → Space)
      =ᵐ[volume] physField (cutRep (symbolX x) n) := fun n =>
    (h1Consistency_holds _ (isH1Field_physField (aesm_cutRep x n) (cutRep_solenoidal _ n)
      (hsNormSq_cutRep x hx n))).2.1
  filter_upwards [hns, ae_all_iff.2 fun i => hH (ns i)] with y a b
  refine tendsto_nhds_unique a ?_
  exact ((tendsto_phys_cut x hx y).comp hmono.tendsto_atTop).congr fun i => (b i).symm

end Breakdown.FracCert.MomentsInternal

namespace Breakdown.FracCert

open MomentsInternal

theorem symbolL1OfMoments : SymbolL1OfMomentsStatement := fun x hx =>
  ⟨fun j => weighted_moment (aesm_symbolX x) (symbolX_zero x) hx j, velocity_ae x hx⟩

end Breakdown.FracCert
