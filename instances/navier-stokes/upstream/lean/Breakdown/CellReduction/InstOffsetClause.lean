import Breakdown.CellReduction.InstanceStatements
import Breakdown.CellReduction.InstMovedParams
import Breakdown.CertCell.CellLayerClosed
import Breakdown.Cert.ExtendedInvariance

open scoped ContDiff ENNReal
open MeasureTheory

noncomputable section

namespace Breakdown

namespace CellReduction

namespace Instantiation

open CertCell CertCell.GivenShape

namespace Internal.OffsetClause

theorem withOrigin_isShapeParams {P : ShapeParams} {g : OriginProfile} (hP : IsShapeParams P)
    (hg : IsOriginProfile g) : IsShapeParams (withOrigin P g) :=
  ⟨hP.chartLength_pos, hP.azimuthOrder_pos, hP.phase, hg⟩

theorem continuous_traceSecond : Continuous (fun A : Space →L[ℝ] Space →L[ℝ] Space => secondDerivTrace A) := by
  unfold secondDerivTrace
  exact continuous_finsetSum _ fun j _ => (continuous_id.clm_apply continuous_const).clm_apply continuous_const

theorem abs_le_coordRadius {k : ℕ} {d : ExtendedCertificateData k} (hs : ∀ j, d.scale j ≠ 0)
    {q : Fin k → ℝ} (hq : q ∈ d.params) (i : Fin k) : |q i| ≤ coordRadius d i := by
  have hq' : (∀ j ∈ d.adjointSet, |q j| ≤ d.radius j) ∧
      ∑ j ∈ d.adjointSetᶜ, (d.scale j * q j) ^ 2 ≤ d.stiffRadius ^ 2 := hq
  unfold coordRadius
  split_ifs with hi
  · exact hq'.1 i hi
  · have hmem : i ∈ d.adjointSetᶜ := Finset.mem_compl.2 hi
    have h1 : (d.scale i * q i) ^ 2 ≤ d.stiffRadius ^ 2 :=
      (Finset.single_le_sum (f := fun j => (d.scale j * q j) ^ 2) (fun j _ => sq_nonneg _) hmem).trans hq'.2
    have h2 : |d.scale i * q i| ≤ |d.stiffRadius| := sq_le_sq.mp h1
    rw [abs_mul] at h2
    rw [le_div_iff₀ (abs_pos.2 (hs i)), mul_comm]
    exact h2

theorem profile_contDiff {k : ℕ} {C : Type} {nE nM : ℕ} {D : CellLayerData k C nE nM}
    {R : ProfileShapeEntry k} (hStep : StepPhaseHolds) (hR : IsProfileShapeEntry D R) (q : Fin k → ℝ) :
    IsShapeParams (R.paramsAt q) ∧ ContDiff ℝ 1 (fun z : ℝ × Space => D.cert.profile q z.1 z.2) ∧
      AEStronglyMeasurable (fun z : ℝ × Space => D.cert.profileSecondDeriv q z.1 z.2) volume := by
  have hmov : IsRadialPhase R.moving :=
    (hStep R.params.chartLength R.stepEdge R.step hR.params_valid.chartLength_pos hR.step_valid).1
  have hPq : IsShapeParams (R.paramsAt q) :=
    movedParamsValid_holds R.params R.moving (phaseRate R.rate q) hR.params_valid hmov
  have s0 := shapeParts_closed.field_smooth _ _ (withOrigin_isShapeParams hPq hR.centreOrigin_valid)
    hR.centre_valid
  have si := fun i => shapeParts_closed.field_smooth _ _
    (withOrigin_isShapeParams hPq (hR.tangentOrigin_valid i)) (hR.tangent_valid i)
  refine ⟨hPq, ?_, ?_⟩
  · rw [hR.profile_eq q]
    simp only [ProfileShapeEntry.field, affineField]
    exact s0.1.add (ContDiff.sum fun i _ => (si i).1.const_smul (q i))
  · rw [hR.profileSecondDeriv_eq q]
    simp only [ProfileShapeEntry.secondDeriv, affineSecondDeriv]
    exact s0.2.2.1.add (Finset.aestronglyMeasurable_fun_sum _ fun i _ => (si i).2.2.1.const_smul (q i))

theorem defect_aestronglyMeasurable {k : ℕ} {C : Type} {nE nM : ℕ} {D : CellLayerData k C nE nM}
    {X : Instance.InstanceData k C nE nM} {SF : GivenShapeEntry k} {R : ProfileShapeEntry k}
    {Pr : PressureShapeEntry k} (hStep : StepPhaseHolds) (hPR : PressureFieldRegularHolds)
    (hSF : IsGivenShapeEntry D X SF) (hR : IsProfileShapeEntry D R) (hP : IsPressureShapeEntry D R Pr)
    (q : Fin k → ℝ) : AEStronglyMeasurable (fun z : ℝ × Space => D.cert.defect q z.1 z.2) volume := by
  obtain ⟨hPq, hW, hH⟩ := profile_contDiff hStep hR q
  have hA : ∀ i, AEStronglyMeasurable (fun z : ℝ × Space => D.cert.actuator i z.1 z.2) volume := fun i => by
    rw [hSF.actuator_eq i]
    exact (shapeParts_closed.field_smooth _ _ (hSF.actuatorParams_valid i)
      (hSF.actuators_valid i).field).1.continuous.aestronglyMeasurable
  have hS : AEStronglyMeasurable (fun z : ℝ × Space => ∑ i, D.cert.multiplier q i • D.cert.actuator i z.1 z.2)
      volume :=
    Finset.aestronglyMeasurable_fun_sum _ fun i _ => (hA i).const_smul (D.cert.multiplier q i)
  have hPc : Continuous (fun z : ℝ × Space => Pr.pressure R q z.1 z.2) := by
    simp only [PressureShapeEntry.pressure]
    exact (hPR _ _ hPq hP.centre_valid).1.add
      (continuous_finsetSum _ fun i _ => continuous_const.mul (hPR _ _ hPq (hP.tangent_valid i)).1)
  have hΦ : Continuous (Function.uncurry fun (σ : ℝ) (y : Space) =>
      Pr.pressure R q σ y - ‖D.cert.profile q σ y‖ ^ 2 / 2) :=
    hPc.sub ((hW.continuous.norm.pow 2).div_const 2)
  have hG : AEStronglyMeasurable (fun z : ℝ × Space => D.cert.pressureGrad q z.1 z.2) volume := by
    have hm := measurable_fderiv_with_param ℝ hΦ
    have e : (fun z : ℝ × Space => D.cert.pressureGrad q z.1 z.2) = fun z =>
        (InnerProductSpace.toDual ℝ Space).symm (fderiv ℝ (fun y => Pr.pressure R q z.1 y -
          ‖D.cert.profile q z.1 y‖ ^ 2 / 2) z.2) := by
      funext z
      rw [hP.pressureGrad_eq]
      rfl
    rw [e]
    exact ((InnerProductSpace.toDual ℝ Space).symm.continuous.measurable.comp hm).aestronglyMeasurable
  have hT : AEStronglyMeasurable (fun z : ℝ × Space => secondDerivTrace (D.cert.profileSecondDeriv q z.1 z.2)) volume :=
    continuous_traceSecond.comp_aestronglyMeasurable hH
  have e : (fun z : ℝ × Space => D.cert.defect q z.1 z.2) = fun z =>
      Cert.Internal.ExtendedInvariance.smoothPart (D.cert.period q) (D.cert.profile q) z.1 z.2
        - secondDerivTrace (D.cert.profileSecondDeriv q z.1 z.2)
        + (∑ i, D.cert.multiplier q i • D.cert.actuator i z.1 z.2) + D.cert.pressureGrad q z.1 z.2 := by
    funext z
    simp only [ExtendedCertificateData.defect, weakDefectField, Cert.Internal.ExtendedInvariance.smoothPart]
    abel
  rw [e]
  exact (((Cert.Internal.ExtendedInvariance.continuous_smoothPart _ hW).aestronglyMeasurable.sub hT).add hS).add hG

theorem periodNorm_le_of_le {F : ℝ → Space → Space} {a : ℝ} (ha0 : 0 ≤ a)
    (h : periodLIntegral (fun σ y => ‖F σ y‖ ^ 2) ≤ ENNReal.ofReal (a ^ 2)) : periodNorm F ≤ a := by
  unfold periodNorm
  calc Real.sqrt (periodLIntegral (fun σ y => ‖F σ y‖ ^ 2)).toReal
        ≤ Real.sqrt (ENNReal.ofReal (a ^ 2)).toReal :=
          Real.sqrt_le_sqrt (ENNReal.toReal_mono ENNReal.ofReal_ne_top h)
    _ = a := by rw [ENNReal.toReal_ofReal (sq_nonneg a), Real.sqrt_sq ha0]

theorem pairing_sub_ball_abs_le {F M : ℝ → Space → Space} {r a b : ℝ}
    (hF : AEStronglyMeasurable (fun z : ℝ × Space => F z.1 z.2) volume)
    (hM : AEStronglyMeasurable (fun z : ℝ × Space => M z.1 z.2) volume)
    (hF2 : periodLIntegral (fun σ y => ‖F σ y‖ ^ 2) < ⊤)
    (hM2 : periodLIntegral (fun σ y => ‖M σ y‖ ^ 2) < ⊤)
    (ha : periodLIntegral (fun σ y => if r < ‖y‖ then ‖F σ y‖ ^ 2 else 0) ≤ ENNReal.ofReal (a ^ 2))
    (hb : periodLIntegral (fun σ y => if r < ‖y‖ then ‖M σ y‖ ^ 2 else 0) ≤ ENNReal.ofReal (b ^ 2))
    (ha0 : 0 ≤ a) (hb0 : 0 ≤ b) :
    |periodPairing F M - ballPairing r F M| ≤ a * b := by
  set F' : ℝ → Space → Space := fun σ y => if r < ‖y‖ then F σ y else 0 with hF'
  set M' : ℝ → Space → Space := fun σ y => if r < ‖y‖ then M σ y else 0 with hM'
  have hT : MeasurableSet {z : ℝ × Space | r < ‖z.2‖} :=
    measurableSet_lt measurable_const measurable_snd.norm
  have hB : MeasurableSet {z : ℝ × Space | ‖z.2‖ ≤ r} :=
    measurableSet_le measurable_snd.norm measurable_const
  have hF'm : AEStronglyMeasurable (fun z : ℝ × Space => F' z.1 z.2) volume := by
    have e : (fun z : ℝ × Space => F' z.1 z.2) =
        {z : ℝ × Space | r < ‖z.2‖}.indicator (fun z => F z.1 z.2) := by
      funext z
      simp only [hF', Set.indicator_apply, Set.mem_ofPred_eq]
    rw [e]
    exact hF.indicator hT
  have hM'm : AEStronglyMeasurable (fun z : ℝ × Space => M' z.1 z.2) volume := by
    have e : (fun z : ℝ × Space => M' z.1 z.2) =
        {z : ℝ × Space | r < ‖z.2‖}.indicator (fun z => M z.1 z.2) := by
      funext z
      simp only [hM', Set.indicator_apply, Set.mem_ofPred_eq]
    rw [e]
    exact hM.indicator hT
  have nF : ∀ σ y, ‖F' σ y‖ ^ 2 = if r < ‖y‖ then ‖F σ y‖ ^ 2 else 0 := by
    intro σ y
    simp only [hF']
    split_ifs <;> simp
  have nM : ∀ σ y, ‖M' σ y‖ ^ 2 = if r < ‖y‖ then ‖M σ y‖ ^ 2 else 0 := by
    intro σ y
    simp only [hM']
    split_ifs <;> simp
  have hF'2 : periodLIntegral (fun σ y => ‖F' σ y‖ ^ 2) ≤ ENNReal.ofReal (a ^ 2) := by
    simp only [nF]
    exact ha
  have hM'2 : periodLIntegral (fun σ y => ‖M' σ y‖ ^ 2) ≤ ENNReal.ofReal (b ^ 2) := by
    simp only [nM]
    exact hb
  have hcs := periodPairing_abs_le hF'm hM'm (hF'2.trans_lt ENNReal.ofReal_lt_top)
    (hM'2.trans_lt ENNReal.ofReal_lt_top)
  have hnF := periodNorm_le_of_le ha0 hF'2
  have hnM := periodNorm_le_of_le hb0 hM'2
  set μ : Measure (ℝ × Space) := (volume.restrict (Set.Icc (0 : ℝ) 1)).prod volume with hμ
  have hμ' : μ = (volume : Measure (ℝ × Space)).restrict (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ) := by
    rw [hμ, Measure.volume_eq_prod, ← Measure.prod_restrict, Measure.restrict_univ]
  have hFμ : AEStronglyMeasurable (fun z : ℝ × Space => F z.1 z.2) μ := by rw [hμ']; exact hF.restrict
  have hMμ : AEStronglyMeasurable (fun z : ℝ × Space => M z.1 z.2) μ := by rw [hμ']; exact hM.restrict
  have hsq : ∀ u : ℝ × Space → Space, AEStronglyMeasurable u μ →
      (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ENNReal.ofReal (‖u (σ, y)‖ ^ 2)) < ⊤ →
      Integrable (fun z => ‖u z‖ ^ 2) μ := by
    intro u hu hfin
    have hl : (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ENNReal.ofReal (‖u (σ, y)‖ ^ 2)) =
        ∫⁻ z, ENNReal.ofReal (‖u z‖ ^ 2) ∂μ := by
      rw [hμ]
      exact (lintegral_prod (fun z => ENNReal.ofReal (‖u z‖ ^ 2))
        ((hu.norm.aemeasurable.pow_const 2).ennreal_ofReal)).symm
    rw [hl] at hfin
    refine (integrable_toReal_of_lintegral_ne_top (hu.norm.pow 2).aemeasurable.ennreal_ofReal
      hfin.ne).congr ?_
    exact ae_of_all _ (fun z => ENNReal.toReal_ofReal (sq_nonneg _))
  have hFi := hsq _ hFμ hF2
  have hMi := hsq _ hMμ hM2
  set g : ℝ × Space → ℝ := fun z => inner ℝ (F z.1 z.2) (M z.1 z.2) with hg
  have hgi : Integrable g μ := by
    have hprod : Integrable (fun z : ℝ × Space => (‖F z.1 z.2‖ ^ 2 + ‖M z.1 z.2‖ ^ 2) / 2) μ :=
      (hFi.add hMi).div_const 2
    refine Integrable.mono' hprod (hFμ.inner hMμ) (ae_of_all _ fun z => ?_)
    rw [Real.norm_eq_abs]
    refine (abs_real_inner_le_norm _ _).trans ?_
    nlinarith [sq_nonneg (‖F z.1 z.2‖ - ‖M z.1 z.2‖)]
  set gb : ℝ × Space → ℝ := {z : ℝ × Space | ‖z.2‖ ≤ r}.indicator g with hgb
  set gt : ℝ × Space → ℝ := {z : ℝ × Space | r < ‖z.2‖}.indicator g with hgt
  have hgbi : Integrable gb μ := hgi.indicator hB
  have hgti : Integrable gt μ := hgi.indicator hT
  have e1 : periodPairing F M = ∫ z, g z ∂μ := by
    rw [hμ, integral_prod _ hgi]
    rfl
  have e2 : ballPairing r F M = ∫ z, gb z ∂μ := by
    rw [hμ, integral_prod _ hgbi]
    unfold ballPairing
    refine integral_congr_ae (ae_of_all _ fun σ => ?_)
    simp only []
    rw [← integral_indicator Metric.isClosed_closedBall.measurableSet]
    refine integral_congr_ae (ae_of_all _ fun y => ?_)
    simp only [hgb, hg, Set.indicator_apply, Set.mem_ofPred_eq]
    by_cases h : ‖y‖ ≤ r <;> simp [h, Metric.mem_closedBall, dist_zero_right]
  have e3 : periodPairing F' M' = ∫ z, gt z ∂μ := by
    rw [hμ, integral_prod _ hgti]
    unfold periodPairing
    refine integral_congr_ae (ae_of_all _ fun σ => ?_)
    refine integral_congr_ae (ae_of_all _ fun y => ?_)
    simp only [hgt, hg, hF', hM', Set.indicator_apply, Set.mem_ofPred_eq]
    split_ifs <;> simp
  have e4 : ∫ z, g z ∂μ = ∫ z, gb z ∂μ + ∫ z, gt z ∂μ := by
    rw [← integral_add hgbi hgti]
    refine integral_congr_ae (ae_of_all _ fun z => ?_)
    simp only [hgb, hgt, Set.indicator_apply, Set.mem_ofPred_eq]
    split_ifs with h1 h2 h2
    · exact absurd h2 (not_lt.2 h1)
    · simp
    · simp
    · exact absurd (lt_of_not_ge h1) h2
  have e5 : periodPairing F M - ballPairing r F M = periodPairing F' M' := by
    rw [e1, e2, e3, e4]
    ring
  rw [e5]
  exact hcs.trans (mul_le_mul hnF hnM (Real.sqrt_nonneg _) ha0)

theorem offset_bound_of_parts {k : ℕ} (j : Fin k) (q cR fr mC oL lE B1 : Fin k → ℝ)
    (mT oQ qE B2 : Fin k → Fin k → ℝ) (Pp Bl B0 sj oC cE fD fA : ℝ)
    (hq : ∀ i, |q i| ≤ cR i)
    (hid : Bl = B0 + (∑ i, q i * B1 i) + ∑ i, ∑ l ∈ Finset.Ici i, q i * q l * B2 i l)
    (hE : |Pp - Bl| ≤ fD * fA)
    (hc : |oC - ((∑ l, fr l * mC l) - B0)| ≤ cE)
    (hlin : ∀ i, |oL i - ((∑ l, fr l * mT i l) - B1 i)| ≤ lE i)
    (hquad : ∀ i l, i ≤ l → |oQ i l + B2 i l| ≤ qE i l) :
    |(∑ l, fr l * (mC l + ∑ i, q i * mT i l)) - Pp - sj * q j| ≤
      |oC| + cE + (∑ i, (|oL i - (if i = j then sj else 0)| + lE i) * cR i)
        + (∑ i, ∑ l ∈ Finset.Ici i, (|oQ i l| + qE i l) * cR i * cR l) + fD * fA := by
  have hcR : ∀ i, 0 ≤ cR i := fun i => (abs_nonneg _).trans (hq i)
  have h1 : (∑ l, fr l * (mC l + ∑ i, q i * mT i l)) =
      (∑ l, fr l * mC l) + ∑ i, q i * ∑ l, fr l * mT i l := by
    simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
    congr 1
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => by ring
  have h2 : (∑ i, q i * (if i = j then sj else 0)) = sj * q j := by
    rw [Finset.sum_eq_single j (fun b _ hb => by rw [if_neg hb, mul_zero])
      (fun h => absurd (Finset.mem_univ j) h), if_pos rfl, mul_comm]
  have h3 : (∑ i, q i * (((∑ l, fr l * mT i l) - B1 i) - (if i = j then sj else 0))) =
      (∑ i, q i * ∑ l, fr l * mT i l) - (∑ i, q i * B1 i) - ∑ i, q i * (if i = j then sj else 0) := by
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have b0 : |(∑ l, fr l * mC l) - B0| ≤ |oC| + cE := by
    have h := abs_le.mp hc
    have h' := abs_le.mp (le_refl |oC|)
    refine abs_le.mpr ⟨?_, ?_⟩ <;> linarith [neg_abs_le oC, le_abs_self oC]
  have b1 : |∑ i, q i * (((∑ l, fr l * mT i l) - B1 i) - (if i = j then sj else 0))| ≤
      ∑ i, (|oL i - (if i = j then sj else 0)| + lE i) * cR i := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    have hl := abs_le.mp (hlin i)
    have hd : |((∑ l, fr l * mT i l) - B1 i) - (if i = j then sj else 0)| ≤
        |oL i - (if i = j then sj else 0)| + lE i := by
      refine abs_le.mpr ⟨?_, ?_⟩ <;>
        linarith [neg_abs_le (oL i - (if i = j then sj else 0)),
          le_abs_self (oL i - (if i = j then sj else 0))]
    rw [abs_mul, mul_comm (|oL i - (if i = j then sj else 0)| + lE i)]
    exact mul_le_mul (hq i) hd (abs_nonneg _) (hcR i)
  have b2 : |∑ i, ∑ l ∈ Finset.Ici i, q i * q l * B2 i l| ≤
      ∑ i, ∑ l ∈ Finset.Ici i, (|oQ i l| + qE i l) * cR i * cR l := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun l hl => ?_)
    have hil : i ≤ l := Finset.mem_Ici.mp hl
    have hh := abs_le.mp (hquad i l hil)
    have hd : |B2 i l| ≤ |oQ i l| + qE i l := by
      refine abs_le.mpr ⟨?_, ?_⟩ <;> linarith [neg_abs_le (oQ i l), le_abs_self (oQ i l)]
    rw [abs_mul, abs_mul]
    calc |q i| * |q l| * |B2 i l| ≤ cR i * cR l * (|oQ i l| + qE i l) :=
          mul_le_mul (mul_le_mul (hq i) (hq l) (abs_nonneg _) (hcR i)) hd (abs_nonneg _)
            (mul_nonneg (hcR i) (hcR l))
      _ = (|oQ i l| + qE i l) * cR i * cR l := by ring
  have key : (∑ l, fr l * (mC l + ∑ i, q i * mT i l)) - Pp - sj * q j =
      ((∑ l, fr l * mC l) - B0)
        + (∑ i, q i * (((∑ l, fr l * mT i l) - B1 i) - (if i = j then sj else 0)))
        - (∑ i, ∑ l ∈ Finset.Ici i, q i * q l * B2 i l) - (Pp - Bl) := by
    rw [h1, h3, h2, hid]
    ring
  rw [key]
  have a0 := abs_le.mp b0
  have a1 := abs_le.mp b1
  have a2 := abs_le.mp b2
  have aE := abs_le.mp hE
  exact abs_le.mpr ⟨by linarith, by linarith⟩

end Internal.OffsetClause

open Internal.OffsetClause

theorem offsetClause_holds_of (hStep : StepPhaseHolds) (hPR : PressureFieldRegularHolds)
    (hBall : OffsetBallIdentityHolds) : OffsetClauseHolds := by
  intro k C nE nM D X SF R Pr Z O hs hSF hIC hO hdef hadj j hj q hq
  obtain ⟨hR, hP, hZ⟩ := hIC
  have hFm := defect_aestronglyMeasurable hStep hPR hSF hR hP q
  have hMs := shapeParts_closed.field_smooth _ _ hZ.params_valid (hZ.field_valid j hj)
  have hM2 : periodLIntegral (fun σ y => ‖D.cert.adjoint j q σ y‖ ^ 2) < ⊤ := by
    have h : periodLIntegral (fun σ y => ‖D.cert.adjoint j q σ y‖ ^ 2) ≤
        ENNReal.ofReal (D.cert.adjointL2 j ^ 2) * volume (Set.Icc (0 : ℝ) 1) := by
      unfold periodLIntegral
      calc (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ENNReal.ofReal (‖D.cert.adjoint j q σ y‖ ^ 2))
          ≤ ∫⁻ σ in Set.Icc (0 : ℝ) 1, ENNReal.ofReal (D.cert.adjointL2 j ^ 2) :=
            lintegral_mono fun σ => hadj j hj q hq σ
        _ = _ := setLIntegral_const _ _
    refine h.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_)
    rw [Real.volume_Icc]
    exact ENNReal.ofReal_lt_top
  rw [hZ.adjoint_eq j hj q] at hM2
  have hsplit := pairing_sub_ball_abs_le (F := D.cert.defect q) (M := shapeInfoField Z.params (Z.field j))
    (r := R.matchRadius) hFm hMs.1.continuous.aestronglyMeasurable
    ((hdef q hq).trans_lt ENNReal.ofReal_lt_top) hM2 (hO.far_defect q hq) (hO.far_adjoint j hj)
    hO.farDefect_nonneg (hO.farAdjoint_nonneg j hj)
  have hid := hBall D X SF R Pr Z O hSF ⟨hR, hP, hZ⟩ hO j hj q hq
  rw [hZ.adjoint_eq j hj q] at hid
  have hgap : ∀ l, D.cert.targetGap q l = 0 := fun l => by
    unfold ExtendedCertificateData.targetGap
    rw [hR.target_eq q l, sub_self]
  have hmul : (∑ i, D.cert.frame i j * D.cert.multiplier q i) =
      ∑ l, D.cert.frame l j * (O.multCentre l + ∑ i, q i * O.multTangent i l) :=
    Finset.sum_congr rfl fun l _ => by rw [hO.multiplier_eq q hq l]
  rw [hO.offset_eq j hj]
  unfold ExtendedCertificateData.adjustedMultiplier offsetSum
  rw [hZ.adjoint_eq j hj q, hmul]
  simp only [hgap, mul_zero, Finset.sum_const_zero, sub_zero]
  exact offset_bound_of_parts j q (coordRadius D.cert) (fun l => D.cert.frame l j) O.multCentre
    (fun i => O.offsetLinear j i) (fun i => O.linearErr j i) _ O.multTangent (fun i l => O.offsetQuad j i l)
    (fun i l => O.quadErr j i l) _ _ _ _ (D.cert.scale j) (O.offsetCentre j) (O.centreErr j) O.farDefect
    (O.farAdjoint j) (abs_le_coordRadius hs hq) hid hsplit (hO.centre_close j hj) (hO.linear_close j hj)
    (hO.quad_close j hj)

end Instantiation

end CellReduction

end Breakdown
