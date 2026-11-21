import Breakdown.FracCell.ModelFormParts

open scoped ContDiff ENNReal
open MeasureTheory

noncomputable section

namespace Breakdown

namespace CellCert

open SteadyCert

def CentrePairingStatement : Prop :=
  ∀ (α : ℝ) {k N : ℕ} (c : FracCellData k N), IsFracCell α c →
    ∀ (v : Space → Space) (G : Space → (Space →L[ℝ] Space)) (H : Space → (Space →L[ℝ] Space →L[ℝ] Space)),
      IsSecondOrderField c.order v G H →
      l2Pair (fun y => (2 : ℝ) • symProduct c.centre c.centreGrad v G y) (negSecondTrace H)
          = (∫ y, jForm (c.centreStrain y) (c.centreCurlGrad y) (G y) (v y)) ∧
      ∀ i, l2Pair (c.actuator i) (negSecondTrace H) = ∫ y, entryInner (G y) (c.actuatorGrad i y)

open ModelFormInternal

theorem modelForm_of (h1 : ChosenAgreeStatement) (h2 : SecondIdentityStatement)
    (h3 : SteadyCert.DriftEnergyStatement) (h4 : CentrePairingStatement) : ModelFormStatement := by
  intro α hα1 hα2 k N c hc p hp v G H hs P _hP hdrift κ
  have hs' : IsSecondOrderField c.order v G H := hs
  have hb := hc.base
  obtain ⟨hGc, hHc⟩ := h1 c.order v G H hs'
  have hform : (c.toCertData α).modelForm p v κ = c.formOf α v G H κ := formOf_congr c α v κ hGc hHc
  obtain ⟨hfull, hcg, hcurl⟩ := h2 c.order v G H hs'
  have hN : MemLp (negSecondTrace H) 2 volume := Internal.DriftSymbolWeak.memLp_negSecondTrace hs'
  have hNi : Integrable (fun y => ‖negSecondTrace H y‖ ^ 2) := (memLp_two_iff_integrable_sq_norm hN.1).1 hN
  have hTi : Integrable (fun y => ‖secondTrace (H y)‖ ^ 2) := by
    simpa only [negSecondTrace, norm_neg] using hNi
  have hGi : Integrable (fun y => entrySq (G y)) := hs'.gradient_two
  have hmω : AEStronglyMeasurable (fun y => curlOf (G y)) volume :=
    continuous_curlOf.comp_aestronglyMeasurable hs'.measurable_gradient
  have hωi : Integrable (fun y => ‖curlOf (G y)‖ ^ 2) :=
    (hGi.const_mul 2).mono' (hmω.norm.pow 2) (ae_of_all _ fun y => by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]; exact curl_sq_le _)
  have hw0 : ∀ y, 0 ≤ c.weight y := fun y => hb.weightMin_pos.le.trans (hb.weight_lower y)
  have hwi : Integrable (fun y => c.weight y * entrySq (G y)) :=
    (hGi.const_mul c.weightMax).mono' (hb.weight_measurable.aestronglyMeasurable.mul hGi.aestronglyMeasurable)
      (ae_of_all _ fun y => by
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hw0 y) (LinearSolveCore.entrySq_nonneg' _))]
        exact mul_le_mul_of_nonneg_right (hb.weight_upper y) (LinearSolveCore.entrySq_nonneg' _))
  set T := ∫ y, ‖secondTrace (H y)‖ ^ 2 with hT
  set Gs := ∫ y, entrySq (G y) with hGs
  set Wg := ∫ y, c.weight y * entrySq (G y) with hWg
  set Jm := ∫ y, jForm (c.modelStrain y) (c.modelCurlGrad y) (G y) (v y) with hJm
  set Jc := ∫ y, jForm (c.centreStrain y) (c.centreCurlGrad y) (G y) (v y) with hJc
  have hBform : c.formOf α v G H κ = c.splitVisc * T + (1 - 3 / (4 * α)) * Gs + Jm
      + ∑ i, κ i * ∫ y, entryInner (G y) (c.modelActuatorGrad i y) := by
    have i4 : ∫ y, ((1 - 3 / (4 * α) - c.curlWeight) * ‖curlOf (G y)‖ ^ 2
        + (c.curlWeight - c.coercivity * c.weight y) * entrySq (G y))
        = (1 - 3 / (4 * α) - c.curlWeight) * Gs + c.curlWeight * Gs - c.coercivity * Wg := by
      have e : ∀ y, ((1 - 3 / (4 * α) - c.curlWeight) * ‖curlOf (G y)‖ ^ 2
          + (c.curlWeight - c.coercivity * c.weight y) * entrySq (G y))
          = ((1 - 3 / (4 * α) - c.curlWeight) * ‖curlOf (G y)‖ ^ 2 + c.curlWeight * entrySq (G y))
            - c.coercivity * (c.weight y * entrySq (G y)) := fun y => by ring
      simp_rw [e]
      have hI1 : Integrable (fun y => (1 - 3 / (4 * α) - c.curlWeight) * ‖curlOf (G y)‖ ^ 2
          + c.curlWeight * entrySq (G y)) := (hωi.const_mul _).add (hGi.const_mul _)
      rw [integral_sub hI1 (hwi.const_mul _),
        integral_add (hωi.const_mul _) (hGi.const_mul _), integral_const_mul, integral_const_mul,
        integral_const_mul, hcurl]
    unfold FracCellData.formOf SteadyCert.weightedEnergy
    rw [i4, hfull, hcg]
    ring
  set F3 : Space → Space := fun y => (2 : ℝ) • symProduct (fun z => c.profile p z - c.centre z)
      (fun z => c.gradProfile p z - c.centreGrad z) v G y with hF3def
  set F4 : Space → Space := fun y => (2 : ℝ) • symProduct c.centre c.centreGrad v G y with hF4def
  obtain ⟨Cp, hCp⟩ := hb.profile_bounds
  obtain ⟨Cc, hCc⟩ := hc.centre_bounds
  have hP2 : MemLp (symProduct (c.profile p) (fun z => fderiv ℝ (c.profile p) z) v G) 2 volume :=
    LinearSolveCore.symProduct_memLp inverseSquareBound (hb.profile_smooth p hp)
      (fun y => ⟨(hCp p hp y).1, (hCp p hp y).2.1⟩) hs'
  have hC2 : MemLp (symProduct c.centre (fun z => fderiv ℝ c.centre z) v G) 2 volume :=
    LinearSolveCore.symProduct_memLp inverseSquareBound hc.centre_smooth
      (fun y => ⟨(hCc y).1, (hCc y).2.1⟩) hs'
  have hF4 : MemLp F4 2 volume := hC2.const_smul (2 : ℝ)
  have hsplit : ∀ y, (2 : ℝ) • symProduct (c.profile p) (c.gradProfile p) v G y = F3 y + F4 y := by
    intro y
    simp only [hF3def, hF4def, symProduct, map_sub, ContinuousLinearMap.sub_apply]
    module
  have hF3 : MemLp F3 2 volume := by
    refine MemLp.ae_eq (ae_of_all _ fun y => ?_) ((hP2.const_smul (2 : ℝ)).sub hF4)
    show (2 : ℝ) • symProduct (c.profile p) (c.gradProfile p) v G y - F4 y = F3 y
    rw [hsplit y]
    abel
  have hloc : ∀ y, inner ℝ ((c.toCertData α).localField α p v G H κ y) (negSecondTrace H y)
      = inner ℝ (driftField α (c.rotationRate p) v G y) (negSecondTrace H y)
        + c.splitVisc * ‖secondTrace (H y)‖ ^ 2
        + inner ℝ (F3 y) (negSecondTrace H y) + inner ℝ (F4 y) (negSecondTrace H y)
        + ∑ i, κ i * inner ℝ (c.actuator i y) (negSecondTrace H y) := by
    intro y
    show inner ℝ (driftField α (c.rotationRate p) v G y - c.splitVisc • secondTrace (H y)
      + (2 : ℝ) • symProduct (c.profile p) (c.gradProfile p) v G y + ∑ i, κ i • c.actuator i y)
        (negSecondTrace H y) = _
    rw [hsplit y]
    simp only [negSecondTrace, inner_add_left, inner_sub_left, real_inner_smul_left, sum_inner, inner_neg_right,
      real_inner_self_eq_norm_sq, mul_neg, Finset.sum_neg_distrib]
    ring
  have hd : Integrable (fun y => inner ℝ (driftField α (c.rotationRate p) v G y) (negSecondTrace H y)) :=
    pair_integrable hdrift hN
  have h3i := pair_integrable hF3 hN
  have h4i := pair_integrable hF4 hN
  have hai : ∀ i, Integrable (fun y => inner ℝ (c.actuator i y) (negSecondTrace H y)) :=
    fun i => pair_integrable (hb.actuator_two i) hN
  have hsumi : Integrable (fun y => ∑ i, κ i * inner ℝ (c.actuator i y) (negSecondTrace H y)) :=
    integrable_finsetSum _ fun i _ => (hai i).const_mul _
  have i1 : Integrable (fun y => inner ℝ (driftField α (c.rotationRate p) v G y) (negSecondTrace H y)
      + c.splitVisc * ‖secondTrace (H y)‖ ^ 2) := hd.add (hTi.const_mul _)
  have i2 : Integrable (fun y => inner ℝ (driftField α (c.rotationRate p) v G y) (negSecondTrace H y)
      + c.splitVisc * ‖secondTrace (H y)‖ ^ 2 + inner ℝ (F3 y) (negSecondTrace H y)) := i1.add h3i
  have i3 : Integrable (fun y => inner ℝ (driftField α (c.rotationRate p) v G y) (negSecondTrace H y)
      + c.splitVisc * ‖secondTrace (H y)‖ ^ 2 + inner ℝ (F3 y) (negSecondTrace H y)
      + inner ℝ (F4 y) (negSecondTrace H y)) := i2.add h4i
  have hRHS : l2Pair ((c.toCertData α).localField α p v G H κ) (negSecondTrace H)
      = l2Pair (driftField α (c.rotationRate p) v G) (negSecondTrace H) + c.splitVisc * T
        + l2Pair F3 (negSecondTrace H) + l2Pair F4 (negSecondTrace H)
        + ∑ i, κ i * l2Pair (c.actuator i) (negSecondTrace H) := by
    unfold l2Pair
    simp_rw [hloc]
    rw [integral_add i3 hsumi, integral_add i2 h4i, integral_add i1 h3i, integral_add hd (hTi.const_mul _),
      integral_const_mul, integral_finsetSum _ fun i _ => (hai i).const_mul _]
    simp only [integral_const_mul]
    rfl
  have hT0 : 0 ≤ T := integral_nonneg fun y => by positivity
  have hGs0 : 0 ≤ Gs := integral_nonneg fun y => LinearSolveCore.entrySq_nonneg' _
  have hWg0 : 0 ≤ Wg := integral_nonneg fun y => mul_nonneg (hw0 y) (LinearSolveCore.entrySq_nonneg' _)
  have hE0 : 0 ≤ T + Wg := add_nonneg hT0 hWg0
  have hP3 : -(c.centreLoss * (T + Wg)) ≤ l2Pair F3 (negSecondTrace H) := by
    have hcs := pairIntegral_bound zero_le_one h3i hF3.1.norm hN.1.norm (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
      ((memLp_two_iff_integrable_sq_norm hF3.1).1 hF3) hNi
      (ae_of_all _ fun y => by rw [one_mul]; exact abs_real_inner_le_norm _ _)
    have hl : Real.sqrt (∫ y, ‖F3 y‖ ^ 2) ≤ c.centreLoss * Real.sqrt (T + Wg) :=
      hc.centreLoss_bound p hp v G H hs'
    have heq : ∫ y, ‖negSecondTrace H y‖ ^ 2 = T := by
      simp only [negSecondTrace, norm_neg, hT]
    have hn : Real.sqrt (∫ y, ‖negSecondTrace H y‖ ^ 2) ≤ Real.sqrt (T + Wg) := by
      rw [heq]; exact Real.sqrt_le_sqrt (by linarith)
    have hγ : 0 ≤ c.centreLoss := hc.losses_nonneg'.1
    have hsq := Real.mul_self_sqrt hE0
    rw [one_mul] at hcs
    have hm := mul_le_mul hl hn (Real.sqrt_nonneg _) (mul_nonneg hγ (Real.sqrt_nonneg _))
    have := (abs_le.mp (hcs.trans hm)).1
    have hm' : c.centreLoss * Real.sqrt (T + Wg) * Real.sqrt (T + Wg) = c.centreLoss * (T + Wg) := by
      rw [mul_assoc, hsq]
    show -(c.centreLoss * (T + Wg)) ≤ ∫ y, inner ℝ (F3 y) (negSecondTrace H y)
    linarith
  have hS := strain_integrable hc hs'
  obtain ⟨hCm, hCi, hCg⟩ := curlGradError_data hc hs'
  have hJci := centre_integrable hc hs'
  have hdiff : ∀ y, jForm (c.centreStrain y) (c.centreCurlGrad y) (G y) (v y)
      - jForm (c.modelStrain y) (c.modelCurlGrad y) (G y) (v y)
      = -inner ℝ (curlOf (G y)) (c.strainError y (curlOf (G y))) + curlGradPart (c.curlGradError y) (G y) (v y) :=
    fun y => jForm_sub _ _ _ _ _ _
  have hJmi : Integrable (fun y => jForm (c.modelStrain y) (c.modelCurlGrad y) (G y) (v y)) := by
    refine (hJci.sub (hS.neg.add hCg)).congr (ae_of_all _ fun y => ?_)
    have := hdiff y
    simp only [Pi.sub_apply, Pi.add_apply, Pi.neg_apply]
    linarith
  have hJdiff : Jc - Jm = -(∫ y, inner ℝ (curlOf (G y)) (c.strainError y (curlOf (G y))))
      + ∫ y, curlGradPart (c.curlGradError y) (G y) (v y) := by
    have hSn : Integrable (fun y => -inner ℝ (curlOf (G y)) (c.strainError y (curlOf (G y)))) := hS.neg
    rw [hJc, hJm, ← integral_sub hJci hJmi, ← integral_neg, ← integral_add hSn hCg]
    exact integral_congr_ae (ae_of_all _ fun y => hdiff y)
  have hstrain : ∫ y, inner ℝ (curlOf (G y)) (c.strainError y (curlOf (G y))) ≤ c.strainLoss * Gs := by
    rw [← hcurl, ← integral_const_mul]
    exact integral_mono hS (hωi.const_mul _) fun y => hc.strainLoss_bound y _
  have hcgb : -(Real.sqrt (7 / 2) * (c.curlGradLoss * Gs)) ≤ ∫ y, curlGradPart (c.curlGradError y) (G y) (v y) := by
    have hbm : AEStronglyMeasurable (fun y => Real.sqrt (entrySq (G y))) volume :=
      Real.continuous_sqrt.comp_aestronglyMeasurable hGi.aestronglyMeasurable
    have hib : Integrable (fun y => Real.sqrt (entrySq (G y)) ^ 2) :=
      hGi.congr (ae_of_all _ fun y => (Real.sq_sqrt (LinearSolveCore.entrySq_nonneg' _)).symm)
    have hcs := pairIntegral_bound (Real.sqrt_nonneg (7 / 2)) hCg hCm hbm (fun y => mul_nonneg (norm_nonneg _) (norm_nonneg _))
      (fun _ => Real.sqrt_nonneg _) hCi hib
      ((trace_zero hc).mono fun y hy => by rw [← mul_assoc]; exact part_bound _ _ _ hy)
    have e2 : ∫ y, Real.sqrt (entrySq (G y)) ^ 2 = Gs :=
      integral_congr_ae (ae_of_all _ fun y => Real.sq_sqrt (LinearSolveCore.entrySq_nonneg' _))
    have e1 : ∫ y, (‖c.curlGradError y‖ * ‖v y‖) ^ 2 = ∫ y, ‖c.curlGradError y‖ ^ 2 * ‖v y‖ ^ 2 :=
      integral_congr_ae (ae_of_all _ fun y => mul_pow _ _ _)
    rw [e1, e2] at hcs
    have hL : Real.sqrt (∫ y, ‖c.curlGradError y‖ ^ 2 * ‖v y‖ ^ 2) ≤ c.curlGradLoss * Real.sqrt Gs :=
      hc.curlGradLoss_bound v G H hs'
    have hsq := Real.mul_self_sqrt hGs0
    have h' := mul_le_mul_of_nonneg_right hL (Real.sqrt_nonneg Gs)
    have h77 := Real.sqrt_nonneg (7 / 2 : ℝ)
    have := (abs_le.mp hcs).1
    have h5 := mul_le_mul_of_nonneg_left h' h77
    rw [mul_assoc c.curlGradLoss, hsq] at h5
    linarith
  have hcE : Continuous entrySq := by
    unfold entrySq
    fun_prop
  obtain ⟨hJid, hAid⟩ := h4 α c hc v G H hs'
  have hact : ∀ i, |(∫ y, entryInner (G y) (c.actuatorGrad i y)) - ∫ y, entryInner (G y) (c.modelActuatorGrad i y)|
      ≤ Real.sqrt Gs * Real.sqrt (∫ y, entrySq (c.actuatorGrad i y - c.modelActuatorGrad i y)) := by
    intro i
    obtain ⟨-, hXm, hXi⟩ := hc.actuator_gradient i
    obtain ⟨hYm, hYi, -⟩ := hc.modelActuatorGrad_data i
    have hDm : AEStronglyMeasurable (fun y => c.actuatorGrad i y - c.modelActuatorGrad i y) volume := hXm.sub hYm
    have hDi : Integrable (fun y => entrySq (c.actuatorGrad i y - c.modelActuatorGrad i y)) :=
      ((hXi.const_mul 2).add (hYi.const_mul 2)).mono' (hcE.comp_aestronglyMeasurable hDm)
        (ae_of_all _ fun y => by
          rw [Real.norm_eq_abs, abs_of_nonneg (LinearSolveCore.entrySq_nonneg' _)]
          exact entrySq_sub_le _ _)
    obtain ⟨hpX, -⟩ := entryInner_pair hs'.measurable_gradient hXm hGi hXi
    obtain ⟨hpY, -⟩ := entryInner_pair hs'.measurable_gradient hYm hGi hYi
    obtain ⟨-, hbd⟩ := entryInner_pair hs'.measurable_gradient hDm hGi hDi
    rw [← integral_sub hpX hpY]
    have e : ∀ y, entryInner (G y) (c.actuatorGrad i y) - entryInner (G y) (c.modelActuatorGrad i y)
        = entryInner (G y) (c.actuatorGrad i y - c.modelActuatorGrad i y) := by
      intro y
      simp only [entryInner, ContinuousLinearMap.sub_apply, inner_sub_right, Finset.sum_sub_distrib]
    simp_rw [e]
    exact hbd
  set K2 := ∑ i, κ i ^ 2 with hK2
  have hK20 : 0 ≤ K2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hY0 : ∀ i, 0 ≤ ∫ y, entrySq (c.actuatorGrad i y - c.modelActuatorGrad i y) :=
    fun i => integral_nonneg fun y => LinearSolveCore.entrySq_nonneg' _
  have hLa0 : 0 ≤ c.actuatorGradLoss := hc.losses_nonneg'.2.2.2.2.2.2.1
  have hactsum : -(Real.sqrt Gs * (Real.sqrt K2 * c.actuatorGradLoss)) ≤
      ∑ i, κ i * ((∫ y, entryInner (G y) (c.actuatorGrad i y)) - ∫ y, entryInner (G y) (c.modelActuatorGrad i y)) := by
    set Y : Fin k → ℝ := fun i => ∫ y, entrySq (c.actuatorGrad i y - c.modelActuatorGrad i y) with hY
    have h1 : ∀ i, -(Real.sqrt Gs * (|κ i| * Real.sqrt (Y i))) ≤
        κ i * ((∫ y, entryInner (G y) (c.actuatorGrad i y)) - ∫ y, entryInner (G y) (c.modelActuatorGrad i y)) := by
      intro i
      have hb2 := neg_abs_le
        (κ i * ((∫ y, entryInner (G y) (c.actuatorGrad i y)) - ∫ y, entryInner (G y) (c.modelActuatorGrad i y)))
      rw [abs_mul] at hb2
      have := mul_le_mul_of_nonneg_left (hact i) (abs_nonneg (κ i))
      linarith [this]
    have h2 : ∑ i, |κ i| * Real.sqrt (Y i) ≤ Real.sqrt K2 * Real.sqrt (∑ i, Y i) := by
      have h := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (fun i => |κ i|) (fun i => Real.sqrt (Y i))
      have e1 : ∑ i, |κ i| ^ 2 = K2 := Finset.sum_congr rfl fun i _ => sq_abs _
      have e2 : ∑ i, Real.sqrt (Y i) ^ 2 = ∑ i, Y i := Finset.sum_congr rfl fun i _ => Real.sq_sqrt (hY0 i)
      rw [e1, e2] at h
      exact h
    have h3 : Real.sqrt (∑ i, Y i) ≤ c.actuatorGradLoss := by
      rw [← Real.sqrt_sq hLa0]
      exact Real.sqrt_le_sqrt hc.actuatorGradLoss_bound
    calc -(Real.sqrt Gs * (Real.sqrt K2 * c.actuatorGradLoss))
        ≤ -(Real.sqrt Gs * ∑ i, |κ i| * Real.sqrt (Y i)) := by
          have := mul_le_mul_of_nonneg_left (h2.trans (mul_le_mul_of_nonneg_left h3 (Real.sqrt_nonneg _)))
            (Real.sqrt_nonneg Gs)
          linarith
      _ = ∑ i, -(Real.sqrt Gs * (|κ i| * Real.sqrt (Y i))) := by
          rw [Finset.mul_sum, Finset.sum_neg_distrib]
      _ ≤ _ := Finset.sum_le_sum fun i _ => h1 i
  have hwE : SteadyCert.weightedEnergy c.weight G H = T + Wg := rfl
  have hsizeSq : (c.toCertData α).size G H κ ^ 2 = T + Wg + c.multiplierScale ^ 2 * K2 := by
    show Real.sqrt (SteadyCert.weightedEnergy c.weight G H + c.multiplierScale ^ 2 * ∑ i, κ i ^ 2) ^ 2 = _
    rw [hwE, Real.sq_sqrt (add_nonneg hE0 (mul_nonneg (sq_nonneg _) hK20))]
  have hpl : (c.toCertData α).potLoss = c.potLoss := rfl
  have hdr : l2Pair (driftField α (c.rotationRate p) v G) (negSecondTrace H) = (1 - 3 / (4 * α)) * Gs :=
    h3 α hα1 hα2 (c.rotationRate p) c.order v G H hs' hdrift
  have hJ4 : l2Pair F4 (negSecondTrace H) = Jc := hJid
  rw [hform, hRHS, hBform, hsizeSq, hpl, hdr, hJ4]
  simp only [hAid]
  have hsumdiff : ∑ i, κ i * (∫ y, entryInner (G y) (c.actuatorGrad i y))
      - ∑ i, κ i * (∫ y, entryInner (G y) (c.modelActuatorGrad i y))
      = ∑ i, κ i * ((∫ y, entryInner (G y) (c.actuatorGrad i y)) - ∫ y, entryInner (G y) (c.modelActuatorGrad i y)) := by
    rw [← Finset.sum_sub_distrib]
    simp only [mul_sub]
  have hμ := hb.multiplierScale_pos
  have hwm := hb.weightMin_pos
  have hγ : 0 ≤ c.centreLoss := hc.losses_nonneg'.1
  have hσ : 0 ≤ c.strainLoss := hc.losses_nonneg'.2.2.1
  have hLc : 0 ≤ c.curlGradLoss := hc.losses_nonneg'.2.2.2.1
  have hpot := hc.potLoss_ge
  have hwmGs : c.weightMin * Gs ≤ Wg := by
    rw [hGs, hWg, ← integral_const_mul]
    exact integral_mono (hGi.const_mul _) hwi fun y =>
      mul_le_mul_of_nonneg_right (hb.weight_lower y) (LinearSolveCore.entrySq_nonneg' _)
  have hS2 : 0 ≤ T + Wg + c.multiplierScale ^ 2 * K2 := add_nonneg hE0 (mul_nonneg (sq_nonneg _) hK20)
  have k1 : Gs ≤ (T + Wg + c.multiplierScale ^ 2 * K2) / c.weightMin := by
    rw [le_div_iff₀ hwm]
    have := mul_nonneg (sq_nonneg c.multiplierScale) hK20
    linarith
  have hq0 : 0 < Real.sqrt c.weightMin := Real.sqrt_pos.mpr hwm
  have k2 : Real.sqrt Gs * Real.sqrt K2 ≤
      (T + Wg + c.multiplierScale ^ 2 * K2) / (2 * c.multiplierScale * Real.sqrt c.weightMin) := by
    rw [le_div_iff₀ (by positivity)]
    have hq := Real.sq_sqrt hwm.le
    have hs := Real.sq_sqrt hGs0
    have hr := Real.sq_sqrt hK20
    have hab := two_mul_le_add_sq (Real.sqrt c.weightMin * Real.sqrt Gs) (c.multiplierScale * Real.sqrt K2)
    have ha2 : (Real.sqrt c.weightMin * Real.sqrt Gs) ^ 2 = c.weightMin * Gs := by rw [mul_pow, hq, hs]
    have hb2 : (c.multiplierScale * Real.sqrt K2) ^ 2 = c.multiplierScale ^ 2 * K2 := by rw [mul_pow, hr]
    calc Real.sqrt Gs * Real.sqrt K2 * (2 * c.multiplierScale * Real.sqrt c.weightMin)
        = 2 * (Real.sqrt c.weightMin * Real.sqrt Gs) * (c.multiplierScale * Real.sqrt K2) := by ring
      _ ≤ (Real.sqrt c.weightMin * Real.sqrt Gs) ^ 2 + (c.multiplierScale * Real.sqrt K2) ^ 2 := hab
      _ ≤ _ := by rw [ha2, hb2]; linarith
  have hX0 : 0 ≤ c.strainLoss + Real.sqrt (7 / 2) * c.curlGradLoss :=
    add_nonneg hσ (mul_nonneg (Real.sqrt_nonneg _) hLc)
  have t1 : c.centreLoss * (T + Wg) ≤ c.centreLoss * (T + Wg + c.multiplierScale ^ 2 * K2) :=
    mul_le_mul_of_nonneg_left (by linarith [mul_nonneg (sq_nonneg c.multiplierScale) hK20]) hγ
  have t2 : (c.strainLoss + Real.sqrt (7 / 2) * c.curlGradLoss) * Gs ≤
      (c.strainLoss + Real.sqrt (7 / 2) * c.curlGradLoss) * ((T + Wg + c.multiplierScale ^ 2 * K2) / c.weightMin) :=
    mul_le_mul_of_nonneg_left k1 hX0
  have t3 : c.actuatorGradLoss * (Real.sqrt Gs * Real.sqrt K2) ≤ c.actuatorGradLoss *
      ((T + Wg + c.multiplierScale ^ 2 * K2) / (2 * c.multiplierScale * Real.sqrt c.weightMin)) :=
    mul_le_mul_of_nonneg_left k2 hLa0
  have t4 := mul_le_mul_of_nonneg_right hpot hS2
  have e4 : (c.centreLoss + (c.strainLoss + Real.sqrt (7 / 2) * c.curlGradLoss) / c.weightMin
      + c.actuatorGradLoss / (2 * c.multiplierScale * Real.sqrt c.weightMin)) * (T + Wg + c.multiplierScale ^ 2 * K2)
      = c.centreLoss * (T + Wg + c.multiplierScale ^ 2 * K2)
        + (c.strainLoss + Real.sqrt (7 / 2) * c.curlGradLoss) * ((T + Wg + c.multiplierScale ^ 2 * K2) / c.weightMin)
        + c.actuatorGradLoss * ((T + Wg + c.multiplierScale ^ 2 * K2) / (2 * c.multiplierScale * Real.sqrt c.weightMin)) := by
    ring
  rw [e4] at t4
  linear_combination hP3 - hJdiff + hstrain + hcgb - hsumdiff + hactsum + t1 + t2 + t3 + t4

end CellCert

end Breakdown
