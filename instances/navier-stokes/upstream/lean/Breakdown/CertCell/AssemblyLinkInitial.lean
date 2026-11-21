import Breakdown.CertCell.AssemblyStatements
import Breakdown.CertCell.ModeTermFlip
import Breakdown.CertCell.CouplingGlobalLeaf

open MeasureTheory
open scoped ENNReal

noncomputable section

namespace Breakdown

namespace CertCell

namespace Assembly

open CellCalculus

namespace Internal.InitialLink

theorem max_sub_max_neg (a : ℝ) : max a 0 - max (-a) 0 = a := by
  rcases le_total 0 a with h | h
  · rw [max_eq_left h, max_eq_right (by linarith)]
    ring
  · rw [max_eq_right h, max_eq_left (by linarith)]
    ring

theorem real_le_of_cell_bound {Q S sl cr kq : ℝ} {N P O Z : ℝ≥0∞} (hP : P ≠ ⊤) (hN : N ≠ ⊤) (hZ : Z = 0)
    (hk : 0 ≤ kq)
    (h : ENNReal.ofReal Q + ENNReal.ofReal (-S) + ENNReal.ofReal sl + ENNReal.ofReal cr + N + O
      ≤ P + Z + ENNReal.ofReal S + ENNReal.ofReal (-Q) + ENNReal.ofReal kq) :
    Q + sl + cr ≤ P.toReal - N.toReal + S + kq := by
  subst hZ
  rw [add_zero] at h
  have h1 : ENNReal.ofReal Q + ENNReal.ofReal (-S) + ENNReal.ofReal sl + ENNReal.ofReal cr + N
      ≤ P + ENNReal.ofReal S + ENNReal.ofReal (-Q) + ENNReal.ofReal kq :=
    le_trans le_self_add h
  have hR : P + ENNReal.ofReal S + ENNReal.ofReal (-Q) + ENNReal.ofReal kq ≠ ⊤ := by
    simp [ENNReal.add_eq_top, hP]
  have h2 := ENNReal.toReal_mono hR h1
  simp only [ENNReal.toReal_add, ENNReal.toReal_ofReal', ne_eq, ENNReal.add_eq_top, ENNReal.ofReal_ne_top,
    hP, hN, not_false_eq_true, or_self] at h2
  have hq := max_sub_max_neg Q
  have hs := max_sub_max_neg S
  have hsl := le_max_left sl 0
  have hcr := le_max_left cr 0
  have hkq : max kq 0 = kq := max_eq_left hk
  linarith

theorem formPos_withFormCoercivity {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM)
    {q : Fin k → ℝ} (hc : (D.pieces q).c = D.coercivity) (v : ℝ → Space → Space)
    (G : ℝ → Space → (Space →L[ℝ] Space)) (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) :
    (D.withFormCoercivity D.coercivity).formPos q v G H = D.formPos q v G H ∧
      (D.withFormCoercivity D.coercivity).formNeg q v G H = D.formNeg q v G H := by
  have hp : ({ D.pieces q with c := D.coercivity } : PieceWeights C nE nM) = D.pieces q := by
    rw [← hc]
  have hl : ∀ ι p, (D.withFormCoercivity D.coercivity).labelDensity q v G H ι p = D.labelDensity q v G H ι p := by
    intro ι p
    unfold CellLayerData.labelDensity CellLayerData.withFormCoercivity
    dsimp only
    rw [hp]
  constructor
  · unfold CellLayerData.formPos
    simp only [hl]
    rfl
  · unfold CellLayerData.formNeg
    simp only [hl]
    rfl

open Bridge.Internal.ModeTermFlip (flipIsometryEquiv flipPoint_flipPoint norm_flipPoint) in
theorem flipAverage_measurable {F : ℝ → Space → Space}
    (hF : AEStronglyMeasurable (fun z : ℝ × Space => F z.1 z.2) volume) :
    AEStronglyMeasurable (fun z : ℝ × Space => flipAverage F z.1 z.2) volume := by
  have hmp : MeasurePreserving (Prod.map id flipPoint : ℝ × Space → ℝ × Space) volume volume := by
    rw [Measure.volume_eq_prod]
    exact (MeasurePreserving.id volume).prod flipIsometryEquiv.measurePreserving
  have hc : AEStronglyMeasurable (fun z : ℝ × Space => flipPoint (F z.1 (flipPoint z.2))) volume :=
    flipIsometryEquiv.continuous.comp_aestronglyMeasurable (hF.comp_measurePreserving hmp)
  exact (hF.add hc).const_smul (1 / 2 : ℝ)

theorem flipAverage_periodic {F : ℝ → Space → Space} (hF : IsTimePeriodic F) :
    IsTimePeriodic (flipAverage F) := by
  intro σ y
  unfold flipAverage
  rw [hF σ y, hF σ (flipPoint y)]

open Bridge.Internal.ModeTermFlip (flipIsometryEquiv norm_flipPoint) in
theorem norm_sq_half_sum_le (a b : Space) :
    ‖(1 / 2 : ℝ) • (a + flipPoint b)‖ ^ 2 ≤ ‖a‖ ^ 2 + ‖b‖ ^ 2 := by
  have h1 : ‖(1 / 2 : ℝ) • (a + flipPoint b)‖ ≤ (1 / 2) * (‖a‖ + ‖b‖) := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    gcongr
    exact (norm_add_le _ _).trans (le_of_eq (by rw [norm_flipPoint]))
  have h0 : 0 ≤ ‖(1 / 2 : ℝ) • (a + flipPoint b)‖ := norm_nonneg _
  have h2 := mul_le_mul h1 h1 h0 (by positivity)
  nlinarith [norm_nonneg a, norm_nonneg b, sq_nonneg (‖a‖ - ‖b‖)]

open Bridge.Internal.ModeTermFlip (flipIsometryEquiv) in
theorem flipAverage_finite {F : ℝ → Space → Space}
    (hF : AEStronglyMeasurable (fun z : ℝ × Space => F z.1 z.2) volume)
    (hF2 : periodLIntegral (fun σ y => ‖F σ y‖ ^ 2) < ⊤) :
    periodLIntegral (fun σ y => ‖flipAverage F σ y‖ ^ 2) < ⊤ := by
  have hFr : AEStronglyMeasurable (fun z : ℝ × Space => F z.1 z.2)
      ((volume.restrict (Set.Icc (0 : ℝ) 1)).prod volume) := by
    rw [Measure.volume_eq_prod] at hF
    exact hF.mono_ac (Measure.AbsolutelyContinuous.prod
      (Measure.absolutelyContinuous_of_le Measure.restrict_le_self) Measure.AbsolutelyContinuous.rfl)
  have hle : periodLIntegral (fun σ y => ‖flipAverage F σ y‖ ^ 2)
      ≤ 2 * periodLIntegral (fun σ y => ‖F σ y‖ ^ 2) := by
    unfold periodLIntegral
    rw [← lintegral_const_mul' 2 _ (by simp)]
    refine lintegral_mono_ae ?_
    filter_upwards [hFr.prodMk_left] with σ hσ
    have hmeas : AEMeasurable (fun y => ENNReal.ofReal (‖F σ y‖ ^ 2)) volume :=
      (hσ.norm.pow 2).aemeasurable.ennreal_ofReal
    have hc : ∫⁻ y, ENNReal.ofReal (‖F σ (flipPoint y)‖ ^ 2) = ∫⁻ y, ENNReal.ofReal (‖F σ y‖ ^ 2) :=
      flipIsometryEquiv.measurePreserving.lintegral_comp_emb
        flipIsometryEquiv.toMeasurableEquiv.measurableEmbedding (fun y => ENNReal.ofReal (‖F σ y‖ ^ 2))
    calc ∫⁻ y, ENNReal.ofReal (‖flipAverage F σ y‖ ^ 2)
        ≤ ∫⁻ y, (ENNReal.ofReal (‖F σ y‖ ^ 2) + ENNReal.ofReal (‖F σ (flipPoint y)‖ ^ 2)) := by
          refine lintegral_mono fun y => ?_
          rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
          exact ENNReal.ofReal_le_ofReal (norm_sq_half_sum_le _ _)
      _ = (∫⁻ y, ENNReal.ofReal (‖F σ y‖ ^ 2)) + ∫⁻ y, ENNReal.ofReal (‖F σ (flipPoint y)‖ ^ 2) :=
          lintegral_add_left' hmeas _
      _ = 2 * ∫⁻ y, ENNReal.ofReal (‖F σ y‖ ^ 2) := by
          rw [hc, two_mul]
  exact hle.trans_lt (ENNReal.mul_lt_top (by simp) hF2)

end Internal.InitialLink

open Internal.InitialLink in
theorem initialStateBound_of_split (hS : FormSplitHolds) (hG : Coupling.GlobalLeafHolds)
    {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM) (R : CellCalculus.CellCalculusEntry D)
    (hmesh : IsCellMesh D.mesh) (ht : 0 < D.pinWeight)
    (hc : ∀ q ∈ D.cert.params, (D.pieces q).c = D.coercivity)
    (hN : FormNegFinite D D.coercivity) (hCell : CellCalculus.CellFormBoundsHold D R)
    (hOff : OffModesVanish D R) (hExt : ExteriorNonneg D) (hRow : RowSharesMatch D)
    (hCredit : CreditLeavesBound D R) (e ePair : ℝ) (hPair : PairSharesBound D R ePair)
    (hE : ∑ K, R.kappaCost K + ePair ≤ e) (hk : ∀ K, 0 ≤ R.kappaCost K) : InitialStateBound D R e := by
  intro q hq x ζ η Pg hPg hPgFlip hSR
  obtain ⟨hPosEq, hNegEq⟩ := formPos_withFormCoercivity D (hc q hq) x.v x.G x.H
  have hPf : D.formPos q x.v x.G x.H ≠ ⊤ := by
    rw [← hPosEq]
    exact x.pos_finite.ne
  have hNf : D.formNeg q x.v x.G x.H ≠ ⊤ := by
    rw [← hNegEq]
    exact (hN q hq x.v x.G x.H x.g x.perturbation).ne
  obtain ⟨hsP, hsN⟩ := hS D hmesh q x.v x.G x.H
  have hSumP : (∑ K, cellPos D K q x.v x.G x.H) ≠ ⊤ :=
    ne_top_of_le_ne_top hPf (hsP ▸ le_self_add)
  have hSumN : (∑ K, cellNeg D K q x.v x.G x.H) ≠ ⊤ :=
    ne_top_of_le_ne_top hNf (hsN ▸ le_self_add)
  have hExtP : extPos D q x.v x.G x.H ≠ ⊤ :=
    ne_top_of_le_ne_top hPf (hsP ▸ le_add_self)
  have hExtN : extNeg D q x.v x.G x.H ≠ ⊤ :=
    ne_top_of_le_ne_top hNf (hsN ▸ le_add_self)
  have hCP : ∀ K, cellPos D K q x.v x.G x.H ≠ ⊤ := fun K =>
    ne_top_of_le_ne_top hSumP (Finset.single_le_sum (f := fun K => cellPos D K q x.v x.G x.H)
      (fun _ _ => bot_le) (Finset.mem_univ K))
  have hCN : ∀ K, cellNeg D K q x.v x.G x.H ≠ ⊤ := fun K =>
    ne_top_of_le_ne_top hSumN (Finset.single_le_sum (f := fun K => cellNeg D K q x.v x.G x.H)
      (fun _ _ => bot_le) (Finset.mem_univ K))
  have hPosReal : (D.formPos q x.v x.G x.H).toReal
      = (∑ K, (cellPos D K q x.v x.G x.H).toReal) + (extPos D q x.v x.G x.H).toReal := by
    rw [hsP, ENNReal.toReal_add hSumP hExtP, ENNReal.toReal_sum (fun K _ => hCP K)]
  have hNegReal : (D.formNeg q x.v x.G x.H).toReal
      = (∑ K, (cellNeg D K q x.v x.G x.H).toReal) + (extNeg D q x.v x.G x.H).toReal := by
    rw [hsN, ENNReal.toReal_add hSumN hExtN, ENNReal.toReal_sum (fun K _ => hCN K)]
  have hExtLe : (extNeg D q x.v x.G x.H).toReal ≤ (extPos D q x.v x.G x.H).toReal :=
    ENNReal.toReal_mono hExtP (hExt q hq x.v x.G x.H x.g x.perturbation).2
  have hFm := flipAverage_measurable x.right_measurable
  have hFp := flipAverage_periodic x.right_periodic
  have hF2 := flipAverage_finite x.right_measurable x.right_finite
  have hκ : 0 ≤ ∑ i, x.κ i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hcell : ∀ K, CellCert.CellFormula.quadFormValue (R.cellForm K)
        (cellState D.mesh K (R.layouts K) x.v x.G x.H Pg x.κ ζ (fun j => η (R.portKey K j)))
        + pairStrainSlack D K (R.pairSlackLabels K) (R.pairSlackWeight K) x.G + creditShare D R K x.v
      ≤ (cellPos D K q x.v x.G x.H).toReal - (cellNeg D K q x.v x.G x.H).toReal
        + (rowShare D K (flipAverage x.F) + pairShare D K R.pairLabels (R.pairProfile K) x.κ ζ x.G)
        + R.kappaCost K * ∑ i, x.κ i ^ 2 := by
    intro K
    exact real_le_of_cell_bound (hCP K) (hCN K) (hOff q hq x.v x.G x.H x.g x.perturbation K)
      (mul_nonneg (hk K) hκ)
      (hCell K q hq x.v x.G x.H x.g x.perturbation x.κ (flipAverage x.F) Pg hFm hFp hF2 hPg hPgFlip hSR ζ
        (fun j => η (R.portKey K j)))
  have hsum := Finset.sum_le_sum (fun K (_ : K ∈ Finset.univ) => hcell K)
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib] at hsum
  have hkap : ∑ K, R.kappaCost K * ∑ i, x.κ i ^ 2 = (∑ K, R.kappaCost K) * ∑ i, x.κ i ^ 2 :=
    (Finset.sum_mul _ _ _).symm
  have hkapE : (∑ K, R.kappaCost K) * ∑ i, x.κ i ^ 2 + ePair * ∑ i, x.κ i ^ 2 ≤ e * ∑ i, x.κ i ^ 2 := by
    rw [← add_mul]
    exact mul_le_mul_of_nonneg_right hE hκ
  have hrow := hRow q hq x
  have hpair := hPair q hq x ζ
  have hcred := hCredit q hq x Pg ζ η
  have hg := hG D.pinWeight 0 (fun i => multiplierRight (D.pieces q) x.v x.G x.H (D.cert.actuator i))
    (fun i => pinValue (D.cert.pin i) x.G) x.κ ζ ht
  rw [Finset.sum_add_distrib] at hg
  have h2 : ∑ i, 2 * ζ i * pinValue (D.cert.pin i) x.G = 2 * ∑ i, ζ i * pinValue (D.cert.pin i) x.G := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [h2] at hg
  have hT : 0 < 4 * Real.pi := by positivity
  have hgT := div_le_div_of_nonneg_right
    (show 2 * ∑ i, ζ i * pinValue (D.cert.pin i) x.G - ∑ i, ζ i ^ 2 / D.pinWeight
      ≤ D.pinWeight * ∑ i, pinValue (D.cert.pin i) x.G ^ 2 by linarith) hT.le
  have hz : ∑ i, ζ i ^ 2 / (4 * Real.pi * D.pinWeight) = (∑ i, ζ i ^ 2 / D.pinWeight) / (4 * Real.pi) := by
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun i _ => by rw [div_div, mul_comm (4 * Real.pi)]
  have hvec : vecNorm (fun i => pinValue (D.cert.pin i) x.G) ^ 2 = ∑ i, pinValue (D.cert.pin i) x.G ^ 2 := by
    unfold vecNorm
    exact Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)
  unfold initialStateValue globalForm AdmissibleTuple.value formValueWith CellLayerData.formScalarWith
  rw [hPosEq, hNegEq, hPosReal, hNegReal, hz, hvec]
  simp only [div_eq_mul_inv] at hgT hpair hrow ⊢
  linarith

theorem initialStateHolds_of_split (hS : FormSplitHolds) (hG : Coupling.GlobalLeafHolds) : InitialStateHolds := by
  intro k C nE nM D R hmesh ht _hmodel hc hN hCell hOff hExt hRow hCredit hk e ePair hPair hE
  exact initialStateBound_of_split hS hG D R hmesh ht hc hN hCell hOff hExt hRow hCredit e ePair hPair hE hk

theorem initialStateHolds_of_formSplit (hS : FormSplitHolds) : InitialStateHolds :=
  initialStateHolds_of_split hS Coupling.globalLeaf

end Assembly

end CertCell

end Breakdown
