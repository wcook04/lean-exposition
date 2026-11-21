import Breakdown.CertCell.Defs
import Breakdown.CertCell.BridgeStatements
import Breakdown.FracCell.GivenChartDefs
import Breakdown.CertCell.StatementDefs

open scoped ENNReal ComplexOrder
open MeasureTheory

noncomputable section

namespace Breakdown

namespace CertCell

open CellCert.CellAnalysis (CellBox IsCellBox)
open CellCert.GivenFields (ChartParams IsChartParams chartT heightRatio Spline TensorMesh IsTensorMesh
  cellCount atFirst atSecond tDeriv xDeriv)

namespace RowValues

variable {count rowCount : ℕ} (R : RowValues count rowCount)

def SameBlock (a b : Fin rowCount) : Prop :=
  R.cellOf a = R.cellOf b ∧ (R.labelOf a = R.labelOf b ∨ R.labelOf a = -R.labelOf b)

open Classical in
def testPairingMatrix (box : Fin count → CellBox) : Matrix (Fin rowCount) (Fin rowCount) ℝ := fun a b =>
  if R.SameBlock a b then
    2 * Real.pi * ∫ p in (box (R.cellOf a)).rect, p.1 *
      ((if R.labelOf a = R.labelOf b then
          rowPartFactor (R.realPart a) * starRingEnd ℂ (rowPartFactor (R.realPart b))
            * ∑ c : Fin 3, R.testValue box a c p * starRingEnd ℂ (R.testValue box b c p)
        else 0)
      + (if R.labelOf a = -R.labelOf b then
          rowPartFactor (R.realPart a) * rowPartFactor (R.realPart b)
            * ∑ c : Fin 3, R.testValue box a c p * R.testValue box b c p
        else 0)).re
  else 0

def upperMoment (box : Fin count → CellBox) (m : ℕ) (a : Fin rowCount) (F : ℝ → Space → Space) : ℝ :=
  2 * Real.pi * ∫ p in (box (R.cellOf a)).rect, p.1 *
    (rowPartFactor (R.realPart a) * ∑ c : Fin 3,
      starRingEnd ℂ (labelVel m (R.labelOf a) F p c) * R.testValue box a c p).re

def lowerMoment (box : Fin count → CellBox) (m : ℕ) (a : Fin rowCount) (F : ℝ → Space → Space) : ℝ :=
  2 * Real.pi * ∫ p in (box (R.cellOf a)).rect, p.1 *
    (rowPartFactor (R.realPart a) * ∑ c : Fin 3, (frameSign c : ℂ) *
      starRingEnd ℂ (labelVel m (labelFlip (R.labelOf a)) F (p.1, -p.2) c) * R.testValue box a c p).re

def cellMoment (box : Fin count → CellBox) (m : ℕ) (K : Fin count) (ι : ℤ × ℤ) (F : ℝ → Space → Space) :
    Fin (R.testCount K ι) → ℂ := fun i =>
  ∫ p in (box K).rect, (p.1 : ℂ) * ∑ c : Fin 3,
    labelVel m ι F p c * starRingEnd ℂ ((R.testField K ι i c).eval (box K) p)

end RowValues

namespace Instance

def GeneratorPairingMatrixFormula : Prop :=
  ∀ {rowCount : ℕ} (M : CellMesh) (R : RowValues M.count rowCount) (m : ℕ) (tauMax : ℝ), IsRowValues M R m tauMax →
    R.fieldPairingMatrix M.box m = R.testPairingMatrix M.box

def RowFieldsOrthonormal : Prop :=
  ∀ {rowCount : ℕ} (M : CellMesh) (R : RowValues M.count rowCount) (m : ℕ) (tauMax : ℝ), IsRowValues M R m tauMax →
    (R.fieldPairingMatrix M.box m).PosDef →
    ∀ a b, periodPairing (R.rowFieldOf M.box m a) (R.rowFieldOf M.box m b) =
      if a = b then 1 else 0

def GeneratorPairingMoments : Prop :=
  ∀ {rowCount : ℕ} (M : CellMesh) (R : RowValues M.count rowCount) (m : ℕ) (tauMax : ℝ), IsRowValues M R m tauMax →
    ∀ F : ℝ → Space → Space, AEStronglyMeasurable (fun z : ℝ × Space => F z.1 z.2) volume →
      IsTimePeriodic F → periodLIntegral (fun σ y => ‖F σ y‖ ^ 2) < ⊤ →
      ∀ a, periodPairing F (R.generatorField M.box m a) =
        R.upperMoment M.box m a F + R.lowerMoment M.box m a F

def RowNormIdentity : Prop :=
  ∀ {rowCount : ℕ} (M : CellMesh) (R : RowValues M.count rowCount) (m : ℕ) (tauMax c : ℝ), IsRowValues M R m tauMax → 0 < c →
    (R.fieldPairingMatrix M.box m).PosDef →
    ∀ F : ℝ → Space → Space, AEStronglyMeasurable (fun z : ℝ × Space => F z.1 z.2) volume →
      IsTimePeriodic F → periodLIntegral (fun σ y => ‖F σ y‖ ^ 2) < ⊤ →
      c * rowNorm (R.rowFieldOf M.box m) (R.rowWeightOf c) F ^ 2 =
        ∑ a, ∑ b, R.testWeight (R.cellOf a) (R.labelOf a) * (R.fieldPairingMatrix M.box m)⁻¹ a b
          * periodPairing F (R.generatorField M.box m a)
          * periodPairing F (R.generatorField M.box m b)

def RowPairingPosDef : Prop :=
  ∀ {rowCount : ℕ} (M : CellMesh) (R : RowValues M.count rowCount) (m : ℕ) (tauMax : ℝ), IsRowValues M R m tauMax →
    (R.testPairingMatrix M.box).PosDef

def RowsClassForm : Prop :=
  ∀ {rowCount : ℕ} (M : CellMesh) (R : RowValues M.count rowCount) (m : ℕ) (tauMax c : ℝ), IsRowValues M R m tauMax →
    0 < c → ∀ F : ℝ → Space → Space, AEStronglyMeasurable (fun z : ℝ × Space => F z.1 z.2) volume →
      IsTimePeriodic F → periodLIntegral (fun σ y => ‖F σ y‖ ^ 2) < ⊤ →
      (∀ σ y, F σ (flipPoint y) = flipPoint (F σ y)) →
      c * rowNorm (R.rowFieldOf M.box m) (R.rowWeightOf c) F ^ 2 =
        4 * Real.pi * ∑ K, ∑ ι ∈ M.tested K, R.testWeight K ι *
          (dotProduct (star (R.cellMoment M.box m K ι F)) (Matrix.mulVec (R.testBlockMatrix M.box K ι)⁻¹ (R.cellMoment M.box m K ι F))).re

theorem rowWeight_le_of_values {rowCount : ℕ} (M : CellMesh) (R : RowValues M.count rowCount)
    {m : ℕ} {tauMax c B : ℝ} (hR : IsRowValues M R m tauMax) (hc : 0 < c) (hB : tauMax / c ≤ B)
    (a : Fin rowCount) : R.rowWeightOf c a ≤ B :=
  (div_le_div_of_nonneg_right (hR.weight_le _ _ (hR.row_tested a)) hc.le).trans hB

theorem rowWeight_nonneg_of_values {rowCount : ℕ} (M : CellMesh) (R : RowValues M.count rowCount)
    {m : ℕ} {tauMax c : ℝ} (hR : IsRowValues M R m tauMax) (hc : 0 < c) (a : Fin rowCount) :
    0 ≤ R.rowWeightOf c a :=
  div_nonneg (hR.weight_pos _ _ (hR.row_tested a)).le hc.le


namespace ChartScalar

end ChartScalar

namespace StepDatum

end StepDatum

namespace WeightValues

variable {C : Type} {nE nM : ℕ} (W : WeightValues C nE nM)

end WeightValues

structure AdmissibleWeightClauses {C : Type} {nE nM : ℕ} (m : PieceWeights C nE nM) : Prop where
  finite_classes : Finite C
  c_pos : 0 < m.c
  c_lt_one : m.c < 1
  cμ_pos : 0 < m.cμ
  cμ_lt_one : m.cμ < 1
  eps_wt_nonneg : ∀ β y, 0 ≤ (m.epsP β).wt y
  mu_wt_nonneg : ∀ β y, 0 ≤ (m.muP β).wt y
  eps_slope_bound : ∀ β, ∃ K, LipschitzWith K (m.epsP β).wt
  mu_slope_bound : ∀ β, ∃ K, LipschitzWith K (m.muP β).wt
  eps_axi : ∀ β, IsAxisymmetric (m.epsP β).wt
  mu_axi : ∀ β, IsAxisymmetric (m.muP β).wt
  eps_decay : ∃ B, ∀ β y, ‖y‖ * (m.epsP β).wt y ≤ B
  mu_decay : ∃ B, ∀ β y, (m.muP β).wt y ≤ B ∧ ‖y‖ ^ 2 * (m.muP β).wt y ≤ B
    ∧ ‖y‖ * PieceWeights.wtGrad (m.muP β).wt y ≤ B
  eps_free_pos : ∀ β y, 0 < (m.epsP β).share1 y ∧ 0 < (m.epsP β).share2 y ∧ 0 < (m.epsP β).len y
    ∧ 0 < (m.epsP β).t0 y ∧ 0 < (m.epsP β).t1 y ∧ 0 < (m.epsP β).t2 y ∧ 0 < (m.epsP β).t3 y
    ∧ 0 < (m.epsP β).scale y
  mu_free_pos : ∀ β y, 0 < (m.muP β).share y ∧ 0 < (m.muP β).t4 y
  mu_eta_pos : ∀ β, 0 < (m.muP β).eta
  eps_free_measurable : ∀ β, Measurable (m.epsP β).share1 ∧ Measurable (m.epsP β).share2
    ∧ Measurable (m.epsP β).len ∧ Measurable (m.epsP β).t0 ∧ Measurable (m.epsP β).t1
    ∧ Measurable (m.epsP β).t2 ∧ Measurable (m.epsP β).t3 ∧ Measurable (m.epsP β).scale
  mu_free_measurable : ∀ β, Measurable (m.muP β).share ∧ Measurable (m.muP β).t4
  eps_free_axi : ∀ β, IsAxisymmetric (m.epsP β).share1 ∧ IsAxisymmetric (m.epsP β).share2
    ∧ IsAxisymmetric (m.epsP β).len ∧ IsAxisymmetric (m.epsP β).t0 ∧ IsAxisymmetric (m.epsP β).t1
    ∧ IsAxisymmetric (m.epsP β).t2 ∧ IsAxisymmetric (m.epsP β).t3 ∧ IsAxisymmetric (m.epsP β).scale
  mu_free_axi : ∀ β, IsAxisymmetric (m.muP β).share ∧ IsAxisymmetric (m.muP β).t4
  convD_even : ∀ ι y, m.convD (m.classOf (-ι)) y = m.convD (m.classOf ι) y
  convZ_even : ∀ ι y, m.convZ (m.classOf (-ι)) y = m.convZ (m.classOf ι) y
  convD_smooth : ∀ c, ContDiff ℝ 2 (m.convD c)
  convZ_smooth : ∀ c, ContDiff ℝ 2 (m.convZ c)
  convD_nonneg : ∀ c y, 0 ≤ m.convD c y
  convD_axi : ∀ c, IsAxisymmetric (m.convD c)
  convZ_axi : ∀ c, IsAxisymmetric (m.convZ c)
  convD_decay : ∃ B, ∀ c y, ∀ j ≤ 2, ‖y‖ ^ j * ‖iteratedFDeriv ℝ j (m.convD c) y‖ ≤ B
  convZ_decay : ∃ B, ∀ c y, ∀ j ≤ 2, (1 + ‖y‖) ^ j * ‖iteratedFDeriv ℝ j (m.convZ c) y‖ ≤ B

structure WeightFlipClauses {C : Type} {nE nM : ℕ} (m : PieceWeights C nE nM) : Prop where
  strain_flip : ∀ ξ y, m.convD (m.classOf (flipLabel ξ)) (flipPoint y) = m.convD (m.classOf ξ) y
  vorticity_flip : ∀ ξ y, m.convZ (m.classOf (flipLabel ξ)) (flipPoint y) = m.convZ (m.classOf ξ) y
  eps_mirror : ∃ π : Equiv.Perm (Fin nE), ∀ β,
    (m.epsP (π β)).modes = flipLabel '' (m.epsP β).modes ∧ (m.epsP (π β)).frame = -(m.epsP β).frame ∧
    ∀ y, (m.epsP (π β)).wt (flipPoint y) = (m.epsP β).wt y
      ∧ (m.epsP (π β)).speed (flipPoint y) = (m.epsP β).speed y
      ∧ (y 2 ≠ 0 → (m.epsP (π β)).share1 (flipPoint y) = (m.epsP β).share1 y
        ∧ (m.epsP (π β)).share2 (flipPoint y) = (m.epsP β).share2 y
        ∧ (m.epsP (π β)).len (flipPoint y) = (m.epsP β).len y
        ∧ (m.epsP (π β)).t0 (flipPoint y) = (m.epsP β).t0 y
        ∧ (m.epsP (π β)).t1 (flipPoint y) = (m.epsP β).t1 y
        ∧ (m.epsP (π β)).t2 (flipPoint y) = (m.epsP β).t2 y
        ∧ (m.epsP (π β)).t3 (flipPoint y) = (m.epsP β).t3 y
        ∧ (m.epsP (π β)).scale (flipPoint y) = (m.epsP β).scale y)
  mu_mirror : ∃ π : Equiv.Perm (Fin nM), ∀ β,
    (m.muP (π β)).modes = flipLabel '' (m.muP β).modes ∧ (m.muP (π β)).frame = -(m.muP β).frame ∧
    (m.muP (π β)).eta = (m.muP β).eta ∧
    ∀ y, (m.muP (π β)).wt (flipPoint y) = (m.muP β).wt y
      ∧ (m.muP (π β)).speed (flipPoint y) = (m.muP β).speed y
      ∧ (y 2 ≠ 0 → (m.muP (π β)).share (flipPoint y) = (m.muP β).share y
        ∧ (m.muP (π β)).t4 (flipPoint y) = (m.muP β).t4 y)

structure OtherFlipClauses {C : Type} {nE nM : ℕ} (m : PieceWeights C nE nM) (h : HarmonicBounds)
    (w : Space → ℝ) : Prop where
  weight_flip : ∀ y, w (flipPoint y) = w y
  harmonics_flip : ∀ β ∈ h.harmonics, flipLabel β ∈ h.harmonics
  amplitudes_flip : ∀ β y, h.ampW (flipLabel β) (flipPoint y) = h.ampW β y
    ∧ h.ampGradW (flipLabel β) (flipPoint y) = h.ampGradW β y
    ∧ h.ampVort (flipLabel β) (flipPoint y) = h.ampVort β y
    ∧ h.ampGradVort (flipLabel β) (flipPoint y) = h.ampGradVort β y
  sups_flip : ∀ y, h.supVort (flipPoint y) = h.supVort y ∧ h.supGradVort (flipPoint y) = h.supGradVort y
  amplitudes_axi : ∀ β φ y, h.ampW β (axialRot φ y) = h.ampW β y
    ∧ h.ampGradW β (axialRot φ y) = h.ampGradW β y
    ∧ h.ampVort β (axialRot φ y) = h.ampVort β y
    ∧ h.ampGradVort β (axialRot φ y) = h.ampGradVort β y
  sups_axi : ∀ φ y, h.supVort (axialRot φ y) = h.supVort y ∧ h.supGradVort (axialRot φ y) = h.supGradVort y
  eps_speed_axi : ∀ β, IsAxisymmetric (m.epsP β).speed
  mu_speed_axi : ∀ β, IsAxisymmetric (m.muP β).speed

theorem isFlipCompatible_of_parts {C : Type} {nE nM : ℕ} {m : PieceWeights C nE nM} {h : HarmonicBounds}
    {w : Space → ℝ} (hw : WeightFlipClauses m) (ho : OtherFlipClauses m h w) : Bridge.IsFlipCompatible m h w where
  strain_flip := hw.strain_flip
  vorticity_flip := hw.vorticity_flip
  weight_flip := ho.weight_flip
  eps_mirror := hw.eps_mirror
  mu_mirror := hw.mu_mirror
  harmonics_flip := ho.harmonics_flip
  amplitudes_flip := ho.amplitudes_flip
  sups_flip := ho.sups_flip
  amplitudes_axi := ho.amplitudes_axi
  sups_axi := ho.sups_axi
  eps_speed_axi := ho.eps_speed_axi
  mu_speed_axi := ho.mu_speed_axi

structure OtherAdmissibleClauses {C : Type} {nE nM : ℕ} (m : PieceWeights C nE nM) (P : ℝ) (h : HarmonicBounds)
    (w : Space → ℝ) (W : ℝ → Space → Space) (HW : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space))
    (w₀ epsSup epsGradSup ratio : ℝ) : Prop where
  period_pos : 0 < P
  weight_pos : 0 < w₀
  weight_lower : ∀ y, w₀ ≤ w y
  weight_measurable : Measurable w
  weight_axi : IsAxisymmetric w
  harmonics_neg : ∀ β ∈ h.harmonics, -β ∈ h.harmonics
  harmonics_zero : (0, 0) ∈ h.harmonics
  harmonics_span : ∀ σ y i, W σ y i = ∑ β ∈ h.harmonics, (modeVel β W σ y i).re
  ampW_ge : ∀ β ∈ h.harmonics, ∀ σ y, Real.sqrt (cnormSq (modeVel β W σ y)) ≤ h.ampW β y
  ampGradW_ge : ∀ β ∈ h.harmonics, ∀ σ y,
    Real.sqrt (cnormSq (modeGrad β (gradField W) σ y)) ≤ h.ampGradW β y
  ampVort_ge : ∀ β ∈ h.harmonics, ∀ σ y,
    Real.sqrt (cnormSq (curlOfGrad (modeGrad β (gradField W) σ y))) ≤ h.ampVort β y
  ampGradVort_ge : ∀ β ∈ h.harmonics, ∀ σ y,
    Real.sqrt (cnormSq (curlGradOfSecondDeriv (modeSecondDeriv β HW σ y))) ≤ h.ampGradVort β y
  supVort_ge : ∀ σ φ y, ‖curlVec (fderiv ℝ (W σ) (axialRot φ y))‖ ≤ h.supVort y
  supGradVort_ge : ∀ σ φ y, ‖CoerciveWeak.vortGradMap (HW σ (axialRot φ y))‖ ≤ h.supGradVort y
  epsSpeed_ge : ∀ β σ φ y, ‖W σ (axialRot φ y) + (1 / 2 : ℝ) • axialRot φ y
    - (m.epsP β).frame • (-(axialRot φ y 1) • unitVector 0 + axialRot φ y 0 • unitVector 1)‖
      ≤ (m.epsP β).speed y
  muSpeed_ge : ∀ β σ φ y, ‖W σ (axialRot φ y) + (1 / 2 : ℝ) • axialRot φ y
    - (m.muP β).frame • (-(axialRot φ y 1) • unitVector 0 + axialRot φ y 0 • unitVector 1)‖
      ≤ (m.muP β).speed y
  eps_oneSided : ∀ β, ∃ Ωs > 0, ∀ ι ∈ (m.epsP β).modes, Ωs ≤ PieceWeights.frameFreq P (m.epsP β).frame ι
  mu_oneSided : ∀ β, ∃ Ωs > 0, ∀ ι ∈ (m.muP β).modes, Ωs ≤ PieceWeights.frameFreq P (m.muP β).frame ι
  mu_ratio : ∀ y ι, (∑ β : Fin nM, |PieceWeights.sgn (m.muP β).modes ι| * (m.muP β).wt y) ^ 2
    ≤ ratio * ∑ β : Fin nM, |PieceWeights.sgn (m.muP β).modes ι| * |PieceWeights.frameFreq P (m.muP β).frame ι|
      * (m.muP β).wt y
  ratio_nonneg : 0 ≤ ratio
  eps_sum_le : ∀ y, ∑ β : Fin nE, (m.epsP β).wt y ≤ epsSup
  eps_grad_sum_le : ∀ y, ∑ β : Fin nE, PieceWeights.wtGrad (m.epsP β).wt y ≤ epsGradSup
  conv_le : ∀ ι y, m.convD (m.classOf ι) y ≤ 1 - m.shareHat h ι y

theorem isAdmissibleWeak_of_parts {C : Type} {nE nM : ℕ} {m : PieceWeights C nE nM} {P : ℝ}
    {h : HarmonicBounds} {w : Space → ℝ} {W : ℝ → Space → Space}
    {HW : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)} {w₀ epsSup epsGradSup ratio : ℝ}
    (ha : AdmissibleWeightClauses m) (ho : OtherAdmissibleClauses m P h w W HW w₀ epsSup epsGradSup ratio) :
    CoerciveWeak.IsAdmissibleWeak m P h w W HW w₀ epsSup epsGradSup ratio where
  finite_classes := ha.finite_classes
  c_pos := ha.c_pos
  c_lt_one := ha.c_lt_one
  cμ_pos := ha.cμ_pos
  cμ_lt_one := ha.cμ_lt_one
  period_pos := ho.period_pos
  weight_pos := ho.weight_pos
  weight_lower := ho.weight_lower
  weight_measurable := ho.weight_measurable
  weight_axi := ho.weight_axi
  harmonics_neg := ho.harmonics_neg
  harmonics_zero := ho.harmonics_zero
  harmonics_span := ho.harmonics_span
  ampW_ge := ho.ampW_ge
  ampGradW_ge := ho.ampGradW_ge
  ampVort_ge := ho.ampVort_ge
  ampGradVort_ge := ho.ampGradVort_ge
  supVort_ge := ho.supVort_ge
  supGradVort_ge := ho.supGradVort_ge
  epsSpeed_ge := ho.epsSpeed_ge
  muSpeed_ge := ho.muSpeed_ge
  eps_oneSided := ho.eps_oneSided
  mu_oneSided := ho.mu_oneSided
  mu_ratio := ho.mu_ratio
  ratio_nonneg := ho.ratio_nonneg
  eps_wt_nonneg := ha.eps_wt_nonneg
  mu_wt_nonneg := ha.mu_wt_nonneg
  eps_increment := ha.eps_slope_bound
  mu_increment := ha.mu_slope_bound
  eps_axi := ha.eps_axi
  mu_axi := ha.mu_axi
  eps_sum_le := ho.eps_sum_le
  eps_grad_sum_le := ho.eps_grad_sum_le
  eps_decay := ha.eps_decay
  mu_decay := ha.mu_decay
  eps_free_pos := ha.eps_free_pos
  mu_free_pos := ha.mu_free_pos
  mu_eta_pos := ha.mu_eta_pos
  eps_free_measurable := ha.eps_free_measurable
  mu_free_measurable := ha.mu_free_measurable
  eps_free_axi := ha.eps_free_axi
  mu_free_axi := ha.mu_free_axi
  convD_even := ha.convD_even
  convZ_even := ha.convZ_even
  convD_smooth := ha.convD_smooth
  convZ_smooth := ha.convZ_smooth
  convD_nonneg := ha.convD_nonneg
  convD_axi := ha.convD_axi
  convZ_axi := ha.convZ_axi
  convD_decay := ha.convD_decay
  convZ_decay := ha.convZ_decay
  conv_le := ho.conv_le

def ScalarSmoothOfJoins : Prop :=
  ∀ (P : ChartParams) (S : ChartScalar) (tStar : ℝ), IsChartParams P → IsJoinedScalar 2 S →
    IsConstantCore tStar S → S.decay = 0 → ContDiff ℝ 2 (S.eval P)

def ScalarDerivativeDecay : Prop :=
  ∀ (P : ChartParams) (S : ChartScalar) (tStar : ℝ), IsChartParams P → IsJoinedScalar 2 S →
    IsConstantCore tStar S → S.decay = 0 → ∃ B, ∀ y, ∀ j ≤ 2, (1 + ‖y‖) ^ j * ‖iteratedFDeriv ℝ j (S.eval P) y‖ ≤ B

def ScalarSlopeBoundOfJoins : Prop :=
  ∀ (P : ChartParams) (S : ChartScalar), IsChartParams P → IsJoinedScalar 0 S → IsFlatAtOrigin S →
    ∃ K, LipschitzWith K (S.eval P)

def ScalarRateOfDecay : Prop :=
  ∀ (P : ChartParams) (S : ChartScalar), IsChartParams P → IsJoinedScalar 0 S → IsFlatAtOrigin S →
    ∃ B, ∀ y, |S.eval P y| ≤ B ∧ ‖y‖ ^ S.decay * |S.eval P y| ≤ B ∧
      ‖y‖ * PieceWeights.wtGrad (S.eval P) y ≤ B

def ScalarBasicFacts : Prop :=
  ∀ (P : ChartParams) (S : ChartScalar), IsChartParams P →
    Measurable (S.eval P) ∧ IsAxisymmetric (S.eval P) ∧ (HasNonnegValues S → ∀ y, 0 ≤ S.eval P y)

def StepBasicFacts : Prop :=
  ∀ (P : ChartParams) (S : StepDatum), IsChartParams P →
    Measurable (S.eval P) ∧ IsAxisymmetric (S.eval P) ∧ (IsPositiveStep S → ∀ y, 0 < S.eval P y)

def MirrorEval : Prop :=
  ∀ (P : ChartParams), IsChartParams P →
    (∀ (S : ChartScalar), IsJoinedScalar 0 S → ∀ y, S.mirror.eval P (flipPoint y) = S.eval P y) ∧
    (∀ (S : StepDatum) y, y 2 ≠ 0 → S.mirror.eval P (flipPoint y) = S.eval P y)

theorem weightClauses_of_values (hsm : ScalarSmoothOfJoins) (hdec : ScalarDerivativeDecay)
    (hlip : ScalarSlopeBoundOfJoins) (hrate : ScalarRateOfDecay) (hbas : ScalarBasicFacts)
    (hstep : StepBasicFacts) {C : Type} {nE nM : ℕ} (W : WeightValues C nE nM) (hW : IsWeightValues W)
    (epsFrame : Fin nE → ℝ) (muFrame : Fin nM → ℝ) (epsSpeed : Fin nE → Space → ℝ)
    (muSpeed : Fin nM → Space → ℝ) :
    AdmissibleWeightClauses (W.pieces epsFrame muFrame epsSpeed muSpeed) := by
  have le_sum_abs_of : ∀ {ι : Type} [Fintype ι] (B : ι → ℝ) (i : ι), B i ≤ ∑ j, |B j| :=
    fun B i => (le_abs_self _).trans
      (Finset.single_le_sum (f := fun j => |B j|) (fun _ _ => abs_nonneg _) (Finset.mem_univ i))
  have hP := hW.chart_valid
  have : Finite C := hW.classes_finite
  have : Fintype C := Fintype.ofFinite C
  have hsc := fun S : ChartScalar => hbas W.chart S hP
  have hst := fun S : StepDatum => hstep W.chart S hP
  choose Be hBe using fun β => hrate W.chart (W.eps β).weight hP (hW.eps_joined β) (hW.eps_flat β)
  choose Bm hBm using fun β => hrate W.chart (W.mu β).weight hP (hW.mu_joined β) (hW.mu_flat β)
  choose Bd hBd using fun c => hdec W.chart (W.strainWeight c) W.centralRadius hP (hW.strain_joined c)
    (hW.strain_core c) (hW.strain_decay c)
  choose Bz hBz using fun c => hdec W.chart (W.vorticityWeight c) W.centralRadius hP (hW.vorticity_joined c)
    (hW.vorticity_core c) (hW.vorticity_decay c)
  exact
  { finite_classes := hW.classes_finite
    c_pos := hW.c_pos
    c_lt_one := hW.c_lt_one
    cμ_pos := hW.cμ_pos
    cμ_lt_one := hW.cμ_lt_one
    eps_wt_nonneg := fun β y => (hsc _).2.2 (hW.eps_nonneg β) y
    mu_wt_nonneg := fun β y => (hsc _).2.2 (hW.mu_nonneg β) y
    eps_slope_bound := fun β => hlip W.chart _ hP (hW.eps_joined β) (hW.eps_flat β)
    mu_slope_bound := fun β => hlip W.chart _ hP (hW.mu_joined β) (hW.mu_flat β)
    eps_axi := fun β => (hsc _).2.1
    mu_axi := fun β => (hsc _).2.1
    eps_decay := by
      refine ⟨∑ j, |Be j|, fun β y => ?_⟩
      have h1 := (hBe β y).2.1
      rw [hW.eps_decay β, pow_one] at h1
      have h2 : ‖y‖ * (W.eps β).weight.eval W.chart y ≤ ‖y‖ * |(W.eps β).weight.eval W.chart y| :=
        mul_le_mul_of_nonneg_left (le_abs_self _) (norm_nonneg _)
      exact h2.trans (h1.trans (le_sum_abs_of Be β))
    mu_decay := by
      refine ⟨∑ j, |Bm j|, fun β y => ⟨?_, ?_, ?_⟩⟩
      · exact (le_abs_self _).trans ((hBm β y).1.trans (le_sum_abs_of Bm β))
      · have h1 := (hBm β y).2.1
        rw [hW.mu_decay β] at h1
        have h2 : ‖y‖ ^ 2 * (W.mu β).weight.eval W.chart y ≤ ‖y‖ ^ 2 * |(W.mu β).weight.eval W.chart y| :=
          mul_le_mul_of_nonneg_left (le_abs_self _) (by positivity)
        exact h2.trans (h1.trans (le_sum_abs_of Bm β))
      · exact (hBm β y).2.2.trans (le_sum_abs_of Bm β)
    eps_free_pos := fun β y => by
      obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hW.eps_steps β
      exact ⟨(hst _).2.2 h1 y, (hst _).2.2 h2 y, (hst _).2.2 h3 y, (hst _).2.2 h4 y, (hst _).2.2 h5 y,
        (hst _).2.2 h6 y, (hst _).2.2 h7 y, (hst _).2.2 h8 y⟩
    mu_free_pos := fun β y => ⟨(hst _).2.2 (hW.mu_steps β).1 y, (hst _).2.2 (hW.mu_steps β).2 y⟩
    mu_eta_pos := hW.mu_eta_pos
    eps_free_measurable := fun β => ⟨(hst _).1, (hst _).1, (hst _).1, (hst _).1, (hst _).1, (hst _).1,
      (hst _).1, (hst _).1⟩
    mu_free_measurable := fun β => ⟨(hst _).1, (hst _).1⟩
    eps_free_axi := fun β => ⟨(hst _).2.1, (hst _).2.1, (hst _).2.1, (hst _).2.1, (hst _).2.1, (hst _).2.1,
      (hst _).2.1, (hst _).2.1⟩
    mu_free_axi := fun β => ⟨(hst _).2.1, (hst _).2.1⟩
    convD_even := fun ι y => by
      show (W.strainWeight (W.classOf (-ι))).eval W.chart y = (W.strainWeight (W.classOf ι)).eval W.chart y
      rw [(hW.class_neg ι).1]
    convZ_even := fun ι y => by
      show (W.vorticityWeight (W.classOf (-ι))).eval W.chart y
        = (W.vorticityWeight (W.classOf ι)).eval W.chart y
      rw [(hW.class_neg ι).2]
    convD_smooth := fun c => hsm W.chart _ W.centralRadius hP (hW.strain_joined c) (hW.strain_core c)
      (hW.strain_decay c)
    convZ_smooth := fun c => hsm W.chart _ W.centralRadius hP (hW.vorticity_joined c) (hW.vorticity_core c)
      (hW.vorticity_decay c)
    convD_nonneg := fun c y => (hsc _).2.2 (hW.strain_nonneg c) y
    convD_axi := fun c => (hsc _).2.1
    convZ_axi := fun c => (hsc _).2.1
    convD_decay := by
      refine ⟨∑ c, |Bd c|, fun c y j hj => ?_⟩
      have h1 : ‖y‖ ^ j ≤ (1 + ‖y‖) ^ j := pow_le_pow_left₀ (norm_nonneg _) (by linarith [norm_nonneg y]) j
      exact (mul_le_mul_of_nonneg_right h1 (norm_nonneg _)).trans
        ((hBd c y j hj).trans (le_sum_abs_of Bd c))
    convZ_decay := ⟨∑ c, |Bz c|, fun c y j hj => (hBz c y j hj).trans (le_sum_abs_of Bz c)⟩ }

theorem weightsFlip_of_values (hmir : MirrorEval) {C : Type} {nE nM : ℕ} (W : WeightValues C nE nM)
    (hW : IsWeightValues W) (epsMirror : Equiv.Perm (Fin nE)) (muMirror : Equiv.Perm (Fin nM))
    (hF : IsFlipClosedValues W epsMirror muMirror) (epsFrame : Fin nE → ℝ) (muFrame : Fin nM → ℝ)
    (epsSpeed : Fin nE → Space → ℝ) (muSpeed : Fin nM → Space → ℝ)
    (hef : ∀ β, epsFrame (epsMirror β) = -epsFrame β) (hmf : ∀ β, muFrame (muMirror β) = -muFrame β)
    (hes : ∀ β y, epsSpeed (epsMirror β) (flipPoint y) = epsSpeed β y)
    (hms : ∀ β y, muSpeed (muMirror β) (flipPoint y) = muSpeed β y) :
    WeightFlipClauses (W.pieces epsFrame muFrame epsSpeed muSpeed) := by
  have hjoin : ∀ {S : ChartScalar}, IsJoinedScalar 2 S → IsJoinedScalar 0 S := by
    intro S h
    have hmono : ∀ {T : Spline}, SplineJoins 2 T → SplineJoins 0 T := fun hT =>
      { mesh := hT.mesh
        t_joins := fun i hi hi' j hj o ho => hT.t_joins i hi hi' j hj o (ho.trans (Nat.zero_le _))
        x_joins := fun j hj hj' i hi o ho => hT.x_joins j hj hj' i hi o (ho.trans (Nat.zero_le _)) }
    exact
      { upper := hmono h.upper
        lower := hmono h.lower
        same_t := h.same_t
        plane_joins := fun i hi o ho => h.plane_joins i hi o (ho.trans (Nat.zero_le _)) }
  have hM := hmir W.chart hW.chart_valid
  refine ⟨fun ξ y => ?_, fun ξ y => ?_, ⟨epsMirror, fun β => ⟨?_, hef β, fun y => ⟨?_, hes β y, fun hy => ?_⟩⟩⟩,
    ⟨muMirror, fun β => ⟨?_, hmf β, ?_, fun y => ⟨?_, hms β y, fun hy => ?_⟩⟩⟩⟩
  · show (W.strainWeight (W.classOf (flipLabel ξ))).eval W.chart (flipPoint y)
      = (W.strainWeight (W.classOf ξ)).eval W.chart y
    rw [hF.strain_flip ξ]
    exact hM.1 _ (hjoin (hW.strain_joined _)) y
  · show (W.vorticityWeight (W.classOf (flipLabel ξ))).eval W.chart (flipPoint y)
      = (W.vorticityWeight (W.classOf ξ)).eval W.chart y
    rw [hF.vorticity_flip ξ]
    exact hM.1 _ (hjoin (hW.vorticity_joined _)) y
  · show (W.eps (epsMirror β)).modes = flipLabel '' (W.eps β).modes
    rw [hF.eps_flip β]
    rfl
  · show (W.eps (epsMirror β)).weight.eval W.chart (flipPoint y) = (W.eps β).weight.eval W.chart y
    rw [hF.eps_flip β]
    exact hM.1 _ (hW.eps_joined β) y
  · show (W.eps (epsMirror β)).share1.eval W.chart (flipPoint y) = (W.eps β).share1.eval W.chart y
      ∧ (W.eps (epsMirror β)).share2.eval W.chart (flipPoint y) = (W.eps β).share2.eval W.chart y
      ∧ (W.eps (epsMirror β)).len.eval W.chart (flipPoint y) = (W.eps β).len.eval W.chart y
      ∧ (W.eps (epsMirror β)).t0.eval W.chart (flipPoint y) = (W.eps β).t0.eval W.chart y
      ∧ (W.eps (epsMirror β)).t1.eval W.chart (flipPoint y) = (W.eps β).t1.eval W.chart y
      ∧ (W.eps (epsMirror β)).t2.eval W.chart (flipPoint y) = (W.eps β).t2.eval W.chart y
      ∧ (W.eps (epsMirror β)).t3.eval W.chart (flipPoint y) = (W.eps β).t3.eval W.chart y
      ∧ (W.eps (epsMirror β)).scale.eval W.chart (flipPoint y) = (W.eps β).scale.eval W.chart y
    rw [hF.eps_flip β]
    exact ⟨hM.2 _ y hy, hM.2 _ y hy, hM.2 _ y hy, hM.2 _ y hy, hM.2 _ y hy, hM.2 _ y hy, hM.2 _ y hy,
      hM.2 _ y hy⟩
  · show (W.mu (muMirror β)).modes = flipLabel '' (W.mu β).modes
    rw [hF.mu_flip β]
    rfl
  · show (W.mu (muMirror β)).eta = (W.mu β).eta
    rw [hF.mu_flip β]
    rfl
  · show (W.mu (muMirror β)).weight.eval W.chart (flipPoint y) = (W.mu β).weight.eval W.chart y
    rw [hF.mu_flip β]
    exact hM.1 _ (hW.mu_joined β) y
  · show (W.mu (muMirror β)).share.eval W.chart (flipPoint y) = (W.mu β).share.eval W.chart y
      ∧ (W.mu (muMirror β)).t4.eval W.chart (flipPoint y) = (W.mu β).t4.eval W.chart y
    rw [hF.mu_flip β]
    exact ⟨hM.2 _ y hy, hM.2 _ y hy⟩

theorem weightInstance_clauses (hsm : ScalarSmoothOfJoins) (hdec : ScalarDerivativeDecay)
    (hlip : ScalarSlopeBoundOfJoins) (hrate : ScalarRateOfDecay) (hbas : ScalarBasicFacts)
    (hstep : StepBasicFacts) (hmir : MirrorEval) {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM)
    (W : WeightValues C nE nM) (epsFrame : (Fin k → ℝ) → Fin nE → ℝ) (muFrame : (Fin k → ℝ) → Fin nM → ℝ)
    (epsSpeed : Fin nE → Space → ℝ) (muSpeed : Fin nM → Space → ℝ)
    (epsMirror : Equiv.Perm (Fin nE)) (muMirror : Equiv.Perm (Fin nM))
    (h : IsWeightInstance D W epsFrame muFrame epsSpeed muSpeed epsMirror muMirror) :
    ∀ q ∈ D.cert.params, AdmissibleWeightClauses (D.pieces q) ∧ WeightFlipClauses (D.pieces q) ∧
      (D.pieces q).c = D.coercivity := by
  intro q hq
  rw [h.pieces_eq q hq]
  exact ⟨weightClauses_of_values hsm hdec hlip hrate hbas hstep W h.values _ _ _ _,
    weightsFlip_of_values hmir W h.values epsMirror muMirror h.flip _ _ _ _ (h.eps_frame_flip q)
      (h.mu_frame_flip q) h.eps_speed_flip h.mu_speed_flip, h.c_eq⟩

theorem constantWeight_clauses (w₀ : ℝ) (h : 0 < w₀) :
    0 < w₀ ∧ (∀ y : Space, w₀ ≤ (fun _ => w₀) y) ∧ Measurable (fun _ : Space => w₀) ∧
      IsAxisymmetric (fun _ : Space => w₀) :=
  ⟨h, fun _ => le_rfl, measurable_const, fun _ _ => rfl⟩



def CellVecFieldRegular : Prop :=
  ∀ (M : CellMesh) (F : CellVecField M.count) (m : ℕ), IsCellMesh M →
    AEStronglyMeasurable (fun z : ℝ × Space => F.field M.box m z.1 z.2) volume ∧
    IsTimePeriodic (F.field M.box m) ∧
    (∃ B R : ℝ, ∀ σ y, ‖F.field M.box m σ y‖ ≤ B ∧ (R < ‖y‖ → F.field M.box m σ y = 0)) ∧
    periodLIntegral (fun σ y => ‖F.field M.box m σ y‖ ^ 2) < ⊤

def CellMatFieldRegular : Prop :=
  ∀ (M : CellMesh) (F : CellMatField M.count) (m : ℕ), IsCellMesh M →
    AEStronglyMeasurable (fun z : ℝ × Space => F.field M.box m z.1 z.2) volume ∧
    IsTimePeriodic (F.field M.box m) ∧
    (∃ B R : ℝ, ∀ σ y, ‖F.field M.box m σ y‖ ≤ B ∧ (R < ‖y‖ → F.field M.box m σ y = 0)) ∧
    periodLIntegral (fun σ y => matSq (F.field M.box m σ y)) < ⊤

structure ActuatorFacts {C : Type} {nE nM : ℕ} (w : PieceWeights C nE nM) (b : ℝ → Space → Space) : Prop where
  measurable : AEStronglyMeasurable (fun z : ℝ × Space => b z.1 z.2) volume
  periodic : IsTimePeriodic b
  bounded_support : ∃ B R : ℝ, ∀ σ y, ‖b σ y‖ ≤ B ∧ (R < ‖y‖ → b σ y = 0)
  square_finite : periodLIntegral (fun σ y => ‖b σ y‖ ^ 2) < ⊤
  gradient_measurable : AEStronglyMeasurable (fun z : ℝ × Space => gradField b z.1 z.2) volume
  gradient_periodic : IsTimePeriodic (gradField b)
  gradient_finite : periodLIntegral (fun σ y => matSq (gradField b σ y)) < ⊤
  weak_gradient : ∀ σ, IsWeakGradient (b σ) (gradField b σ)
  finite_modes : ∃ S : Finset (ℤ × ℤ), ∀ ξ ∉ S, ∀ σ y, (pointPlane y).1 ≠ 0 → modeVel ξ b σ y = 0
  mu_free : ∀ β ξ, (∃ σ y, (pointPlane y).1 ≠ 0 ∧ modeVel ξ b σ y ≠ 0) →
    ¬ PieceWeights.inPiece (w.muP β).modes ξ
  eps_vanish : ∀ β ξ, (∃ σ y, (pointPlane y).1 ≠ 0 ∧ modeVel ξ b σ y ≠ 0) →
    PieceWeights.inPiece (w.epsP β).modes ξ →
    ∀ y, (∃ σ, b σ y ≠ 0) → (w.epsP β).wt y = 0

theorem actuatorInvariant_of_shape {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM)
    (modes : Fin k → Finset (ℤ × ℤ)) (hfmt : ∀ i, ActuatorShapeFacts D.azimuthOrder (modes i) (D.cert.actuator i))
    (hgen : GeneratedByClassSymmetries D) :
    ∀ i, ∀ γ ∈ D.cert.symmetries, ∀ᵐ z : ℝ × Space,
      D.cert.actuator i (z.1 + γ.2) (γ.1 z.2) = γ.1 (D.cert.actuator i z.1 z.2) := by
  have r0 : ∀ (φ : ℝ) (y : Space), axialRot φ y 0 = Real.cos φ * y 0 - Real.sin φ * y 1 := by
    intro φ y
    simp [axialRot, unitVector]
  have r1 : ∀ (φ : ℝ) (y : Space), axialRot φ y 1 = Real.sin φ * y 0 + Real.cos φ * y 1 := by
    intro φ y
    simp [axialRot, unitVector]
  have r2 : ∀ (φ : ℝ) (y : Space), axialRot φ y 2 = y 2 := by
    intro φ y
    simp [axialRot, unitVector]
  have f0 : ∀ y : Space, flipPoint y 0 = y 0 := by
    intro y
    simp [flipPoint, unitVector]
  have f1 : ∀ y : Space, flipPoint y 1 = -y 1 := by
    intro y
    simp [flipPoint, unitVector]
  have f2 : ∀ y : Space, flipPoint y 2 = -y 2 := by
    intro y
    simp [flipPoint, unitVector]
  have pt : ∀ {u v : Space}, u 0 = v 0 → u 1 = v 1 → u 2 = v 2 → u = v := by
    intro u v h0 h1 h2
    ext j
    fin_cases j
    · exact h0
    · exact h1
    · exact h2
  have hcomp : ∀ (α β : ℝ) (y : Space), axialRot α (axialRot β y) = axialRot (α + β) y := by
    intro α β y
    refine pt ?_ ?_ ?_
    · simp only [r0, r1, Real.cos_add, Real.sin_add]
      ring
    · simp only [r0, r1, Real.cos_add, Real.sin_add]
      ring
    · simp only [r2]
  have hzero : ∀ y : Space, axialRot 0 y = y := by
    intro y
    refine pt ?_ ?_ ?_
    · simp [r0]
    · simp [r1]
    · simp [r2]
  have hrotmp : ∀ φ : ℝ, MeasurePreserving (axialRot φ) (volume : Measure Space) volume := by
    intro φ
    let L : Space ≃ₗᵢ[ℝ] Space :=
      { toFun := axialRot φ
        invFun := axialRot (-φ)
        map_add' := fun u v => pt (by simp only [r0, PiLp.add_apply]; ring)
          (by simp only [r1, PiLp.add_apply]; ring) (by simp only [r2, PiLp.add_apply])
        map_smul' := fun c u => pt (by simp only [r0, PiLp.smul_apply, smul_eq_mul, RingHom.id_apply]; ring)
          (by simp only [r1, PiLp.smul_apply, smul_eq_mul, RingHom.id_apply]; ring)
          (by simp only [r2, PiLp.smul_apply, smul_eq_mul, RingHom.id_apply])
        left_inv := fun y => by rw [hcomp, neg_add_cancel, hzero]
        right_inv := fun y => by rw [hcomp, add_neg_cancel, hzero]
        norm_map' := fun y => by
          show ‖axialRot φ y‖ = ‖y‖
          rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
          congr 1
          simp only [Fin.sum_univ_three, Real.norm_eq_abs, sq_abs, r0, r1, r2]
          linear_combination (y 0 ^ 2 + y 1 ^ 2) * Real.sin_sq_add_cos_sq φ }
    show MeasurePreserving (L : Space → Space) volume volume
    exact L.measurePreserving
  have hflipmp : MeasurePreserving flipPoint (volume : Measure Space) volume := by
    let L : Space ≃ₗᵢ[ℝ] Space :=
      { toFun := flipPoint
        invFun := flipPoint
        map_add' := fun u v => pt (by simp only [f0, PiLp.add_apply])
          (by simp only [f1, PiLp.add_apply]; ring) (by simp only [f2, PiLp.add_apply]; ring)
        map_smul' := fun c u => pt (by simp only [f0, PiLp.smul_apply, smul_eq_mul, RingHom.id_apply])
          (by simp only [f1, PiLp.smul_apply, smul_eq_mul, RingHom.id_apply]; ring)
          (by simp only [f2, PiLp.smul_apply, smul_eq_mul, RingHom.id_apply]; ring)
        left_inv := fun y => pt (by rw [f0, f0]) (by rw [f1, f1, neg_neg]) (by rw [f2, f2, neg_neg])
        right_inv := fun y => pt (by rw [f0, f0]) (by rw [f1, f1, neg_neg]) (by rw [f2, f2, neg_neg])
        norm_map' := fun y => by
          show ‖flipPoint y‖ = ‖y‖
          rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
          congr 1
          simp only [Fin.sum_univ_three, Real.norm_eq_abs, sq_abs, f0, f1, f2, neg_sq] }
    show MeasurePreserving (L : Space → Space) volume volume
    exact L.measurePreserving
  have hqrot : ∀ c φ : ℝ,
      Measure.QuasiMeasurePreserving (fun z : ℝ × Space => (z.1 + c, axialRot φ z.2)) volume volume := by
    intro c φ
    have h := (measurePreserving_add_right (volume : Measure ℝ) c).prod (hrotmp φ)
    rw [← Measure.volume_eq_prod ℝ Space] at h
    exact h.quasiMeasurePreserving
  have hqflip :
      Measure.QuasiMeasurePreserving (fun z : ℝ × Space => (z.1, flipPoint z.2)) volume volume := by
    have h := (MeasurePreserving.id (volume : Measure ℝ)).prod hflipmp
    rw [← Measure.volume_eq_prod ℝ Space] at h
    exact h.quasiMeasurePreserving
  have hshift : ∀ {f : ℝ → Space → Space}, IsTimePeriodic f → ∀ (j : ℤ) σ y, f (σ + j) y = f σ y := by
    intro f hf j
    refine Int.induction_on j ?_ ?_ ?_
    · intro σ y
      simp
    · intro n ih σ y
      have e : σ + ((n + 1 : ℤ) : ℝ) = (σ + ((n : ℤ) : ℝ)) + 1 := by
        push_cast
        ring
      rw [e, hf, ih]
    · intro n ih σ y
      have h1 := hf (σ + ((-(n : ℤ) - 1 : ℤ) : ℝ)) y
      have e : σ + ((-(n : ℤ) - 1 : ℤ) : ℝ) + 1 = σ + ((-(n : ℤ) : ℤ) : ℝ) := by
        push_cast
        ring
      rw [e, ih] at h1
      exact h1.symm
  have hiter : ∀ (f : ℝ → Space → Space) (θ : ℝ),
      (∀ᵐ z : ℝ × Space, f (z.1 + 1 / 2) (axialRot θ z.2) = axialRot θ (f z.1 z.2)) → ∀ a : ℕ,
      ∀ᵐ z : ℝ × Space, f (z.1 + (a : ℝ) / 2) (axialRot ((a : ℝ) * θ) z.2)
        = axialRot ((a : ℝ) * θ) (f z.1 z.2) := by
    intro f θ hinv a
    induction a with
    | zero =>
      filter_upwards with z
      simp [hzero]
    | succ n ih =>
      have h1 := (hqrot (1 / 2) θ).ae ih
      filter_upwards [h1, hinv] with z h1 h2
      have e1 : z.1 + ((n + 1 : ℕ) : ℝ) / 2 = z.1 + 1 / 2 + (n : ℝ) / 2 := by
        push_cast
        ring
      have e2 : ∀ v, axialRot (((n + 1 : ℕ) : ℝ) * θ) v = axialRot ((n : ℝ) * θ) (axialRot θ v) := by
        intro v
        rw [hcomp]
        congr 1
        push_cast
        ring
      rw [e1, e2, e2, h1, h2]
  intro i γ hγ
  obtain ⟨a, b, j, hγ1, hγ2⟩ := hgen γ hγ
  have hrot := (hfmt i).invariant
  have hR := hiter (D.cert.actuator i) (Real.pi / D.azimuthOrder) (hrot.mono fun z h => h.1) a
  have hF : ∀ᵐ z : ℝ × Space, D.cert.actuator i z.1 (flipPoint z.2) = flipPoint (D.cert.actuator i z.1 z.2) :=
    hrot.mono fun z h => h.2
  have hRF := hqflip.ae hR
  have hper := hshift (hfmt i).periodic j
  filter_upwards [hR, hRF, hF] with z h1 h2 h3
  rw [hγ1, hγ1, hγ2]
  have e : z.1 + ((a : ℝ) / 2 + (j : ℝ)) = (z.1 + (a : ℝ) / 2) + (j : ℝ) := by ring
  rw [e, hper]
  cases b
  · rw [if_neg (by decide), if_neg (by decide)]
    exact h1
  · rw [if_pos rfl, if_pos rfl, h2, h3]

theorem actuatorFacts_of_instance {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM)
    (modes : Fin k → Finset (ℤ × ℤ)) (jmax : ℕ) (h : IsActuatorInstance D modes jmax)
    (hfmt : ∀ i, ActuatorShapeFacts D.azimuthOrder (modes i) (D.cert.actuator i)) (q : Fin k → ℝ)
    (hq : q ∈ D.cert.params) (i : Fin k) :
    ActuatorFacts (D.pieces q) (D.cert.actuator i) := by
  have hf := hfmt i
  have key : ∀ ξ, (∃ σ y, (pointPlane y).1 ≠ 0 ∧ modeVel ξ (D.cert.actuator i) σ y ≠ 0) →
      ∃ ι : ℤ × ℤ, |ι.2| ≤ jmax ∧ |ι.2 - ι.1| ≤ jmax ∧
        (labelHarmonic D.azimuthOrder ι = ξ ∨ labelHarmonic D.azimuthOrder ι = -ξ) := by
    rintro ξ ⟨σ, y, hy, hne⟩
    obtain ⟨ι, hι, hξ⟩ := hf.modes_in ξ σ y hy hne
    exact ⟨ι, (h.modes_bound i ι hι).1, (h.modes_bound i ι hι).2, hξ⟩
  have piece : ∀ (T : Set (ℤ × ℤ)) (ξ ι : ℤ × ℤ),
      (labelHarmonic D.azimuthOrder ι = ξ ∨ labelHarmonic D.azimuthOrder ι = -ξ) →
      PieceWeights.inPiece T ξ → PieceWeights.inPiece T (labelHarmonic D.azimuthOrder ι) := by
    rintro T ξ ι (hξ | hξ) hT
    · rw [hξ]
      exact hT
    · rw [hξ]
      unfold PieceWeights.inPiece at hT ⊢
      rw [neg_neg]
      exact hT.symm
  refine
    { measurable := hf.measurable
      periodic := hf.periodic
      bounded_support := hf.bounded_support
      square_finite := hf.square_finite
      gradient_measurable := hf.gradient_measurable
      gradient_periodic := hf.gradient_periodic
      gradient_finite := hf.gradient_finite
      weak_gradient := hf.weak_gradient
      finite_modes := ?_
      mu_free := ?_
      eps_vanish := ?_ }
  · refine ⟨(modes i).image (labelHarmonic D.azimuthOrder) ∪
      (modes i).image (fun ι => -labelHarmonic D.azimuthOrder ι), ?_⟩
    intro ξ hξ σ y hy
    by_contra hne
    obtain ⟨ι, hι, hh⟩ := hf.modes_in ξ σ y hy hne
    apply hξ
    rcases hh with hh | hh
    · exact Finset.mem_union_left _ (Finset.mem_image.2 ⟨ι, hι, hh⟩)
    · exact Finset.mem_union_right _ (Finset.mem_image.2 ⟨ι, hι, by rw [hh, neg_neg]⟩)
  · intro β ξ hex hin
    obtain ⟨ι, h1, h2, hξ⟩ := key ξ hex
    exact h.mu_avoid q hq β ι h1 h2 (piece _ ξ ι hξ hin)
  · intro β ξ hex hin
    obtain ⟨ι, h1, h2, hξ⟩ := key ξ hex
    exact absurd (piece _ ξ ι hξ hin) (h.eps_avoid q hq β ι h1 h2)

theorem pinInstance_clauses (hreg : CellMatFieldRegular) {k : ℕ} {C : Type} {nE nM : ℕ}
    (D : CellLayerData k C nE nM) (h : IsPinInstance D) :
    (∀ i, AEStronglyMeasurable (fun z : ℝ × Space => D.cert.pin i z.1 z.2) volume) ∧
    (∀ i, periodLIntegral (fun σ y => matSq (D.cert.pin i σ y)) < ⊤) := by
  have hg : ∀ i, D.cert.pin i = (D.pinValues i).field D.mesh.box D.azimuthOrder := by
    intro i
    rw [h.pin_eq]
    rfl
  refine ⟨fun i => ?_, fun i => ?_⟩
  · rw [hg i]
    exact (hreg D.mesh (D.pinValues i) D.azimuthOrder h.mesh_valid).1
  · rw [hg i]
    exact (hreg D.mesh (D.pinValues i) D.azimuthOrder h.mesh_valid).2.2.2

theorem rowInstance_clauses (hreg : CellVecFieldRegular) (hpair : GeneratorPairingMatrixFormula)
    (hpd : RowPairingPosDef) (horth : RowFieldsOrthonormal) {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM)
    (tauMax : ℝ) (h : IsRowInstance D tauMax) :
    (∀ a, AEStronglyMeasurable (fun z : ℝ × Space => D.cert.rowField a z.1 z.2) volume) ∧
    (∀ a, IsTimePeriodic (D.cert.rowField a)) ∧
    (∀ a, periodLIntegral (fun σ y => ‖D.cert.rowField a σ y‖ ^ 2) < ⊤) ∧
    (∀ a b, periodPairing (D.cert.rowField a) (D.cert.rowField b) = if a = b then 1 else 0) ∧
    (∀ a, 0 ≤ D.cert.rowWeight a) ∧ (∀ a, D.cert.rowWeight a ≤ D.cert.rowBound ^ 2) := by
  have hfin : ∀ (g : ℝ → Space → ℝ) (B R : ℝ), (∀ σ y, g σ y ≤ B) → (∀ σ y, R < ‖y‖ → g σ y ≤ 0) →
      periodLIntegral g < ⊤ := by
    intro g B R hg hs
    unfold periodLIntegral
    have hin : ∀ σ, (∫⁻ y, ENNReal.ofReal (g σ y)) ≤
        ENNReal.ofReal B * volume (Metric.closedBall (0 : Space) R) := by
      intro σ
      rw [← lintegral_indicator_const Metric.isClosed_closedBall.measurableSet]
      refine lintegral_mono fun y => ?_
      by_cases hy : y ∈ Metric.closedBall (0 : Space) R
      · rw [Set.indicator_of_mem hy]
        exact ENNReal.ofReal_le_ofReal (hg σ y)
      · have hR : R < ‖y‖ := by
          simpa [Metric.mem_closedBall, dist_zero_right, not_le] using hy
        rw [ENNReal.ofReal_eq_zero.2 (hs σ y hR)]
        simp
    calc (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ENNReal.ofReal (g σ y))
        ≤ ∫⁻ _ in Set.Icc (0 : ℝ) 1, ENNReal.ofReal B * volume (Metric.closedBall (0 : Space) R) :=
          lintegral_mono fun σ => hin σ
      _ = ENNReal.ofReal B * volume (Metric.closedBall (0 : Space) R) * volume (Set.Icc (0 : ℝ) 1) :=
          setLIntegral_const _ _
      _ < ⊤ := by
          refine ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top measure_closedBall_lt_top) ?_
          simp [Real.volume_Icc]
  have hM : IsCellMesh D.mesh := h.values.mesh_valid
  have hreg' : ∀ a, AEStronglyMeasurable
      (fun z : ℝ × Space => D.rows.rowFieldOf D.mesh.box D.azimuthOrder a z.1 z.2) volume ∧
      IsTimePeriodic (D.rows.rowFieldOf D.mesh.box D.azimuthOrder a) ∧
      periodLIntegral (fun σ y => ‖D.rows.rowFieldOf D.mesh.box D.azimuthOrder a σ y‖ ^ 2) < ⊤ := by
    intro a
    have hg : ∀ b, AEStronglyMeasurable
        (fun z : ℝ × Space => D.rows.generatorField D.mesh.box D.azimuthOrder b z.1 z.2) volume ∧
        IsTimePeriodic (D.rows.generatorField D.mesh.box D.azimuthOrder b) ∧
        (∃ B Rb : ℝ, ∀ σ y, ‖D.rows.generatorField D.mesh.box D.azimuthOrder b σ y‖ ≤ B ∧
          (Rb < ‖y‖ → D.rows.generatorField D.mesh.box D.azimuthOrder b σ y = 0)) := fun b =>
      ⟨(hreg D.mesh (D.rows.generator b) D.azimuthOrder hM).1,
        (hreg D.mesh (D.rows.generator b) D.azimuthOrder hM).2.1,
        (hreg D.mesh (D.rows.generator b) D.azimuthOrder hM).2.2.1⟩
    choose hmeas hper B Rb hB using hg
    refine ⟨?_, ?_, ?_⟩
    · exact Finset.aestronglyMeasurable_fun_sum Finset.univ fun b _ =>
        (hmeas b).const_smul (D.rows.mix D.mesh.box D.azimuthOrder a b)
    · intro σ y
      simp only [RowValues.rowFieldOf]
      exact Finset.sum_congr rfl fun b _ => by rw [hper b σ y]
    · refine hfin _ ((∑ b, |D.rows.mix D.mesh.box D.azimuthOrder a b| * B b) ^ 2) (∑ b, |Rb b|) ?_ ?_
      · intro σ y
        have hle : ‖D.rows.rowFieldOf D.mesh.box D.azimuthOrder a σ y‖
            ≤ ∑ b, |D.rows.mix D.mesh.box D.azimuthOrder a b| * B b := by
          simp only [RowValues.rowFieldOf]
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun b _ => ?_)
          rw [norm_smul, Real.norm_eq_abs]
          exact mul_le_mul_of_nonneg_left (hB b σ y).1 (abs_nonneg _)
        exact pow_le_pow_left₀ (norm_nonneg _) hle 2
      · intro σ y hy
        have hz : D.rows.rowFieldOf D.mesh.box D.azimuthOrder a σ y = 0 := by
          simp only [RowValues.rowFieldOf]
          refine Finset.sum_eq_zero fun b _ => ?_
          have hb : Rb b < ‖y‖ := lt_of_le_of_lt ((le_abs_self _).trans
            (Finset.single_le_sum (f := fun j => |Rb j|) (fun _ _ => abs_nonneg _) (Finset.mem_univ b))) hy
          rw [(hB b σ y).2 hb, smul_zero]
        rw [hz, norm_zero]
        norm_num
  have hG : (D.rows.fieldPairingMatrix D.mesh.box D.azimuthOrder).PosDef := by
    rw [hpair D.mesh D.rows D.azimuthOrder tauMax h.values]
    exact hpd D.mesh D.rows D.azimuthOrder tauMax h.values
  rw [h.rowField_eq, h.rowWeight_eq]
  exact ⟨fun a => (hreg' a).1, fun a => (hreg' a).2.1, fun a => (hreg' a).2.2,
    horth D.mesh D.rows D.azimuthOrder tauMax h.values hG,
    rowWeight_nonneg_of_values D.mesh D.rows h.values h.coercivity_pos,
    rowWeight_le_of_values D.mesh D.rows h.values h.coercivity_pos h.rowBound_ge⟩

structure InstanceConsequences {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM) : Prop where
  rowField_measurable : ∀ a, AEStronglyMeasurable (fun z : ℝ × Space => D.cert.rowField a z.1 z.2) volume
  rowField_periodic : ∀ a, IsTimePeriodic (D.cert.rowField a)
  rowField_finite : ∀ a, periodLIntegral (fun σ y => ‖D.cert.rowField a σ y‖ ^ 2) < ⊤
  rowField_orthonormal : ∀ a b, periodPairing (D.cert.rowField a) (D.cert.rowField b) = if a = b then 1 else 0
  rowWeight_nonneg : ∀ a, 0 ≤ D.cert.rowWeight a
  rowWeight_le : ∀ a, D.cert.rowWeight a ≤ D.cert.rowBound ^ 2
  rows_class_form : ∀ F : ℝ → Space → Space, AEStronglyMeasurable (fun z : ℝ × Space => F z.1 z.2) volume →
    IsTimePeriodic F → periodLIntegral (fun σ y => ‖F σ y‖ ^ 2) < ⊤ →
    (∀ σ y, F σ (flipPoint y) = flipPoint (F σ y)) →
    D.coercivity * D.cert.rows F ^ 2 =
      4 * Real.pi * ∑ K, ∑ ι ∈ D.mesh.tested K, D.rows.testWeight K ι *
        (dotProduct (star (D.rows.cellMoment D.mesh.box D.azimuthOrder K ι F))
          (Matrix.mulVec (D.rows.testBlockMatrix D.mesh.box K ι)⁻¹
            (D.rows.cellMoment D.mesh.box D.azimuthOrder K ι F))).re
  weights : ∀ q ∈ D.cert.params, AdmissibleWeightClauses (D.pieces q) ∧ WeightFlipClauses (D.pieces q) ∧
    (D.pieces q).c = D.coercivity
  actuators : ∀ q ∈ D.cert.params, ∀ i, ActuatorFacts (D.pieces q) (D.cert.actuator i)
  actuator_invariant : ∀ i, ∀ γ ∈ D.cert.symmetries, ∀ᵐ z : ℝ × Space,
    D.cert.actuator i (z.1 + γ.2) (γ.1 z.2) = γ.1 (D.cert.actuator i z.1 z.2)
  pin_measurable : ∀ i, AEStronglyMeasurable (fun z : ℝ × Space => D.cert.pin i z.1 z.2) volume
  pin_finite : ∀ i, periodLIntegral (fun σ y => matSq (D.cert.pin i σ y)) < ⊤

structure InstanceParts : Prop where
  pairing_formula : GeneratorPairingMatrixFormula
  pairing_posDef : RowPairingPosDef
  orthonormal : RowFieldsOrthonormal
  moments : GeneratorPairingMoments
  norm_identity : RowNormIdentity
  class_form : RowsClassForm
  smooth : ScalarSmoothOfJoins
  derivative_decay : ScalarDerivativeDecay
  slope_bound : ScalarSlopeBoundOfJoins
  rate : ScalarRateOfDecay
  scalar_basic : ScalarBasicFacts
  step_basic : StepBasicFacts
  mirror : MirrorEval
  vec_regular : CellVecFieldRegular
  mat_regular : CellMatFieldRegular

theorem instanceConsequences_of_entry (hN : InstanceParts) {k : ℕ} {C : Type} {nE nM : ℕ}
    (D : CellLayerData k C nE nM) (X : InstanceData k C nE nM) (h : IsInstanceEntry D X)
    (hfmt : ∀ i, ActuatorShapeFacts D.azimuthOrder (X.actuatorModes i) (D.cert.actuator i)) :
    InstanceConsequences D := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := rowInstance_clauses hN.vec_regular hN.pairing_formula
    hN.pairing_posDef hN.orthonormal D X.rowWeightMax h.rows
  refine
    { rowField_measurable := h1
      rowField_periodic := h2
      rowField_finite := h3
      rowField_orthonormal := h4
      rowWeight_nonneg := h5
      rowWeight_le := h6
      rows_class_form := ?_
      weights := weightInstance_clauses hN.smooth hN.derivative_decay hN.slope_bound hN.rate
        hN.scalar_basic hN.step_basic hN.mirror D X.weights X.epsFrame X.muFrame X.epsSpeed X.muSpeed
        X.epsMirror X.muMirror h.weights
      actuators := fun q hq i => actuatorFacts_of_instance D X.actuatorModes X.actuatorRange h.actuators hfmt q hq i
      actuator_invariant := actuatorInvariant_of_shape D X.actuatorModes hfmt h.symmetries
      pin_measurable := (pinInstance_clauses hN.mat_regular D h.pins).1
      pin_finite := (pinInstance_clauses hN.mat_regular D h.pins).2 }
  intro F hF1 hF2 hF3 hF4
  have hform := hN.class_form D.mesh D.rows D.azimuthOrder X.rowWeightMax D.coercivity h.rows.values
    h.rows.coercivity_pos F hF1 hF2 hF3 hF4
  simp only [ExtendedCertificateData.rows]
  rw [h.rows.rowField_eq, h.rows.rowWeight_eq]
  exact hform

end Instance

end CertCell

end Breakdown
