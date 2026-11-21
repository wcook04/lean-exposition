import Breakdown.CertCell.InstanceStatements
import Breakdown.CertCell.StatementDefs

open scoped ENNReal ComplexOrder
open MeasureTheory

noncomputable section

namespace Breakdown

namespace CertCell

namespace InstanceSplit

open Instance

structure ShapeAdmissibleClauses (P : ℝ) (h : HarmonicBounds) (w : Space → ℝ) (W : ℝ → Space → Space)
    (w₀ : ℝ) : Prop where
  period_pos : 0 < P
  weight_pos : 0 < w₀
  weight_lower : ∀ y, w₀ ≤ w y
  weight_measurable : Measurable w
  weight_axi : IsAxisymmetric w
  harmonics_neg : ∀ β ∈ h.harmonics, -β ∈ h.harmonics
  harmonics_zero : (0, 0) ∈ h.harmonics
  harmonics_span : ∀ σ y i, W σ y i = ∑ β ∈ h.harmonics, (modeVel β W σ y i).re

theorem otherAdmissibleClauses_of_split {C : Type} {nE nM : ℕ} {m : PieceWeights C nE nM} {P : ℝ}
    {h : HarmonicBounds} {w : Space → ℝ} {W : ℝ → Space → Space}
    {HW : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)} {w₀ epsSup epsGradSup ratio : ℝ}
    (hf : ShapeAdmissibleClauses P h w W w₀) (he : EnclosureAdmissibleClauses m P h W HW epsSup epsGradSup ratio) :
    OtherAdmissibleClauses m P h w W HW w₀ epsSup epsGradSup ratio where
  period_pos := hf.period_pos
  weight_pos := hf.weight_pos
  weight_lower := hf.weight_lower
  weight_measurable := hf.weight_measurable
  weight_axi := hf.weight_axi
  harmonics_neg := hf.harmonics_neg
  harmonics_zero := hf.harmonics_zero
  harmonics_span := hf.harmonics_span
  ampW_ge := he.ampW_ge
  ampGradW_ge := he.ampGradW_ge
  ampVort_ge := he.ampVort_ge
  ampGradVort_ge := he.ampGradVort_ge
  supVort_ge := he.supVort_ge
  supGradVort_ge := he.supGradVort_ge
  epsSpeed_ge := he.epsSpeed_ge
  muSpeed_ge := he.muSpeed_ge
  eps_oneSided := he.eps_oneSided
  mu_oneSided := he.mu_oneSided
  mu_ratio := he.mu_ratio
  ratio_nonneg := he.ratio_nonneg
  eps_sum_le := he.eps_sum_le
  eps_grad_sum_le := he.eps_grad_sum_le
  conv_le := he.conv_le

structure ShapeFlipClauses (h : HarmonicBounds) (w : Space → ℝ) : Prop where
  weight_flip : ∀ y, w (flipPoint y) = w y
  harmonics_flip : ∀ β ∈ h.harmonics, flipLabel β ∈ h.harmonics

theorem otherFlipClauses_of_split {C : Type} {nE nM : ℕ} {m : PieceWeights C nE nM} {h : HarmonicBounds}
    {w : Space → ℝ} (hf : ShapeFlipClauses h w) (ht : ValuesFlipClauses m h) : OtherFlipClauses m h w where
  weight_flip := hf.weight_flip
  harmonics_flip := hf.harmonics_flip
  amplitudes_flip := ht.amplitudes_flip
  sups_flip := ht.sups_flip
  amplitudes_axi := ht.amplitudes_axi
  sups_axi := ht.sups_axi
  eps_speed_axi := ht.eps_speed_axi
  mu_speed_axi := ht.mu_speed_axi

theorem constantWeight_shapeFlip (w₀ : ℝ) (h : HarmonicBounds) (hh : ∀ β ∈ h.harmonics, flipLabel β ∈ h.harmonics) :
    ShapeFlipClauses h (fun _ => w₀) :=
  ⟨fun _ => rfl, hh⟩

end InstanceSplit

end CertCell

end Breakdown
