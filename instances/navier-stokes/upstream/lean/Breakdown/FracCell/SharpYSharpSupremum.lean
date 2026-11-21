import Breakdown.FracCell.SharpYChargeSt

open MeasureTheory

noncomputable section

namespace Breakdown

namespace CellCert

namespace CellAnalysis

open SteadyCert Assembly SharpParts

namespace SharpSupremumParts

variable {k N : ℕ} (c : FracCellData k N) (K : CellBox) (S : CellScalars) (x : FieldTuple k)

def waveSum (p : ℝ × ℝ) : ℂ :=
  ∑' n : ℤ, ∑' n' : ℤ,
    pairWave c n n' p (sharpGrad c K S x n p) (sharpVel c K S x n p) (sharpGrad c K S x n' p) (sharpVel c K S x n' p)

end SharpSupremumParts

open SharpSupremumParts

def SharpCircleSquareStatement : Prop :=
  ∀ (α : ℝ), 1 < α → α < 5 / 4 → ∀ {k N : ℕ} (c : FracCellData k N), IsFormData α c →
    ∀ (K : CellBox) (S : CellScalars) (B : CellBases) (Cl : CellClasses) {slots : ℕ}
      (R : CellRows N slots k), IsCellData α c K S B Cl R → IsAxisymmetricWeight c K →
    ∀ x : FieldTuple k, IsAdmissible c x →
      ∀ᵐ p ∂(volume.restrict K.rect), Summable (fun n : ℤ => sumSq (sharpGrad c K S x n p)) ∧
        Summable (fun n : ℤ => vecSq (sharpVel c K S x n p))

def SharpCircleBoundStatement : Prop :=
  ∀ (α : ℝ), 1 < α → α < 5 / 4 → ∀ {k N : ℕ} (c : FracCellData k N), IsFormData α c →
    ∀ (K : CellBox) (S : CellScalars) (B : CellBases) (Cl : CellClasses) {slots : ℕ}
      (R : CellRows N slots k), IsCellData α c K S B Cl R → IsAxisymmetricWeight c K →
    ∀ x : FieldTuple k, IsAdmissible c x →
      ∀ᵐ p ∂(volume.restrict K.rect), Summable (fun n : ℤ => sumSq (sharpGrad c K S x n p)) →
        Summable (fun n : ℤ => vecSq (sharpVel c K S x n p)) →
        -(∑' n : ℤ, supDensity c K S x n p) ≤ (waveSum c K S x p).re

def SharpSupremumRegularStatement : Prop :=
  ∀ (α : ℝ), 1 < α → α < 5 / 4 → ∀ {k N : ℕ} (c : FracCellData k N), IsFormData α c →
    ∀ (K : CellBox) (S : CellScalars) (B : CellBases) (Cl : CellClasses) {slots : ℕ}
      (R : CellRows N slots k), IsCellData α c K S B Cl R → IsAxisymmetricWeight c K →
    ∀ x : FieldTuple k, IsAdmissible c x →
      (∀ n : ℤ, IntegrableOn (fun p : ℝ × ℝ => p.1 * supDensity c K S x n p) K.rect) ∧
      Summable (fun n : ℤ => ∫ p in K.rect, ‖p.1 * supDensity c K S x n p‖) ∧
      IntegrableOn (fun p : ℝ × ℝ => p.1 * (waveSum c K S x p).re) K.rect

namespace SharpSupremumParts

private theorem integrable_tsum_of {μ : Measure (ℝ × ℝ)} {F : ℤ → ℝ × ℝ → ℝ}
    (hF : ∀ i, Integrable (F i) μ) (hs : Summable fun i => ∫ a, ‖F i a‖ ∂μ) :
    Integrable (fun a => ∑' i, F i a) μ := by
  have hlin : ∀ i, ∫⁻ a, ‖F i a‖ₑ ∂μ = ENNReal.ofReal (∫ a, ‖F i a‖ ∂μ) := fun i =>
    (ofReal_integral_norm_eq_lintegral_enorm (hF i)).symm
  have hm : ∀ i, AEMeasurable (fun a => ‖F i a‖ₑ) μ := fun i => (hF i).1.enorm
  have hfin : ∫⁻ a, ∑' i, ‖F i a‖ₑ ∂μ ≠ ⊤ := by
    rw [lintegral_tsum hm]
    simp_rw [hlin]
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun i => integral_nonneg fun a => norm_nonneg _) hs]
    exact ENNReal.ofReal_ne_top
  have hae : ∀ᵐ a ∂μ, Summable fun i => F i a := by
    filter_upwards [ae_lt_top' (AEMeasurable.tsum hm) hfin] with a ha
    apply Summable.of_norm
    have h1 : (∑' i, ((‖F i a‖₊ : NNReal) : ENNReal)) ≠ ⊤ := ha.ne
    exact NNReal.summable_coe.2 (ENNReal.tsum_coe_ne_top_iff_summable.1 h1)
  refine ⟨?_, ?_⟩
  · exact aestronglyMeasurable_of_tendsto_ae Filter.atTop
      (fun s : Finset ℤ => Finset.aestronglyMeasurable_sum s fun i _ => (hF i).1)
      (hae.mono fun a ha => by
        simp only [Finset.sum_apply]
        exact ha.hasSum)
  · calc ∫⁻ a, ‖∑' i, F i a‖ₑ ∂μ ≤ ∫⁻ a, ∑' i, ‖F i a‖ₑ ∂μ :=
          lintegral_mono fun a => enorm_tsum_le_tsum_enorm
      _ < ⊤ := lt_top_iff_ne_top.2 hfin

end SharpSupremumParts

theorem sharpSupremum_of (hQ : SharpCircleSquareStatement) (hB : SharpCircleBoundStatement)
    (hR : SharpSupremumRegularStatement) : SharpSupremumStatement := by
  intro α h1 h2 k N c hc K S B Cl slots R hd hw x hx
  obtain ⟨hI, hS, hW⟩ := hR α h1 h2 c hc K S B Cl R hd hw x hx
  have hQ' := hQ α h1 h2 c hc K S B Cl R hd hw x hx
  have hB' := hB α h1 h2 c hc K S B Cl R hd hw x hx
  have hsum : supSum c K S x = ∫ p in K.rect, ∑' n : ℤ, p.1 * supDensity c K S x n p :=
    integral_tsum_of_summable_integral_norm hI hS
  have hF : IntegrableOn (fun p : ℝ × ℝ => ∑' n : ℤ, p.1 * supDensity c K S x n p) K.rect :=
    SharpSupremumParts.integrable_tsum_of hI hS
  have hrect : MeasurableSet K.rect := measurableSet_Icc.prod measurableSet_Icc
  have hr : ∀ᵐ p ∂(volume.restrict K.rect), 0 ≤ p.1 := by
    filter_upwards [ae_restrict_mem hrect] with p hp
    exact le_trans hd.box.r_order.1 hp.1.1
  show -supSum c K S x ≤ ∫ p in K.rect, p.1 * (waveSum c K S x p).re
  rw [hsum, ← integral_neg]
  refine integral_mono_ae hF.neg hW ?_
  filter_upwards [hr, hQ', hB'] with p hp0 hq hb
  have h3 := hb hq.1 hq.2
  show -(∑' n : ℤ, p.1 * supDensity c K S x n p) ≤ p.1 * (waveSum c K S x p).re
  rw [tsum_mul_left]
  nlinarith

end CellAnalysis

end CellCert

end Breakdown
