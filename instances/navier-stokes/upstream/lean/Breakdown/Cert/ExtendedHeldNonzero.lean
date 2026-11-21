import Breakdown.Cert.ExtendedNodes
import Breakdown.Cert.HeldNonzero

open scoped ContDiff ENNReal
open MeasureTheory Filter Set

noncomputable section

namespace Breakdown.Cert

open Freq

open Internal.HeldNonzero

theorem extendedHeldNonzeroHolds_of (h : ReadingEnergyHolds) : ExtendedHeldNonzeroHolds := by
  intro k d hd q hq f κ hs v G H hr hz
  have hw : IsAdmissibleWeight d.weightFn d.weight :=
    ⟨hd.weight_pos, hd.weightFn_measurable, hd.weightFn_lower, d.weightMax, hd.weightFn_upper⟩
  obtain ⟨he, -, -⟩ := h _ _ hw _ v G H hr
  have hW : ∀ σ, ContDiff ℝ 1 (d.profile q σ) := fun σ =>
    hd.profile_smooth.comp (contDiff_const.prodMk (contDiff_const.prodMk contDiff_id))
  have h5 := hd.nontrivial q hq
  rw [periodLIntegral_matSq_eq hW hr hz] at h5
  have hBt : periodLIntegral (fun σ y => matSq (G σ y)) ≠ ⊤ := by
    intro hB
    rw [hB, ENNReal.toReal_top] at h5
    have := hd.weight_pos
    have : 0 ≤ 4 * d.sizeBound ^ 2 / d.weight := by positivity
    linarith
  have hAt := weighted_ne_top hw hr hBt
  have hlow := ENNReal.toReal_mono hAt (weighted_lower hw G H)
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hd.weight_pos.le] at hlow
  unfold weightedEnergy at he
  have hκ : 0 ≤ ∑ i, κ i ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have h2 : energyW d.weightFn (freeInv (d.period q) f) + ∑ i, κ i ^ 2 ≤ (2 * d.sizeBound) ^ 2 :=
    (Real.sqrt_le_iff.1 (show Real.sqrt (energyW d.weightFn (freeInv (d.period q) f) + ∑ i, κ i ^ 2)
      ≤ 2 * d.sizeBound from hs.size)).2
  rw [div_lt_iff₀ hd.weight_pos] at h5
  exact arith_contra hlow he h2 hκ h5

end Breakdown.Cert
