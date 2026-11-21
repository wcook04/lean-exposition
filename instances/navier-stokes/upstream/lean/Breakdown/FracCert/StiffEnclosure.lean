import Breakdown.FracCert.StHeld
import Mathlib

open scoped ContDiff ENNReal
open MeasureTheory Matrix

noncomputable section

namespace Breakdown

namespace SteadyCert

namespace StiffEnclosureInternal

lemma sum_sq_add_le {ι : Type*} (s : Finset ι) (a b : ι → ℝ) :
    ∑ j ∈ s, (a j + b j) ^ 2 ≤ (Real.sqrt (∑ j ∈ s, a j ^ 2) + Real.sqrt (∑ j ∈ s, b j ^ 2)) ^ 2 := by
  have hA : 0 ≤ ∑ j ∈ s, a j ^ 2 := Finset.sum_nonneg fun j _ => sq_nonneg _
  have hB : 0 ≤ ∑ j ∈ s, b j ^ 2 := Finset.sum_nonneg fun j _ => sq_nonneg _
  have hexp : ∑ j ∈ s, (a j + b j) ^ 2 =
      ∑ j ∈ s, a j ^ 2 + 2 * ∑ j ∈ s, a j * b j + ∑ j ∈ s, b j ^ 2 := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hcs : ∑ j ∈ s, a j * b j ≤ Real.sqrt (∑ j ∈ s, a j ^ 2) * Real.sqrt (∑ j ∈ s, b j ^ 2) := by
    rw [← Real.sqrt_mul hA]
    calc ∑ j ∈ s, a j * b j ≤ |∑ j ∈ s, a j * b j| := le_abs_self _
      _ = Real.sqrt ((∑ j ∈ s, a j * b j) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
      _ ≤ Real.sqrt ((∑ j ∈ s, a j ^ 2) * ∑ j ∈ s, b j ^ 2) :=
        Real.sqrt_le_sqrt (Finset.sum_mul_sq_le_sq_mul_sq s a b)
  have h1 := Real.sq_sqrt hA
  have h2 := Real.sq_sqrt hB
  rw [hexp, add_sq, h1, h2]
  linarith

lemma transpose_sq_le {k : ℕ} (A : Matrix (Fin k) (Fin k) ℝ) (δ : ℝ)
    (h : ∀ z : Fin k → ℝ, |∑ j, (A *ᵥ z) j ^ 2 - ∑ j, z j ^ 2| ≤ δ * ∑ j, z j ^ 2) (x : Fin k → ℝ) :
    ∑ j, (Aᵀ *ᵥ x) j ^ 2 ≤ (1 + δ) * ∑ j, x j ^ 2 := by
  set w := Aᵀ *ᵥ x with hw
  have hW : 0 ≤ ∑ j, w j ^ 2 := Finset.sum_nonneg fun j _ => sq_nonneg _
  have hX : 0 ≤ ∑ j, x j ^ 2 := Finset.sum_nonneg fun j _ => sq_nonneg _
  have hAw : ∑ j, (A *ᵥ w) j ^ 2 ≤ (1 + δ) * ∑ j, w j ^ 2 := by
    have := (abs_le.mp (h w)).2
    linarith
  have hAx : ∑ j, (A *ᵥ x) j ^ 2 ≤ (1 + δ) * ∑ j, x j ^ 2 := by
    have := (abs_le.mp (h x)).2
    linarith
  have hAx0 : 0 ≤ (1 + δ) * ∑ j, x j ^ 2 :=
    le_trans (Finset.sum_nonneg fun j _ => sq_nonneg _) hAx
  have hdot : ∑ j, w j ^ 2 = ∑ j, x j * (A *ᵥ w) j := by
    have e1 : ∑ j, w j ^ 2 = w ⬝ᵥ w := by
      simp only [dotProduct, sq]
    have e2 : ∑ j, x j * (A *ᵥ w) j = x ⬝ᵥ (A *ᵥ w) := rfl
    have e3 : w = x ᵥ* A := by rw [hw, mulVec_transpose]
    rw [e1, e2, dotProduct_mulVec x A w, ← e3]
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ x (A *ᵥ w)
  rw [← hdot] at hcs
  have hsq : (∑ j, w j ^ 2) ^ 2 ≤ (∑ j, w j ^ 2) * ((1 + δ) * ∑ j, x j ^ 2) := by
    calc (∑ j, w j ^ 2) ^ 2 ≤ (∑ j, x j ^ 2) * ∑ j, (A *ᵥ w) j ^ 2 := hcs
      _ ≤ (∑ j, x j ^ 2) * ((1 + δ) * ∑ j, w j ^ 2) := mul_le_mul_of_nonneg_left hAw hX
      _ = (∑ j, w j ^ 2) * ((1 + δ) * ∑ j, x j ^ 2) := by ring
  rcases hW.lt_or_eq with hpos | hzero
  · nlinarith
  · rw [← hzero]; exact hAx0

end StiffEnclosureInternal

open StiffEnclosureInternal

theorem stiffEnclosure : StiffEnclosureStatement := by
  intro α _ _ k N d hd p hp u G H P κ _ hsize
  have hμ : 0 < d.multiplierScale := hd.multiplierScale_pos
  have hE : 0 ≤ d.energy G H := by
    unfold FracCertData.energy weightedEnergy
    exact add_nonneg (integral_nonneg fun y => sq_nonneg _)
      (integral_nonneg fun y => mul_nonneg (hd.weightMin_pos.le.trans (hd.weight_lower y))
        (Finset.sum_nonneg fun i _ => sq_nonneg _))
  have hκ0 : 0 ≤ ∑ i, κ i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hS0 : 0 ≤ d.size G H κ := Real.sqrt_nonneg _
  have hR : 0 ≤ d.heldRadius := hS0.trans hsize
  have hsq : d.size G H κ ^ 2 = d.energy G H + d.multiplierScale ^ 2 * ∑ i, κ i ^ 2 :=
    Real.sq_sqrt (add_nonneg hE (mul_nonneg (sq_nonneg _) hκ0))
  have hK : d.multiplierScale ^ 2 * ∑ i, κ i ^ 2 ≤ d.heldRadius ^ 2 := by
    nlinarith [pow_le_pow_left₀ hS0 hsize 2]
  have hK' : ∑ i, κ i ^ 2 ≤ (d.heldRadius / d.multiplierScale) ^ 2 := by
    rw [div_pow, le_div_iff₀ (by positivity)]
    linarith
  have hKs : Real.sqrt (∑ i, κ i ^ 2) ≤ d.heldRadius / d.multiplierScale := by
    calc Real.sqrt (∑ i, κ i ^ 2) ≤ Real.sqrt ((d.heldRadius / d.multiplierScale) ^ 2) :=
          Real.sqrt_le_sqrt hK'
      _ = d.heldRadius / d.multiplierScale := Real.sqrt_sq (div_nonneg hR hμ.le)
  have hT := transpose_sq_le d.frame d.frameDefect hd.frame_near κ
  have hB : Real.sqrt (∑ j ∈ d.activeSetᶜ, (d.frameᵀ *ᵥ κ) j ^ 2) ≤
      Real.sqrt (1 + d.frameDefect) * d.heldRadius / d.multiplierScale := by
    calc Real.sqrt (∑ j ∈ d.activeSetᶜ, (d.frameᵀ *ᵥ κ) j ^ 2)
        ≤ Real.sqrt (∑ j, (d.frameᵀ *ᵥ κ) j ^ 2) :=
          Real.sqrt_le_sqrt (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
            fun j _ _ => sq_nonneg _)
      _ ≤ Real.sqrt ((1 + d.frameDefect) * ∑ i, κ i ^ 2) := Real.sqrt_le_sqrt hT
      _ = Real.sqrt (1 + d.frameDefect) * Real.sqrt (∑ i, κ i ^ 2) := Real.sqrt_mul' _ hκ0
      _ ≤ Real.sqrt (1 + d.frameDefect) * (d.heldRadius / d.multiplierScale) :=
          mul_le_mul_of_nonneg_left hKs (Real.sqrt_nonneg _)
      _ = Real.sqrt (1 + d.frameDefect) * d.heldRadius / d.multiplierScale := by ring
  have hincl := hd.stiff_inclusion p hp
  have heq : d.frameᵀ *ᵥ d.heldMultiplier p κ = d.frameᵀ *ᵥ d.multiplier p + d.frameᵀ *ᵥ κ := by
    rw [← mulVec_add]
    rfl
  have hA0 : 0 ≤ Real.sqrt (∑ j ∈ d.activeSetᶜ, ((d.frameᵀ *ᵥ d.multiplier p) j - d.slope j * p j) ^ 2) +
      Real.sqrt (∑ j ∈ d.activeSetᶜ, (d.frameᵀ *ᵥ κ) j ^ 2) :=
    add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  calc ∑ j ∈ d.activeSetᶜ, ((d.frameᵀ *ᵥ d.heldMultiplier p κ) j - d.slope j * p j) ^ 2
      = ∑ j ∈ d.activeSetᶜ, (((d.frameᵀ *ᵥ d.multiplier p) j - d.slope j * p j) + (d.frameᵀ *ᵥ κ) j) ^ 2 := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [heq, Pi.add_apply]
        ring
    _ ≤ (Real.sqrt (∑ j ∈ d.activeSetᶜ, ((d.frameᵀ *ᵥ d.multiplier p) j - d.slope j * p j) ^ 2) +
          Real.sqrt (∑ j ∈ d.activeSetᶜ, (d.frameᵀ *ᵥ κ) j ^ 2)) ^ 2 := sum_sq_add_le _ _ _
    _ ≤ d.ellipsoidRadius ^ 2 := pow_le_pow_left₀ hA0 (by linarith) 2

end SteadyCert

end Breakdown
