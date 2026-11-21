import Breakdown.Cert.Nodes
import Breakdown.Cert.BoxZero

open MeasureTheory

noncomputable section

namespace Breakdown.Cert

namespace Internal.ExistsZeroHeld

theorem energyW_nonneg_of {w : Space → ℝ} (hw : ∀ y, 0 ≤ w y) (u : XX) : 0 ≤ energyW w u := by
  unfold energyW sliceWeightedGrad
  refine add_nonneg (sq_nonneg _) (integral_nonneg fun t => integral_nonneg fun y => ?_)
  exact mul_nonneg (hw y) (Finset.sum_nonneg fun j _ => sq_nonneg _)

theorem abs_le_sizeZ {k : ℕ} {w : Space → ℝ} (hw : ∀ y, 0 ≤ w y) (u : XX) (κ : Fin k → ℝ)
    (j : Fin k) : |κ j| ≤ sizeZ w u κ := by
  rw [← Real.sqrt_sq_eq_abs]
  unfold sizeZ
  refine Real.sqrt_le_sqrt ?_
  have h1 : κ j ^ 2 ≤ ∑ i, κ i ^ 2 :=
    Finset.single_le_sum (f := fun i => κ i ^ 2) (fun i _ => sq_nonneg (κ i)) (Finset.mem_univ j)
  linarith [energyW_nonneg_of hw u]

theorem abs_add_sub_le {a b c s o : ℝ} (hac : |a - c| ≤ o) (hb : |b| ≤ s) :
    |a + b - c| ≤ s + o := by
  have h : a + b - c = (a - c) + b := by ring
  rw [h]
  exact le_trans (abs_add_le _ _) (by linarith)

theorem multiplierOf_eq {k : ℕ} (d : CertificateData k) (p : Fin k → ℝ)
    (h : ∃ κ, ∃ f, IsHeldSolution d p f κ) : multiplierOf d p = d.multiplier p + h.choose := by
  unfold multiplierOf
  rw [dif_pos h]

end Internal.ExistsZeroHeld

open Internal.ExistsZeroHeld in
theorem existsZeroHeldHolds_of (h1 : HeldExistsUniqueHolds) (h2 : MultiplierContinuityHolds) :
    ExistsZeroHeldHolds := by
  intro k d hd
  have hw : ∀ y, 0 ≤ d.weightFn y := fun y => le_trans hd.weight_pos.le (hd.weightFn_lower y)
  have hex : ∀ p ∈ d.box, ∃ κ, ∃ f, IsHeldSolution d p f κ := by
    intro p hp
    obtain ⟨f, κ, hs, -⟩ := h1 d hd p hp
    exact ⟨κ, f, hs⟩
  have hdev : ∀ p ∈ Set.Icc (d.center - d.radius) (d.center + d.radius), ∀ j,
      |multiplierOf d p j - (d.slope.mulVec (p - d.center)) j| ≤ 2 * d.sizeBound + d.slopeOffset j := by
    intro p hp j
    have he := hex p hp
    obtain ⟨f, hf⟩ := he.choose_spec
    have hκ : |he.choose j| ≤ 2 * d.sizeBound :=
      le_trans (abs_le_sizeZ hw _ _ j) hf.size
    have hm := hd.slope_offset p hp j
    rw [multiplierOf_eq d p he, Pi.add_apply]
    exact abs_add_sub_le hm hκ
  obtain ⟨p, hp, hz⟩ := exists_zero_of_inclusion d.center d.radius hd.radius_nonneg d.slope
    d.slopeInverse hd.slope_inverse (2 * d.sizeBound) d.slopeOffset (multiplierOf d)
    (h2 d hd) hdev hd.inclusion
  have he := hex p hp
  obtain ⟨f, hf⟩ := he.choose_spec
  refine ⟨p, hp, f, he.choose, hf, ?_⟩
  rw [← multiplierOf_eq d p he]
  exact hz

end Breakdown.Cert
