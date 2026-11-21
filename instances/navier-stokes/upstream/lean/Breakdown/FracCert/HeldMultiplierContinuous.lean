import Breakdown.FracCert.StHeldParts

open MeasureTheory Filter Topology

noncomputable section

namespace Breakdown

namespace SteadyCert

namespace HeldMultiplierContinuousInternal

theorem sqrt_energy_le_size {k N : ℕ} (d : FracCertData k N) (G : Space → (Space →L[ℝ] Space))
    (H : Space → (Space →L[ℝ] Space →L[ℝ] Space)) (κ : Fin k → ℝ) :
    Real.sqrt (d.energy G H) ≤ d.size G H κ := by
  unfold FracCertData.size sizeNorm FracCertData.energy
  apply Real.sqrt_le_sqrt
  have : 0 ≤ d.multiplierScale ^ 2 * ∑ i, κ i ^ 2 :=
    mul_nonneg (sq_nonneg _) (Finset.sum_nonneg fun i _ => sq_nonneg _)
  linarith

theorem size_nonneg {k N : ℕ} (d : FracCertData k N) (G : Space → (Space →L[ℝ] Space))
    (H : Space → (Space →L[ℝ] Space →L[ℝ] Space)) (κ : Fin k → ℝ) :
    0 ≤ d.size G H κ := by
  unfold FracCertData.size sizeNorm
  exact Real.sqrt_nonneg _

theorem held_radius_le {k N : ℕ} (d : FracCertData k N) (h : 0 ≤ d.heldRadius) :
    d.heldRadius ≤ 2 * d.sizeBound := by
  unfold FracCertData.heldRadius radiusOf at *
  have hs : 0 ≤ Real.sqrt (1 - 4 * d.rowConst * d.productConst * d.sizeBound) := Real.sqrt_nonneg _
  have hpos : 0 < 1 + Real.sqrt (1 - 4 * d.rowConst * d.productConst * d.sizeBound) := by linarith
  have h2 : 0 ≤ 2 * d.sizeBound := by
    have := mul_nonneg h hpos.le
    rwa [div_mul_cancel₀ _ hpos.ne'] at this
  exact div_le_self h2 (by linarith)

theorem unique_condition {α : ℝ} {k N : ℕ} (d : FracCertData k N) (hd : IsFracCert α d)
    (G G' : Space → (Space →L[ℝ] Space)) (H H' : Space → (Space →L[ℝ] Space →L[ℝ] Space))
    (κ κ' : Fin k → ℝ) (h : d.size G H κ ≤ d.heldRadius) (h' : d.size G' H' κ' ≤ d.heldRadius) :
    (Real.sqrt (d.energy G H) + Real.sqrt (d.energy G' H')) * (d.rowConst * d.productConst) < 1 := by
  have e1 := sqrt_energy_le_size d G H κ
  have e2 := sqrt_energy_le_size d G' H' κ'
  have hr := held_radius_le d ((size_nonneg d G H κ).trans h)
  have hsum0 : 0 ≤ Real.sqrt (d.energy G H) + Real.sqrt (d.energy G' H') := by positivity
  have hsum : Real.sqrt (d.energy G H) + Real.sqrt (d.energy G' H') ≤ 4 * d.sizeBound := by linarith
  have hsmall := hd.size_small
  rcases le_or_gt 0 (d.rowConst * d.productConst) with hc | hc
  · calc (Real.sqrt (d.energy G H) + Real.sqrt (d.energy G' H')) * (d.rowConst * d.productConst)
        ≤ 4 * d.sizeBound * (d.rowConst * d.productConst) := mul_le_mul_of_nonneg_right hsum hc
      _ = 4 * d.rowConst * d.productConst * d.sizeBound := by ring
      _ < 1 := hsmall
  · have : (Real.sqrt (d.energy G H) + Real.sqrt (d.energy G' H')) * (d.rowConst * d.productConst) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hsum0 hc.le
    linarith

end HeldMultiplierContinuousInternal

open HeldMultiplierContinuousInternal in
theorem heldMultiplierContinuous (h1 : HeldExistsStatement) (h2 : HeldUniqueStatement)
    (h3 : HeldLimitStatement) : HeldMultiplierContinuousStatement := by
  intro α hα1 hα2 k N d hd
  have hex := h1 α hα1 hα2 d hd
  choose! u G H P κ hsol hsize using hex
  refine ⟨fun p i => d.multiplier p i + κ p i, ?_, ?_⟩
  · have hκ : ContinuousOn κ (box d.radius) := by
      intro q hq
      show Tendsto κ (𝓝[box d.radius] q) (𝓝 (κ q))
      apply tendsto_of_subseq_tendsto
      intro ns hns
      rw [tendsto_nhdsWithin_iff] at hns
      obtain ⟨hlim, hev⟩ := hns
      obtain ⟨M, hM⟩ := eventually_atTop.mp hev
      have hpbox : ∀ n, ns (n + M) ∈ box d.radius := fun n => hM _ (Nat.le_add_left _ _)
      have hplim : Tendsto (fun n => ns (n + M)) atTop (𝓝 q) := hlim.comp (tendsto_add_atTop_nat M)
      obtain ⟨φ, -, u₀, G₀, H₀, P₀, κ₀, hs₀, hz₀, hκ₀⟩ :=
        h3 α hα1 hα2 d hd (fun n => ns (n + M)) q hpbox hq hplim (fun n => u (ns (n + M)))
          (fun n => G (ns (n + M))) (fun n => H (ns (n + M))) (fun n => P (ns (n + M)))
          (fun n => κ (ns (n + M))) (fun n => hsol _ (hpbox n)) (fun n => hsize _ (hpbox n))
      have heq : κ₀ = κ q := (h2 α hα1 hα2 d hd q hq _ _ _ _ _ _ _ _ _ _ hs₀ (hsol q hq)
        (unique_condition d hd _ _ _ _ _ _ hz₀ (hsize q hq))).2
      refine ⟨fun n => φ n + M, ?_⟩
      rw [← heq]
      exact hκ₀
    exact hd.multiplier_continuous.add hκ
  · intro p hp
    have hfun : (fun i => d.multiplier p i + κ p i - d.multiplier p i) = κ p := by
      funext i
      ring
    refine ⟨u p, G p, H p, P p, ?_⟩
    rw [hfun]
    exact ⟨hsol p hp, hsize p hp⟩

end SteadyCert

end Breakdown
