import Breakdown.FracCell.StClauses

open scoped ContDiff ENNReal
open MeasureTheory Matrix

noncomputable section

namespace Breakdown

namespace CellCert

open SteadyCert

namespace ModelLowerInternal

theorem chosen_spec {m : ℕ} {v : Space → Space} {G : Space → (Space →L[ℝ] Space)}
    {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)} (hv : IsSecondOrderField m v G H) :
    IsSecondOrderField m v (FracCellData.chosenGrad m v) (FracCellData.chosenSecond m v) := by
  have h : ∃ G H, IsSecondOrderField m v G H := ⟨G, H, hv⟩
  unfold FracCellData.chosenGrad FracCellData.chosenSecond
  rw [dif_pos h, dif_pos h]
  exact h.choose_spec.choose_spec

theorem weightedEnergy_congr {wt : Space → ℝ} {G G' : Space → (Space →L[ℝ] Space)}
    {H H' : Space → (Space →L[ℝ] Space →L[ℝ] Space)} (hG : G =ᵐ[volume] G') (hH : H =ᵐ[volume] H') :
    weightedEnergy wt G H = weightedEnergy wt G' H' := by
  unfold weightedEnergy
  congr 1
  · exact integral_congr_ae (hH.mono fun y hy => by simp only [hy])
  · exact integral_congr_ae (hG.mono fun y hy => by simp only [hy])

theorem weightedEnergy_nonneg {wt : Space → ℝ} (hw : ∀ y, 0 ≤ wt y) (G : Space → (Space →L[ℝ] Space))
    (H : Space → (Space →L[ℝ] Space →L[ℝ] Space)) : 0 ≤ weightedEnergy wt G H := by
  unfold weightedEnergy
  have h1 : 0 ≤ ∫ y, ‖secondTrace (H y)‖ ^ 2 := integral_nonneg fun y => by positivity
  have h2 : 0 ≤ ∫ y, wt y * entrySq (G y) :=
    integral_nonneg fun y => mul_nonneg (hw y) (by unfold entrySq; positivity)
  linarith

end ModelLowerInternal

open ModelLowerInternal in
theorem modelLower_of (h1 : ChosenAgreeStatement) (h2 : ClassAverageRowsStatement) (h3 : ModelRegularStatement) :
    ModelLowerStatement := by
  intro α hα1 hα2 k N c hc p hp v G H hv κ Q hQ
  have hv' : IsSecondOrderField c.order v G H := hv
  have hch := chosen_spec hv'
  obtain ⟨hGa, hHa⟩ := h1 c.order v G H hv'
  obtain ⟨hmeas, hloc⟩ := h3 α hα1 hα2 c hc p hp v G H hv κ
  obtain ⟨Q', hQ'g, hQ'c, hrows⟩ := h2 α c hc
    (c.modelFieldOf α v (FracCellData.chosenGrad c.order v) (FracCellData.chosenSecond c.order v) κ)
    hmeas hloc Q hQ
  have hq := hc.form_nonneg v _ _ hch κ Q' hQ'g hQ'c
  have hE : weightedEnergy c.weight G H = weightedEnergy c.weight (FracCellData.chosenGrad c.order v)
      (FracCellData.chosenSecond c.order v) := weightedEnergy_congr hGa.symm hHa.symm
  have hEnn : 0 ≤ weightedEnergy c.weight G H :=
    weightedEnergy_nonneg (fun y => hc.base.weightMin_pos.le.trans (hc.base.weight_lower y)) G H
  have hS : (c.toCertData α).size G H κ ^ 2 =
      weightedEnergy c.weight G H + c.multiplierScale ^ 2 * ∑ i, κ i ^ 2 := by
    show Real.sqrt (weightedEnergy c.weight G H + c.multiplierScale ^ 2 * ∑ i, κ i ^ 2) ^ 2 = _
    exact Real.sq_sqrt (add_nonneg hEnn (mul_nonneg (sq_nonneg _) (Finset.sum_nonneg fun i _ => sq_nonneg _)))
  show c.coercivity * (c.toCertData α).size G H κ ^ 2 ≤
    c.formOf α v (FracCellData.chosenGrad c.order v) (FracCellData.chosenSecond c.order v) κ
      + c.toFracCertData.rows (fun y => c.modelFieldOf α v (FracCellData.chosenGrad c.order v)
          (FracCellData.chosenSecond c.order v) κ y + Q y) ^ 2
      + c.pinWeight * ∑ i, c.pinOf (FracCellData.chosenGrad c.order v) i ^ 2
  rw [hS, hE]
  unfold FracCellData.quadForm at hq
  rw [hrows] at hq
  nlinarith [hq]

end CellCert

end Breakdown
