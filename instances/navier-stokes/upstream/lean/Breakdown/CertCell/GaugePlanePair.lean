import Breakdown.CertCell.GaugePlanePairKeys

open MeasureTheory ComplexConjugate

noncomputable section

namespace Breakdown.CertCell

namespace PlanePairInternal

open PlaneFlipFacts

structure PlaneTraceFacts : Prop where
  lift : CellCalculus.HarmonicLiftStatement
  second : PeriodicSecondOrderHolds
  strip : StripDataFlipAxisHolds
  corner : CornerDataFlipAxisHolds
  pressure : PressureStripFlipHolds
  shift : PotentialShiftHolds
  square : HarmonicPressureSquareHolds
  flip : HarmonicPressureFlipHolds

end PlanePairInternal

namespace TreeEntry

open CellCert.CellCoordinates PlanePairInternal

variable {k : ℕ} {C : Type} {nE nM : ℕ} {D : CellLayerData k C nE nM} {R : CellCalculus.CellCalculusEntry D}

theorem fieldPlanePairZero_of (hF : PlaneTraceFacts) (T : TreeEntry D R) : T.FieldPlanePairZero := by
  intro q v G H g Pg hyp ι key imag hom hhalf
  obtain ⟨-, hmc, hp, hPP, hPf⟩ := hyp
  obtain ⟨h12, hl, hmode, hsign⟩ := hom
  have ht : labelTime ι = 0 := by simp only [labelTime]; omega
  rw [ht, keyHarmonic_at_zero]
  cases key with
  | velocity n rad lev lo hi t a d =>
      have hn : n = 2 * ι.2 := by simp only [GaugeKey.keyMode, Option.some.injEq] at hmode; omega
      subst hn
      by_cases hc : rad = false ∧ lev = 0
      · obtain ⟨rfl, rfl⟩ := hc
        simp only [GaugeKey.planeSign, true_and, if_true, Option.some.injEq] at hsign
        simp only [GaugeKey.KeyInHalfPlane, Bool.false_eq_true, if_false] at hhalf
        exact keyPart_zero_of_conj (velocity_key_conj hF.lift hF.second Pg hp hmc.flip T.keyLayout ι.2 hF.strip
          hi t a d hhalf) hsign
      · exfalso
        simp [GaugeKey.planeSign, hc] at hsign
  | gradient n rad lev lo hi t a d =>
      have hn : n = 2 * ι.2 := by simp only [GaugeKey.keyMode, Option.some.injEq] at hmode; omega
      subst hn
      by_cases hc : rad = false ∧ lev = 0
      · obtain ⟨rfl, rfl⟩ := hc
        simp only [GaugeKey.planeSign, true_and, if_true, Option.some.injEq] at hsign
        simp only [GaugeKey.KeyInHalfPlane, Bool.false_eq_true, if_false] at hhalf
        exact keyPart_zero_of_conj (gradient_key_conj hF.lift hF.second Pg hp hmc.flip T.keyLayout ι.2 hF.strip
          hi t a d hhalf) hsign
      · exfalso
        simp [GaugeKey.planeSign, hc] at hsign
  | pressure n rad lev lo hi t d =>
      by_cases hc : rad = false ∧ lev = 0
      · obtain ⟨rfl, rfl⟩ := hc
        simp only [GaugeKey.planeSign, true_and, if_true, Option.some.injEq] at hsign
        simp only [GaugeKey.KeyInHalfPlane, Bool.false_eq_true, if_false] at hhalf
        refine keyPart_zero_of_conj (s := 1) ?_ (hsign.imp_left fun h => ⟨rfl, h⟩)
        rw [Complex.ofReal_one, one_mul]
        exact pressure_key_conj hF.pressure hF.shift hF.square hF.flip hPP hPf T.keyLayout n hi t d hhalf
      · exfalso
        simp [GaugeKey.planeSign, hc] at hsign
  | corner n p a =>
      have hn : n = 2 * ι.2 := by simp only [GaugeKey.keyMode, Option.some.injEq] at hmode; omega
      subst hn
      obtain ⟨pr, pz⟩ := p
      by_cases hc : pz = 0
      · subst hc
        simp only [GaugeKey.planeSign, if_true, Option.some.injEq] at hsign
        simp only [GaugeKey.KeyInHalfPlane] at hhalf
        exact keyPart_zero_of_conj (corner_key_conj hF.lift hF.second Pg hp hmc.flip T.keyLayout ι.2 hF.corner a
          hhalf) hsign
      · exfalso
        simp [GaugeKey.planeSign, hc] at hsign
  | stream p =>
      exfalso
      simp only [GaugeKey.keyMode, Option.some.injEq] at hmode
      omega
  | private_ =>
      exfalso
      simp [GaugeKey.keyMode] at hmode

end TreeEntry

end Breakdown.CertCell

