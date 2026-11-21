import Breakdown.FracCell.StCoordsProof

open MeasureTheory Matrix

noncomputable section

namespace Breakdown.CellCert.CellFormula

open SteadyCert Assembly CellAnalysis

namespace ShiftedParamInternal

variable {D : Type} [Fintype D] [DecidableEq D]

private theorem freePart_add (P : ParamData D) (u v : D → ℂ) :
    P.freePart (u + v) = P.freePart u + P.freePart v := by
  funext d
  simp only [ParamData.freePart, Pi.add_apply]
  split_ifs <;> simp

theorem param_add (P : ParamData D) (u v : D → ℂ) : P.param (u + v) = P.param u + P.param v := by
  simp only [ParamData.param, freePart_add, Matrix.mulVec_add, Pi.add_apply, Pi.single_add,
    Finset.sum_add_distrib]
  abel

variable (L : CellLayout)

def presPt (i : L.modes × Fin L.presCount × Fin L.degSide) : L.Datum :=
  Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl i))))

theorem unitAt_presPt (d : L.Datum) (i) (h : presPt L i ≠ d) : L.unitAt d (presPt L i) = 0 := by
  simp [CellLayout.unitAt, h]

theorem velocityAt_presPt (n a j l i) : L.velocityAt n a j l (presPt L i) = 0 := by
  unfold CellLayout.velocityAt
  split_ifs
  · exact unitAt_presPt L _ i (by simp [presPt, CellDatum.lowVelocity])
  · rfl

theorem strainAt_presPt (n a b j l i) : L.strainAt n a b j l (presPt L i) = 0 := by
  unfold CellLayout.strainAt
  split_ifs
  · exact unitAt_presPt L _ i (by simp [presPt, CellDatum.lowStrain])
  · rfl

theorem extraAt_presPt (n e a d i) : L.extraAt n e a d (presPt L i) = 0 := by
  unfold CellLayout.extraAt
  split_ifs
  · exact unitAt_presPt L _ i (by simp [presPt, CellDatum.extraVelocity])
  · rfl

theorem streamAt_presPt (c i) : L.streamAt c (presPt L i) = 0 := by
  cases c with
  | none => rfl
  | some c => exact unitAt_presPt L _ i (by simp [presPt, CellDatum.cornerStream])

theorem sideVelocity_presPt (n s a d i) : L.unitAt (CellDatum.sideVelocity n s a d) (presPt L i) = 0 :=
  unitAt_presPt L _ i (by simp [presPt, CellDatum.sideVelocity])

theorem turnRow_presPt (n a j l i) : L.turnRow n a j l (presPt L i) = 0 := by
  unfold CellLayout.turnRow
  split_ifs <;> simp [velocityAt_presPt]

theorem relationRow_presPt (ρ : L.RelIndex) (i) : L.relationRow ρ (presPt L i) = 0 := by
  rcases ρ with ρ | ρ | ρ | ρ | ρ | ρ | ρ | ρ | ρ | ρ
  · simp only [CellLayout.relationRow, Sum.elim_inl]
    split_ifs <;> simp [Finset.sum_apply, velocityAt_presPt, strainAt_presPt]
  · simp only [CellLayout.relationRow, Sum.elim_inl, Sum.elim_inr]
    split_ifs <;> simp [Finset.sum_apply, velocityAt_presPt, strainAt_presPt]
  · simp [CellLayout.relationRow, Finset.sum_apply, turnRow_presPt, strainAt_presPt]
  · simp [CellLayout.relationRow, Finset.sum_apply, strainAt_presPt]
  · simp only [CellLayout.relationRow, Sum.elim_inl, Sum.elim_inr]
    rcases L.zeroMode with _ | n0
    · rfl
    · exact strainAt_presPt L _ _ _ _ _ i
  · simp only [CellLayout.relationRow, Sum.elim_inl, Sum.elim_inr]
    split_ifs <;> simp [Finset.sum_apply, velocityAt_presPt, strainAt_presPt, extraAt_presPt]
  · simp [CellLayout.relationRow, Finset.sum_apply, velocityAt_presPt, strainAt_presPt, extraAt_presPt]
  · simp only [CellLayout.relationRow, Sum.elim_inl, Sum.elim_inr]
    rcases L.zeroMode with _ | n0
    · rfl
    · dsimp only
      split_ifs <;> simp [Finset.sum_apply, strainAt_presPt, extraAt_presPt]
  · simp only [CellLayout.relationRow, Sum.elim_inl, Sum.elim_inr]
    rcases L.zeroMode with _ | n0
    · rfl
    · dsimp only
      by_cases hr : (L.segment ρ).radial <;>
        simp [hr, streamAt_presPt, sideVelocity_presPt]
  · simp only [CellLayout.relationRow, Sum.elim_inr]
    split_ifs <;> simp [Finset.sum_apply, extraAt_presPt, sideVelocity_presPt]

theorem relationRow_mul_pressureShift {k : ℕ} (g : GaugeShift k) (x : FieldTuple k) (ρ : L.RelIndex) :
    ∑ d, L.relationRow ρ d * L.pressureShift g x d = 0 := by
  refine Finset.sum_eq_zero fun d _ => ?_
  rcases d with d | d | d | d | d | d | d | d
  · simp [CellLayout.pressureShift]
  · simp [CellLayout.pressureShift]
  · simp [CellLayout.pressureShift]
  · simp [CellLayout.pressureShift]
  · have := relationRow_presPt L ρ d
    simp only [presPt] at this
    simp [this]
  · simp [CellLayout.pressureShift]
  · simp [CellLayout.pressureShift]
  · simp [CellLayout.pressureShift]

end ShiftedParamInternal

open ShiftedParamInternal in
theorem shiftedParam_of_recover (h1 : TrueParamStatement) (h2 : ParamRecoverStatement) : ShiftedParamStatement := by
  intro k N c K S B L hL P sel hP g x hx
  have hsplit : L.shiftedData g x = L.trueData x + L.pressureShift g x := rfl
  have hrel : P.relation *ᵥ L.pressureShift g x = 0 := by
    funext i
    simp only [Matrix.mulVec, dotProduct, hP.rows i, Pi.zero_apply]
    exact relationRow_mul_pressureShift L g x (sel i)
  rw [hsplit, param_add, h1 c K S B L hL P sel hP x hx, h2 P hP.param _ hrel]

end Breakdown.CellCert.CellFormula
