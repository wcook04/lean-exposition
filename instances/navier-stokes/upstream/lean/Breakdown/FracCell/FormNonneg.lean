import Breakdown.FracCell.StAssembly
import Breakdown.FracCell.TreeFinal

open MeasureTheory Matrix

noncomputable section

namespace Breakdown

namespace CellCert

namespace Assembly

open SteadyCert _root_.Breakdown.CellCert.Finite

namespace FormNonnegInternal

variable {k N : ℕ}

def admissibleSpace (c : FracCellData k N) (hadm : AdmissibleLinearStatement) :
    Submodule ℝ (FieldTuple k) where
  carrier := {x | IsAdmissible c x}
  add_mem' := fun hx hy => (hadm c).2.1 _ _ hx hy
  zero_mem' := (hadm c).1
  smul_mem' := fun r _ hx => (hadm c).2.2 r _ hx

def momentMap (c : FracCellData k N) (hadm : AdmissibleLinearStatement) (S : CellSplit k N) {α : ℝ}
    (hS : S.IsCellSplit c α) : admissibleSpace c hadm →ₗ[ℝ] (Fin S.slots → ℝ) where
  toFun x := S.moment x.1
  map_add' x y := hS.moment_additive x.1 y.1 x.2 y.2
  map_smul' r x := hS.moment_homogeneous r x.1 x.2

theorem single_zero' (i : Fin 3) : EuclideanSpace.single i (0 : ℝ) = 0 :=
  (PiLp.single_eq_zero_iff 2 i).mpr rfl

theorem modelField_zero (c : FracCellData k N) (α : ℝ) :
    (fun y => c.modelFieldOf α (0 : Space → Space) 0 0 0 y + (0 : Space → Space) y) = fun _ => 0 := by
  funext y
  simp [FracCellData.modelFieldOf, driftField, secondTrace, crossVec, curlOf, entry, axialTurn, single_zero']

theorem quadForm_zero (c : FracCellData k N) (α : ℝ) :
    c.quadForm α 0 0 0 0 0 ≤ 0 := by
  rw [FracCellData.quadForm, modelField_zero]
  simp [FracCellData.formOf, weightedEnergy, fullSecondSq, curlGradSq, jForm, curlOf, entry, entrySq,
    FracCellData.pinOf, pinValue, entryInner, FracCertData.rows, rowSize, l2Pair, secondTrace]

end FormNonnegInternal

theorem formNonneg_of_tree_of (hsplit : QuadFormSplitStatement) (hadm : AdmissibleLinearStatement) (α : ℝ) (hα₁ : 1 < α) (hα₂ : α < 5 / 4) {k N : ℕ} (c : FracCellData k N)
    (hc : IsFormData α c) (S : CellSplit k N) (hS : S.IsCellSplit c α) (T : TreeCertificate S.slots k)
    (hT : IsTreeCertificate T)
    (hcells : ∃ e : T.Cell ≃ Fin S.cellCount ⊕ Fin S.delayCount,
      ∀ K, T.cellForm K = Sum.elim S.cellMatrix S.delayForm (e K))
    (hglobal : T.globalForm = S.globalMatrix c) :
    ∀ v G H, IsSecondOrderField c.order v G H → ∀ κ : Fin k → ℝ, ∀ Q, IsGradientField Q →
      IsClassField c.order Q → 0 ≤ c.quadForm α v G H κ Q := by
  intro v G H hv κ Q hQ hQc
  obtain ⟨e, he⟩ := hcells
  let V := FormNonnegInternal.admissibleSpace c hadm
  let z₀ := FormNonnegInternal.momentMap c hadm S hS
  let q : V → ℝ := fun x => c.quadForm α x.1.1 x.1.2.1 x.1.2.2.1 x.1.2.2.2.1 x.1.2.2.2.2
  have hq0 : q 0 ≤ 0 := FormNonnegInternal.quadForm_zero c α
  have hx0 : (v, G, H, κ, Q) ∈ V := (⟨hv, hQ, hQc⟩ : IsAdmissible c (v, G, H, κ, Q))
  refine tree_final V q z₀ S.freeMap T hT hq0 ?_ ⟨(v, G, H, κ, Q), hx0⟩
  intro x u
  let _ := T.cellFintype
  have hx : IsAdmissible c x.1 := x.2
  have hsum : (∑ K, T.cellForm K) = (∑ K, S.cellMatrix K) + ∑ j, S.delayForm j := by
    rw [Finset.sum_congr rfl (fun K _ => he K), Equiv.sum_comp e (Sum.elim S.cellMatrix S.delayForm),
      Fintype.sum_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr]
  have hst : (Sum.elim (z₀ x + S.freeMap *ᵥ u) u : Fin S.slots ⊕ Fin k → ℝ) = S.stateOf x.1 u := rfl
  show quadValue ((∑ K, T.cellForm K) + T.globalForm) (Sum.elim (z₀ x + S.freeMap *ᵥ u) u) ≤
    c.quadForm α x.1.1 x.1.2.1 x.1.2.2.1 x.1.2.2.2.1 x.1.2.2.2.2
  rw [hst, hsum, hglobal, TreeFinalInternal.quad_add, TreeFinalInternal.quad_add,
    TreeFinalInternal.quad_sum, TreeFinalInternal.quad_sum]
  have h2 : ∑ j, quadValue (S.delayForm j) (S.stateOf x.1 u) = 0 :=
    Finset.sum_eq_zero (fun j _ => hS.delay_vanish j x.1 hx u)
  have h3 := hS.exterior_bound x.1 hx
  have h4 := hsplit α hα₁ hα₂ c hc S hS x.1 hx u
  have h5 : ∑ K, quadValue (S.cellMatrix K) (S.stateOf x.1 u) ≤ ∑ K, S.cellPart c α K x.1 u :=
    Finset.sum_le_sum (fun K _ => hS.cell_bound K x.1 hx u)
  rw [h2]
  linarith

end Assembly

end CellCert

end Breakdown
