import PCP.Complexity.ThreeColorBaseBranchState
import PCP.Complexity.ThreeColorBaseOuterCost
import PCP.Complexity.ThreeColorBaseDifferenceCost
import PCP.Complexity.ThreeColorBaseDerivedCost

/-! # A uniform actual cost bound for all seven production branches -/

namespace PCP.Lang.ThreeColorBaseBranches

open PCP.Algebraic ThreeColorFullFieldSampling

def BranchCost (C d : ℕ) : Prop :=
  ∀ (x bits bs : List Bool) (qs : List ℕ),
    Valid (ThreeColorBaseSeed.sample (ThreeColorEncoding.vertexCount x) bits) →
    ∀ (i : Fin 7) (st : State 400 128), Context x bits bs qs st →
      ((branch i).run st).2 ≤ C*(x.length+listSize qs+bs.length+1)^d

theorem enlarge_monomial {a C D b d e : ℕ} (h : a ≤ C * b ^ d)
    (hC : C ≤ D) (hde : d ≤ e) (hb : 1 ≤ b) : a ≤ D*b^e :=
  h.trans (Nat.mul_le_mul hC (Nat.pow_le_pow_right hb hde))

attribute [local irreducible] ThreeColorBaseOuter.program ThreeColorBaseDerived.program
  ThreeColorBaseDifference.program ThreeColorBaseOuter.costConstant
  ThreeColorBaseOuter.budgetConstant ThreeColorBaseDifference.costConstant

theorem branch_input_cost : ∃ C d : ℕ, BranchCost C d := by
  obtain ⟨Cd,dd,hd⟩ := ThreeColorBaseDerived.program_input_cost
  let Co := fun k => ThreeColorBaseOuter.costConstant k*ThreeColorBaseOuter.budgetConstant^18
  let Cf := ThreeColorBaseDifference.costConstant*ThreeColorBaseOuter.budgetConstant^8
  let C := Cd+Co .color+Co .valid+Co .difference+Co .proper+Cf
  let d := max dd 432
  refine ⟨C,d,?_⟩
  intro x bits bs qs hv i st hc
  have hbase : 1 ≤ x.length+listSize qs+bs.length+1 := by omega
  have ho (k : OuterBranch.Kind) : ((ThreeColorBaseOuter.program k).run st).2 ≤
      C*(x.length+listSize qs+bs.length+1)^d := by
    apply enlarge_monomial (ThreeColorBaseOuter.program_input_cost k x bits qs bs st
      hc.ready.data hc.ready.cardinal hc.ready.seeds hc.history hc.ready.sources.answers)
    · change Co k ≤ C
      cases k <;> dsimp only [C] <;> omega
    · exact le_max_right dd 432
    · exact hbase
  have hg (k : LocalCorrection.Certificate) : ((ThreeColorBaseDerived.program k).run st).2 ≤
      C*(x.length+listSize qs+bs.length+1)^d := by
    apply enlarge_monomial (hd k x bits qs bs st hc.ready.data hc.ready.cardinal
      hc.ready.seeds hv hc.ready.sources.graph hc.history hc.ready.sources.answers)
    · dsimp only [C]; omega
    · exact le_max_left dd 432
    · exact hbase
  have hf : (ThreeColorBaseDifference.program.run st).2 ≤
      C*(x.length+listSize qs+bs.length+1)^d := by
    apply enlarge_monomial (ThreeColorBaseDifference.program_input_cost x bits qs bs st
      hc.ready.data hc.ready.cardinal hc.ready.seeds hc.history hc.ready.sources.answers)
    · change Cf ≤ C
      dsimp only [C]; omega
    · exact (by decide : 192 ≤ 432).trans (le_max_right dd 432)
    · exact hbase
  fin_cases i
  · exact ho .color
  · exact ho .valid
  · exact ho .difference
  · exact ho .proper
  · exact hg .valid
  · exact hg .proper
  · exact hf

end PCP.Lang.ThreeColorBaseBranches
