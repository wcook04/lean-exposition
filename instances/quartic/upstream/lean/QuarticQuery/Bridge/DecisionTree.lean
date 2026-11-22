module

public import QuarticQuery.Model.Quantum
public import Complexity.Computability.DecisionTree.Basic

/-!
# Decision trees: our `QueryTree` and complexitylib's `DecisionTree`

The two inductive types are the same tree with renamed constructors. The maps
below are mutually inverse and preserve evaluation and depth, so `D` of a total
function is `Cslib.DecisionTree.complexity`, in both directions.
-/

public section

namespace QuarticQuery

open Cslib

variable {ι : Type}

namespace QueryTree

/-- Ledger: def-D. Rename constructors. -/
def toDecisionTree : QueryTree ι → DecisionTree ι Bool
  | .leaf b => .leaf b
  | .query i l r => .node i l.toDecisionTree r.toDecisionTree

/-- Ledger: def-D. Rename constructors back. -/
def ofDecisionTree : DecisionTree ι Bool → QueryTree ι
  | .leaf b => .leaf b
  | .node i l r => .query i (ofDecisionTree l) (ofDecisionTree r)

theorem ofDecisionTree_toDecisionTree (t : QueryTree ι) :
    ofDecisionTree t.toDecisionTree = t := by
  induction t with
  | leaf b => rfl
  | query i l r ihl ihr => simp only [toDecisionTree, ofDecisionTree, ihl, ihr]

theorem toDecisionTree_ofDecisionTree (t : DecisionTree ι Bool) :
    (ofDecisionTree t).toDecisionTree = t := by
  induction t with
  | leaf b => rfl
  | node i l r ihl ihr => simp only [toDecisionTree, ofDecisionTree, ihl, ihr]

/-- Ledger: def-D. The translation keeps the output on every input. -/
theorem eval_toDecisionTree (t : QueryTree ι) (x : BitInput ι) :
    t.toDecisionTree.eval x = t.eval x := by
  induction t with
  | leaf b => rfl
  | query i l r ihl ihr =>
    rw [toDecisionTree, DecisionTree.eval_node, ihl, ihr, eval_query]
    cases x i <;> rfl

/-- Ledger: def-D. The translation keeps the depth. -/
theorem depth_toDecisionTree (t : QueryTree ι) : t.toDecisionTree.depth = t.depth := by
  induction t with
  | leaf b => rfl
  | query i l r ihl ihr =>
    rw [toDecisionTree, DecisionTree.depth_node, ihl, ihr, depth_query]
    omega

end QueryTree

/-- Ledger: def-D. `D` on a total function is complexitylib's decision tree
complexity. -/
theorem D_totalise_eq_complexity [Fintype ι] (f : TotalBool ι) :
    D (totalise f) = DecisionTree.complexity f := by
  apply le_antisymm
  · obtain ⟨t, ht, hd⟩ := DecisionTree.exists_computes_depth_eq_complexity f
    refine D_le_of_DLe ⟨QueryTree.ofDecisionTree t, ?_, fun x b hx => ?_⟩
    · rw [← QueryTree.depth_toDecisionTree, QueryTree.toDecisionTree_ofDecisionTree, hd]
    · rw [← QueryTree.eval_toDecisionTree, QueryTree.toDecisionTree_ofDecisionTree, ht x]
      exact Option.some.inj hx
  · obtain ⟨T, hT, hc⟩ := DLe_D (totalise f)
    have hcomp : T.toDecisionTree.Computes f := fun x => by
      rw [QueryTree.eval_toDecisionTree]
      exact hc x (f x) rfl
    exact (DecisionTree.complexity_le_depth hcomp).trans
      ((QueryTree.depth_toDecisionTree T).trans_le hT)

end QuarticQuery
