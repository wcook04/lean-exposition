import PCP.Complexity.InterpolationWeightLoad

/-!
# Charged cost of loading and evaluating an interpolation weight
-/

namespace PCP.Lang.InterpolationWeightLoad

open PCP.Algebraic BinaryFieldCode FieldExpression

variable {t : ℕ} [NeZero t]

theorem load_cost (a : Fin 5 → BinaryMaterializedField.Element t)
    (z : BinaryMaterializedField.Element t) (st : State 48 14) (hc : Context a z st) :
    (load.run st).2 ≤ 40*(t+1) := by
  have ha (i : Fin 5) : Nat.size (fieldEquiv t (a i)).val ≤ t :=
    Nat.size_le.mpr (fieldEquiv t (a i)).isLt
  have hz : Nat.size (fieldEquiv t z).val ≤ t := Nat.size_le.mpr (fieldEquiv t z).isLt
  change Nat.size (code z.coefficients) ≤ t at hz
  have ht := size_le_self t
  have hlist : listSize (List.ofFn (fun i => (fieldEquiv t (a i)).val)) ≤ 5*(t+1) := by
    simp only [listSize, List.map_ofFn, Fin.sum_ofFn]
    calc
      _ ≤ ∑ _i : Fin 5, (t+1) := Finset.sum_le_sum fun i _ => Nat.add_le_add_right (ha i) 1
      _ = _ := by simp
  simp [load, Stmt.run, Expr.cost, Expr.readSize, Expr.eval, Function.update,
    hc.1, hc.2.1, hc.2.2.2.2, listSize] at ⊢ hlist
  have h0 := ha 0
  have h1 := ha 1
  have h2 := ha 2
  have h3 := ha 3
  have h4 := ha 4
  omega

/-- A fixed syntactic constant bounds every one of the five weight programs. -/
def constant : ℕ := 41 + ∑ i : Fin 5, ((interpolationTerm 4 i).weight + 2)

theorem program_cost (a : Fin 5 → BinaryMaterializedField.Element t)
    (z : BinaryMaterializedField.Element t) (i : Fin 5) (st : State 48 14)
    (hc : Context a z st) :
    ((program i).run st).2 ≤ constant*(t+1)^4 := by
  have hl := load_cost a z st hc
  have hv := load_view a z st hc
  have hw := FieldExpression.interpolation_cost a z i _ hv
  have he := congrArg Prod.snd (weight_result i (load.run st).1)
  dsimp only [Prod.snd] at he
  rw [← he] at hw
  have hi : (interpolationTerm 4 i).weight+2 ≤
      ∑ j : Fin 5, ((interpolationTerm 4 j).weight+2) :=
    Finset.single_le_sum (f := fun j : Fin 5 => (interpolationTerm 4 j).weight+2)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  have hlin : t+1 ≤ (t+1)^4 := Nat.le_self_pow (by decide) _
  have hpos : 1 ≤ (t+1)^4 := Nat.one_le_pow _ _ (by omega)
  rw [program, run_seq_snd]
  unfold constant
  nlinarith [Nat.mul_le_mul_right ((t+1)^4) hi]

end PCP.Lang.InterpolationWeightLoad
