import PCP.Complexity.FieldExpressionCost
import PCP.Algebraic.FieldQueryArithmetic

/-!
# Concrete programs for the interpolation weights

For each fixed degree and node index, one fixed language program computes the
Lagrange weight on natural field codes. The field width and node values remain
inputs. In particular, the production degree four gives five fixed programs.
-/

namespace PCP.Lang.FieldExpression

open PCP.Algebraic BinaryField BinaryFieldCode Finset

variable {n t : ℕ}

/-- A finite product is expanded into fixed arithmetic code. -/
def Term.product : List (Term n) → Term n
  | [] => .bit true
  | a :: as => .bin .mul a (Term.product as)

@[simp] theorem Term.eval_product [NeZero t]
    (env : Fin n → BinaryMaterializedField.Element t) (xs : List (Term n)) :
    (Term.product xs).eval env = (xs.map (Term.eval env)).prod := by
  induction xs with
  | nil => simp [Term.product, Term.eval]
  | cons a as ih => simp [Term.product, Term.eval, ih, Op.fieldEval]

/-- Node values occupy the first `c+1` inputs and the independent sample is last. -/
def interpolationEnv {c : ℕ} (a : Fin (c + 1) → BinaryMaterializedField.Element t)
    (z : BinaryMaterializedField.Element t) : Fin (c + 2) → BinaryMaterializedField.Element t :=
  Fin.lastCases z a

/-- In characteristic two the two differences are sums, including zero coefficients. -/
def interpolationTerm (c : ℕ) (i : Fin (c + 1)) : Term (c + 2) :=
  Term.product (((List.finRange (c + 1)).filter (fun j => decide (j ≠ i))).map
    fun j : Fin (c + 1) =>
    .bin .mul (.bin .add (.input (Fin.last (c + 1))) (.input j.castSucc))
      (.inv (.bin .add (.input i.castSucc) (.input j.castSucc))))

/-- The expression is precisely the generator test's field interpolation weight. -/
theorem interpolationTerm_eval [NeZero t] {c : ℕ}
    (a : Fin (c + 1) → BinaryMaterializedField.Element t)
    (z : BinaryMaterializedField.Element t) (i : Fin (c + 1)) :
    (interpolationTerm c i).eval (interpolationEnv a z) =
      FieldQueryArithmetic.interpolationWeight a z i := by
  simp only [interpolationTerm, Term.eval_product, List.map_map]
  have hno : ((List.finRange (c + 1)).filter (fun j => decide (j ≠ i))).Nodup :=
    (List.nodup_finRange (c + 1)).filter _
  have hset : ((List.finRange (c + 1)).filter (fun j => decide (j ≠ i))).toFinset =
      univ.erase i := by ext j; simp [ne_comm]
  rw [← List.prod_toFinset _ hno, hset]
  unfold FieldQueryArithmetic.interpolationWeight
  apply Finset.prod_congr rfl
  intro j _
  simp only [Function.comp_apply, Term.eval, interpolationEnv, Fin.lastCases_last,
    Fin.lastCases_castSucc, Op.fieldEval]
  rw [div_eq_mul_inv, sub_eq_add_neg, sub_eq_add_neg]
  rfl

/-- One actual fixed program for each interpolation node, with no proof-table lookup. -/
def interpolation (c : ℕ) (i : Fin (c + 1)) : Stmt (c + 2 + 36) 12 :=
  scalar (interpolationTerm c i)

theorem interpolation_run [NeZero t] {c : ℕ}
    (a : Fin (c + 1) → BinaryMaterializedField.Element t)
    (z : BinaryMaterializedField.Element t) (i : Fin (c + 1))
    (st : State (c + 2 + 36) 12) (hv : View t (interpolationEnv a z) st) :
    ((interpolation c i).run st).1.regs (slot (c + 2) 26) =
      (fieldEquiv t (FieldQueryArithmetic.interpolationWeight a z i)).val ∧
      ((interpolation c i).run st).1.lists 11 = st.lists 11 ∧
      View t (interpolationEnv a z) ((interpolation c i).run st).1 := by
  simpa only [interpolation, interpolationTerm_eval] using scalar_spec (interpolationTerm c i) st
    (interpolationEnv a z) hv

/-- The fixed degree contributes only a syntactic constant to the quartic field-width cost. -/
theorem interpolation_cost [NeZero t] {c : ℕ}
    (a : Fin (c + 1) → BinaryMaterializedField.Element t)
    (z : BinaryMaterializedField.Element t) (i : Fin (c + 1))
    (st : State (c + 2 + 36) 12) (hv : View t (interpolationEnv a z) st) :
    ((interpolation c i).run st).2 ≤ ((interpolationTerm c i).weight + 2) * (t + 1) ^ 4 :=
  scalar_cost (interpolationTerm c i) st (interpolationEnv a z) hv

/-- The affine point coordinate used by every line query is another fixed field expression. -/
def affineTerm : Term 3 := .bin .add (.input 0) (.bin .mul (.input 2) (.input 1))

theorem affineTerm_eval [NeZero t] (u v a : BinaryMaterializedField.Element t) :
    affineTerm.eval ![u, v, a] = u + a * v := by rfl

end PCP.Lang.FieldExpression
