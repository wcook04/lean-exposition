import PCP.Complexity.InterpolationWeightLang

/-! # Fixed field expressions for the generator constraint's Lagrange weights -/

namespace PCP.Lang.FieldExpression

open PCP.Algebraic BinaryFieldCode Finset

variable {t : ℕ} [NeZero t]

def generatorPower : ℕ → Term 1
  | 0 => .bit true
  | n+1 => .bin .mul (.input 0) (generatorPower n)

@[simp] theorem generatorPower_eval (ζ : BinaryMaterializedField.Element t) (n : ℕ) :
    (generatorPower n).eval (fun _ => ζ) = ζ ^ n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [generatorPower, Term.eval, Op.fieldEval, ih, pow_succ']

def generatorWeightTerm (c : ℕ) (i : Fin (c + 1)) : Term 1 :=
  Term.product (((List.finRange (c+1)).filter (fun j => decide (j ≠ i))).map
    fun j => .bin .mul (generatorPower (j.val+1))
      (.inv (.bin .add (generatorPower (i.val+1)) (generatorPower (j.val+1)))))

theorem generatorWeightTerm_eval (ζ : BinaryMaterializedField.Element t)
    {c : ℕ} (i : Fin (c+1)) :
    (generatorWeightTerm c i).eval (fun _ => ζ) =
      FieldQueryArithmetic.interpolationWeight (GeneratorLowDegreeTest.nodes c ζ) 0 i := by
  simp only [generatorWeightTerm, Term.eval_product, List.map_map]
  have hno := (List.nodup_finRange (c+1)).filter (fun j => decide (j ≠ i))
  have hset : ((List.finRange (c+1)).filter (fun j => decide (j ≠ i))).toFinset =
      univ.erase i := by ext j; simp [ne_comm]
  rw [← List.prod_toFinset _ hno, hset]
  unfold FieldQueryArithmetic.interpolationWeight
  apply prod_congr rfl
  intro j _
  simp only [Function.comp_apply, Term.eval, Op.fieldEval, generatorPower_eval,
    GeneratorLowDegreeTest.nodes, div_eq_mul_inv, sub_eq_add_neg, zero_add]
  rfl

def generatorWeight (c : ℕ) (i : Fin (c+1)) : Stmt 37 12 :=
  scalar (generatorWeightTerm c i)

theorem generatorWeight_run (ζ : BinaryMaterializedField.Element t)
    {c : ℕ} (i : Fin (c+1)) (st : State 37 12) (hv : View t (fun _ => ζ) st) :
    ((generatorWeight c i).run st).1.regs 27 =
      (fieldEquiv t (FieldQueryArithmetic.interpolationWeight
        (GeneratorLowDegreeTest.nodes c ζ) 0 i)).val ∧
    View t (fun _ => ζ) ((generatorWeight c i).run st).1 := by
  have h := scalar_spec (generatorWeightTerm c i) st (fun _ => ζ) hv
  rw [generatorWeightTerm_eval] at h
  exact ⟨h.1, h.2.2⟩

theorem generatorWeight_cost (ζ : BinaryMaterializedField.Element t)
    {c : ℕ} (i : Fin (c+1)) (st : State 37 12) (hv : View t (fun _ => ζ) st) :
    ((generatorWeight c i).run st).2 ≤
      ((generatorWeightTerm c i).weight+2)*(t+1)^4 :=
  scalar_cost (generatorWeightTerm c i) st (fun _ => ζ) hv

end PCP.Lang.FieldExpression
