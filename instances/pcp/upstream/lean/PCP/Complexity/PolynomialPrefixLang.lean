/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Complexity.PolynomialBudgetLang
import PCP.Complexity.ArithmeticLookupCost

/-!
# Computing three fixed polynomial budgets and prefixing the input

The program measures the actual source length, evaluates three fixed coefficient
lists, and returns `[T(n), B(n), W(n), n] ++ input`. Its cost and the stored output
size have polynomial bounds for arbitrary lists of natural numbers.
-/

namespace PCP.Lang.PolynomialPrefix

open ArithmeticExpression ArithmeticLookup

variable {n : ℕ}

def hornerTerm : List ℕ → Term n → Term n
  | [], _ => .const 0
  | a :: cs, x => .bin .add (.bin .mul (hornerTerm cs x) x) (.const a)

theorem hornerTerm_eval (cs : List ℕ) (x : Term n) (r : Fin n → ℕ) :
    (hornerTerm cs x).eval r = PolynomialBudget.value cs (x.eval r) := by
  induction cs <;> simp [hornerTerm, Term.eval, Op.eval, PolynomialBudget.value, *]

@[irreducible] def code (time space witness : List ℕ) : Code 4 :=
  .seq (.assign 1 (hornerTerm time (.input 0)))
    (.seq (.assign 2 (hornerTerm space (.input 0))) (.assign 3 (hornerTerm witness (.input 0))))

theorem code_eval (time space witness input : List ℕ) (r : Fin 4 → ℕ) :
    (code time space witness).eval input r =
      ![r 0, PolynomialBudget.value time (r 0), PolynomialBudget.value space (r 0),
        PolynomialBudget.value witness (r 0)] := by
  simp only [code, Code.eval, hornerTerm_eval, Term.eval]
  funext i
  fin_cases i <;> simp [Function.update]

def finish : Stmt 8 3 :=
  .seq (.copy 0 1) (.seq (.push 1 0) (.seq (.push 1 3) (.seq (.push 1 2) (.push 1 1))))

def program (time space witness : List ℕ) : Prog where
  R := 8
  Q := 3
  hQ := by decide
  body := .seq (.len 0 0) (.seq (code time space witness).compile finish)

def afterLength (input : List ℕ) : State 8 3 :=
  ⟨Function.update (fun _ => 0) 0 input.length, fun L => if L = 0 then input else []⟩

theorem program_run (time space witness input : List ℕ) :
    (program time space witness).run input =
      PolynomialBudget.value time input.length :: PolynomialBudget.value space input.length ::
        PolynomialBudget.value witness input.length :: input.length :: input := by
  have h := (code time space witness).spec (afterLength input)
  have hr := h.1.trans (code_eval time space witness input (inputs (afterLength input)))
  have h0 := congrFun hr 0
  have h1 := congrFun hr 1
  have h2 := congrFun hr 2
  have h3 := congrFun hr 3
  change (finish.run ((code time space witness).compile.run (afterLength input)).1).1.lists 1 = _
  simp only [finish, Stmt.run, setList, Function.update_self]
  change ((code time space witness).compile.run (afterLength input)).1.regs 1 ::
    ((code time space witness).compile.run (afterLength input)).1.regs 2 ::
    ((code time space witness).compile.run (afterLength input)).1.regs 3 ::
    ((code time space witness).compile.run (afterLength input)).1.regs 0 ::
    ((code time space witness).compile.run (afterLength input)).1.lists 0 = _
  exact congrArg₂ List.cons h1 (congrArg₂ List.cons h2
    (congrArg₂ List.cons h3 (congrArg₂ List.cons h0 h.2.1)))

/-- The prefix computation and its stored output have uniform polynomial bounds. -/
theorem program_bounds (time space witness : List ℕ) : ∃ C : ℕ, ∀ input : List ℕ,
    (program time space witness).cost input ≤ C * (listSize input + 1) ^ 2 ∧
    listSize ((program time space witness).run input) ≤ C * (listSize input + 1) := by
  obtain ⟨K, _, hK⟩ := (code time space witness).cost_bound
  refine ⟨6 * K + 20, fun input => ?_⟩
  let S := listSize input
  let st := afterLength input
  let out := ((code time space witness).compile.run st).1
  have hn : Nat.size input.length ≤ S := (size_le_self _).trans (length_le_listSize _)
  have hi : ∀ i : Fin 4, Nat.size (inputs st i) ≤ S := by
    intro i
    fin_cases i <;> simp [inputs, st, afterLength, Function.update, S, hn]
  have hl : listSize (st.lists 0) ≤ S := le_refl _
  have hc := (hK st S hi hl).1
  have hb := (hK st S hi hl).2
  have hb0 : Nat.size (out.regs 0) ≤ K * (S + 1) := hb 0
  have hb1 : Nat.size (out.regs 1) ≤ K * (S + 1) := hb 1
  have hb2 : Nat.size (out.regs 2) ≤ K * (S + 1) := hb 2
  have hb3 : Nat.size (out.regs 3) ≤ K * (S + 1) := hb 3
  have hsource : out.lists 0 = input := (code time space witness).spec st |>.2.1
  have hsquare : S + 1 ≤ (S + 1) ^ 2 := by nlinarith
  constructor
  · change S + Nat.size input.length + 1 +
      (((code time space witness).compile.run st).2 + (finish.run out).2 + 1) + 1 ≤ _
    simp only [finish, Stmt.run, setList, hsource]
    change S + Nat.size input.length + 1 +
      (((code time space witness).compile.run st).2 +
        (S + 1 + (Nat.size (out.regs 0) + 1 + (Nat.size (out.regs 3) + 1 +
          (Nat.size (out.regs 2) + 1 + (Nat.size (out.regs 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1
      ≤ (6 * K + 20) * (S + 1) ^ 2
    nlinarith [Nat.mul_le_mul_left K hsquare]
  · change listSize ((finish.run out).1.lists 1) ≤ _
    simp only [finish, Stmt.run, setList, Function.update_self, hsource]
    change Nat.size (out.regs 1) + 1 + (Nat.size (out.regs 2) + 1 +
      (Nat.size (out.regs 3) + 1 + (Nat.size (out.regs 0) + 1 + S))) ≤
        (6 * K + 20) * (S + 1)
    nlinarith

/-- Every three fixed natural polynomials admit this actual budget-prefix program. -/
theorem exists_program (time space witness : Polynomial ℕ) :
    ∃ (P : Prog) (C : ℕ), ∀ input : List ℕ,
      P.run input = time.eval input.length :: space.eval input.length ::
        witness.eval input.length :: input.length :: input ∧
      P.cost input ≤ C * (listSize input + 1) ^ 2 ∧
      listSize (P.run input) ≤ C * (listSize input + 1) := by
  obtain ⟨ct, ht⟩ := PolynomialBudget.exists_coefficients time
  obtain ⟨cb, hb⟩ := PolynomialBudget.exists_coefficients space
  obtain ⟨cw, hw⟩ := PolynomialBudget.exists_coefficients witness
  obtain ⟨C, hC⟩ := program_bounds ct cb cw
  refine ⟨program ct cb cw, C, fun input => ?_⟩
  exact ⟨by rw [program_run, ht, hb, hw], hC input⟩


/-- A fixed coefficient list has an ordinary polynomial growth bound. -/
theorem value_bound (cs : List ℕ) : ∃ C d : ℕ, ∀ n,
    PolynomialBudget.value cs n ≤ C * (n + 1) ^ d := by
  induction cs with
  | nil => exact ⟨0, 0, fun _ => by simp [PolynomialBudget.value]⟩
  | cons a cs ih =>
      obtain ⟨C, d, hC⟩ := ih
      refine ⟨C + a, d + 1, fun n => ?_⟩
      have hp : 1 ≤ (n + 1) ^ (d + 1) := Nat.one_le_pow _ _ (by omega)
      have hm := Nat.mul_le_mul_right n (hC n)
      have hc := Nat.mul_le_mul_left (C * (n + 1) ^ d) (Nat.le_succ n)
      have ha := Nat.mul_le_mul_left a hp
      simp only [Nat.mul_one, pow_succ] at ha
      simp only [PolynomialBudget.value, pow_succ]
      nlinarith only [hm, hc, ha]

/-- Natural polynomial budgets imply the monomial bounds required by the machine bridge. -/
theorem exists_eval_bound (p : Polynomial ℕ) : ∃ C d : ℕ, ∀ n,
    p.eval n ≤ C * (n + 1) ^ d := by
  obtain ⟨cs, hcs⟩ := PolynomialBudget.exists_coefficients p
  obtain ⟨C, d, hC⟩ := value_bound cs
  exact ⟨C, d, fun n => by simpa only [hcs] using hC n⟩

end PCP.Lang.PolynomialPrefix
