import PCP.Complexity.LangStep
import PCP.Complexity.LangCompiledProgram
import PCP.Complexity.PolyTimeMap

/-!
# The verified compiler and the bridge to cost certificates

`CompilesInPolyTime P` states that a concrete `Turing.FinTM2` machine reads
`encodeNats l`, produces `encodeNats (P.run l)`, empties every other tape, and halts
within `c * (P.cost l + |encodeNats l| + 1)^k` actual machine steps, with constants
fixed by the program. `compile` proves this for every program.

`LangCompiledProgram` supplies the executable machine. Arithmetic and list
instructions have checked finite-machine traces; structural induction composes
sequence, conditional, and captured-counter loops; final cleanup establishes the
machine model's exact `haltList` configuration. The machine definitions use
computable finite control and explicitly enumerated tape indices.

`PCP.Machine.LangSymbolBridge.polyTimeMap_of_program` combines a compiler
certificate with program correctness and a polynomial source-cost bound. Its
explicit compiler argument remains useful for callers with independently
constructed machines; `compile P` supplies it unconditionally for every program.
-/

namespace PCP.Lang

open PCP PCP.Machine Turing

/-- **A program compiles to a polynomial-time machine**: on `encodeNats l` it outputs
`encodeNats (P.run l)` within `c · (cost + input length + 1)^k` steps. -/
def CompilesInPolyTime (P : Prog) : Prop :=
  ∃ (tm : FinTM2) (ein : tm.Γ tm.k₀ ≃ Sym) (eout : tm.Γ tm.k₁ ≃ Sym) (c k : ℕ),
    ∀ l : List ℕ, Nonempty (TM2OutputsInTime tm ((encodeNats l).map ein.invFun)
      (some ((encodeNats (P.run l)).map eout.invFun))
      (c * (P.cost l + (encodeNats l).length + 1) ^ k))

/-- **COMPILE: every program compiles to a polynomial-time `FinTM2` machine.** -/
theorem compile (P : Prog) : CompilesInPolyTime P :=
  Compiler.exists_program_machine P

/-- The time polynomial the bridge produces. -/
noncomputable def bridgeTime (c k c₁ k₁ : ℕ) : Polynomial ℕ :=
  Polynomial.C (c * (c₁ + 1) ^ k) * (Polynomial.X + 1) ^ ((k₁ + 1) * k)

theorem bridgeTime_bound (c k c₁ k₁ L cost : ℕ) (hcost : cost ≤ c₁ * (L + 1) ^ k₁) :
    c * (cost + L + 1) ^ k ≤ (bridgeTime c k c₁ k₁).eval L := by
  simp only [bridgeTime, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
    Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_one]
  have h1 : (L + 1) ^ k₁ ≤ (L + 1) ^ (k₁ + 1) := Nat.pow_le_pow_right (by omega) (by omega)
  have h2 : L + 1 ≤ (L + 1) ^ (k₁ + 1) := by
    calc L + 1 = (L + 1) ^ 1 := (pow_one _).symm
      _ ≤ (L + 1) ^ (k₁ + 1) := Nat.pow_le_pow_right (by omega) (by omega)
  have hsum : cost + L + 1 ≤ (c₁ + 1) * (L + 1) ^ (k₁ + 1) := by
    have : c₁ * (L + 1) ^ k₁ ≤ c₁ * (L + 1) ^ (k₁ + 1) := Nat.mul_le_mul_left _ h1
    nlinarith
  calc c * (cost + L + 1) ^ k ≤ c * ((c₁ + 1) * (L + 1) ^ (k₁ + 1)) ^ k :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hsum k)
    _ = c * (c₁ + 1) ^ k * (L + 1) ^ ((k₁ + 1) * k) := by rw [mul_pow, ← pow_mul]; ring

/-- `Nat.size` is the length of `encodeNats`'s binary numeral. -/
theorem size_eq_bl (x : ℕ) : Nat.size x = (binDigits x).length := by
  simp only [binDigits, List.length_map]
  apply le_antisymm
  · exact Nat.size_le.2 (Nat.lt_base_pow_length_digits (by norm_num))
  · exact (Nat.digits_length_le_iff (by norm_num) x).2 (Nat.lt_size_self x)

/-- **`listSize` is the encoded length.** -/
theorem listSize_eq (l : List ℕ) : listSize l = (encodeNats l).length := by
  rw [length_encodeNats, listSize]
  congr 1
  exact List.map_congr_left fun x _ => by rw [size_eq_bl]

/-- The compiler's output length is bounded by input length plus the program's charged cost. -/
theorem Prog.run_encoded_length_le (P : Prog) (l : List ℕ) :
    (encodeNats (P.run l)).length ≤ (encodeNats l).length + P.cost l := by
  simpa only [listSize_eq] using P.run_listSize_le l

/-- Every operational prefix is bounded using the compiler's actual binary input length. -/
theorem Prog.prefix_encoded_bound (P : Prog) (l : List ℕ) {n c : ℕ} {a : Config P.R P.Q}
    (h : Steps (P.start l) n c a) :
    n ≤ c ∧ c ≤ P.cost l ∧ a.Sized ((encodeNats l).length + P.cost l) ∧
      a.todo.length ≤ 1 + n := by
  simpa only [listSize_eq] using P.prefix_bound l h

end PCP.Lang
