import PCP.Complexity.ReferenceNTMDigits
import Complexitylib.Models.TuringMachine

/-!
# Arithmetic tapes for the reference nondeterministic machine

Blank, zero, one, and the start marker have digits 0, 1, 2, and 3. The cached
place value makes every tape operation a fixed arithmetic expression. Decoding
agrees exactly with the reference's one-sided tape, including ignored writes at
cell zero and saturated left moves.
-/

namespace PCP.ReferenceNTM

open Complexity

def symbolCode : Γ → ℕ
  | .blank => 0
  | .zero => 1
  | .one => 2
  | .start => 3

def symbol : ℕ → Γ
  | 0 => .blank
  | 1 => .zero
  | 2 => .one
  | _ => .start

@[simp] theorem symbol_symbolCode (s : Γ) : symbol (symbolCode s) = s := by
  cases s <;> rfl

theorem symbolCode_lt (s : Γ) : symbolCode s < 4 := by
  cases s <;> decide

@[simp] theorem symbolCode_ofBool (b : Bool) : symbolCode (Γ.ofBool b) = b.toNat + 1 := by
  cases b <;> rfl

theorem symbolCode_symbol (a : ℕ) (ha : a < 4) : symbolCode (symbol a) = a := by
  interval_cases a <;> rfl

@[ext] structure Tape where
  code : ℕ
  head : ℕ
  power : ℕ
  deriving DecidableEq, Repr

namespace Tape

def Valid (t : Tape) : Prop := t.power = 4 ^ t.head

def decode (t : Tape) : Complexity.Tape :=
  ⟨t.head, fun i => symbol (digit t.code i)⟩

def read (t : Tape) : Γ := symbol (t.code / t.power % 4)

def write (t : Tape) (s : Γ) : Tape :=
  if t.head = 0 then t
  else { t with code := t.code - (t.code / t.power % 4) * t.power + symbolCode s * t.power }

def move (t : Tape) : Dir3 → Tape
  | .left => if t.head = 0 then t else { t with head := t.head - 1, power := t.power / 4 }
  | .right => { t with head := t.head + 1, power := t.power * 4 }
  | .stay => t

def writeAndMove (t : Tape) (s : Γ) (d : Dir3) : Tape := (t.write s).move d

def init (xs : List Γ) : Tape :=
  ⟨Nat.ofDigits 4 (3 :: xs.map symbolCode), 0, 1⟩

@[simp] theorem read_decode (t : Tape) (ht : t.Valid) : t.read = t.decode.read := by
  change t.power = 4 ^ t.head at ht
  simp [read, decode, Complexity.Tape.read, digit, ht]

@[simp] theorem write_head (t : Tape) (s : Γ) : (t.write s).head = t.head := by
  simp only [write]
  split <;> rfl

@[simp] theorem write_power (t : Tape) (s : Γ) : (t.write s).power = t.power := by
  simp only [write]
  split <;> rfl

theorem Valid.write {t : Tape} (ht : t.Valid) (s : Γ) : (t.write s).Valid := by
  simpa [Valid] using ht

theorem Valid.move {t : Tape} (ht : t.Valid) (d : Dir3) : (t.move d).Valid := by
  have hp : t.power = 4 ^ t.head := ht
  cases d with
  | stay => exact ht
  | right => simpa [Tape.move, Valid, pow_succ] using hp
  | left =>
      by_cases h : t.head = 0
      · simpa [Tape.move, h] using ht
      · simp only [Tape.move, h, ite_false, Valid]
        have he : 4 ^ t.head = 4 ^ (t.head - 1) * 4 := by
          nth_rw 1 [← Nat.sub_add_cancel (by omega : 1 ≤ t.head)]
          exact pow_succ _ _
        rw [hp, he]
        exact Nat.mul_div_cancel _ (by decide)

theorem decode_write (t : Tape) (ht : t.Valid) (s : Γ) :
    (t.write s).decode = t.decode.write s := by
  change t.power = 4 ^ t.head at ht
  by_cases h : t.head = 0
  · simp [write, Complexity.Tape.write, decode, h]
  · apply Complexity.Tape.ext
    · simp [write, Complexity.Tape.write, decode, h]
    · funext i
      simp only [write, h, ite_false, decode, Complexity.Tape.write, ht]
      change symbol (digit (setDigit t.code t.head (symbolCode s)) i) =
        Function.update (fun j => symbol (digit t.code j)) t.head s i
      rw [digit_setDigit _ _ _ _ (symbolCode_lt s)]
      by_cases hi : i = t.head
      · subst i; simp
      · simp [hi]

theorem decode_move (t : Tape) (d : Dir3) :
    (t.move d).decode = t.decode.move d := by
  cases d with
  | stay => rfl
  | right => rfl
  | left =>
      by_cases h : t.head = 0
      · simp [move, decode, Complexity.Tape.move, h]
      · simp [move, decode, Complexity.Tape.move, h]

theorem decode_writeAndMove (t : Tape) (ht : t.Valid) (s : Γ) (d : Dir3) :
    (t.writeAndMove s d).decode = t.decode.writeAndMove s d := by
  rw [writeAndMove, decode_move, decode_write t ht]

@[simp] theorem valid_init (xs : List Γ) : (init xs).Valid := rfl

theorem decode_init (xs : List Γ) : (init xs).decode = Complexity.Tape.init xs := by
  apply Complexity.Tape.ext
  · rfl
  · funext i
    have hx : ∀ a ∈ 3 :: xs.map symbolCode, a < 4 := by
      intro a ha
      rcases List.mem_cons.mp ha with rfl | ha
      · decide
      · obtain ⟨s, _, rfl⟩ := List.mem_map.mp ha
        exact symbolCode_lt s
    simp only [decode, init, digit_ofDigits _ hx]
    cases i with
    | zero => rfl
    | succ i =>
        simp only [Complexity.Tape.init, Nat.add_eq_zero_iff,
          Nat.one_ne_zero, and_false, ite_false, Nat.add_sub_cancel, cell]
        cases hi : xs[i]? with
        | none => simp [hi, symbol]
        | some s => simp [hi]

theorem init_code_lt (xs : List Γ) : (init xs).code < 4 ^ (xs.length + 1) := by
  have h := Nat.ofDigits_lt_base_pow_length (by decide : 1 < 4)
    (l := 3 :: xs.map symbolCode) (by
      intro a ha
      rcases List.mem_cons.mp ha with rfl | ha
      · decide
      · obtain ⟨s, _, rfl⟩ := List.mem_map.mp ha
        exact symbolCode_lt s)
  simpa [init] using h

theorem init_append_code (xs : List Γ) (s : Γ) :
    (init (xs ++ [s])).code = (init xs).code + symbolCode s * 4 ^ (xs.length + 1) := by
  change Nat.ofDigits 4 (3 :: (xs ++ [s]).map symbolCode) =
    Nat.ofDigits 4 (3 :: xs.map symbolCode) + symbolCode s * 4 ^ (xs.length + 1)
  rw [List.map_append, List.map_singleton, ← List.cons_append, Nat.ofDigits_append]
  simp [Nat.mul_comm]

theorem head_move_le (t : Tape) (d : Dir3) : (t.move d).head ≤ t.head + 1 := by
  cases d with
  | left =>
      simp only [move]
      split
      · exact Nat.le_succ _
      · change t.head - 1 ≤ t.head + 1
        omega
  | right => exact le_rfl
  | stay => exact Nat.le_succ _

theorem move_code (t : Tape) (d : Dir3) : (t.move d).code = t.code := by
  cases d with
  | left => simp only [move]; split <;> rfl
  | right => rfl
  | stay => rfl

theorem write_code_lt (t : Tape) (ht : t.Valid) (s : Γ) (B : ℕ)
    (hc : t.code < 4 ^ B) (hh : t.head < B) : (t.write s).code < 4 ^ B := by
  change t.power = 4 ^ t.head at ht
  by_cases h : t.head = 0
  · simpa [write, h] using hc
  · simpa [write, h, ht, setDigit, digit] using
      setDigit_lt_pow t.code t.head (symbolCode s) B hc hh (symbolCode_lt s)

end Tape
end PCP.ReferenceNTM
