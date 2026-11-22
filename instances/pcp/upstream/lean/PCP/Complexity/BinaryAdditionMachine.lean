import PCP.Complexity.BinaryZipMachine
import PCP.Complexity.LangTapeEncoding

/-!
# Canonical binary addition by a concrete framed machine

A synchronous two-tape scan propagates one carry bit. Its output is proved equal
to the exact canonical binary representation of natural addition, including zero
inputs and overflow. The machine consumes both arguments, clears scratch,
preserves arbitrary caller stacks, and takes at most twice the longer bit length
plus three steps. This is a register-operation certificate, not a whole compiler.
-/

namespace PCP.Machine.BinaryAddition
open Turing PCP.Lang StateTransition

def sumBit (a b carry : Bool) : Bool := xor (xor a b) carry

def carryBit (a b carry : Bool) : Bool := (a && b) || (a && carry) || (b && carry)

def readBit : Option Sym → Bool
  | some (.bit b) => b
  | _ => false

abbrev spec : BinaryZip.Spec where
  State := Bool
  init := false
  next carry a b := carryBit (readBit a) (readBit b) carry
  emit carry a b := some (.bit (sumBit (readBit a) (readBit b) carry))
  finish carry := if carry then some (.bit true) else none

theorem bit_sum (n m : ℕ) (a b carry : Bool)
    (h : (n = 0 → a = true) ∨ (m = 0 → b = true)) :
    sumBit a b carry :: (n + m + cond (carryBit a b carry) 1 0).bits =
      (Nat.bit a n + Nat.bit b m + cond carry 1 0).bits := by
  have he : Nat.bit a n + Nat.bit b m + cond carry 1 0 =
      Nat.bit (sumBit a b carry) (n + m + cond (carryBit a b carry) 1 0) := by
    cases a <;> cases b <;> cases carry <;> simp [Nat.bit, sumBit, carryBit] <;> omega
  rw [he, Nat.bits_append_bit]
  intro hz
  cases a <;> cases b <;> cases carry <;>
    simp [sumBit, carryBit] at *
  all_goals omega

theorem output_nil_nil (carry : Bool) :
    spec.output carry [] [] = ofBits (cond carry [true] []) := by
  cases carry <;> simp [BinaryZip.Spec.output, spec, ofBits]

theorem output_nil_cons (carry b : Bool) (ys : List Bool) :
    spec.output carry [] (ofBits (b :: ys)) =
      .bit (sumBit false b carry) ::
        spec.output (carryBit false b carry) [] (ofBits ys) := by
  simp [BinaryZip.Spec.output, spec, ofBits, readBit]

theorem output_cons_nil (carry a : Bool) (xs : List Bool) :
    spec.output carry (ofBits (a :: xs)) [] =
      .bit (sumBit a false carry) ::
        spec.output (carryBit a false carry) (ofBits xs) [] := by
  simp [BinaryZip.Spec.output, spec, ofBits, readBit]

theorem output_cons_cons (carry a b : Bool) (xs ys : List Bool) :
    spec.output carry (ofBits (a :: xs)) (ofBits (b :: ys)) =
      .bit (sumBit a b carry) ::
        spec.output (carryBit a b carry) (ofBits xs) (ofBits ys) := by
  simp [BinaryZip.Spec.output, spec, ofBits, readBit]

theorem output_bits (n m : ℕ) (carry : Bool) :
    spec.output carry (ofBits n.bits) (ofBits m.bits) =
      ofBits (n + m + cond carry 1 0).bits := by
  induction n using Nat.binaryRec' generalizing m carry with
  | zero =>
      induction m using Nat.binaryRec' generalizing carry with
      | zero => cases carry <;> simp [BinaryZip.Spec.output, spec, ofBits]
      | bit b m hm ih =>
          rw [Nat.bits_append_bit m b hm]
          change spec.output carry [] (ofBits (b :: m.bits)) = _
          change ∀ carry, spec.output carry [] (ofBits m.bits) = _ at ih
          rw [output_nil_cons, ih]
          have hh := congrArg ofBits (bit_sum 0 m false b carry (Or.inr hm))
          simpa only [ofBits, List.map_cons, Nat.bit_false, Nat.mul_zero, Nat.zero_add] using hh
  | bit a n hn ih =>
      induction m using Nat.binaryRec' generalizing carry with
      | zero =>
          rw [Nat.bits_append_bit n a hn]
          change spec.output carry (ofBits (a :: n.bits)) [] = _
          rw [output_cons_nil]
          have hi := ih 0 (carryBit a false carry)
          change spec.output (carryBit a false carry) (ofBits n.bits) [] = _ at hi
          rw [hi]
          have hh := congrArg ofBits (bit_sum n 0 a false carry (Or.inl hn))
          simpa only [ofBits, List.map_cons, Nat.bit_false, Nat.mul_zero, Nat.add_zero] using hh
      | bit b m hm _ =>
          rw [Nat.bits_append_bit n a hn, Nat.bits_append_bit m b hm]
          rw [output_cons_cons, ih]
          exact congrArg ofBits (bit_sum n m a b carry (Or.inl hn))

/-- The adder's canonical output, with no incoming carry. -/
theorem output_natTape (n m : ℕ) :
    spec.output false (natTape n) (natTape m) = natTape (n + m) := by
  simpa only [natTape, binDigits_eq_bits, Bool.cond_false, Nat.add_zero] using
    output_bits n m false

/-- An actual finite-control addition computation with arbitrary caller storage. -/
def additionEvals (F : Type) [DecidableEq F] [Fintype F] (Γf : F → Type)
    (n m : ℕ) (S : ∀ j : F, List (Γf j)) :
    EvalsToInTime (BinaryZip.machine spec F Γf).step
      (BinaryZip.cfg spec F Γf (some .one) false (natTape n) (natTape m) [] [] S)
      (some (BinaryZip.cfg spec F Γf none false [] [] [] (natTape (n + m)) S))
      (2 * max (Nat.size n) (Nat.size m) + 3) where
  steps := max (Nat.size n) (Nat.size m) + Nat.size (n + m) + 2
  evals_in_steps := by
    simpa only [show spec.init = false from rfl, output_natTape, natTape_length] using
      (BinaryZip.trace (spec := spec) (natTape n) (natTape m) S)
  steps_le_m := by
    have h := BinaryZip.Spec.output_length_le spec (natTape n) (natTape m) false
    simp only [output_natTape, natTape_length] at h
    omega

/-- The exact cost also records the physically emitted result length. -/
theorem additionEvals_steps (F : Type) [DecidableEq F] [Fintype F] (Γf : F → Type)
    (n m : ℕ) (S : ∀ j : F, List (Γf j)) :
    (additionEvals F Γf n m S).steps =
      max (Nat.size n) (Nat.size m) + Nat.size (n + m) + 2 := rfl

end PCP.Machine.BinaryAddition
