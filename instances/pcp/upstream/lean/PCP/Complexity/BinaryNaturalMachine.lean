import PCP.Complexity.FinalTransducer
import PCP.Complexity.LangTapeEncoding

/-!
# Concrete machines for binary natural-register primitives

Successor uses finite carry control and may append a final high bit. Division by
two removes precisely the low bit. The zero test inspects whether the canonical
numeral tape is empty. Every operation uses the materialized `natTape` encoding;
no unbounded natural number is stored in finite machine control.
-/

namespace PCP.Machine.BinaryNatural

open Turing PCP.Lang StateTransition

/-- Carry propagation on little-endian bits, extending the word on overflow. -/
def increment : List Bool → List Bool
  | [] => [true]
  | false :: xs => true :: xs
  | true :: xs => false :: increment xs

/-- Carry propagation returns the exact canonical numeral, without high zero padding. -/
theorem increment_bits (n : ℕ) : increment n.bits = (n + 1).bits := by
  induction n using Nat.binaryRec' with
  | zero => simp [increment]
  | bit b n hn ih =>
      cases b with
      | false =>
          rw [Nat.bits_append_bit n false hn]
          simp [increment, Nat.bit]
      | true =>
          rw [Nat.bits_append_bit n true hn]
          simp only [increment, ih]
          rw [show Nat.bit true n + 1 = 2 * (n + 1) by simp [Nat.bit]; omega]
          exact (Nat.bit0_bits (n + 1) (by omega)).symm

/-- The only control bit is the pending carry. -/
def incrementSpec : FinalTransducer.Spec where
  State := Bool
  init := true
  next carry cell := match cell with
    | .bit b => carry && b
    | .sep => carry
  emit carry cell := match cell with
    | .bit b => some (.bit (xor carry b))
    | .sep => none
  finish carry := if carry then some (.bit true) else none

theorem increment_output_false (xs : List Bool) :
    incrementSpec.output false (ofBits xs) = ofBits xs := by
  induction xs with
  | nil => rfl
  | cons b xs ih =>
      cases b <;> simpa [ofBits, FinalTransducer.Spec.output, incrementSpec] using ih

theorem increment_output_true (xs : List Bool) :
    incrementSpec.output true (ofBits xs) = ofBits (increment xs) := by
  induction xs with
  | nil => rfl
  | cons b xs ih =>
      cases b with
      | false =>
          simpa [ofBits, FinalTransducer.Spec.output, incrementSpec, increment] using
            congrArg (Sym.bit true :: ·) (increment_output_false xs)
      | true =>
          simpa [ofBits, FinalTransducer.Spec.output, incrementSpec, increment] using
            congrArg (Sym.bit false :: ·) ih

/-- The executable transducer computes successor at the compiler's exact register encoding. -/
theorem increment_output_natTape (n : ℕ) :
    incrementSpec.output true (natTape n) = natTape (n + 1) := by
  simp only [natTape, binDigits_eq_bits, increment_output_true, increment_bits]

/-- Successor is certified by an actual finite-control stack machine. -/
noncomputable def incrementWitness :
    TM2ComputableInPolyTime natTape natTape (fun n : ℕ => n + 1) :=
  FinalTransducer.transducerComputable incrementSpec Empty (fun _ => Sym)
    natTape natTape (fun n => n + 1) (fun n => (increment_output_natTape n).symm)

/-- Arbitrary caller registers are preserved by binary increment. -/
def incrementEvals (F : Type) [DecidableEq F] [Fintype F] (Γf : F → Type)
    (n : ℕ) (S : ∀ j : F, List (Γf j)) :
    EvalsToInTime (FinalTransducer.transducerTM incrementSpec F Γf).step
      (FinalTransducer.transducerCfg incrementSpec F Γf (some .one)
        (true, none, false) (natTape n) [] [] S)
      (some (FinalTransducer.transducerCfg incrementSpec F Γf none
        (true, none, false) [] [] (natTape (n + 1)) S)) (2 * Nat.size n + 3) := by
  simpa only [show incrementSpec.init = true from rfl,
    increment_output_natTape, natTape_length] using
    (FinalTransducer.transducerEvals (spec := incrementSpec) (natTape n) S)

/-- A finite control bit records whether the first input bit was consumed. -/
def halfSpec : TransducerSpec where
  State := Bool
  init := false
  next _ _ := true
  emit seen cell := if seen then some cell else none

theorem half_output_true (xs : List Sym) : halfSpec.output true xs = xs := by
  induction xs with
  | nil => rfl
  | cons c xs ih => simpa [TransducerSpec.output, halfSpec] using congrArg (c :: ·) ih

theorem half_output_false (xs : List Sym) : halfSpec.output false xs = xs.tail := by
  cases xs with
  | nil => rfl
  | cons c xs => simpa [TransducerSpec.output, halfSpec] using half_output_true xs

/-- Removing the low bit implements ordinary natural division by two. -/
theorem half_output_natTape (n : ℕ) : halfSpec.output false (natTape n) = natTape (n / 2) := by
  rw [half_output_false]
  simp only [natTape, binDigits_eq_bits, ofBits, ← List.map_tail]
  congr 1
  exact (Nat.div2_bits_eq_tail n).symm

/-- Actual linear-time division-by-two machine at canonical binary encodings. -/
noncomputable def halfWitness :
    TM2ComputableInPolyTime natTape natTape (fun n : ℕ => n / 2) :=
  transducerComputable halfSpec Empty (fun _ => Sym) natTape natTape (fun n => n / 2)
    (fun n => (half_output_natTape n).symm)

/-- Empty input is the only canonical representation of zero. -/
def zeroSpec : FinalTransducer.Spec where
  State := Bool
  init := true
  next _ _ := false
  emit _ _ := none
  finish empty := if empty then some (.bit true) else none

theorem zero_output_false (xs : List Sym) : zeroSpec.output false xs = [] := by
  induction xs with
  | nil => rfl
  | cons c xs ih => simpa [FinalTransducer.Spec.output, zeroSpec] using ih

theorem zero_output (xs : List Sym) :
    zeroSpec.output true xs = if xs = [] then [.bit true] else [] := by
  cases xs with
  | nil => rfl
  | cons c xs => simpa [FinalTransducer.Spec.output, zeroSpec] using zero_output_false xs

/-- The zero test returns the canonical binary natural `1` or `0`. -/
theorem zero_output_natTape (n : ℕ) :
    zeroSpec.output true (natTape n) = natTape (if n = 0 then 1 else 0) := by
  have hzero : natTape 0 = [] := rfl
  have he : natTape n = [] ↔ n = 0 := by
    rw [← hzero]
    exact natTape_injective.eq_iff
  simp only [zero_output, he]
  split <;> rfl

/-- Actual linear-time zero-test machine, with an encoded natural output. -/
noncomputable def zeroWitness :
    TM2ComputableInPolyTime natTape natTape (fun n : ℕ => if n = 0 then 1 else 0) :=
  FinalTransducer.transducerComputable zeroSpec Empty (fun _ => Sym)
    natTape natTape (fun n => if n = 0 then 1 else 0)
    (fun n => (zero_output_natTape n).symm)

@[simp] theorem incrementWitness_time : incrementWitness.time = 2 * Polynomial.X + 3 := rfl

@[simp] theorem halfWitness_time : halfWitness.time = 2 * Polynomial.X + 2 := rfl

@[simp] theorem zeroWitness_time : zeroWitness.time = 2 * Polynomial.X + 3 := rfl

end PCP.Machine.BinaryNatural
