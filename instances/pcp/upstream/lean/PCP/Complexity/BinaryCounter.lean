import PCP.Complexity.Encoding

/-!
# Fixed-width binary counters: the representation layer

The witness-search loop needs a counter it can test and decrement at a cost depending on the
address's **bit length**, never on its value. This module fixes the representation and proves the
arithmetic facts the machine contracts will be stated against.

## Conventions

Least-significant bit first, matching `Nat.bits`. Internally a **fixed width** is kept: decrements
never trim the high zero bits a power-of-two input produces, so the width stays the `k` it started
with and no canonicalisation runs between iterations. `Nat.bits` itself is canonical, so
`bitsValue_bits` is the bridge between the external address and the internal tape.

## Scope

Everything here is arithmetic on `List Bool`. Nothing is a machine, a step count, or a computability
claim; the execution and cost contracts are stated separately and refer back to these functions.
-/

namespace PCP.Machine

/-- The value of a little-endian bit list.  Defined through `Nat.bit` so that the existing
`fold_bits` bridge to `Nat.bits` applies directly. -/
def bitsValue (bs : List Bool) : ℕ := bs.foldr Nat.bit 0

@[simp] theorem bitsValue_nil : bitsValue [] = 0 := rfl

theorem bitsValue_cons (b : Bool) (bs : List Bool) :
    bitsValue (b :: bs) = Nat.bit b (bitsValue bs) := rfl

@[simp] theorem bitsValue_false_cons (bs : List Bool) :
    bitsValue (false :: bs) = 2 * bitsValue bs := by
  rw [bitsValue_cons]; simp [Nat.bit]

@[simp] theorem bitsValue_true_cons (bs : List Bool) :
    bitsValue (true :: bs) = 2 * bitsValue bs + 1 := by
  rw [bitsValue_cons]; simp [Nat.bit]

/-- **The bridge to the external address.**  `Nat.bits` is canonical, so a freshly loaded counter
holds exactly the address. -/
@[simp] theorem bitsValue_bits (n : ℕ) : bitsValue n.bits = n := fold_bits n

/-- An all-zero tape has value zero, whatever its width — which is what makes fixed-width
representations safe. -/
theorem bitsValue_eq_zero_iff : ∀ bs : List Bool, bitsValue bs = 0 ↔ ∀ b ∈ bs, b = false
  | [] => by simp
  | false :: bs => by
      rw [bitsValue_false_cons]
      constructor
      · intro h c hc
        rcases List.mem_cons.1 hc with rfl | hc'
        · rfl
        · exact (bitsValue_eq_zero_iff bs).1 (by omega) c hc'
      · intro h
        have := (bitsValue_eq_zero_iff bs).2 fun c hc => h c (List.mem_cons_of_mem _ hc)
        omega
  | true :: bs => by
      rw [bitsValue_true_cons]
      constructor
      · intro h; omega
      · intro h; exact absurd (h true (List.mem_cons_self ..)) (by simp)

/-- **Decrement with a borrow, in place.**  While borrowing, `false` becomes `true`; the first
`true` becomes `false` and clears the borrow; the rest is untouched.  High zero bits are *not*
trimmed. -/
def decrBits : List Bool → List Bool
  | [] => []
  | false :: bs => true :: decrBits bs
  | true :: bs => false :: bs

/-- The width is preserved — the point of the fixed-width convention. -/
@[simp] theorem length_decrBits : ∀ bs : List Bool, (decrBits bs).length = bs.length
  | [] => rfl
  | false :: bs => by rw [decrBits, List.length_cons, List.length_cons, length_decrBits bs]
  | true :: bs => rfl

/-- On a positive value the decrement is exactly one less. -/
theorem bitsValue_decrBits : ∀ (bs : List Bool), 0 < bitsValue bs →
    bitsValue (decrBits bs) = bitsValue bs - 1
  | [], h => by simp at h
  | false :: bs, h => by
      rw [bitsValue_false_cons] at h
      have hb : 0 < bitsValue bs := by omega
      rw [decrBits, bitsValue_true_cons, bitsValue_decrBits bs hb, bitsValue_false_cons]
      omega
  | true :: bs, _ => by
      rw [decrBits, bitsValue_false_cons, bitsValue_true_cons]
      omega

/-- Zero is the only value a decrement is not defined to decrease, and the search loop discharges
that by testing first. -/
theorem decrBits_of_value_zero : ∀ {bs : List Bool}, bitsValue bs = 0 →
    decrBits bs = bs.map (fun _ => true)
  | [], _ => rfl
  | false :: bs, h => by
      rw [bitsValue_false_cons] at h
      rw [decrBits, decrBits_of_value_zero (by omega : bitsValue bs = 0)]
      simp
  | true :: bs, h => by rw [bitsValue_true_cons] at h; omega

/-! ## The borrow scan, semantically

The machine scans the whole width with a finite borrow flag.  Stating the transformation with an
**explicit incoming borrow** is what lets one induction cover the moment the borrow clears and the
untouched suffix after it. -/

/-- The bit written out, from the incoming borrow and the bit read. -/
def outBit (borrow c : Bool) : Bool := if borrow then !c else c

/-- The borrow passed on. -/
def nextBorrow (borrow c : Bool) : Bool := borrow && !c

/-- The whole transformation, with an explicit incoming borrow. -/
def transform : Bool → List Bool → List Bool
  | false, bs => bs
  | true, bs => decrBits bs

/-- The borrow left at the end: still pending exactly when it came in pending and every bit read was
zero. -/
def finalBorrow : Bool → List Bool → Bool
  | false, _ => false
  | true, bs => bs.all (fun b => !b)

@[simp] theorem transform_false (bs : List Bool) : transform false bs = bs := rfl

@[simp] theorem transform_true (bs : List Bool) : transform true bs = decrBits bs := rfl

@[simp] theorem transform_nil (b : Bool) : transform b [] = [] := by cases b <;> rfl

@[simp] theorem finalBorrow_false (bs : List Bool) : finalBorrow false bs = false := rfl

@[simp] theorem finalBorrow_nil (b : Bool) : finalBorrow b [] = b := by cases b <;> rfl

/-- **The per-bit step.**  Both the output bit and the outgoing borrow are computed from the *old*
borrow and the bit just read. -/
theorem transform_cons (borrow c : Bool) (bs : List Bool) :
    transform borrow (c :: bs) = outBit borrow c :: transform (nextBorrow borrow c) bs := by
  cases borrow <;> cases c <;> rfl

theorem finalBorrow_cons (borrow c : Bool) (bs : List Bool) :
    finalBorrow borrow (c :: bs) = finalBorrow (nextBorrow borrow c) bs := by
  cases borrow <;> cases c <;> simp [finalBorrow, nextBorrow]

@[simp] theorem length_transform (borrow : Bool) (bs : List Bool) :
    (transform borrow bs).length = bs.length := by cases borrow <;> simp

/-! ## Acceptance

The cases the counter contracts have to survive: value one, a power of two needing a borrow chain,
an odd value needing none, and a representation carrying high zero bits. -/

example : bitsValue [true] = 1 := rfl
example : decrBits [true] = [false] := rfl

/-- A power of two: the borrow runs the whole way up. -/
example : bitsValue [false, false, true] = 4 := rfl
example : decrBits [false, false, true] = [true, true, false] := rfl
example : bitsValue (decrBits [false, false, true]) = 3 := rfl

/-- An odd value: no chain at all, and everything above the low bit is untouched. -/
example : bitsValue [true, false, true] = 5 := rfl
example : decrBits [true, false, true] = [false, false, true] := rfl

/-- **High zero bits are kept**, so the width is stable across iterations. -/
example : bitsValue [true, false, false] = 1 := rfl
example : decrBits [true, false, false] = [false, false, false] := rfl
example : (decrBits [true, false, false]).length = 3 := rfl

/-- An all-zero tape of positive width still reads as zero. -/
example : bitsValue [false, false, false] = 0 := rfl

example (n : ℕ) : bitsValue (Nat.bits n) = n := bitsValue_bits n

/-- The borrow scan agrees with `decrBits` when it starts pending, and is the identity when it does
not. -/
example (bs : List Bool) : transform true bs = decrBits bs := rfl
example (bs : List Bool) : transform false bs = bs := rfl

/-- The borrow survives a run of zeros and is cleared by the first set bit. -/
example : finalBorrow true [false, false] = true := rfl
example : finalBorrow true [false, true, false] = false := rfl

end PCP.Machine
