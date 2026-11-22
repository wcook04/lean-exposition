import PCP.Complexity.BinaryCounter
import PCP.Complexity.CostModel

/-!
# Fixed-width seed succession: the representation layer

Seeds are `bitsOfFin k r`, **least significant bit first**, and — unlike canonical address
numerals — they keep all `k` cells, high zeros included.  This module defines incrementing such a
tape with wrap-around, and relates it to `bitsOfFin`.

## An explicit incoming carry

`incTransform carry bs` and `finalCarry carry bs` take the carry as an argument, exactly as the
decrement's `transform` and `finalBorrow` take a borrow.  The output cell is the old cell XOR
the incoming carry — the same `outBit` the decrement uses — and the carry passed on is the
conjunction of the two, `nextCarry`.  With carry `false` the tape is unchanged.

## Overflow is the all-true tape — including the empty one

`finalCarry true bs = true` exactly when every cell is set.  The empty tape has no cell that is not
set, so **width zero overflows immediately**: its single seed, `[]`, is followed by overflow.  The
enumerator must therefore process the current seed *before* testing the carry.

## Scope

These are statements about lists.  Nothing here is a machine step, and nothing here certifies that
any machine computes these functions; that is `SeedIncrement.lean`'s job.
-/

namespace PCP.Machine

/-! ### The increment -/

/-- Add one, wrapping around at the tape's width. -/
def incBits : List Bool → List Bool
  | [] => []
  | false :: bs => true :: bs
  | true :: bs => false :: incBits bs

/-- The carry passed on. -/
def nextCarry (carry c : Bool) : Bool := carry && c

/-- The whole transformation, with an explicit incoming carry. -/
def incTransform : Bool → List Bool → List Bool
  | false, bs => bs
  | true, bs => incBits bs

/-- The carry left at the end: still set exactly when it came in set and every cell read was set. -/
def finalCarry : Bool → List Bool → Bool
  | false, _ => false
  | true, bs => bs.all id

@[simp] theorem incTransform_false (bs : List Bool) : incTransform false bs = bs := rfl

@[simp] theorem incTransform_true (bs : List Bool) : incTransform true bs = incBits bs := rfl

@[simp] theorem incTransform_nil (carry : Bool) : incTransform carry [] = [] := by
  cases carry <;> rfl

@[simp] theorem finalCarry_nil (carry : Bool) : finalCarry carry [] = carry := by
  cases carry <;> rfl

/-- One cell of the scan: the output uses the **old** carry and the cell just read. -/
theorem incTransform_cons (carry c : Bool) (bs : List Bool) :
    incTransform carry (c :: bs) = outBit carry c :: incTransform (nextCarry carry c) bs := by
  cases carry <;> cases c <;> rfl

theorem finalCarry_cons (carry c : Bool) (bs : List Bool) :
    finalCarry carry (c :: bs) = finalCarry (nextCarry carry c) bs := by
  cases carry <;> cases c <;> simp [finalCarry, nextCarry]

@[simp] theorem length_incBits : ∀ bs : List Bool, (incBits bs).length = bs.length
  | [] => rfl
  | false :: _ => rfl
  | true :: bs => by simp [incBits, length_incBits bs]

@[simp] theorem length_incTransform (carry : Bool) (bs : List Bool) :
    (incTransform carry bs).length = bs.length := by
  cases carry <;> simp

/-! ### What the increment does to the value -/

/-- **The increment's value equation**: the result plus the overflowing carry's weight is one more
than the input. -/
theorem bitsValue_incBits : ∀ bs : List Bool,
    bitsValue (incBits bs) + 2 ^ bs.length * (if bs.all id then 1 else 0) = bitsValue bs + 1
  | [] => by simp [incBits]
  | false :: bs => by simp [incBits]
  | true :: bs => by
      have ih := bitsValue_incBits bs
      simp only [incBits, bitsValue_false_cons, bitsValue_true_cons, List.length_cons,
        List.all_cons, id, Bool.true_and, pow_succ]
      split <;> simp_all <;> ring_nf <;> omega

/-- A tape's value is less than two to its width. -/
theorem bitsValue_lt : ∀ bs : List Bool, bitsValue bs < 2 ^ bs.length
  | [] => by simp
  | false :: bs => by
      have := bitsValue_lt bs
      simp only [bitsValue_false_cons, List.length_cons, pow_succ]; omega
  | true :: bs => by
      have := bitsValue_lt bs
      simp only [bitsValue_true_cons, List.length_cons, pow_succ]; omega

/-- **Increment modulo `2 ^ width`.** -/
theorem bitsValue_incBits_mod (bs : List Bool) :
    bitsValue (incBits bs) = (bitsValue bs + 1) % 2 ^ bs.length := by
  have h := bitsValue_incBits bs
  have hlt := bitsValue_lt (incBits bs)
  rw [length_incBits] at hlt
  split at h
  · rw [← h, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]
  · simp only [mul_zero, add_zero] at h
    rw [← h, Nat.mod_eq_of_lt hlt]

/-! ### Overflow -/

/-- **Overflow is exactly the all-true tape** — the empty tape included. -/
theorem finalCarry_true_iff (bs : List Bool) : finalCarry true bs = true ↔ ∀ b ∈ bs, b = true := by
  simp [finalCarry, List.all_eq_true]

/-- Width zero overflows at once: its single seed is followed by overflow, never by a second one. -/
example : finalCarry true [] = true := rfl

/-- Overflowing the all-true tape returns the all-false tape of the same width. -/
theorem incBits_replicate_true : ∀ k : ℕ, incBits (List.replicate k true) = List.replicate k false
  | 0 => rfl
  | k + 1 => by simp [List.replicate_succ, incBits, incBits_replicate_true k]

@[simp] theorem bitsValue_replicate_false : ∀ k : ℕ, bitsValue (List.replicate k false) = 0
  | 0 => rfl
  | k + 1 => by simp [List.replicate_succ, bitsValue_replicate_false k]

theorem bitsValue_replicate_true : ∀ k : ℕ, bitsValue (List.replicate k true) + 1 = 2 ^ k
  | 0 => rfl
  | k + 1 => by
      have := bitsValue_replicate_true k
      simp only [List.replicate_succ, bitsValue_true_cons, pow_succ]; omega

/-! ### Fixed width is faithful -/

/-- **Two tapes of the same width with the same value are the same tape.**  This is what fails for
unbounded numerals — high zeros — and holds once the width is fixed. -/
theorem bitsValue_inj : ∀ {bs cs : List Bool}, bs.length = cs.length →
    bitsValue bs = bitsValue cs → bs = cs
  | [], [], _, _ => rfl
  | b :: bs, c :: cs, hl, hv => by
      have hl' : bs.length = cs.length := by simpa using hl
      cases b <;> cases c <;>
        simp only [bitsValue_false_cons, bitsValue_true_cons] at hv
      · rw [bitsValue_inj hl' (by omega)]
      · omega
      · omega
      · rw [bitsValue_inj hl' (by omega)]

/-! ### Agreement with `bitsOfFin` -/

/-- The fixed-width, least-significant-first expansion, by recursion on the width. -/
def natBits : ℕ → ℕ → List Bool
  | 0, _ => []
  | k + 1, n => n.testBit 0 :: natBits k (n / 2)

@[simp] theorem length_natBits : ∀ k n, (natBits k n).length = k
  | 0, _ => rfl
  | k + 1, n => by simp [natBits, length_natBits k]

theorem range_map_testBit (k n : ℕ) :
    (List.range k).map (fun j => n.testBit j) = natBits k n := by
  induction k generalizing n with
  | zero => rfl
  | succ k ih =>
    rw [List.range_succ_eq_map, List.map_cons, List.map_map, natBits, ← ih (n / 2)]
    congr 1
    refine List.map_congr_left (fun j _ => ?_)
    simp [Function.comp, Nat.testBit_succ]

/-- `bitsOfFin` is `natBits` at the seed's value. -/
theorem bitsOfFin_eq_natBits (k : ℕ) (r : Fin (2 ^ k)) : bitsOfFin k r = natBits k r.val :=
  range_map_testBit k r.val

/-- `natBits` reads a number modulo two to the width. -/
theorem bitsValue_natBits : ∀ k n, bitsValue (natBits k n) = n % 2 ^ k
  | 0, n => by simp [natBits, Nat.mod_one]
  | k + 1, n => by
      rw [natBits, bitsValue_cons, bitsValue_natBits k (n / 2), pow_succ, Nat.mul_comm (2 ^ k) 2,
        Nat.mod_mul]
      rcases Nat.mod_two_eq_zero_or_one n with h | h <;>
        simp [Nat.testBit_zero, h, Nat.bit] <;> omega

/-- **A seed's value is its index.** -/
@[simp] theorem bitsValue_bitsOfFin (k : ℕ) (r : Fin (2 ^ k)) :
    bitsValue (bitsOfFin k r) = r.val := by
  rw [bitsOfFin_eq_natBits, bitsValue_natBits, Nat.mod_eq_of_lt r.isLt]

/-- **Without overflow, the increment is the successor seed.** -/
theorem incBits_bitsOfFin (k : ℕ) (r : Fin (2 ^ k)) (h : r.val + 1 < 2 ^ k) :
    incBits (bitsOfFin k r) = bitsOfFin k ⟨r.val + 1, h⟩ := by
  apply bitsValue_inj
  · simp
  · rw [bitsValue_incBits_mod, bitsValue_bitsOfFin, bitsValue_bitsOfFin, length_bitsOfFin,
      Nat.mod_eq_of_lt h]

/-- …and no overflow happens there. -/
theorem finalCarry_bitsOfFin_of_lt (k : ℕ) (r : Fin (2 ^ k)) (h : r.val + 1 < 2 ^ k) :
    finalCarry true (bitsOfFin k r) = false := by
  have hv := bitsValue_incBits (bitsOfFin k r)
  rw [bitsValue_bitsOfFin, length_bitsOfFin] at hv
  have hlt := bitsValue_lt (incBits (bitsOfFin k r))
  simp only [length_incBits, length_bitsOfFin] at hlt
  change (bitsOfFin k r).all id = false
  cases hall : (bitsOfFin k r).all id
  · rfl
  · rw [hall] at hv; simp at hv; omega

/-- The first seed is the all-false tape. -/
theorem bitsOfFin_zero (k : ℕ) : bitsOfFin k ⟨0, Nat.two_pow_pos k⟩ = List.replicate k false := by
  apply bitsValue_inj <;> simp

/-- The last seed is the all-true tape… -/
theorem bitsOfFin_last (k : ℕ) :
    bitsOfFin k ⟨2 ^ k - 1, Nat.sub_lt (Nat.two_pow_pos k) Nat.one_pos⟩
      = List.replicate k true := by
  apply bitsValue_inj
  · simp
  · have := bitsValue_replicate_true k
    rw [bitsValue_bitsOfFin]; dsimp only; omega

/-- …so it overflows, and the increment wraps it to the first. -/
theorem finalCarry_bitsOfFin_last (k : ℕ) :
    finalCarry true (bitsOfFin k ⟨2 ^ k - 1, Nat.sub_lt (Nat.two_pow_pos k) Nat.one_pos⟩)
      = true := by
  rw [bitsOfFin_last, finalCarry_true_iff]
  intro b hb; exact (List.eq_of_mem_replicate hb)

theorem incBits_bitsOfFin_last (k : ℕ) :
    incBits (bitsOfFin k ⟨2 ^ k - 1, Nat.sub_lt (Nat.two_pow_pos k) Nat.one_pos⟩)
      = bitsOfFin k ⟨0, Nat.two_pow_pos k⟩ := by
  rw [bitsOfFin_last, incBits_replicate_true, bitsOfFin_zero]

end PCP.Machine
