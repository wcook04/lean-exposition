import PCP.Complexity.BinarySubtractionMachine

/-!
# Binary long division semantics and charged bit-scan costs

A high-to-low scan maintains quotient and remainder. Each bit shifts the
remainder, compares it to the divisor, and conditionally subtracts the divisor.
The zero-divisor branch implements Lean's natural division and modulo exactly.
Runtime counts the concrete restoring comparison, retained-input subtraction,
and in-place normalization scans, rather than charging arithmetic constant time.
-/

namespace PCP.Machine.BinaryDivision

open PCP.Lang

/-- Subtract the retained left divisor from the replaceable right remainder. -/
abbrev subSpec : BinaryZip.Spec where
  State := Bool
  init := false
  next s a b := BinarySubtraction.spec.next s b a
  emit s a b := BinarySubtraction.spec.emit s b a
  finish s := BinarySubtraction.spec.finish s

/-- Swapping the scan ports gives right-minus-left subtraction. -/
theorem subSpec_output (s : Bool) (xs ys : List Sym) :
    subSpec.output s xs ys = BinarySubtraction.spec.output s ys xs := by
  induction xs generalizing ys s with
  | nil =>
      induction ys generalizing s with
      | nil => simp [BinaryZip.Spec.output, subSpec]
      | cons c ys ih =>
          simp only [BinaryZip.Spec.output, subSpec, List.head?_nil, List.tail_nil]
          rw [ih]
  | cons c xs ih =>
      cases ys with
      | nil =>
          simp only [BinaryZip.Spec.output, subSpec, List.head?_nil, List.tail_nil]
          rw [ih]
      | cons d ys =>
          simp only [BinaryZip.Spec.output, subSpec, List.head?_cons, List.tail_cons]
          rw [ih]

/-- The normalized retained-input subtraction is canonical truncated subtraction. -/
theorem subSpec_normalized (d r : ℕ) :
    (BinaryNormalize.spec.output BinaryNormalize.spec.init
      (subSpec.output false (natTape d) (natTape r)).reverse).reverse = natTape (r - d) := by
  rw [subSpec_output]
  exact BinarySubtraction.output_natTape r d

/-- One high-to-low long-division step. -/
def stepValue (d q r : ℕ) (b : Bool) : ℕ × ℕ :=
  if d = 0 then (q, Nat.bit b r)
  else if d ≤ Nat.bit b r then (Nat.bit true q, Nat.bit b r - d)
  else (Nat.bit false q, Nat.bit b r)

/-- The standard quotient and remainder obey precisely this binary step. -/
theorem stepValue_div_mod (d n : ℕ) (b : Bool) :
    stepValue d (n / d) (n % d) b = ((Nat.bit b n) / d, (Nat.bit b n) % d) := by
  by_cases hd : d = 0
  · subst d; simp [stepValue]
  have hdpos : 0 < d := Nat.pos_of_ne_zero hd
  have hdecomp := Nat.mod_add_div n d
  have hmod := Nat.mod_lt n hdpos
  have hbit : Nat.bit b (n % d) < 2 * d := by
    cases b <;> simp [Nat.bit] <;> omega
  by_cases hge : d ≤ Nat.bit b (n % d)
  · have hq : (Nat.bit b n) / d = Nat.bit true (n / d) := by
      apply Nat.div_eq_of_lt_le
      · cases b <;> simp only [Nat.bit, Bool.cond_false, Bool.cond_true] at * <;>
          nlinarith [Nat.zero_le (n % d)]
      · cases b <;> simp only [Nat.bit, Bool.cond_false, Bool.cond_true] at * <;> nlinarith
    have hr : (Nat.bit b n) % d = Nat.bit b (n % d) - d := by
      have he := Nat.mod_add_div (Nat.bit b n) d
      have hs := Nat.sub_add_cancel hge
      rw [hq] at he
      cases b <;> simp only [Nat.bit, Bool.cond_false, Bool.cond_true] at * <;> nlinarith
    simp only [stepValue, hd, ite_false, hge, ite_true, hq, hr]
  · have hq : (Nat.bit b n) / d = Nat.bit false (n / d) := by
      apply Nat.div_eq_of_lt_le
      · cases b <;> simp only [Nat.bit, Bool.cond_false, Bool.cond_true] at * <;>
          nlinarith [Nat.zero_le (n % d)]
      · cases b <;> simp only [Nat.bit, Bool.cond_false, Bool.cond_true] at * <;> nlinarith
    have hr : (Nat.bit b n) % d = Nat.bit b (n % d) := by
      have he := Nat.mod_add_div (Nat.bit b n) d
      rw [hq] at he
      cases b <;> simp only [Nat.bit, Bool.cond_false, Bool.cond_true] at * <;> nlinarith
    simp only [stepValue, hd, ite_false, hge, hq, hr]

/-- Scan a high-bit-first word with arbitrary initial quotient and remainder. -/
def value (d q r : ℕ) : List Bool → ℕ × ℕ
  | [] => (q, r)
  | b :: bs => value d (stepValue d q r b).1 (stepValue d q r b).2 bs

@[simp] theorem value_append (d q r : ℕ) (xs ys : List Bool) :
    value d q r (xs ++ ys) = value d (value d q r xs).1 (value d q r xs).2 ys := by
  induction xs generalizing q r with
  | nil => rfl
  | cons b xs ih => exact ih _ _

/-- Reversed canonical digits produce both exact natural division operations. -/
theorem value_bits (d n : ℕ) : value d 0 0 n.bits.reverse = (n / d, n % d) := by
  induction n using Nat.binaryRec' with
  | zero => simp [value]
  | bit b n hn ih =>
      rw [Nat.bits_append_bit n b hn, List.reverse_cons, value_append, ih]
      exact stepValue_div_mod d n b

/-- Raw subtraction output before stripping high padding. -/
def raw (d r : ℕ) : List Sym := subSpec.output false (natTape d) (natTape r)

/-- The retained-input subtractor's exact materialization and restoration count. -/
def subtractionTime (d r : ℕ) : ℕ :=
  max (Nat.size d) (Nat.size r) + max (Nat.size d) (raw d r).length + 2

/-- The comparison restores both operands, including its final finite-state result. -/
def comparisonTime (d r : ℕ) : ℕ := 2 * max (Nat.size d) (Nat.size r) + 2

/-- Raw-result normalization includes every filtered cell in both passes. -/
def normalizationTime (d r : ℕ) : ℕ := 2 * (raw d r).length + 2

/-- Actual control and callee work for one processed dividend bit. -/
def stepTime (d r : ℕ) (b : Bool) : ℕ :=
  if d = 0 then 1
  else comparisonTime d (Nat.bit b r) + 2 +
    if d ≤ Nat.bit b r then
      subtractionTime d (Nat.bit b r) + normalizationTime d (Nat.bit b r) + 1
    else 0

/-- Count every bit, every concrete callee, and the final empty-bit test. -/
def runtime (d q r : ℕ) : List Bool → ℕ
  | [] => 1
  | b :: bs => runtime d (stepValue d q r b).1 (stepValue d q r b).2 bs + stepTime d r b

lemma raw_length_le (d r : ℕ) :
    (raw d r).length ≤ max (Nat.size d) (Nat.size r) + 1 := by
  simpa only [raw, natTape_length] using
    BinaryZip.Spec.output_length_le subSpec (natTape d) (natTape r) false

lemma size_bit (r : ℕ) (b : Bool) : Nat.size (Nat.bit b r) ≤ Nat.size r + 1 := by
  rw [Nat.size_le, pow_succ]
  have := Nat.lt_size_self r
  cases b <;> simp [Nat.bit] <;> omega

lemma size_step_remainder (d q r : ℕ) (b : Bool) :
    Nat.size (stepValue d q r b).2 ≤ Nat.size r + 1 := by
  have h : (stepValue d q r b).2 ≤ Nat.bit b r := by
    simp only [stepValue]
    split_ifs <;> simp
  exact (Nat.size_le_size h).trans (size_bit r b)

lemma stepTime_le (d r : ℕ) (b : Bool) :
    stepTime d r b ≤ 6 * max (Nat.size d) (Nat.size r) + 18 := by
  have hraw := raw_length_le d (Nat.bit b r)
  have hbit := size_bit r b
  unfold stepTime comparisonTime subtractionTime normalizationTime
  split_ifs <;> omega

/-- The complete scan has quadratic bit-length overhead, without a value-sized loop. -/
theorem runtime_le (d q r : ℕ) (bs : List Bool) :
    runtime d q r bs ≤
      (6 * (max (Nat.size d) (Nat.size r) + bs.length) + 18) * bs.length + 1 := by
  induction bs generalizing q r with
  | nil => simp [runtime]
  | cons b bs ih =>
      let M := max (Nat.size d) (Nat.size r)
      have hs := size_step_remainder d q r b
      have hm : max (Nat.size d) (Nat.size (stepValue d q r b).2) ≤ M + 1 := by
        dsimp [M]; omega
      have hi := ih (stepValue d q r b).1 (stepValue d q r b).2
      have hcoef : 6 * (max (Nat.size d) (Nat.size (stepValue d q r b).2) + bs.length) + 18 ≤
          6 * (M + (bs.length + 1)) + 18 := by omega
      have hib := hi.trans (Nat.add_le_add_right (Nat.mul_le_mul_right bs.length hcoef) 1)
      have hc := stepTime_le d r b
      simp only [runtime, List.length_cons]
      change _ ≤ (6 * (M + (bs.length + 1)) + 18) * (bs.length + 1) + 1
      dsimp [M] at *
      nlinarith

/-- One input reversal followed by long division is polynomial in operand bit lengths. -/
theorem full_runtime_le (d n : ℕ) :
    Nat.size n + 1 + runtime d 0 0 n.bits.reverse ≤
      40 * (Nat.size d + Nat.size n + 1) ^ 2 := by
  have hn : n.bits.reverse.length = Nat.size n := by
    simpa only [natTape, binDigits_eq_bits, length_ofBits, List.length_reverse] using
      natTape_length n
  have h := runtime_le d 0 0 n.bits.reverse
  rw [hn] at h
  simp only [Nat.size_zero, Nat.max_zero] at h
  nlinarith

end PCP.Machine.BinaryDivision
