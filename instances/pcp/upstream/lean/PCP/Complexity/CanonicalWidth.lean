import PCP.Complexity.SeedEnumBound

/-!
# Canonical seed width: the arithmetic, and the enumeration's polynomial

Two obligations are kept apart, and this module is only the first: bounding an enumerator that
has been *supplied* a seed tape of the canonical width.  Building that tape is a machine obligation
of its own, discharged in `SeedConstruct.lean` and `SeedConstructLoop.lean`.

## The halving count is the logarithm

The planned construction halves a unary tape of length `n + 1` until it is empty.  `halvings m`
counts the nonempty passes, and `halvings_eq_clog` proves it is `Nat.clog 2 (m + 1)` — so starting
from `n + 1` it is exactly `Nat.clog 2 (n + 2)`, the logarithm in the canonical width
`a * Nat.clog 2 (n + 2) + b`.  Both sides are characterised by the same inequality,
`· ≤ y ↔ m < 2 ^ y`; no fencepost is argued informally.

## The polynomial

With `L = n + W + 1` — the length of `encodePair (x, w)` — `enumPoly` bounds the enumeration's
recorded count.  The seed count is handled first and exactly, through `two_pow_canonical_le`; only
the per-seed cost uses the coarse `k ≤ a (L + 2) + b`.  The logarithm is never replaced by a linear
bound *inside* the exponent.  Coefficients depend on the fixed `a`, `b`, `q` and the fixed witness
machine only; the witness length is an input-size variable like any other.
-/

namespace PCP.Machine

open Turing Polynomial

/-! ### The halving count -/

/-- The number of nonempty passes a unary tape of length `m` survives, halving (rounding down) each
time. -/
def halvings : ℕ → ℕ
  | 0 => 0
  | m + 1 => halvings ((m + 1) / 2) + 1
decreasing_by omega

@[simp] theorem halvings_zero : halvings 0 = 0 := by rw [halvings]

theorem halvings_succ (m : ℕ) : halvings (m + 1) = halvings ((m + 1) / 2) + 1 := by
  rw [halvings]

/-- The characterisation both sides share. -/
theorem halvings_le_iff : ∀ (m y : ℕ), halvings m ≤ y ↔ m < 2 ^ y := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro y
    rcases m with _ | m
    · simp
    · rw [halvings_succ]
      rcases y with _ | y
      · simp
      · have hlt : (m + 1) / 2 < m + 1 := by omega
        rw [Nat.add_le_add_iff_right, ih _ hlt y, pow_succ, Nat.div_lt_iff_lt_mul (by norm_num)]

/-- **The halving count is the ceiling logarithm.** -/
theorem halvings_eq_clog (m : ℕ) : halvings m = Nat.clog 2 (m + 1) := by
  apply le_antisymm
  · rw [halvings_le_iff]
    have := Nat.le_pow_clog (by norm_num : 1 < 2) (m + 1)
    omega
  · rw [Nat.clog_le_iff_le_pow (by norm_num : 1 < 2)]
    have := (halvings_le_iff m (halvings m)).1 le_rfl
    omega

/-- The canonical seed width for input length `n`. -/
def canonicalWidth (a b n : ℕ) : ℕ := a * Nat.clog 2 (n + 2) + b

/-- …which is exactly what `a` emissions per nonempty halving pass of a unary tape of length
`n + 1`, plus `b` more, produce. -/
theorem canonicalWidth_eq_halvings (a b n : ℕ) :
    canonicalWidth a b n = a * halvings (n + 1) + b := by
  rw [canonicalWidth, halvings_eq_clog]

/-- A coarse bound, used only for the per-seed cost — never inside the exponent. -/
theorem clog_le_self (m : ℕ) : Nat.clog 2 m ≤ m := by
  rw [Nat.clog_le_iff_le_pow (by norm_num : 1 < 2)]
  exact Nat.lt_two_pow_self.le

theorem canonicalWidth_le (a b n : ℕ) : canonicalWidth a b n ≤ a * (n + 2) + b := by
  have := clog_le_self (n + 2)
  have : a * Nat.clog 2 (n + 2) ≤ a * (n + 2) := Nat.mul_le_mul_left a this
  simp only [canonicalWidth]; omega

/-! ### Monotonicity of the per-seed bound -/

section Mono

variable {f : List Bool × List Bool × List Bool → Bool ⊕ ℕ}

theorem roundBoundL_mono (hw : TM2ComputableInPolyTime encodeTriple encodeAnswer f)
    {n n' s s' W W' A : ℕ} (hn : n ≤ n') (hs : s ≤ s') (hW : W ≤ W') :
    roundBoundL hw n s W A ≤ roundBoundL hw n' s' W' A := by
  have hN : n + s + A + 2 ≤ n' + s' + A + 2 := by omega
  have hC := eval_mono (callPoly hw.tm hw.time) hN
  have hQ := eval_mono (outputPoly hw.tm hw.time) hN
  have hWQ : W * (4 * (outputPoly hw.tm hw.time).eval (n + s + A + 2) + 10)
      ≤ W' * (4 * (outputPoly hw.tm hw.time).eval (n' + s' + A + 2) + 10) :=
    Nat.mul_le_mul hW (by omega)
  simp only [roundBoundL]
  omega

theorem seedRoundBound_mono (hw : TM2ComputableInPolyTime encodeTriple encodeAnswer f)
    {n n' k k' W W' : ℕ} (q : ℕ) (hn : n ≤ n') (hk : k ≤ k') (hW : W ≤ W') :
    seedRoundBound hw n k W q ≤ seedRoundBound hw n' k' W' q := by
  have hR := roundBoundL_mono hw (A := q) hn hk hW
  have hQ := eval_mono (outputPoly hw.tm hw.time) (show n + k + q + 2 ≤ n' + k' + q + 2 by omega)
  have hmul := Nat.mul_le_mul_left (q + 1) hR
  simp only [seedRoundBound]
  omega

end Mono

/-! ### The enumeration's polynomial -/

section Poly

variable {f : List Bool × List Bool × List Bool → Bool ⊕ ℕ}

/-- The coarse width bound, as a polynomial in `L`. -/
noncomputable def widthPoly (a b : ℕ) : Polynomial ℕ := C a * (X + 2) + C b

/-- `N`, as a polynomial in `L`. -/
noncomputable def tuplePoly (a b q : ℕ) : Polynomial ℕ := X + widthPoly a b + C q + 2

/-- `S + 2k + 5`, as a polynomial in `L`. -/
noncomputable def iterPoly (hw : TM2ComputableInPolyTime encodeTriple encodeAnswer f)
    (a b q : ℕ) : Polynomial ℕ :=
  C (q + 1) *
      ((2 * (X + widthPoly a b + C q) + 8) + (callPoly hw.tm hw.time).comp (tuplePoly a b q)
        + (X * (4 * (outputPoly hw.tm hw.time).comp (tuplePoly a b q) + 10)
          + 3 * (outputPoly hw.tm hw.time).comp (tuplePoly a b q) + 10)
        + (X + widthPoly a b + 3 * C q + 8))
    + ((outputPoly hw.tm hw.time).comp (tuplePoly a b q) + tuplePoly a b q + C q + 5)
    + 2 * widthPoly a b + 5

/-- **The enumeration's polynomial**, in the pair-encoding length. -/
noncomputable def enumPoly (hw : TM2ComputableInPolyTime encodeTriple encodeAnswer f)
    (a b q : ℕ) : Polynomial ℕ :=
  C (2 ^ (a + b)) * (X + 2) ^ a * iterPoly hw a b q

theorem widthPoly_eval (a b L : ℕ) : (widthPoly a b).eval L = a * (L + 2) + b := by
  simp [widthPoly]

theorem iterPoly_eval (hw : TM2ComputableInPolyTime encodeTriple encodeAnswer f) (a b q L : ℕ) :
    (iterPoly hw a b q).eval L
      = seedRoundBound hw L (a * (L + 2) + b) L q + 2 * (a * (L + 2) + b) + 5 := by
  simp [iterPoly, tuplePoly, widthPoly, seedRoundBound, roundBoundL, eval_comp]

theorem enumPoly_eval (hw : TM2ComputableInPolyTime encodeTriple encodeAnswer f) (a b q L : ℕ) :
    (enumPoly hw a b q).eval L = 2 ^ (a + b) * (L + 2) ^ a * (iterPoly hw a b q).eval L := by
  simp [enumPoly]

end Poly

section Enum

variable {G : Type} [DecidableEq G] [Fintype G] {Γg : G → Type}
  {f : List Bool × List Bool × List Bool → Bool ⊕ ℕ}

/-- **The enumeration at canonical width, bounded by a polynomial in the pair-encoding length.**

This charges enumeration only: the seed tape is *supplied* at width `canonicalWidth a b x.length`.
Constructing it, initialising the machine and the final output and cleanup are charged
separately. -/
theorem enum_steps_le_poly (q : ℕ) (U₀ : Type) [Fintype U₀]
    (hw : TM2ComputableInPolyTime encodeTriple encodeAnswer f)
    (p₀ : Bool × (Bool × DepthPay q (Bool × U₀)))
    (rest : CallLabel → PrepStmt hw.tm (LookupSlot ⊕ G) (lkΓ G Γg)
      (Bool × (Bool × DepthPay q (Bool × U₀))))
    (x w : List Bool) (u₀ : U₀) (g : ∀ j : G, List (Γg j)) (a b : ℕ) (v : hw.tm.σ)
    (temp : Option Sym) (flag res : Bool) :
    (enumCert q U₀ hw p₀ rest x w u₀ g (canonicalWidth a b x.length)
        (2 ^ canonicalWidth a b x.length - 1) ⟨0, Nat.two_pow_pos _⟩
        (by simp only; have := Nat.two_pow_pos (canonicalWidth a b x.length); omega) true v temp
        flag res).steps
      ≤ (enumPoly hw a b q).eval (x.length + w.length + 1) := by
  set k := canonicalWidth a b x.length with hk
  set L := x.length + w.length + 1 with hL
  have h := enum_steps_le q U₀ hw p₀ rest x w u₀ g k v temp flag res
  have hcount : 2 ^ k ≤ 2 ^ (a + b) * (L + 2) ^ a := by
    have := two_pow_canonical_le a b x.length
    have hpow : (x.length + 2) ^ a ≤ (L + 2) ^ a := Nat.pow_le_pow_left (by omega) a
    calc 2 ^ k ≤ 2 ^ (a + b) * (x.length + 2) ^ a := this
      _ ≤ 2 ^ (a + b) * (L + 2) ^ a := Nat.mul_le_mul_left _ hpow
  have hkL : k ≤ a * (L + 2) + b := by
    have := canonicalWidth_le a b x.length
    have : a * (x.length + 2) ≤ a * (L + 2) := Nat.mul_le_mul_left a (by omega)
    omega
  have hS := seedRoundBound_mono hw q (show x.length ≤ L by omega) hkL
    (show w.length ≤ L by omega)
  have hiter : seedRoundBound hw x.length k w.length q + 2 * k + 5
      ≤ (iterPoly hw a b q).eval L := by
    rw [iterPoly_eval]; omega
  rw [enumPoly_eval]
  calc _ ≤ 2 ^ k * (seedRoundBound hw x.length k w.length q + 2 * k + 5) := h
    _ ≤ 2 ^ (a + b) * (L + 2) ^ a * (iterPoly hw a b q).eval L := Nat.mul_le_mul hcount hiter

end Enum

end PCP.Machine
