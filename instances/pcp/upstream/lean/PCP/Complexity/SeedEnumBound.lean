import PCP.Complexity.SeedEnum
import PCP.Complexity.SeedBound

/-!
# A bound on the actual enumeration

The bound is about the **constructor** `enumCert` — its recursion is unfolded — and then about the
certificate `enum_checkAll` uses.  `EnumCert`'s type restricts nothing about cost, so nothing here
is claimed of an arbitrary value of it.  The recorded count is kept; the bound is an inequality
about it.

## One seed round depends only on lengths

`seedRound_steps_le`, at empty history and full depth `q`, mentions the seed only through its
**length** — never its contents, and never the running aggregate carried beside it.  So one number
`S` bounds every seed's round:

```text
N = n + k + q + 2
Q = (outputPoly hw.tm hw.time).eval N
C = (callPoly hw.tm hw.time).eval N
B = 2(n + k + q) + 8 + C + (W(4Q + 10) + 3Q + 10) + (n + k + 3q + 8)
S = (q + 1)·B + (Q + N + q + 5)
```

## One iteration

Beyond its round, each iteration costs the fold (one step), the increment (`2k + 3`) and the
overflow test (one step) — `2k + 5`, the last iteration included.  So `2^k` seeds cost at most
`2^k · (S + 2k + 5)`.

## What is not included

Building the seed tape of canonical width, initialising the machine, and the final output and
cleanup are all charged separately, later.
-/

namespace PCP.Machine

open Turing Turing.TM2 Turing.TM2.Stmt StateTransition

section

variable {f : List Bool × List Bool × List Bool → Bool ⊕ ℕ}

/-- The per-round budget `B`, in lengths alone: input `n`, seed width `s`, witness `W`, and
history-plus-depth allowance `A`. -/
noncomputable def roundBoundL (hw : TM2ComputableInPolyTime encodeTriple encodeAnswer f)
    (n s W A : ℕ) : ℕ :=
  (2 * (n + s + A) + 8) + (callPoly hw.tm hw.time).eval (n + s + A + 2)
    + (W * (4 * (outputPoly hw.tm hw.time).eval (n + s + A + 2) + 10)
        + 3 * (outputPoly hw.tm hw.time).eval (n + s + A + 2) + 10)
    + (n + s + 3 * A + 8)

/-- **`roundBound` reads only lengths.** -/
theorem roundBound_eq_L (hw : TM2ComputableInPolyTime encodeTriple encodeAnswer f)
    (x rs w : List Bool) (A : ℕ) :
    roundBound hw x rs w A = roundBoundL hw x.length rs.length w.length A := rfl

/-- **`S`: one complete seed round**, at empty history and full depth `q`, for a seed of width
`k`. -/
noncomputable def seedRoundBound (hw : TM2ComputableInPolyTime encodeTriple encodeAnswer f)
    (n k W q : ℕ) : ℕ :=
  (q + 1) * roundBoundL hw n k W q
    + ((outputPoly hw.tm hw.time).eval (n + k + q + 2) + (n + k + q + 2) + q + 5)

end

section Bound

variable {G : Type} [DecidableEq G] [Fintype G] {Γg : G → Type}
  {f : List Bool × List Bool × List Bool → Bool ⊕ ℕ}

/-- **Every seed's round fits `S`** — whichever seed it is, and whatever aggregate, flags or state
it starts with. -/
theorem enRound_steps_le (q : ℕ) (U₀ : Type) [Fintype U₀]
    (hw : TM2ComputableInPolyTime encodeTriple encodeAnswer f)
    (p₀ : Bool × (Bool × DepthPay q (Bool × U₀)))
    (rest : CallLabel → PrepStmt hw.tm (LookupSlot ⊕ G) (lkΓ G Γg)
      (Bool × (Bool × DepthPay q (Bool × U₀))))
    (x w : List Bool) (u₀ : U₀) (g : ∀ j : G, List (Γg j)) (k : ℕ) (j : Fin (2 ^ k)) (A : Bool)
    (v : hw.tm.σ) (temp : Option Sym) (flag res : Bool) :
    (enRound q U₀ hw p₀ rest x w u₀ g k j A v temp flag res).steps
      ≤ seedRoundBound hw x.length k w.length q := by
  have h := seedRound_steps_le q (Bool × U₀) hw p₀ (enRest q U₀ hw rest) x (bitsOfFin k j) w
    (A, u₀) g q (Fin.last q) rfl [] v temp flag res
  simpa [seedRoundBound, roundBound_eq_L, tupleBound, length_bitsOfFin] using h

/-- The base case's recorded count, read off the constructor. -/
theorem enumCert_zero_steps (q : ℕ) (U₀ : Type) [Fintype U₀]
    (hw : TM2ComputableInPolyTime encodeTriple encodeAnswer f)
    (p₀ : Bool × (Bool × DepthPay q (Bool × U₀)))
    (rest : CallLabel → PrepStmt hw.tm (LookupSlot ⊕ G) (lkΓ G Γg)
      (Bool × (Bool × DepthPay q (Bool × U₀))))
    (x w : List Bool) (u₀ : U₀) (g : ∀ j : G, List (Γg j)) (k : ℕ) (j : Fin (2 ^ k))
    (hm : j.val + 0 + 1 = 2 ^ k) (A : Bool) (v : hw.tm.σ) (temp : Option Sym) (flag res : Bool) :
    (enumCert q U₀ hw p₀ rest x w u₀ g k 0 j hm A v temp flag res).steps
      = (enRound q U₀ hw p₀ rest x w u₀ g k j A v temp flag res).steps + 1 + (2 * k + 3) + 1 :=
  rfl

/-- The successor case's recorded count, read off the constructor: this iteration, then the rest. -/
theorem enumCert_succ_steps (q : ℕ) (U₀ : Type) [Fintype U₀]
    (hw : TM2ComputableInPolyTime encodeTriple encodeAnswer f)
    (p₀ : Bool × (Bool × DepthPay q (Bool × U₀)))
    (rest : CallLabel → PrepStmt hw.tm (LookupSlot ⊕ G) (lkΓ G Γg)
      (Bool × (Bool × DepthPay q (Bool × U₀))))
    (x w : List Bool) (u₀ : U₀) (g : ∀ j : G, List (Γg j)) (k m : ℕ) (j : Fin (2 ^ k))
    (hm : j.val + (m + 1) + 1 = 2 ^ k) (A : Bool) (v : hw.tm.σ) (temp : Option Sym)
    (flag res : Bool) :
    (enumCert q U₀ hw p₀ rest x w u₀ g k (m + 1) j hm A v temp flag res).steps
      = (enRound q U₀ hw p₀ rest x w u₀ g k j A v temp flag res).steps + 1 + (2 * k + 3) + 1
        + (enumCert q U₀ hw p₀ rest x w u₀ g k m ⟨j.val + 1, by omega⟩ (by simp only; omega)
            (A && seedRes f q x w k j) hw.tm.initialState none false (seedRes f q x w k j)).steps :=
  rfl

/-- **The enumeration's recorded count, bounded by the constructor's own recursion**:
`(m + 1)·(S + 2k + 5)` when `m` seeds remain after the current one — for any incoming aggregate,
flags and state. -/
theorem enumCert_steps_le (q : ℕ) (U₀ : Type) [Fintype U₀]
    (hw : TM2ComputableInPolyTime encodeTriple encodeAnswer f)
    (p₀ : Bool × (Bool × DepthPay q (Bool × U₀)))
    (rest : CallLabel → PrepStmt hw.tm (LookupSlot ⊕ G) (lkΓ G Γg)
      (Bool × (Bool × DepthPay q (Bool × U₀))))
    (x w : List Bool) (u₀ : U₀) (g : ∀ j : G, List (Γg j)) (k : ℕ) :
    ∀ (m : ℕ) (j : Fin (2 ^ k)) (hm : j.val + m + 1 = 2 ^ k) (A : Bool) (v : hw.tm.σ)
      (temp : Option Sym) (flag res : Bool),
      (enumCert q U₀ hw p₀ rest x w u₀ g k m j hm A v temp flag res).steps
        ≤ (m + 1) * (seedRoundBound hw x.length k w.length q + 2 * k + 5) := by
  intro m
  induction m with
  | zero =>
    intro j hm A v temp flag res
    rw [enumCert_zero_steps]
    have := enRound_steps_le q U₀ hw p₀ rest x w u₀ g k j A v temp flag res
    omega
  | succ m ih =>
    intro j hm A v temp flag res
    rw [enumCert_succ_steps]
    have h1 := enRound_steps_le q U₀ hw p₀ rest x w u₀ g k j A v temp flag res
    have h2 := ih ⟨j.val + 1, by omega⟩ (by simp only; omega) (A && seedRes f q x w k j)
      hw.tm.initialState none false (seedRes f q x w k j)
    have hring : (m + 1 + 1) * (seedRoundBound hw x.length k w.length q + 2 * k + 5)
        = (seedRoundBound hw x.length k w.length q + 2 * k + 5)
          + (m + 1) * (seedRoundBound hw x.length k w.length q + 2 * k + 5) := by ring
    rw [hring]
    omega

/-- **All `2^k` seeds, bounded**: the certificate `enum_checkAll` uses records at most
`2^k · (S + 2k + 5)` steps.  Width zero gives multiplier one: its single seed is a full round. -/
theorem enum_steps_le (q : ℕ) (U₀ : Type) [Fintype U₀]
    (hw : TM2ComputableInPolyTime encodeTriple encodeAnswer f)
    (p₀ : Bool × (Bool × DepthPay q (Bool × U₀)))
    (rest : CallLabel → PrepStmt hw.tm (LookupSlot ⊕ G) (lkΓ G Γg)
      (Bool × (Bool × DepthPay q (Bool × U₀))))
    (x w : List Bool) (u₀ : U₀) (g : ∀ j : G, List (Γg j)) (k : ℕ) (v : hw.tm.σ)
    (temp : Option Sym) (flag res : Bool) :
    (enumCert q U₀ hw p₀ rest x w u₀ g k (2 ^ k - 1) ⟨0, Nat.two_pow_pos k⟩
        (by simp only; have := Nat.two_pow_pos k; omega) true v temp flag res).steps
      ≤ 2 ^ k * (seedRoundBound hw x.length k w.length q + 2 * k + 5) := by
  have h := enumCert_steps_le q U₀ hw p₀ rest x w u₀ g k (2 ^ k - 1) ⟨0, Nat.two_pow_pos k⟩
    (by simp only; have := Nat.two_pow_pos k; omega) true v temp flag res
  have hk : 2 ^ k - 1 + 1 = 2 ^ k := Nat.sub_add_cancel (Nat.two_pow_pos k)
  rwa [hk] at h

end Bound

end PCP.Machine
