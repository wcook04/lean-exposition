import PCP.Complexity.SeedRound

/-!
# A uniform bound for the seed round

The bound is about the **specific constructor** `pathCert` — its recursion — and then about the
composed `seedRoundEvals`.  `PathCert`'s fields specify an execution and an endpoint but no cost
recurrence, so nothing here is inferred from that structure's type: the induction below unfolds the
constructor itself.

## Eliminating the address

`searchSteps` depends on the query numeral's *width*.  The algorithm witness's own output bound
controls that width — `encoded_output_length_le` bounds the encoded answer, and a query's encoding
is its numeral plus one separator — so no bound on the numeric address is needed anywhere.

## Fixing the sizes

With `A` an upper bound on history length plus remaining depth — invariant along a path, by
`PathCert.budget` and its positive-round counterpart `depth_budget` —

```text
N = x.length + rs.length + A + 2          every encoded triple on the path is at most this long
Q = (outputPoly hw.tm hw.time).eval N     every encoded answer is at most this long
C = (callPoly hw.tm hw.time).eval N       every preparation-and-call costs at most (2L+8) + C
```

and one round of any kind costs at most

```text
B = (2L + 8) + C + (W·(4Q + 10) + 3Q + 10) + (x.length + rs.length + 3A + 8),   L = N - 2.
```

A terminal round fits `B` with room to spare: it runs no search and no turnaround.

## The `+ 1`

The path at depth `d` is bounded by `(d + 1)·B`, not `d·B`: depth zero **still calls the
algorithm**, so a zero-depth path costs a full round.  Replacing the multiplier by `d` would be
false at `d = 0`.
-/

namespace PCP.Machine

open Turing Turing.TM2 Turing.TM2.Stmt StateTransition

/-! ### The sizes -/

/-- Every encoded triple along a path whose history stays within `A` is at most this long. -/
def tupleBound (x rs : List Bool) (A : ℕ) : ℕ := x.length + rs.length + A + 2

theorem length_encodeTriple_le (x rs a : List Bool) {A : ℕ} (hA : a.length ≤ A) :
    (encodeTriple (x, rs, a)).length ≤ tupleBound x rs A := by
  simp only [length_encodeTriple, tupleBound]
  omega

section Sizes

variable {f : List Bool × List Bool × List Bool → Bool ⊕ ℕ}

/-- The per-round budget `B`. -/
noncomputable def roundBound (hw : TM2ComputableInPolyTime encodeTriple encodeAnswer f)
    (x rs w : List Bool) (A : ℕ) : ℕ :=
  (2 * (x.length + rs.length + A) + 8) + (callPoly hw.tm hw.time).eval (tupleBound x rs A)
    + (w.length * (4 * (outputPoly hw.tm hw.time).eval (tupleBound x rs A) + 10)
        + 3 * (outputPoly hw.tm hw.time).eval (tupleBound x rs A) + 10)
    + (x.length + rs.length + 3 * A + 8)

/-- **The query numeral's width, bounded by the witness's own output bound** — the step that
removes the numeric address from every cost below. -/
theorem query_width_le (hw : TM2ComputableInPolyTime encodeTriple encodeAnswer f)
    (x rs a : List Bool) (addr : ℕ) (hans : f (x, rs, a) = .inr addr) {A : ℕ}
    (hA : a.length ≤ A) :
    (Nat.bits addr).length + 1 ≤ (outputPoly hw.tm hw.time).eval (tupleBound x rs A) := by
  have hout := encoded_output_length_le hw (x, rs, a)
  rw [hans] at hout
  have hlen : (encodeAnswer (Sum.inr addr)).length = (Nat.bits addr).length + 1 := by
    simp [encodeAnswer]
  have hmono := eval_mono (outputPoly hw.tm hw.time) (length_encodeTriple_le x rs a hA)
  omega

/-- A terminal round's residual destination is no wider than an encoded answer. -/
theorem terminalResid_length_le (hw : TM2ComputableInPolyTime encodeTriple encodeAnswer f)
    (x rs hist : List Bool) (ans : Bool ⊕ ℕ) (hans : f (x, rs, hist) = ans) {A : ℕ}
    (hA : hist.length ≤ A) :
    (terminalResid ans).length ≤ (outputPoly hw.tm hw.time).eval (tupleBound x rs A) := by
  cases ans with
  | inl b => simp [terminalResid]
  | inr addr =>
    have := query_width_le hw x rs hist addr hans hA
    simp only [terminalResid, length_ofBits]
    omega

/-- The search, charged at the numeral's width and then at `Q`. -/
theorem search_part_le (hw : TM2ComputableInPolyTime encodeTriple encodeAnswer f)
    (x rs a w : List Bool) (addr : ℕ) (hans : f (x, rs, a) = .inr addr) {A : ℕ}
    (hA : a.length ≤ A) :
    2 + searchSteps w (Nat.bits addr)
      ≤ w.length * (4 * (outputPoly hw.tm hw.time).eval (tupleBound x rs A) + 10)
        + 3 * (outputPoly hw.tm hw.time).eval (tupleBound x rs A) + 10 := by
  have hs := lk_search_steps_le w (Nat.bits addr)
  have hk := query_width_le hw x rs a addr hans hA
  have hmul : w.length * (4 * (Nat.bits addr).length + 10)
      ≤ w.length * (4 * (outputPoly hw.tm hw.time).eval (tupleBound x rs A) + 10) :=
    Nat.mul_le_mul_left _ (by omega)
  omega

/-- Preparation and the call, charged at `N` through the recorded bound. -/
theorem prepCall_steps_le (G : Type) [DecidableEq G] [Fintype G] (Γg : G → Type)
    (P : Type) [Fintype P] (hw : TM2ComputableInPolyTime encodeTriple encodeAnswer f) (p₀ : P)
    (route : CallLabel → PrepStmt hw.tm G Γg P) (x rs a : List Bool) (v : hw.tm.σ)
    (temp : Option Sym) (pay : P) (g : ∀ j : G, List (Γg j)) {A : ℕ} (hA : a.length ≤ A) :
    (prepCallEvals G Γg P hw p₀ route x rs a [] v temp pay g).steps
      ≤ (2 * (x.length + rs.length + A) + 8)
        + (callPoly hw.tm hw.time).eval (tupleBound x rs A) := by
  have h1 := (prepCallEvals G Γg P hw p₀ route x rs a [] v temp pay g).steps_le_m
  have h2 := eval_mono (callPoly hw.tm hw.time) (length_encodeTriple_le x rs a hA)
  omega

end Sizes

/-! ### Each kind of round fits `B` -/

section Rounds

variable {G : Type} [DecidableEq G] [Fintype G] {Γg : G → Type} {R : Type} [Fintype R]
  {f : List Bool × List Bool × List Bool → Bool ⊕ ℕ}

theorem aDecide_steps_le (hw : TM2ComputableInPolyTime encodeTriple encodeAnswer f)
    (p₀ : Bool × (Bool × R)) (dzero : R → Bool) (ddec : R → R)
    (rest : CallLabel → PrepStmt hw.tm (LookupSlot ⊕ G) (lkΓ G Γg) (Bool × (Bool × R)))
    (x rs a : List Bool) (b : Bool) (hans : f (x, rs, a) = .inl b) (v : hw.tm.σ)
    (temp : Option Sym) (flag res : Bool) (r : R) (wit pre : List Sym)
    (g : ∀ j : G, List (Γg j)) (w : List Bool) {A : ℕ} (hA : a.length ≤ A) :
    (aDecideEvals hw p₀ dzero ddec rest x rs a b hans v temp flag res r wit pre g).steps
      ≤ roundBound hw x rs w A := by
  have h := prepCall_steps_le (LookupSlot ⊕ G) (lkΓ G Γg) (Bool × (Bool × R)) hw p₀
    (queryRoute hw.tm G Γg R dzero (turnRoute hw.tm G Γg R ddec rest)) x rs a v temp
    (flag, (res, r)) (lkFrame G Γg wit pre g) hA
  change (prepCallEvals (LookupSlot ⊕ G) (lkΓ G Γg) (Bool × (Bool × R)) hw p₀
    (queryRoute hw.tm G Γg R dzero (turnRoute hw.tm G Γg R ddec rest)) x rs a [] v temp
    (flag, (res, r)) (lkFrame G Γg wit pre g)).steps + 1 ≤ _
  simp only [roundBound]
  omega

theorem aReject_steps_le (hw : TM2ComputableInPolyTime encodeTriple encodeAnswer f)
    (p₀ : Bool × (Bool × R)) (dzero : R → Bool) (ddec : R → R)
    (rest : CallLabel → PrepStmt hw.tm (LookupSlot ⊕ G) (lkΓ G Γg) (Bool × (Bool × R)))
    (x rs a : List Bool) (addr : ℕ) (hans : f (x, rs, a) = .inr addr) (v : hw.tm.σ)
    (temp : Option Sym) (flag res : Bool) (r : R) (hd : dzero r = true) (wit pre : List Sym)
    (g : ∀ j : G, List (Γg j)) (w : List Bool) {A : ℕ} (hA : a.length ≤ A) :
    (aRejectEvals hw p₀ dzero ddec rest x rs a addr hans v temp flag res r hd wit pre g).steps
      ≤ roundBound hw x rs w A := by
  have h := prepCall_steps_le (LookupSlot ⊕ G) (lkΓ G Γg) (Bool × (Bool × R)) hw p₀
    (queryRoute hw.tm G Γg R dzero (turnRoute hw.tm G Γg R ddec rest)) x rs a v temp
    (flag, (res, r)) (lkFrame G Γg wit pre g) hA
  change (prepCallEvals (LookupSlot ⊕ G) (lkΓ G Γg) (Bool × (Bool × R)) hw p₀
    (queryRoute hw.tm G Γg R dzero (turnRoute hw.tm G Γg R ddec rest)) x rs a [] v temp
    (flag, (res, r)) (lkFrame G Γg wit pre g)).steps + 1 ≤ _
  simp only [roundBound]
  omega

/-- **A positive round fits `B`**: preparation and the call at `N`, the search at `Q`, and the
turnaround at `A`. -/
theorem aIter_steps_le (hw : TM2ComputableInPolyTime encodeTriple encodeAnswer f)
    (p₀ : Bool × (Bool × R)) (dzero : R → Bool) (ddec : R → R)
    (rest : CallLabel → PrepStmt hw.tm (LookupSlot ⊕ G) (lkΓ G Γg) (Bool × (Bool × R)))
    (x rs a : List Bool) (addr : ℕ) (hans : f (x, rs, a) = .inr addr) (w : List Bool)
    (v : hw.tm.σ) (temp : Option Sym) (flag res : Bool) (r : R) (g : ∀ j : G, List (Γg j))
    (hd : dzero r = false) {A : ℕ} (hA : a.length ≤ A) :
    (aIterEvals hw p₀ dzero ddec rest x rs a addr hans w v temp flag res r g hd).steps
      ≤ roundBound hw x rs w A := by
  have h1 := prepCall_steps_le (LookupSlot ⊕ G) (lkΓ G Γg) (Bool × (Bool × R)) hw p₀
    (queryRoute hw.tm G Γg R dzero (turnRoute hw.tm G Γg R ddec rest)) x rs a v temp
    (flag, (res, r)) (lkFrame G Γg (ofBits w) [] g) hA
  have h2 := search_part_le hw x rs a w addr hans hA
  have h3 : turnSteps a (encodeTriple (x, rs, a)) ≤ x.length + rs.length + 3 * A + 8 := by
    rw [turnSteps_encodeTriple]; omega
  change (prepCallEvals (LookupSlot ⊕ G) (lkΓ G Γg) (Bool × (Bool × R)) hw p₀
      (queryRoute hw.tm G Γg R dzero (turnRoute hw.tm G Γg R ddec rest)) x rs a [] v temp
      (flag, (res, r)) (lkFrame G Γg (ofBits w) [] g)).steps
      + (2 + searchSteps w (Nat.bits addr)) + turnSteps a (encodeTriple (x, rs, a)) ≤ _
  simp only [roundBound]
  omega

end Rounds

/-! ### The path, by the constructor's own recursion -/

section PathBound

variable {G : Type} [DecidableEq G] [Fintype G] {Γg : G → Type}
  {f : List Bool × List Bool × List Bool → Bool ⊕ ℕ}

/-- **The uniform path bound, about `pathCert` itself.**

`(d + 1)·B` for a path started at depth `d` with history `a`, whenever `a.length + d ≤ A`.  The
proof follows the constructor's recursion — it unfolds `pathCert` — rather than reading a bound off
`PathCert`'s type, which has none. -/
theorem pathCert_steps_le (q : ℕ) (U : Type) [Fintype U]
    (hw : TM2ComputableInPolyTime encodeTriple encodeAnswer f)
    (p₀ : Bool × (Bool × DepthPay q U))
    (rest : CallLabel → PrepStmt hw.tm (LookupSlot ⊕ G) (lkΓ G Γg)
      (Bool × (Bool × DepthPay q U)))
    (x rs w : List Bool) (u : U) (g : ∀ j : G, List (Γg j)) (A : ℕ) :
    ∀ (d : ℕ) (i : Fin (q + 1)) (hi : (i : ℕ) = d) (a : List Bool) (v : hw.tm.σ)
      (temp : Option Sym) (flag res : Bool), a.length + d ≤ A →
      (pathCert q U hw p₀ rest x rs w u g d i hi a v temp flag res).steps
        ≤ (d + 1) * roundBound hw x rs w A := by
  intro d
  induction d with
  | zero =>
    intro i hi a v temp flag res hA
    unfold pathCert
    split
    · rename_i b hans
      have := aDecide_steps_le hw p₀ (depthZero q U) (depthPred q U) rest x rs a b hans v temp flag
        res (i, u) (ofBits w) [] g w (A := A) (by omega)
      simpa using this
    · rename_i addr hans
      have := aReject_steps_le hw p₀ (depthZero q U) (depthPred q U) rest x rs a addr hans v temp
        flag res (i, u) (by simp [depthZero, hi]) (ofBits w) [] g w (A := A) (by omega)
      simpa using this
  | succ d ih =>
    intro i hi a v temp flag res hA
    unfold pathCert
    split
    · rename_i b hans
      have := aDecide_steps_le hw p₀ (depthZero q U) (depthPred q U) rest x rs a b hans v temp flag
        res (i, u) (ofBits w) [] g w (A := A) (by omega)
      have hB : roundBound hw x rs w A ≤ (d + 1 + 1) * roundBound hw x rs w A :=
        Nat.le_mul_of_pos_left _ (by omega)
      exact le_trans this hB
    · rename_i addr hans
      have hpos : 0 < (i : ℕ) := by omega
      have hiter := aIter_steps_le hw p₀ (depthZero q U) (depthPred q U) rest x rs a addr hans w v
        temp flag res (i, u) g (depthZero_of_pos hpos u) (A := A) (by omega)
      have hrec := ih (depthPred q U (i, u)).1 (by simp only [depthPred_fst]; omega)
        (a ++ [oracleOfWitness w addr]) hw.tm.initialState none false (oracleOfWitness w addr)
        (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)
      have hring : (d + 1 + 1) * roundBound hw x rs w A
          = roundBound hw x rs w A + (d + 1) * roundBound hw x rs w A := by ring
      rw [hring]
      exact Nat.add_le_add hiter hrec

/-- The cleanup share, bounded without reference to the address: `Q + N + A + 5`. -/
theorem seedCleanupSteps_le (hw : TM2ComputableInPolyTime encodeTriple encodeAnswer f)
    (x rs hist : List Bool) (ans : Bool ⊕ ℕ) (hans : f (x, rs, hist) = ans) {A : ℕ}
    (hA : hist.length ≤ A) :
    seedCleanupSteps x rs ans hist
      ≤ (outputPoly hw.tm hw.time).eval (tupleBound x rs A) + tupleBound x rs A + A + 5 := by
  have h := terminalResid_length_le hw x rs hist ans hans hA
  rw [seedCleanupSteps_eq]
  simp only [tupleBound] at h ⊢
  omega

/-- **The whole seed round, uniformly bounded.**  `(d + 1)·B` for the path plus `Q + N + A + 5` for
cleanup, with `A = a.length + d` and every term in witness length, seed and input lengths, and the
initial history length — never the numeric address.  The certificate's *recorded* count is what is
bounded; it is not replaced by the bound. -/
theorem seedRound_steps_le (q : ℕ) (U : Type) [Fintype U]
    (hw : TM2ComputableInPolyTime encodeTriple encodeAnswer f)
    (p₀ : Bool × (Bool × DepthPay q U))
    (rest : CallLabel → PrepStmt hw.tm (LookupSlot ⊕ G) (lkΓ G Γg)
      (Bool × (Bool × DepthPay q U)))
    (x rs w : List Bool) (u : U) (g : ∀ j : G, List (Γg j))
    (d : ℕ) (i : Fin (q + 1)) (hi : (i : ℕ) = d) (a : List Bool) (v : hw.tm.σ)
    (temp : Option Sym) (flag res : Bool) :
    (seedRoundEvals q U hw p₀ rest x rs w u g d i hi a v temp flag res).steps
      ≤ (d + 1) * roundBound hw x rs w (a.length + d)
        + ((outputPoly hw.tm hw.time).eval (tupleBound x rs (a.length + d))
          + tupleBound x rs (a.length + d) + (a.length + d) + 5) := by
  rw [seedRoundEvals_steps]
  have hpath := pathCert_steps_le q U hw p₀
    (cleanRoute hw.tm G Γg (DepthPay q U) (depthReset q U) rest) x rs w u g (a.length + d) d i hi
    a v temp flag res le_rfl
  have hbud := (seedPath q U hw p₀ rest x rs w u g d i hi a v temp flag res).budget
  have hclean := seedCleanupSteps_le hw x rs
    (seedPath q U hw p₀ rest x rs w u g d i hi a v temp flag res).hist
    (seedPath q U hw p₀ rest x rs w u g d i hi a v temp flag res).answer
    (seedPath q U hw p₀ rest x rs w u g d i hi a v temp flag res).answer_eq
    (A := a.length + d) (by omega)
  exact Nat.add_le_add hpath hclean

end PathBound

end PCP.Machine
