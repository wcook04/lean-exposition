import PCP.Complexity.SeedIncrement

/-!
# Enumerating every seed of a fixed width

## One machine for every width

The program below has the same statements for every seed width `k`.  Neither `k` nor the seed index
is a control field: the seed is a tape, the increment finds its end by an empty exit, and completion
is detected by the increment's **overflow**.  Proofs quantify over `k` and over a mathematical seed
index; the machine never sees either.

## Process first, then increment, then test

Each iteration runs the whole seed round on the current seed, folds its result into the aggregate,
increments the seed, and only then tests the overflow.  So **width zero is one seed, not zero**: the
round runs on `[]`, the increment of `[]` overflows at once, and the loop stops.  The same order
processes the all-true last seed exactly once.

## The aggregate

`U := Bool × U₀`: the running conjunction beside the caller's own data.  It is separate from the
seed round's result field, which each round overwrites; `clDone`'s continuation folds that result
into the aggregate in one counted step **before** the increment can disturb anything.

## Depth

Cleanup already restores the budget to `q` at `clDone`, and the next `prepA1` uses that value as it
stands — no second reset is performed or charged.

## Evaluating every seed

The loop evaluates all `2 ^ k` seeds, never stopping early.  Its result equals `checkAll` — whose
`List.all` may short-circuit when evaluated — as a Boolean; no claim is made that the two evaluation
orders agree.
-/

namespace PCP.Machine

open Turing Turing.TM2 Turing.TM2.Stmt StateTransition

section

variable (tm : FinTM2) (G : Type) [DecidableEq G] [Fintype G] (Γg : G → Type)
  (q : ℕ) (U₀ : Type) [Fintype U₀]

/-- `clDone`'s continuation: fold the round's result into the aggregate, then increment. -/
def enAggStmt : PrepStmt tm (LookupSlot ⊕ G) (lkΓ G Γg) (Bool × (Bool × DepthPay q (Bool × U₀))) :=
  load (fun p => (p.1, (none, (p.2.2.1, (p.2.2.2.1,
      (p.2.2.2.2.1, (p.2.2.2.2.2.1 && p.2.2.2.1, p.2.2.2.2.2.2)))))))
    (goto (fun _ => .inr .inInit))

/-- `inTest`: stop on overflow, otherwise start the next seed's round. -/
def enTestStmt : PrepStmt tm (LookupSlot ⊕ G) (lkΓ G Γg) (Bool × (Bool × DepthPay q (Bool × U₀))) :=
  branch (fun p => p.2.2.1) (goto (fun _ => .inr .enDone)) (goto (fun _ => .inr .prepA1))

/-- The enumerator's labels.  `enDone` is its active boundary and dispatches through `rest`. -/
def enumRoute
    (rest : CallLabel → PrepStmt tm (LookupSlot ⊕ G) (lkΓ G Γg)
      (Bool × (Bool × DepthPay q (Bool × U₀)))) :
    CallLabel → PrepStmt tm (LookupSlot ⊕ G) (lkΓ G Γg) (Bool × (Bool × DepthPay q (Bool × U₀)))
  | .clDone => enAggStmt tm G Γg q U₀
  | .inTest => enTestStmt tm G Γg q U₀
  | l => rest l

variable {tm G Γg q U₀}

section Steps

variable (eIn : tm.Γ tm.k₀ ≃ Sym) (eOut : tm.Γ tm.k₁ ≃ Sym)
  (p₀ : Bool × (Bool × DepthPay q (Bool × U₀)))
  (rest : CallLabel → PrepStmt tm (LookupSlot ⊕ G) (lkΓ G Γg)
    (Bool × (Bool × DepthPay q (Bool × U₀))))

/-- The whole loop: the seed round, cleanup, the aggregate, the increment and the test. -/
abbrev eTM : FinTM2 :=
  iTM eIn eOut p₀ (depthZero q (Bool × U₀)) (depthPred q (Bool × U₀)) (depthReset q (Bool × U₀))
    (enumRoute tm G Γg q U₀ rest)

/-- A configuration of it. -/
def enCfg (l : Option (tm.Λ ⊕ CallLabel)) (v : tm.σ) (temp : Option Sym)
    (pay : Bool × (Bool × DepthPay q (Bool × U₀))) (S : ∀ k, List (tm.Γ k))
    (inp dst scr xt rt at' wit pre : List Sym) (g : ∀ j : G, List (Γg j)) :
    (eTM eIn eOut p₀ rest).Cfg :=
  inCfg eIn eOut p₀ (depthZero q (Bool × U₀)) (depthPred q (Bool × U₀)) (depthReset q (Bool × U₀))
    (enumRoute tm G Γg q U₀ rest) l v temp pay S inp dst scr xt rt at' wit pre g

theorem en_bind_of_step {c c' : (eTM eIn eOut p₀ rest).Cfg}
    (h : (eTM eIn eOut p₀ rest).step c = some c') :
    (flip Bind.bind (eTM eIn eOut p₀ rest).step) (some c) = some c' := h

/-- The fold: one counted step, the result conjoined into the aggregate. -/
theorem en_step_agg (v : tm.σ) (temp : Option Sym) (flag b : Bool) (dep : Fin (q + 1))
    (A : Bool) (u₀ : U₀) (S : ∀ k, List (tm.Γ k)) (inp dst scr xt rt at' wit pre : List Sym)
    (g : ∀ j : G, List (Γg j)) :
    (eTM eIn eOut p₀ rest).step
        (enCfg eIn eOut p₀ rest (some (.inr CallLabel.clDone)) v temp (flag, (b, (dep, (A, u₀)))) S
          inp dst scr xt rt at' wit pre g)
      = some (enCfg eIn eOut p₀ rest (some (.inr CallLabel.inInit)) v none
          (flag, (b, (dep, (A && b, u₀)))) S inp dst scr xt rt at' wit pre g) :=
  rfl

/-- No overflow: the next seed's round begins. -/
theorem en_step_next (v : tm.σ) (temp : Option Sym) (b : Bool) (r : DepthPay q (Bool × U₀))
    (S : ∀ k, List (tm.Γ k)) (inp dst scr xt rt at' wit pre : List Sym)
    (g : ∀ j : G, List (Γg j)) :
    (eTM eIn eOut p₀ rest).step
        (enCfg eIn eOut p₀ rest (some (.inr CallLabel.inTest)) v temp (false, (b, r)) S inp dst scr
          xt rt at' wit pre g)
      = some (enCfg eIn eOut p₀ rest (some (.inr CallLabel.prepA1)) v temp (false, (b, r)) S inp
          dst scr xt rt at' wit pre g) :=
  rfl

/-- Overflow: the enumeration's boundary. -/
theorem en_step_done (v : tm.σ) (temp : Option Sym) (b : Bool) (r : DepthPay q (Bool × U₀))
    (S : ∀ k, List (tm.Γ k)) (inp dst scr xt rt at' wit pre : List Sym)
    (g : ∀ j : G, List (Γg j)) :
    (eTM eIn eOut p₀ rest).step
        (enCfg eIn eOut p₀ rest (some (.inr CallLabel.inTest)) v temp (true, (b, r)) S inp dst scr
          xt rt at' wit pre g)
      = some (enCfg eIn eOut p₀ rest (some (.inr CallLabel.enDone)) v temp (true, (b, r)) S inp
          dst scr xt rt at' wit pre g) :=
  rfl

end Steps

end

/-! ## The loop -/

/-- The result of seed `j` of width `k`, and `true` past the last seed. -/
def seedRes (f : List Bool × List Bool × List Bool → Bool ⊕ ℕ) (q : ℕ) (x w : List Bool)
    (k j : ℕ) : Bool :=
  if h : j < 2 ^ k then
    runAdaptive (fun c => f (x, bitsOfFin k ⟨j, h⟩, c)) (oracleOfWitness w) q []
  else true

/-- **Evaluating every seed is `checkAll`.**  As Booleans only: `List.all` may short-circuit, and no
claim is made about evaluation order. -/
theorem range_all_seedRes (f : List Bool × List Bool × List Bool → Bool ⊕ ℕ) (q : ℕ)
    (x w : List Bool) (k : ℕ) :
    (List.range' 0 (2 ^ k)).all (seedRes f q x w k)
      = checkAll (fun x r a => f (x, r, a)) q k x w := by
  rw [← List.range_eq_range']
  refine Bool.eq_iff_iff.2 ⟨fun h => ?_, fun h => ?_⟩
  · rw [checkAll_eq_true_iff]
    intro r
    have := List.all_eq_true.1 h r.val (List.mem_range.2 r.isLt)
    simpa [seedRes, r.isLt] using this
  · rw [List.all_eq_true]
    intro j hj
    have hj' := List.mem_range.1 hj
    have := (checkAll_eq_true_iff _ q k x w).1 h ⟨j, hj'⟩
    simpa [seedRes, hj'] using this

section Loop

variable {G : Type} [DecidableEq G] [Fintype G] {Γg : G → Type}
  {f : List Bool × List Bool × List Bool → Bool ⊕ ℕ}

/-- The continuation the seed round is built on: the increment, then the enumerator. -/
abbrev enRest (q : ℕ) (U₀ : Type) [Fintype U₀]
    (hw : TM2ComputableInPolyTime encodeTriple encodeAnswer f)
    (rest : CallLabel → PrepStmt hw.tm (LookupSlot ⊕ G) (lkΓ G Γg)
      (Bool × (Bool × DepthPay q (Bool × U₀)))) :
    CallLabel → PrepStmt hw.tm (LookupSlot ⊕ G) (lkΓ G Γg)
      (Bool × (Bool × DepthPay q (Bool × U₀))) :=
  incRoute hw.tm G Γg (DepthPay q (Bool × U₀)) (enumRoute hw.tm G Γg q U₀ rest)

/-- Where each iteration starts: `prepA1` with an empty history, the full budget, the current seed,
and the aggregate so far. -/
noncomputable def enStart (q : ℕ) (U₀ : Type) [Fintype U₀]
    (hw : TM2ComputableInPolyTime encodeTriple encodeAnswer f)
    (p₀ : Bool × (Bool × DepthPay q (Bool × U₀)))
    (rest : CallLabel → PrepStmt hw.tm (LookupSlot ⊕ G) (lkΓ G Γg)
      (Bool × (Bool × DepthPay q (Bool × U₀))))
    (x w : List Bool) (u₀ : U₀) (g : ∀ j : G, List (Γg j)) (k : ℕ) (j : Fin (2 ^ k)) (A : Bool)
    (v : hw.tm.σ) (temp : Option Sym) (flag res : Bool) :
    (eTM hw.inputAlphabet hw.outputAlphabet p₀ rest).Cfg :=
  pathStart q (Bool × U₀) hw p₀
    (cleanRoute hw.tm G Γg (DepthPay q (Bool × U₀)) (depthReset q (Bool × U₀))
      (enRest q U₀ hw rest))
    x (bitsOfFin k j) w (A, u₀) g (Fin.last q) [] v temp flag res

/-- The enumeration's endpoint. -/
noncomputable def enStop (q : ℕ) (U₀ : Type) [Fintype U₀]
    (hw : TM2ComputableInPolyTime encodeTriple encodeAnswer f)
    (p₀ : Bool × (Bool × DepthPay q (Bool × U₀)))
    (rest : CallLabel → PrepStmt hw.tm (LookupSlot ⊕ G) (lkΓ G Γg)
      (Bool × (Bool × DepthPay q (Bool × U₀))))
    (x w : List Bool) (u₀ : U₀) (g : ∀ j : G, List (Γg j)) (k : ℕ) (A lastRes : Bool) :
    (eTM hw.inputAlphabet hw.outputAlphabet p₀ rest).Cfg :=
  enCfg hw.inputAlphabet hw.outputAlphabet p₀ rest (some (.inr CallLabel.enDone))
    hw.tm.initialState none (true, (lastRes, (Fin.last q, (A, u₀)))) (fun _ => []) [] [] []
    (ofBits x) (ofBits (bitsOfFin k ⟨0, Nat.two_pow_pos k⟩)) [] (ofBits w) [] g

/-- One seed's round, built on the completed loop program. -/
noncomputable abbrev enRound (q : ℕ) (U₀ : Type) [Fintype U₀]
    (hw : TM2ComputableInPolyTime encodeTriple encodeAnswer f)
    (p₀ : Bool × (Bool × DepthPay q (Bool × U₀)))
    (rest : CallLabel → PrepStmt hw.tm (LookupSlot ⊕ G) (lkΓ G Γg)
      (Bool × (Bool × DepthPay q (Bool × U₀))))
    (x w : List Bool) (u₀ : U₀) (g : ∀ j : G, List (Γg j)) (k : ℕ) (j : Fin (2 ^ k)) (A : Bool)
    (v : hw.tm.σ) (temp : Option Sym) (flag res : Bool) :=
  seedRoundEvals q (Bool × U₀) hw p₀ (enRest q U₀ hw rest) x (bitsOfFin k j) w (A, u₀) g q
    (Fin.last q) rfl [] v temp flag res

/-- **One iteration, up to the overflow test**: the seed round, the fold, and the increment — the
current seed is processed *before* anything looks at the carry. -/
theorem en_iter (q : ℕ) (U₀ : Type) [Fintype U₀]
    (hw : TM2ComputableInPolyTime encodeTriple encodeAnswer f)
    (p₀ : Bool × (Bool × DepthPay q (Bool × U₀)))
    (rest : CallLabel → PrepStmt hw.tm (LookupSlot ⊕ G) (lkΓ G Γg)
      (Bool × (Bool × DepthPay q (Bool × U₀))))
    (x w : List Bool) (u₀ : U₀) (g : ∀ j : G, List (Γg j)) (k : ℕ) (j : Fin (2 ^ k)) (A : Bool)
    (v : hw.tm.σ) (temp : Option Sym) (flag res : Bool) :
    (flip Bind.bind (eTM hw.inputAlphabet hw.outputAlphabet p₀ rest).step)^[
        (enRound q U₀ hw p₀ rest x w u₀ g k j A v temp flag res).steps + 1 + (2 * k + 3)]
        (some (enStart q U₀ hw p₀ rest x w u₀ g k j A v temp flag res))
      = some (enCfg hw.inputAlphabet hw.outputAlphabet p₀ rest (some (.inr CallLabel.inTest))
          hw.tm.initialState none
          (finalCarry true (bitsOfFin k j),
            (seedRes f q x w k j, (Fin.last q, (A && seedRes f q x w k j, u₀))))
          (fun _ => []) [] [] [] (ofBits x) (ofBits (incBits (bitsOfFin k j))) [] (ofBits w) []
          g) := by
  have hres : seedRes f q x w k j
      = runAdaptive (fun c => f (x, bitsOfFin k j, c)) (oracleOfWitness w) q [] := by
    simp [seedRes, j.isLt]
  have hround : (flip Bind.bind (eTM hw.inputAlphabet hw.outputAlphabet p₀ rest).step)^[
        (enRound q U₀ hw p₀ rest x w u₀ g k j A v temp flag res).steps]
        (some (enStart q U₀ hw p₀ rest x w u₀ g k j A v temp flag res))
      = some (enCfg hw.inputAlphabet hw.outputAlphabet p₀ rest (some (.inr CallLabel.clDone))
          hw.tm.initialState none (false, (seedRes f q x w k j, (Fin.last q, (A, u₀))))
          (fun _ => []) [] [] [] (ofBits x) (ofBits (bitsOfFin k j)) [] (ofBits w) [] g) := by
    rw [hres]
    exact (enRound q U₀ hw p₀ rest x w u₀ g k j A v temp flag res).evals_in_steps
  have hinc := in_trace hw.inputAlphabet hw.outputAlphabet p₀ (depthZero q (Bool × U₀))
    (depthPred q (Bool × U₀)) (depthReset q (Bool × U₀)) (enumRoute hw.tm G Γg q U₀ rest)
    (bitsOfFin k j) hw.tm.initialState none false (seedRes f q x w k j)
    (Fin.last q, (A && seedRes f q x w k j, u₀)) (fun _ => []) [] [] (ofBits x) [] (ofBits w) [] g
  rw [length_bitsOfFin] at hinc
  have hsplit : (enRound q U₀ hw p₀ rest x w u₀ g k j A v temp flag res).steps + 1 + (2 * k + 3)
      = (2 * k + 3) + (1 + (enRound q U₀ hw p₀ rest x w u₀ g k j A v temp flag res).steps) := by
    omega
  rw [hsplit,
    Function.iterate_add_apply
      (flip Bind.bind (eTM hw.inputAlphabet hw.outputAlphabet p₀ rest).step) (2 * k + 3)
      (1 + (enRound q U₀ hw p₀ rest x w u₀ g k j A v temp flag res).steps),
    Function.iterate_add_apply
      (flip Bind.bind (eTM hw.inputAlphabet hw.outputAlphabet p₀ rest).step) 1
      (enRound q U₀ hw p₀ rest x w u₀ g k j A v temp flag res).steps,
    hround, Function.iterate_one,
    en_bind_of_step hw.inputAlphabet hw.outputAlphabet p₀ rest
      (en_step_agg hw.inputAlphabet hw.outputAlphabet p₀ rest hw.tm.initialState none false
        (seedRes f q x w k j) (Fin.last q) A u₀ (fun _ => []) [] [] [] (ofBits x)
        (ofBits (bitsOfFin k j)) [] (ofBits w) [] g)]
  exact hinc

/-- **What an enumeration from seed `j` delivers**: its exact recorded count, and the execution to
`enDone` with the aggregate extended by every result from seed `j` on. -/
structure EnumCert (q : ℕ) (U₀ : Type) [Fintype U₀]
    (hw : TM2ComputableInPolyTime encodeTriple encodeAnswer f)
    (p₀ : Bool × (Bool × DepthPay q (Bool × U₀)))
    (rest : CallLabel → PrepStmt hw.tm (LookupSlot ⊕ G) (lkΓ G Γg)
      (Bool × (Bool × DepthPay q (Bool × U₀))))
    (x w : List Bool) (u₀ : U₀) (g : ∀ j : G, List (Γg j)) (k : ℕ) (j : Fin (2 ^ k)) (A : Bool)
    (v : hw.tm.σ) (temp : Option Sym) (flag res : Bool) where
  /-- The exact recorded count: the sum of every iteration's own count. -/
  steps : ℕ
  /-- The execution. -/
  run : (flip Bind.bind (eTM hw.inputAlphabet hw.outputAlphabet p₀ rest).step)^[steps]
        (some (enStart q U₀ hw p₀ rest x w u₀ g k j A v temp flag res))
      = some (enStop q U₀ hw p₀ rest x w u₀ g k
          (A && (List.range' j.val (2 ^ k - j.val)).all (seedRes f q x w k))
          (seedRes f q x w k (2 ^ k - 1)))

/-- **The enumeration**, by recursion on how many seeds remain after the current one.  The machine
never counts: it stops when the increment overflows, and the recursion only mirrors that. -/
noncomputable def enumCert (q : ℕ) (U₀ : Type) [Fintype U₀]
    (hw : TM2ComputableInPolyTime encodeTriple encodeAnswer f)
    (p₀ : Bool × (Bool × DepthPay q (Bool × U₀)))
    (rest : CallLabel → PrepStmt hw.tm (LookupSlot ⊕ G) (lkΓ G Γg)
      (Bool × (Bool × DepthPay q (Bool × U₀))))
    (x w : List Bool) (u₀ : U₀) (g : ∀ j : G, List (Γg j)) (k : ℕ) :
    ∀ (m : ℕ) (j : Fin (2 ^ k)), j.val + m + 1 = 2 ^ k → ∀ (A : Bool) (v : hw.tm.σ)
      (temp : Option Sym) (flag res : Bool),
      EnumCert q U₀ hw p₀ rest x w u₀ g k j A v temp flag res
  | 0, j, hm, A, v, temp, flag, res =>
      { steps := (enRound q U₀ hw p₀ rest x w u₀ g k j A v temp flag res).steps + 1 + (2 * k + 3)
          + 1
        run := by
          have hlast : j = ⟨2 ^ k - 1, Nat.sub_lt (Nat.two_pow_pos k) Nat.one_pos⟩ :=
            Fin.ext (by simp only; omega)
          have hcarry : finalCarry true (bitsOfFin k j) = true := by
            rw [hlast]; exact finalCarry_bitsOfFin_last k
          have hwrap : incBits (bitsOfFin k j) = bitsOfFin k ⟨0, Nat.two_pow_pos k⟩ := by
            rw [hlast]; exact incBits_bitsOfFin_last k
          have hspan : (List.range' j.val (2 ^ k - j.val)).all (seedRes f q x w k)
              = seedRes f q x w k j.val := by
            rw [show 2 ^ k - j.val = 0 + 1 by omega]; simp
          have hj : j.val = 2 ^ k - 1 := by omega
          rw [Function.iterate_succ_apply', en_iter, hcarry, hwrap, hspan, ← hj]
          exact en_bind_of_step hw.inputAlphabet hw.outputAlphabet p₀ rest
            (en_step_done hw.inputAlphabet hw.outputAlphabet p₀ rest hw.tm.initialState none
              (seedRes f q x w k j) (Fin.last q, (A && seedRes f q x w k j, u₀)) (fun _ => []) []
              [] [] (ofBits x) (ofBits (bitsOfFin k ⟨0, Nat.two_pow_pos k⟩)) [] (ofBits w) [] g) }
  | m + 1, j, hm, A, v, temp, flag, res =>
      let hnext : j.val + 1 < 2 ^ k := by omega
      let ih := enumCert q U₀ hw p₀ rest x w u₀ g k m ⟨j.val + 1, hnext⟩ (by simp only; omega)
        (A && seedRes f q x w k j) hw.tm.initialState none false (seedRes f q x w k j)
      { steps := (enRound q U₀ hw p₀ rest x w u₀ g k j A v temp flag res).steps + 1 + (2 * k + 3)
          + 1 + ih.steps
        run := by
          have hcarry : finalCarry true (bitsOfFin k j) = false :=
            finalCarry_bitsOfFin_of_lt k j hnext
          have hsucc : incBits (bitsOfFin k j) = bitsOfFin k ⟨j.val + 1, hnext⟩ :=
            incBits_bitsOfFin k j hnext
          have hspan : (A && (List.range' j.val (2 ^ k - j.val)).all (seedRes f q x w k))
              = ((A && seedRes f q x w k j)
                && (List.range' (j.val + 1) (2 ^ k - (j.val + 1))).all (seedRes f q x w k)) := by
            rw [show 2 ^ k - j.val = (2 ^ k - (j.val + 1)) + 1 by omega, List.range'_succ,
              List.all_cons, Bool.and_assoc]
          rw [hspan, Nat.add_comm _ ih.steps, Function.iterate_add_apply,
            Function.iterate_succ_apply', en_iter, hcarry, hsucc,
            en_bind_of_step hw.inputAlphabet hw.outputAlphabet p₀ rest
              (en_step_next hw.inputAlphabet hw.outputAlphabet p₀ rest hw.tm.initialState none
                (seedRes f q x w k j) (Fin.last q, (A && seedRes f q x w k j, u₀)) (fun _ => [])
                [] [] [] (ofBits x) (ofBits (bitsOfFin k ⟨j.val + 1, hnext⟩)) [] (ofBits w) [] g)]
          exact ih.run }

/-- **The whole enumeration.**  From the first seed with the aggregate `true`, the machine reaches
`enDone` holding exactly `checkAll` for `alg x r a := f (x, r, a)` — for every width `k`, width zero
included, where the single empty seed is processed once and then overflows. -/
theorem enum_checkAll (q : ℕ) (U₀ : Type) [Fintype U₀]
    (hw : TM2ComputableInPolyTime encodeTriple encodeAnswer f)
    (p₀ : Bool × (Bool × DepthPay q (Bool × U₀)))
    (rest : CallLabel → PrepStmt hw.tm (LookupSlot ⊕ G) (lkΓ G Γg)
      (Bool × (Bool × DepthPay q (Bool × U₀))))
    (x w : List Bool) (u₀ : U₀) (g : ∀ j : G, List (Γg j)) (k : ℕ) (v : hw.tm.σ)
    (temp : Option Sym) (flag res : Bool) :
    (flip Bind.bind (eTM hw.inputAlphabet hw.outputAlphabet p₀ rest).step)^[
        (enumCert q U₀ hw p₀ rest x w u₀ g k (2 ^ k - 1) ⟨0, Nat.two_pow_pos k⟩
          (by simp only; have := Nat.two_pow_pos k; omega) true v temp flag res).steps]
        (some (enStart q U₀ hw p₀ rest x w u₀ g k ⟨0, Nat.two_pow_pos k⟩ true v temp flag res))
      = some (enStop q U₀ hw p₀ rest x w u₀ g k (checkAll (fun x r a => f (x, r, a)) q k x w)
          (seedRes f q x w k (2 ^ k - 1))) := by
  have h := (enumCert q U₀ hw p₀ rest x w u₀ g k (2 ^ k - 1) ⟨0, Nat.two_pow_pos k⟩
    (by simp only; have := Nat.two_pow_pos k; omega) true v temp flag res).run
  simp only [Bool.true_and, Nat.sub_zero] at h
  rwa [range_all_seedRes] at h

end Loop

end PCP.Machine
