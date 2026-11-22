import PCP.Complexity.WitnessSearch

/-!
# The witness search: the loop, restoration and drain

`WitnessSearch.lean` proves the program's eleven one-step equations and one positive advance.  This
module runs the loop: induction on the **remaining Boolean witness**, never on the numeric address,
then the two cleanup scans and the full contract.

## What the loop maintains

At every visit to `lkMain` the witness has been split as `w = done ++ remaining`:

```text
witness stack  = ofBits remaining
prefix stack   = (ofBits done).reverse
bitsValue cs + done.length = bitsValue bs
cs.length = bs.length
scratch = []
```

`done` is in the witness's own order; the *stack* holds its reversal, because the advance pushes.
The induction below carries this implicitly by phrasing the endpoint with `w.take` and `w.drop`.

## The two exits

An empty witness exits through `lkExhausted`, which records `false`.  A nonempty witness with a
zero counter exits through `ztZero`, `lkSelected`, which records the addressed bit and leaves the
symbol carrying it on the stack for restoration to find.  Both then reach `lkRestore`.

## Work is bounded by the witness, not the address

`lk_search_steps_le` bounds the whole search by `w.length * (4k + 10) + 3k + 8` for a counter of
width `k`.  Nothing here is proportional to `bitsValue bs`: a long address with a short witness
exhausts the witness first, and a wide counter costs its width per scan, not its value.
-/

namespace PCP.Machine

open Turing Turing.TM2 Turing.TM2.Stmt StateTransition

/-! ### How far the loop runs -/

/-- The number of advances the search performs: one per traversed witness symbol, stopping at
whichever runs out first — the witness or the counter's value. -/
def advances : List Bool → List Bool → ℕ
  | [], _ => 0
  | _ :: w, cs => if bitsValue cs = 0 then 0 else advances w (decrBits cs) + 1

/-- The exact number of steps from the loop head to the restoration label. -/
def loopSteps : List Bool → List Bool → ℕ
  | [], _ => 2
  | _ :: w, cs =>
      if bitsValue cs = 0 then 2 * cs.length + 6
      else loopSteps w (decrBits cs) + (4 * cs.length + 9)

@[simp] theorem advances_nil (cs : List Bool) : advances [] cs = 0 := rfl

@[simp] theorem loopSteps_nil (cs : List Bool) : loopSteps [] cs = 2 := rfl

theorem advances_cons (b : Bool) (w cs : List Bool) :
    advances (b :: w) cs = if bitsValue cs = 0 then 0 else advances w (decrBits cs) + 1 := rfl

theorem loopSteps_cons (b : Bool) (w cs : List Bool) :
    loopSteps (b :: w) cs =
      if bitsValue cs = 0 then 2 * cs.length + 6
      else loopSteps w (decrBits cs) + (4 * cs.length + 9) := rfl

/-- The loop never traverses more of the witness than there is. -/
theorem advances_le_length (w cs : List Bool) : advances w cs ≤ w.length := by
  induction w generalizing cs with
  | nil => simp
  | cons b w ih =>
    rw [advances_cons]
    split
    · exact Nat.zero_le _
    · have := ih (decrBits cs); simp only [List.length_cons]; omega

/-- **The loop counts witness symbols, not address units.**  It stops at whichever of the two runs
out first. -/
theorem advances_eq_min (w cs : List Bool) : advances w cs = min w.length (bitsValue cs) := by
  induction w generalizing cs with
  | nil => simp
  | cons b w ih =>
    rw [advances_cons]
    split
    · next h => simp [h]
    · next h =>
      have hpos : 0 < bitsValue cs := Nat.pos_of_ne_zero h
      rw [ih (decrBits cs), bitsValue_decrBits cs hpos]
      simp only [List.length_cons]
      omega

/-- The counter keeps its width however many times it is decremented. -/
theorem length_iterate_decrBits (m : ℕ) (cs : List Bool) :
    (decrBits^[m] cs).length = cs.length := by
  induction m generalizing cs with
  | zero => rfl
  | succ m ih => rw [Function.iterate_succ_apply, ih (decrBits cs), length_decrBits]

/-- The closed form of the loop's cost: one advance per traversed symbol, then whichever exit
route was taken.  The two routes are **not** merged: selection costs a full zero test, exhaustion
costs two steps. -/
theorem loopSteps_eq (w cs : List Bool) :
    loopSteps w cs = advances w cs * (4 * cs.length + 9)
      + (if bitsValue cs < w.length then 2 * cs.length + 6 else 2) := by
  induction w generalizing cs with
  | nil => simp
  | cons b w ih =>
    rw [loopSteps_cons, advances_cons]
    split
    · next h => simp [h]
    · next h =>
      have hpos : 0 < bitsValue cs := Nat.pos_of_ne_zero h
      have hlen : (decrBits cs).length = cs.length := length_decrBits cs
      have hval : bitsValue (decrBits cs) = bitsValue cs - 1 := bitsValue_decrBits cs hpos
      rw [ih (decrBits cs), hlen, hval]
      by_cases hc : bitsValue cs < (b :: w).length
      · have hc' : bitsValue cs - 1 < w.length := by
          simp only [List.length_cons] at hc; omega
        rw [ite_eq_left hc, ite_eq_left hc']; ring
      · have hc' : ¬ bitsValue cs - 1 < w.length := by
          simp only [List.length_cons] at hc; omega
        rw [ite_eq_right hc, ite_eq_right hc']; ring

/-! ### The address, read through an ordered split -/

/-- **The index/append equation the loop turns on.**  Once `done.length` symbols have been
traversed and the counter has dropped by exactly that much, the original address into the whole
witness and the residual address into the remaining suffix name the same bit. -/
theorem oracleOfWitness_advance (done remaining : List Bool) {cs bs : List Bool}
    (h : bitsValue cs + done.length = bitsValue bs) :
    oracleOfWitness (done ++ remaining) (bitsValue bs)
      = oracleOfWitness remaining (bitsValue cs) := by
  have hle : done.length ≤ bitsValue bs := by omega
  have hidx : bitsValue bs - done.length = bitsValue cs := by omega
  simp only [oracleOfWitness, List.getD_eq_getElem?_getD, List.getElem?_append_right hle, hidx]

/-- Exhaustion is the same equation at the end of the witness: every address at or past the end
reads `false`. -/
theorem oracleOfWitness_of_length_le {w : List Bool} {n : ℕ} (h : w.length ≤ n) :
    oracleOfWitness w n = false := by
  simp only [oracleOfWitness, List.getD_eq_getElem?_getD]
  rw [List.getElem?_eq_none h]
  rfl

@[simp] theorem ofBits_append (x y : List Bool) : ofBits (x ++ y) = ofBits x ++ ofBits y := by
  simp [ofBits]

@[simp] theorem ofBits_cons (b : Bool) (x : List Bool) :
    ofBits (b :: x) = Sym.bit b :: ofBits x := rfl

@[simp] theorem ofBits_nil : ofBits [] = [] := rfl

section

variable {tm : FinTM2} {G : Type} [DecidableEq G] [Fintype G] {Γg : G → Type}
  {R : Type} [Fintype R]
  (eIn : tm.Γ tm.k₀ ≃ Sym) (eOut : tm.Γ tm.k₁ ≃ Sym) (p₀ : Bool × (Bool × R))
  (rest : CallLabel → PrepStmt tm (LookupSlot ⊕ G) (lkΓ G Γg) (Bool × (Bool × R)))

/-! ### The loop -/

/-- **The search loop**, from the loop head to the restoration label.

The induction is on the remaining Boolean witness, generalised over the counter, the traversed
prefix already on the stack, the helper flag and the incoming result — so the recursive step can be
taken at `finalBorrow true cs` without a separate flag lemma.

At the endpoint the result is exactly `w.getD (bitsValue cs) false`, in both exits at once: a
witness shorter than the address exhausts and records `false`, which is what an out-of-range
`getD` returns anyway. -/
theorem lk_loop (w : List Bool) :
    ∀ (cs : List Bool) (v : tm.σ) (temp : Option Sym) (flag res : Bool) (r : R)
      (pre : List Sym) (S : ∀ k, List (tm.Γ k)) (t : TripleSlot → List Sym) (inp : List Sym)
      (g : ∀ j : G, List (Γg j)),
    (flip Bind.bind (lkTM eIn eOut p₀ rest).step)^[loopSteps w cs]
        (some (lkCfg eIn eOut p₀ rest (some (.inr CallLabel.lkMain)) v temp (flag, (res, r)) S inp
          (ofBits cs) [] t (ofBits w) pre g))
      = some (lkCfg eIn eOut p₀ rest (some (.inr CallLabel.lkRestore)) v none
          (false, (oracleOfWitness w (bitsValue cs), r)) S inp
          (ofBits (decrBits^[advances w cs] cs)) [] t (ofBits (w.drop (advances w cs)))
          ((ofBits (w.take (advances w cs))).reverse ++ pre) g) := by
  induction w with
  | nil =>
    intro cs v temp flag res r pre S t inp g
    have hsplit : loopSteps ([] : List Bool) cs = 1 + 1 := rfl
    rw [hsplit, Function.iterate_add_apply (flip Bind.bind (lkTM eIn eOut p₀ rest).step) 1 1,
      Function.iterate_one, ofBits_nil,
      lk_bind_of_step eIn eOut p₀ rest
        (lk_step_main_nil eIn eOut p₀ rest v temp flag res r pre S t inp (ofBits cs) [] g),
      lk_bind_of_step eIn eOut p₀ rest
        (lk_step_exhausted eIn eOut p₀ rest v none flag res r [] pre S t inp (ofBits cs) [] g)]
    simp [oracleOfWitness, ofBits]
  | cons b w ih =>
    intro cs v temp flag res r pre S t inp g
    rw [loopSteps_cons, advances_cons]
    by_cases h : bitsValue cs = 0
    · rw [ite_eq_left h, ite_eq_left h]
      have hsplit : 2 * cs.length + 6 = 1 + (1 + ((2 * cs.length + 3) + 1)) := by omega
      rw [hsplit,
        Function.iterate_add_apply (flip Bind.bind (lkTM eIn eOut p₀ rest).step) 1
          (1 + ((2 * cs.length + 3) + 1)),
        Function.iterate_add_apply (flip Bind.bind (lkTM eIn eOut p₀ rest).step) 1
          ((2 * cs.length + 3) + 1),
        Function.iterate_add_apply (flip Bind.bind (lkTM eIn eOut p₀ rest).step)
          (2 * cs.length + 3) 1,
        Function.iterate_one,
        ofBits_cons,
        lk_bind_of_step eIn eOut p₀ rest
          (lk_step_main_cons eIn eOut p₀ rest v temp flag res r (Sym.bit b) (ofBits w) pre S t
            inp (ofBits cs) [] g),
        lk_zt_trace eIn eOut p₀ rest cs v none flag res r (Sym.bit b :: ofBits w) pre S t inp g,
        ite_eq_left h, decide_eq_false (by simp [h] : ¬ bitsValue cs ≠ 0),
        lk_bind_of_step eIn eOut p₀ rest
          (lk_step_zero eIn eOut p₀ rest v none false res r (Sym.bit b :: ofBits w) pre S t inp
            (ofBits cs) [] g),
        lk_bind_of_step eIn eOut p₀ rest
          (lk_step_selected eIn eOut p₀ rest v none false res b r (ofBits w) pre S t inp
            (ofBits cs) [] g)]
      simp [h, oracleOfWitness]
    · have hpos : 0 < bitsValue cs := Nat.pos_of_ne_zero h
      rw [ite_eq_right h, ite_eq_right h,
        Function.iterate_add_apply (flip Bind.bind (lkTM eIn eOut p₀ rest).step)
          (loopSteps w (decrBits cs)) (4 * cs.length + 9),
        ofBits_cons,
        lk_advance eIn eOut p₀ rest cs hpos v temp flag res r (Sym.bit b) (ofBits w) pre S t inp g,
        ih (decrBits cs) v none (finalBorrow true cs) res r (Sym.bit b :: pre) S t inp g,
        Function.iterate_succ_apply]
      have hval : bitsValue (decrBits cs) = bitsValue cs - 1 := bitsValue_decrBits cs hpos
      have hres : oracleOfWitness w (bitsValue (decrBits cs))
          = oracleOfWitness (b :: w) (bitsValue cs) := by
        obtain ⟨n, hn⟩ : ∃ n, bitsValue cs = n + 1 := ⟨bitsValue cs - 1, by omega⟩
        simp [oracleOfWitness, hval, hn]
      rw [hres]
      simp

/-! ### Restoration and drain -/

/-- **The restoring scan**, with an arbitrary accumulator so the induction gives the reversal
outright.  Every pop/push is one step, and the empty exit is the `+ 1`. -/
theorem lk_restore_trace (pre : List Sym) :
    ∀ (wit : List Sym) (v : tm.σ) (temp : Option Sym) (flag res : Bool) (r : R)
      (S : ∀ k, List (tm.Γ k)) (t : TripleSlot → List Sym) (inp dst scr : List Sym)
      (g : ∀ j : G, List (Γg j)),
    (flip Bind.bind (lkTM eIn eOut p₀ rest).step)^[pre.length + 1]
        (some (lkCfg eIn eOut p₀ rest (some (.inr CallLabel.lkRestore)) v temp (flag, (res, r)) S
          inp dst scr t wit pre g))
      = some (lkCfg eIn eOut p₀ rest (some (.inr CallLabel.lkDrain)) v none (flag, (res, r)) S
          inp dst scr t (pre.reverse ++ wit) [] g) := by
  induction pre with
  | nil =>
    intro wit v temp flag res r S t inp dst scr g
    rw [List.length_nil, Nat.zero_add, Function.iterate_one,
      lk_bind_of_step eIn eOut p₀ rest
        (lk_step_restore_nil eIn eOut p₀ rest v temp flag res r wit S t inp dst scr g)]
    simp
  | cons c pre ih =>
    intro wit v temp flag res r S t inp dst scr g
    change (flip Bind.bind (lkTM eIn eOut p₀ rest).step)^[(pre.length + 1) + 1] _ = _
    rw [Function.iterate_add_apply (flip Bind.bind (lkTM eIn eOut p₀ rest).step)
        (pre.length + 1) 1,
      Function.iterate_one,
      lk_bind_of_step eIn eOut p₀ rest
        (lk_step_restore_cons eIn eOut p₀ rest v temp flag res r c wit pre S t inp dst scr g),
      ih (c :: wit) v none flag res r S t inp dst scr g]
    simp

/-- **The drain**, emptying the destination stack.  Its cost is the counter's *width* — one step
per remaining symbol plus the empty exit — not the counter's value. -/
theorem lk_drain_trace (dst : List Sym) :
    ∀ (v : tm.σ) (temp : Option Sym) (flag res : Bool) (r : R) (wit pre : List Sym)
      (S : ∀ k, List (tm.Γ k)) (t : TripleSlot → List Sym) (inp scr : List Sym)
      (g : ∀ j : G, List (Γg j)),
    (flip Bind.bind (lkTM eIn eOut p₀ rest).step)^[dst.length + 1]
        (some (lkCfg eIn eOut p₀ rest (some (.inr CallLabel.lkDrain)) v temp (flag, (res, r)) S
          inp dst scr t wit pre g))
      = some (lkCfg eIn eOut p₀ rest (some (.inr CallLabel.lkDone)) v none (flag, (res, r)) S
          inp [] scr t wit pre g) := by
  induction dst with
  | nil =>
    intro v temp flag res r wit pre S t inp scr g
    rw [List.length_nil, Nat.zero_add, Function.iterate_one,
      lk_bind_of_step eIn eOut p₀ rest
        (lk_step_drain_nil eIn eOut p₀ rest v temp flag res r wit pre S t inp scr g)]
  | cons c dst ih =>
    intro v temp flag res r wit pre S t inp scr g
    change (flip Bind.bind (lkTM eIn eOut p₀ rest).step)^[(dst.length + 1) + 1] _ = _
    rw [Function.iterate_add_apply (flip Bind.bind (lkTM eIn eOut p₀ rest).step)
        (dst.length + 1) 1,
      Function.iterate_one,
      lk_bind_of_step eIn eOut p₀ rest
        (lk_step_drain_cons eIn eOut p₀ rest v temp flag res r c wit pre S t inp dst scr g),
      ih v none flag res r wit pre S t inp scr g]

/-! ### The whole search -/

/-- The exact cost of the whole search: the loop, then one restoration step per traversed symbol
plus its empty exit, then one drain step per counter cell plus its empty exit. -/
def searchSteps (w bs : List Bool) : ℕ :=
  loopSteps w bs + (advances w bs + 1) + (bs.length + 1)

/-- **The witness search, end to end.**

From the loop head with the address on the counter tape and the witness in place, to the active
completion boundary `lkDone` — whose continuation has *not* run.  The witness comes back in its
original order, the prefix stack and the counter tape are empty, scratch is empty again — the zero
test and the decrement both scan through it, and both restore it — the temporary is cleared, and
the result is exactly `oracleOfWitness w (bitsValue bs)`: the addressed bit when the
witness reaches that far, and `false` when it does not.

`bs` is an arbitrary bit list, not a canonical one — `bitsValue` reads high zero bits as the value
they denote, so no canonicality hypothesis is needed here. -/
theorem lk_search (w bs : List Bool) (v : tm.σ) (temp : Option Sym) (flag res : Bool) (r : R)
    (S : ∀ k, List (tm.Γ k)) (t : TripleSlot → List Sym) (inp : List Sym)
    (g : ∀ j : G, List (Γg j)) :
    (flip Bind.bind (lkTM eIn eOut p₀ rest).step)^[searchSteps w bs]
        (some (lkCfg eIn eOut p₀ rest (some (.inr CallLabel.lkMain)) v temp (flag, (res, r)) S inp
          (ofBits bs) [] t (ofBits w) [] g))
      = some (lkCfg eIn eOut p₀ rest (some (.inr CallLabel.lkDone)) v none
          (false, (oracleOfWitness w (bitsValue bs), r)) S inp [] [] t (ofBits w) [] g) := by
  have hm : advances w bs ≤ w.length := advances_le_length w bs
  have hsplit : searchSteps w bs
      = (bs.length + 1) + ((advances w bs + 1) + loopSteps w bs) := by
    simp only [searchSteps]; omega
  have hlen : ((ofBits (w.take (advances w bs))).reverse ++ ([] : List Sym)).length
      = advances w bs := by
    simp [Nat.min_eq_left hm]
  have hdlen : (ofBits (decrBits^[advances w bs] bs)).length = bs.length := by
    simp [length_iterate_decrBits]
  have hrest := lk_restore_trace eIn eOut p₀ rest
    ((ofBits (w.take (advances w bs))).reverse ++ ([] : List Sym))
    (ofBits (w.drop (advances w bs))) v none false (oracleOfWitness w (bitsValue bs)) r S t inp
    (ofBits (decrBits^[advances w bs] bs)) [] g
  rw [hlen] at hrest
  have hdrain := lk_drain_trace eIn eOut p₀ rest (ofBits (decrBits^[advances w bs] bs)) v none
    false (oracleOfWitness w (bitsValue bs)) r
    (((ofBits (w.take (advances w bs))).reverse ++ ([] : List Sym)).reverse
      ++ ofBits (w.drop (advances w bs))) [] S t inp [] g
  rw [hdlen] at hdrain
  rw [hsplit,
    Function.iterate_add_apply (flip Bind.bind (lkTM eIn eOut p₀ rest).step) (bs.length + 1)
      ((advances w bs + 1) + loopSteps w bs),
    Function.iterate_add_apply (flip Bind.bind (lkTM eIn eOut p₀ rest).step)
      (advances w bs + 1) (loopSteps w bs),
    lk_loop eIn eOut p₀ rest w bs v temp flag res r [] S t inp g, hrest, hdrain]
  congr 2
  simp only [List.append_nil, List.reverse_reverse, ← ofBits_append, List.take_append_drop]

/-- The search certificate, with its count written out. -/
def lkSearchEvals (w bs : List Bool) (v : tm.σ) (temp : Option Sym) (flag res : Bool) (r : R)
    (S : ∀ k, List (tm.Γ k)) (t : TripleSlot → List Sym) (inp : List Sym)
    (g : ∀ j : G, List (Γg j)) :
    EvalsToInTime (lkTM eIn eOut p₀ rest).step
      (lkCfg eIn eOut p₀ rest (some (.inr CallLabel.lkMain)) v temp (flag, (res, r)) S inp
        (ofBits bs) [] t (ofBits w) [] g)
      (some (lkCfg eIn eOut p₀ rest (some (.inr CallLabel.lkDone)) v none
        (false, (oracleOfWitness w (bitsValue bs), r)) S inp [] [] t (ofBits w) [] g))
      (searchSteps w bs) where
  steps := searchSteps w bs
  evals_in_steps := lk_search eIn eOut p₀ rest w bs v temp flag res r S t inp g
  steps_le_m := le_refl _

@[simp] theorem lkSearchEvals_steps (w bs : List Bool) (v : tm.σ) (temp : Option Sym)
    (flag res : Bool) (r : R) (S : ∀ k, List (tm.Γ k)) (t : TripleSlot → List Sym)
    (inp : List Sym) (g : ∀ j : G, List (Γg j)) :
    (lkSearchEvals eIn eOut p₀ rest w bs v temp flag res r S t inp g).steps = searchSteps w bs :=
  rfl

end

/-- **The exhaustion route, exactly.**  When the address is at least the witness's length the
witness runs out first, and the count does not mention the address's value at all — only how much
of the witness was traversed and how wide the counter is. -/
theorem searchSteps_of_exhausted (w bs : List Bool) (h : w.length ≤ bitsValue bs) :
    searchSteps w bs = w.length * (4 * bs.length + 10) + bs.length + 4 := by
  have hm : advances w bs = w.length := by rw [advances_eq_min]; omega
  have hif : ¬ bitsValue bs < w.length := by omega
  simp only [searchSteps, loopSteps_eq, hm, ite_eq_right hif]
  ring

/-- **The selection route, exactly.**  When the address is inside the witness the counter runs out
first, so the number of advances is the address's value. -/
theorem searchSteps_of_selected (w bs : List Bool) (h : bitsValue bs < w.length) :
    searchSteps w bs = bitsValue bs * (4 * bs.length + 10) + 3 * bs.length + 8 := by
  have hm : advances w bs = bitsValue bs := by rw [advances_eq_min]; omega
  simp only [searchSteps, loopSteps_eq, hm, ite_eq_left h]
  ring

/-- **The whole search is bounded by witness length and counter width**, with no dependence on the
address's numeric value.

*At a fixed counter width*, an address far past the end of the witness costs exactly what one just
past it costs: the loop stops when the witness runs out, and the exhaustion count
`advances w bs * (4k + 10) + k + 4` does not mention the value.  Width is not free, though — a
one-bit witness against the one-cell counter `[true]` takes 19 steps, and against the seven-cell
encoding of 64 it takes 49.  Both exhaust; they differ in `k`, not in the address. -/
theorem lk_search_steps_le (w bs : List Bool) :
    searchSteps w bs ≤ w.length * (4 * bs.length + 10) + 3 * bs.length + 8 := by
  have hm : advances w bs ≤ w.length := advances_le_length w bs
  have h1 : advances w bs * (4 * bs.length + 9) ≤ w.length * (4 * bs.length + 9) :=
    Nat.mul_le_mul_right _ hm
  have h2 : w.length * (4 * bs.length + 10) = w.length * (4 * bs.length + 9) + w.length := by
    ring
  have h3 : (if bitsValue bs < w.length then 2 * bs.length + 6 else 2) ≤ 2 * bs.length + 6 := by
    split <;> omega
  simp only [searchSteps, loopSteps_eq]
  omega

end PCP.Machine
