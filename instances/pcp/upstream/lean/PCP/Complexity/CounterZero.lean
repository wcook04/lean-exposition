import PCP.Complexity.CallPrepare
import PCP.Complexity.BinaryCounter

/-!
# The counter's zero test, as a machine

The counter lives on the call's destination stack (where dispatch left the query numeral) and uses
the call scratch.  The caller payload is `Bool × Q`: the **helper flag** the scan accumulates, and
everything else the checker carries.  Making it concrete rather than an abstract setter/getter pair
is what lets "depth, selected result and unrelated payload fields are preserved" be read straight
off the statements — it is exactly `q` carried through untouched.

## Initialisation is explicit

`ztInit` is a **counted step** that sets the flag to `false` regardless of what it was.  Nothing
here assumes an incoming accumulator is already clear.

## Counting

One initialisation step, a forward scan of `bs.length + 1`, and a restoring scan of `bs.length + 1`:
`2 * bs.length + 3`, with both empty exits and the boundary selection inside that count.
-/

namespace PCP.Machine

open Turing Turing.TM2 Turing.TM2.Stmt StateTransition

section

variable (tm : FinTM2) (G : Type) [DecidableEq G] [Fintype G] (Γg : G → Type)
  (Q : Type) [Fintype Q]

/-- Does this popped symbol carry a set bit? -/
def symIsTrue : Option Sym → Bool
  | some (.bit b) => b
  | _ => false

/-- One counted step: clear the helper flag, whatever it was, and start scanning. -/
def ztInitStmt : PrepStmt tm G Γg (Bool × Q) :=
  load (fun p => (p.1, (none, (false, p.2.2.2)))) (goto (fun _ => .inr .ztScan))

/-- The forward scan: move each counter bit to scratch, remembering whether a set bit was seen. -/
def ztScanStmt : PrepStmt tm G Γg (Bool × Q) :=
  pop (.inr (.inl .dst)) (fun p o => (p.1, (o, p.2.2))) <|
    branch (fun p => p.2.1.isSome)
      (push (.inr (.inl .scratch)) (fun p => p.2.1.getD Sym.sep)
        (load (fun p => (p.1, (none, (p.2.2.1 || symIsTrue p.2.1, p.2.2.2))))
          (goto (fun _ => .inr .ztScan))))
      (load (fun p => (p.1, (none, p.2.2))) (goto (fun _ => .inr .ztRestore)))

/-- The restoring scan: move the bits back, restoring their order, then select the boundary from
the flag — which every pop and reset along the way preserves. -/
def ztRestoreStmt : PrepStmt tm G Γg (Bool × Q) :=
  pop (.inr (.inl .scratch)) (fun p o => (p.1, (o, p.2.2))) <|
    branch (fun p => p.2.1.isSome)
      (push (.inr (.inl .dst)) (fun p => p.2.1.getD Sym.sep)
        (load (fun p => (p.1, (none, p.2.2))) (goto (fun _ => .inr .ztRestore))))
      (load (fun p => (p.1, (none, p.2.2)))
        (branch (fun p => p.2.2.1) (goto (fun _ => .inr .ztPos)) (goto (fun _ => .inr .ztZero))))

/-- Route the three zero-test labels; everything else goes on. -/
def ztRoute (rest : CallLabel → PrepStmt tm G Γg (Bool × Q)) :
    CallLabel → PrepStmt tm G Γg (Bool × Q)
  | .ztInit => ztInitStmt tm G Γg Q
  | .ztScan => ztScanStmt tm G Γg Q
  | .ztRestore => ztRestoreStmt tm G Γg Q
  | l => rest l

/-- Does any symbol on this tape carry a set bit? -/
def symsAnyTrue (l : List Sym) : Bool := l.any (fun c => symIsTrue (some c))

@[simp] theorem symsAnyTrue_nil : symsAnyTrue [] = false := rfl

theorem symsAnyTrue_ofBits : ∀ bs : List Bool, symsAnyTrue (ofBits bs) = bs.any id
  | [] => rfl
  | b :: bs => by
      simp only [ofBits, List.map_cons, symsAnyTrue, List.any_cons]
      rw [show symIsTrue (some (Sym.bit b)) = b from by cases b <;> rfl]
      have := symsAnyTrue_ofBits bs
      simp only [symsAnyTrue, ofBits] at this
      rw [this]
      simp

theorem any_id_eq (bs : List Bool) : bs.any id = decide (bitsValue bs ≠ 0) := by
  rw [Bool.eq_iff_iff]
  simp only [List.any_eq_true, id_eq, decide_eq_true_iff, ne_eq, bitsValue_eq_zero_iff,
    not_forall]
  constructor
  · rintro ⟨b, hb, rfl⟩
    exact ⟨true, by simpa using hb⟩
  · rintro ⟨b, hb⟩
    obtain ⟨hmem, hne⟩ := by simpa using hb
    exact ⟨b, hmem, by cases b <;> simp_all⟩

variable {tm G Γg Q}

section Steps

variable (eIn : tm.Γ tm.k₀ ≃ Sym) (eOut : tm.Γ tm.k₁ ≃ Sym) (p₀ : Bool × Q)
  (rest : CallLabel → PrepStmt tm G Γg (Bool × Q))

/-- **Initialisation**, one counted step: the flag is cleared whatever it was, and `q` survives. -/
theorem zt_step_init (v : tm.σ) (temp : Option Sym) (seen : Bool) (q : Q) (dst scr : List Sym)
    (S : ∀ k, List (tm.Γ k)) (t : TripleSlot → List Sym) (inp : List Sym)
    (g : ∀ j : G, List (Γg j)) :
    (callTM tm (TripleSlot ⊕ G) (prepΓ G Γg) (Bool × Q) eIn eOut p₀
      (prepCont tm G Γg (Bool × Q) (ztRoute tm G Γg Q rest))).step
        (prepCfg eIn eOut p₀ (ztRoute tm G Γg Q rest)
          (some (.inr CallLabel.ztInit)) v temp (seen, q) S inp (dst) (scr) t g)
      = some (prepCfg eIn eOut p₀ (ztRoute tm G Γg Q rest)
          (some (.inr CallLabel.ztScan)) v none ((false, q)) S inp (dst) (scr)
          t g) := by
  change some (stepAux ((callTM tm (TripleSlot ⊕ G) (prepΓ G Γg) (Bool × Q) eIn eOut p₀
        (prepCont tm G Γg (Bool × Q) (ztRoute tm G Γg Q rest))).m
      (Sum.inr CallLabel.ztInit)) (v, (temp, (seen, q)))
      (embedStacks tm (CallSlot ⊕ (TripleSlot ⊕ G)) (callΓ (TripleSlot ⊕ G) (prepΓ G Γg)) S
        (callFrame (TripleSlot ⊕ G) (prepΓ G Γg) inp (dst) (scr)
          (prepFrame G Γg t g)))) = _
  simp only [callTM, parentTM, callProgram, prepCont, ztRoute, ztInitStmt, ztScanStmt,
    ztRestoreStmt, symIsTrue, Turing.TM2.stepAux, embedStacks_inr, callFrame, prepFrame]
  refine congrArg some (congrArg (fun T =>
    (⟨some (.inr CallLabel.ztScan), (v, (none, (false, q))), T⟩ : (callTM tm (TripleSlot ⊕ G)
        (prepΓ G Γg) (Bool × Q) eIn
        eOut p₀
      (prepCont tm G Γg (Bool × Q) (ztRoute tm G Γg Q rest))).Cfg)) ?_)
  funext i
  rcases i with k | cs | ts | j'
  · first | rfl | simp [Function.update, embedStacks, callFrame, prepFrame]
  · cases cs <;>
      first | rfl | simp [Function.update, embedStacks, callFrame, prepFrame]
  · first | rfl | simp [Function.update, embedStacks, callFrame, prepFrame]
  · first | rfl | simp [Function.update, embedStacks, callFrame, prepFrame]

/-- The scan moves one bit to scratch and ORs its value into the flag. -/
theorem zt_step_scan_cons (v : tm.σ) (temp : Option Sym) (seen : Bool) (q : Q) (c : Sym)
    (dst scr : List Sym)
    (S : ∀ k, List (tm.Γ k)) (t : TripleSlot → List Sym) (inp : List Sym)
    (g : ∀ j : G, List (Γg j)) :
    (callTM tm (TripleSlot ⊕ G) (prepΓ G Γg) (Bool × Q) eIn eOut p₀
      (prepCont tm G Γg (Bool × Q) (ztRoute tm G Γg Q rest))).step
        (prepCfg eIn eOut p₀ (ztRoute tm G Γg Q rest)
          (some (.inr CallLabel.ztScan)) v temp (seen, q) S inp (c :: dst) (scr) t g)
      = some (prepCfg eIn eOut p₀ (ztRoute tm G Γg Q rest)
          (some (.inr CallLabel.ztScan)) v none ((seen || symIsTrue (some c), q)) S inp (dst)
              (c :: scr)
          t g) := by
  change some (stepAux ((callTM tm (TripleSlot ⊕ G) (prepΓ G Γg) (Bool × Q) eIn eOut p₀
        (prepCont tm G Γg (Bool × Q) (ztRoute tm G Γg Q rest))).m
      (Sum.inr CallLabel.ztScan)) (v, (temp, (seen, q)))
      (embedStacks tm (CallSlot ⊕ (TripleSlot ⊕ G)) (callΓ (TripleSlot ⊕ G) (prepΓ G Γg)) S
        (callFrame (TripleSlot ⊕ G) (prepΓ G Γg) inp (c :: dst) (scr)
          (prepFrame G Γg t g)))) = _
  simp only [callTM, parentTM, callProgram, prepCont, ztRoute, ztInitStmt, ztScanStmt,
    ztRestoreStmt, symIsTrue, Turing.TM2.stepAux, embedStacks_inr, callFrame, prepFrame,
    List.head?_cons, List.tail_cons, Option.isSome_some, Bool.cond_true, Option.getD_some]
  refine congrArg some (congrArg (fun T =>
    (⟨some (.inr CallLabel.ztScan), (v, (none, (seen || symIsTrue (some c), q))), T⟩ :
        (callTM tm (TripleSlot ⊕ G) (prepΓ G Γg) (Bool × Q) eIn
        eOut p₀
      (prepCont tm G Γg (Bool × Q) (ztRoute tm G Γg Q rest))).Cfg)) ?_)
  funext i
  rcases i with k | cs | ts | j'
  · first | rfl | simp [Function.update, embedStacks, callFrame, prepFrame]
  · cases cs <;>
      first | rfl | simp [Function.update, embedStacks, callFrame, prepFrame]
  · first | rfl | simp [Function.update, embedStacks, callFrame, prepFrame]
  · first | rfl | simp [Function.update, embedStacks, callFrame, prepFrame]

/-- Its empty exit hands the accumulated flag to the restoring scan. -/
theorem zt_step_scan_nil (v : tm.σ) (temp : Option Sym) (seen : Bool) (q : Q) (scr : List Sym)
    (S : ∀ k, List (tm.Γ k)) (t : TripleSlot → List Sym) (inp : List Sym)
    (g : ∀ j : G, List (Γg j)) :
    (callTM tm (TripleSlot ⊕ G) (prepΓ G Γg) (Bool × Q) eIn eOut p₀
      (prepCont tm G Γg (Bool × Q) (ztRoute tm G Γg Q rest))).step
        (prepCfg eIn eOut p₀ (ztRoute tm G Γg Q rest)
          (some (.inr CallLabel.ztScan)) v temp (seen, q) S inp ([]) (scr) t g)
      = some (prepCfg eIn eOut p₀ (ztRoute tm G Γg Q rest)
          (some (.inr CallLabel.ztRestore)) v none ((seen, q)) S inp ([]) (scr)
          t g) := by
  change some (stepAux ((callTM tm (TripleSlot ⊕ G) (prepΓ G Γg) (Bool × Q) eIn eOut p₀
        (prepCont tm G Γg (Bool × Q) (ztRoute tm G Γg Q rest))).m
      (Sum.inr CallLabel.ztScan)) (v, (temp, (seen, q)))
      (embedStacks tm (CallSlot ⊕ (TripleSlot ⊕ G)) (callΓ (TripleSlot ⊕ G) (prepΓ G Γg)) S
        (callFrame (TripleSlot ⊕ G) (prepΓ G Γg) inp ([]) (scr)
          (prepFrame G Γg t g)))) = _
  simp only [callTM, parentTM, callProgram, prepCont, ztRoute, ztInitStmt, ztScanStmt,
    ztRestoreStmt, symIsTrue, Turing.TM2.stepAux, embedStacks_inr, callFrame, prepFrame,
    List.head?_nil, List.tail_nil, Option.isSome_none, Bool.cond_false]
  refine congrArg some (congrArg (fun T =>
    (⟨some (.inr CallLabel.ztRestore), (v, (none, (seen, q))), T⟩ : (callTM tm (TripleSlot ⊕ G)
        (prepΓ G Γg) (Bool × Q) eIn
        eOut p₀
      (prepCont tm G Γg (Bool × Q) (ztRoute tm G Γg Q rest))).Cfg)) ?_)
  funext i
  rcases i with k | cs | ts | j'
  · first | rfl | simp [Function.update, embedStacks, callFrame, prepFrame]
  · cases cs <;>
      first | rfl | simp [Function.update, embedStacks, callFrame, prepFrame]
  · first | rfl | simp [Function.update, embedStacks, callFrame, prepFrame]
  · first | rfl | simp [Function.update, embedStacks, callFrame, prepFrame]

/-- The restoring scan moves one bit back, preserving the flag. -/
theorem zt_step_restore_cons (v : tm.σ) (temp : Option Sym) (seen : Bool) (q : Q) (c : Sym)
    (dst scr : List Sym)
    (S : ∀ k, List (tm.Γ k)) (t : TripleSlot → List Sym) (inp : List Sym)
    (g : ∀ j : G, List (Γg j)) :
    (callTM tm (TripleSlot ⊕ G) (prepΓ G Γg) (Bool × Q) eIn eOut p₀
      (prepCont tm G Γg (Bool × Q) (ztRoute tm G Γg Q rest))).step
        (prepCfg eIn eOut p₀ (ztRoute tm G Γg Q rest)
          (some (.inr CallLabel.ztRestore)) v temp (seen, q) S inp (dst) (c :: scr) t g)
      = some (prepCfg eIn eOut p₀ (ztRoute tm G Γg Q rest)
          (some (.inr CallLabel.ztRestore)) v none ((seen, q)) S inp (c :: dst) (scr)
          t g) := by
  change some (stepAux ((callTM tm (TripleSlot ⊕ G) (prepΓ G Γg) (Bool × Q) eIn eOut p₀
        (prepCont tm G Γg (Bool × Q) (ztRoute tm G Γg Q rest))).m
      (Sum.inr CallLabel.ztRestore)) (v, (temp, (seen, q)))
      (embedStacks tm (CallSlot ⊕ (TripleSlot ⊕ G)) (callΓ (TripleSlot ⊕ G) (prepΓ G Γg)) S
        (callFrame (TripleSlot ⊕ G) (prepΓ G Γg) inp (dst) (c :: scr)
          (prepFrame G Γg t g)))) = _
  simp only [callTM, parentTM, callProgram, prepCont, ztRoute, ztInitStmt, ztScanStmt,
    ztRestoreStmt, symIsTrue, Turing.TM2.stepAux, embedStacks_inr, callFrame, prepFrame,
    List.head?_cons, List.tail_cons, Option.isSome_some, Bool.cond_true, Option.getD_some]
  refine congrArg some (congrArg (fun T =>
    (⟨some (.inr CallLabel.ztRestore), (v, (none, (seen, q))), T⟩ : (callTM tm (TripleSlot ⊕ G)
        (prepΓ G Γg) (Bool × Q) eIn
        eOut p₀
      (prepCont tm G Γg (Bool × Q) (ztRoute tm G Γg Q rest))).Cfg)) ?_)
  funext i
  rcases i with k | cs | ts | j'
  · first | rfl | simp [Function.update, embedStacks, callFrame, prepFrame]
  · cases cs <;>
      first | rfl | simp [Function.update, embedStacks, callFrame, prepFrame]
  · first | rfl | simp [Function.update, embedStacks, callFrame, prepFrame]
  · first | rfl | simp [Function.update, embedStacks, callFrame, prepFrame]

/-- Its empty exit selects the **nonzero** boundary when a set bit was seen… -/
theorem zt_step_restore_nil_pos (v : tm.σ) (temp : Option Sym) (q : Q) (dst : List Sym)
    (S : ∀ k, List (tm.Γ k)) (t : TripleSlot → List Sym) (inp : List Sym)
    (g : ∀ j : G, List (Γg j)) :
    (callTM tm (TripleSlot ⊕ G) (prepΓ G Γg) (Bool × Q) eIn eOut p₀
      (prepCont tm G Γg (Bool × Q) (ztRoute tm G Γg Q rest))).step
        (prepCfg eIn eOut p₀ (ztRoute tm G Γg Q rest)
          (some (.inr CallLabel.ztRestore)) v temp (true, q) S inp dst [] t g)
      = some (prepCfg eIn eOut p₀ (ztRoute tm G Γg Q rest)
          (some (.inr CallLabel.ztPos)) v none (true, q) S inp dst [] t g) := by
  change some (stepAux ((callTM tm (TripleSlot ⊕ G) (prepΓ G Γg) (Bool × Q) eIn eOut p₀
        (prepCont tm G Γg (Bool × Q) (ztRoute tm G Γg Q rest))).m
      (Sum.inr CallLabel.ztRestore)) (v, (temp, (true, q)))
      (embedStacks tm (CallSlot ⊕ (TripleSlot ⊕ G)) (callΓ (TripleSlot ⊕ G) (prepΓ G Γg)) S
        (callFrame (TripleSlot ⊕ G) (prepΓ G Γg) inp dst [] (prepFrame G Γg t g)))) = _
  simp only [callTM, parentTM, callProgram, prepCont, ztRoute, ztRestoreStmt,
    Turing.TM2.stepAux, embedStacks_inr, callFrame, prepFrame, List.head?_nil, List.tail_nil,
    Option.isSome_none, Bool.cond_true]
  refine congrArg some (congrArg (fun T =>
    (⟨some (.inr CallLabel.ztPos), (v, (none, (true, q))), T⟩ : (callTM tm (TripleSlot ⊕ G)
        (prepΓ G Γg) (Bool × Q) eIn
        eOut p₀
      (prepCont tm G Γg (Bool × Q) (ztRoute tm G Γg Q rest))).Cfg)) ?_)
  funext i
  rcases i with k | cs | ts | j'
  · first | rfl | simp [Function.update, embedStacks, callFrame, prepFrame]
  · cases cs <;>
      first | rfl | simp [Function.update, embedStacks, callFrame, prepFrame]
  · first | rfl | simp [Function.update, embedStacks, callFrame, prepFrame]
  · first | rfl | simp [Function.update, embedStacks, callFrame, prepFrame]

/-- …and the **zero** boundary otherwise. -/
theorem zt_step_restore_nil_zero (v : tm.σ) (temp : Option Sym) (q : Q) (dst : List Sym)
    (S : ∀ k, List (tm.Γ k)) (t : TripleSlot → List Sym) (inp : List Sym)
    (g : ∀ j : G, List (Γg j)) :
    (callTM tm (TripleSlot ⊕ G) (prepΓ G Γg) (Bool × Q) eIn eOut p₀
      (prepCont tm G Γg (Bool × Q) (ztRoute tm G Γg Q rest))).step
        (prepCfg eIn eOut p₀ (ztRoute tm G Γg Q rest)
          (some (.inr CallLabel.ztRestore)) v temp (false, q) S inp dst [] t g)
      = some (prepCfg eIn eOut p₀ (ztRoute tm G Γg Q rest)
          (some (.inr CallLabel.ztZero)) v none (false, q) S inp dst [] t g) := by
  change some (stepAux ((callTM tm (TripleSlot ⊕ G) (prepΓ G Γg) (Bool × Q) eIn eOut p₀
        (prepCont tm G Γg (Bool × Q) (ztRoute tm G Γg Q rest))).m
      (Sum.inr CallLabel.ztRestore)) (v, (temp, (false, q)))
      (embedStacks tm (CallSlot ⊕ (TripleSlot ⊕ G)) (callΓ (TripleSlot ⊕ G) (prepΓ G Γg)) S
        (callFrame (TripleSlot ⊕ G) (prepΓ G Γg) inp dst [] (prepFrame G Γg t g)))) = _
  simp only [callTM, parentTM, callProgram, prepCont, ztRoute, ztRestoreStmt,
    Turing.TM2.stepAux, embedStacks_inr, callFrame, prepFrame, List.head?_nil, List.tail_nil,
    Option.isSome_none, Bool.cond_false]
  refine congrArg some (congrArg (fun T =>
    (⟨some (.inr CallLabel.ztZero), (v, (none, (false, q))), T⟩ : (callTM tm (TripleSlot ⊕ G)
        (prepΓ G Γg) (Bool × Q) eIn
        eOut p₀
      (prepCont tm G Γg (Bool × Q) (ztRoute tm G Γg Q rest))).Cfg)) ?_)
  funext i
  rcases i with k | cs | ts | j'
  · first | rfl | simp [Function.update, embedStacks, callFrame, prepFrame]
  · cases cs <;>
      first | rfl | simp [Function.update, embedStacks, callFrame, prepFrame]
  · first | rfl | simp [Function.update, embedStacks, callFrame, prepFrame]
  · first | rfl | simp [Function.update, embedStacks, callFrame, prepFrame]

/-! ### The two scans -/

theorem zt_scan : ∀ (bs : List Sym) (v : tm.σ) (temp : Option Sym) (seen : Bool) (q : Q)
    (scr : List Sym) (S : ∀ k, List (tm.Γ k)) (t : TripleSlot → List Sym) (inp : List Sym)
    (g : ∀ j : G, List (Γg j)),
    (flip Bind.bind (callTM tm (TripleSlot ⊕ G) (prepΓ G Γg) (Bool × Q) eIn eOut p₀
        (prepCont tm G Γg (Bool × Q) (ztRoute tm G Γg Q rest))).step)^[bs.length + 1]
        (some (prepCfg eIn eOut p₀ (ztRoute tm G Γg Q rest) (some (.inr .ztScan)) v temp
            (seen, q) S inp bs scr t g))
      = some (prepCfg eIn eOut p₀ (ztRoute tm G Γg Q rest) (some (.inr .ztRestore)) v none
          (seen || symsAnyTrue bs, q) S inp []
          (bs.reverse ++ scr) t g)
  | [], v, temp, seen, q, scr, S, t, inp, g => by
      change (callTM tm (TripleSlot ⊕ G) (prepΓ G Γg) (Bool × Q) eIn eOut p₀
        (prepCont tm G Γg (Bool × Q) (ztRoute tm G Γg Q rest))).step
        (prepCfg eIn eOut p₀ (ztRoute tm G Γg Q rest) (some (.inr .ztScan)) v temp (seen, q) S
            inp [] scr t g) = _
      rw [zt_step_scan_nil eIn eOut p₀ rest v temp seen q scr S t inp g]
      simp [symsAnyTrue]
  | c :: bs, v, temp, seen, q, scr, S, t, inp, g => by
      rw [List.length_cons, Function.iterate_succ_apply]
      change (flip Bind.bind (callTM tm (TripleSlot ⊕ G) (prepΓ G Γg) (Bool × Q) eIn eOut p₀
        (prepCont tm G Γg (Bool × Q) (ztRoute tm G Γg Q rest))).step)^[bs.length + 1]
        ((callTM tm (TripleSlot ⊕ G) (prepΓ G Γg) (Bool × Q) eIn eOut p₀
        (prepCont tm G Γg (Bool × Q) (ztRoute tm G Γg Q rest))).step
          (prepCfg eIn eOut p₀ (ztRoute tm G Γg Q rest) (some (.inr .ztScan)) v temp (seen, q) S
              inp (c :: bs) scr t g)) = _
      rw [zt_step_scan_cons eIn eOut p₀ rest v temp seen q c bs scr S t inp g,
        zt_scan bs v none (seen || symIsTrue (some c)) q (c :: scr) S t inp g]
      simp [symsAnyTrue, Bool.or_assoc]

theorem zt_restore : ∀ (rs : List Sym) (v : tm.σ) (temp : Option Sym) (seen : Bool) (q : Q)
    (dst : List Sym) (S : ∀ k, List (tm.Γ k)) (t : TripleSlot → List Sym) (inp : List Sym)
    (g : ∀ j : G, List (Γg j)),
    (flip Bind.bind (callTM tm (TripleSlot ⊕ G) (prepΓ G Γg) (Bool × Q) eIn eOut p₀
        (prepCont tm G Γg (Bool × Q) (ztRoute tm G Γg Q rest))).step)^[rs.length + 1]
        (some (prepCfg eIn eOut p₀ (ztRoute tm G Γg Q rest) (some (.inr .ztRestore)) v temp
            (seen, q) S inp dst rs t g))
      = some (prepCfg eIn eOut p₀ (ztRoute tm G Γg Q rest) (some (.inr
          (if seen then CallLabel.ztPos else CallLabel.ztZero))) v none
          (seen, q) S inp (rs.reverse ++ dst) [] t g)
  | [], v, temp, seen, q, dst, S, t, inp, g => by
      change (callTM tm (TripleSlot ⊕ G) (prepΓ G Γg) (Bool × Q) eIn eOut p₀
        (prepCont tm G Γg (Bool × Q) (ztRoute tm G Γg Q rest))).step
        (prepCfg eIn eOut p₀ (ztRoute tm G Γg Q rest) (some (.inr .ztRestore)) v temp (seen, q)
            S inp dst [] t g) = _
      cases seen
      · rw [zt_step_restore_nil_zero eIn eOut p₀ rest v temp q dst S t inp g]; simp
      · rw [zt_step_restore_nil_pos eIn eOut p₀ rest v temp q dst S t inp g]; simp
  | c :: rs, v, temp, seen, q, dst, S, t, inp, g => by
      rw [List.length_cons, Function.iterate_succ_apply]
      change (flip Bind.bind (callTM tm (TripleSlot ⊕ G) (prepΓ G Γg) (Bool × Q) eIn eOut p₀
        (prepCont tm G Γg (Bool × Q) (ztRoute tm G Γg Q rest))).step)^[rs.length + 1]
        ((callTM tm (TripleSlot ⊕ G) (prepΓ G Γg) (Bool × Q) eIn eOut p₀
        (prepCont tm G Γg (Bool × Q) (ztRoute tm G Γg Q rest))).step
          (prepCfg eIn eOut p₀ (ztRoute tm G Γg Q rest) (some (.inr .ztRestore)) v temp
              (seen, q) S inp dst (c :: rs) t g)) = _
      rw [zt_step_restore_cons eIn eOut p₀ rest v temp seen q c dst rs S t inp g,
        zt_restore rs v none seen q (c :: dst) S t inp g]
      simp

/-! ### The complete zero test -/

/-- **The zero test.**  From `ztInit` with the counter holding `ofBits bs` and scratch empty:
`2 * bs.length + 3` steps restore the counter **in its original order**, leave scratch empty, and
select `ztZero` exactly when the counter's value is zero — with every callee stack, source tape,
input, unrelated frame and the payload component `q` untouched. -/
theorem zt_trace (bs : List Bool) (v : tm.σ) (temp : Option Sym) (seen : Bool) (q : Q)
    (S : ∀ k, List (tm.Γ k)) (t : TripleSlot → List Sym) (inp : List Sym)
    (g : ∀ j : G, List (Γg j)) :
    (flip Bind.bind (callTM tm (TripleSlot ⊕ G) (prepΓ G Γg) (Bool × Q) eIn eOut p₀
        (prepCont tm G Γg (Bool × Q) (ztRoute tm G Γg Q rest))).step)^[2 * bs.length + 3]
        (some (prepCfg eIn eOut p₀ (ztRoute tm G Γg Q rest) (some (.inr .ztInit)) v temp
            (seen, q) S inp (ofBits bs) [] t g))
      = some (prepCfg eIn eOut p₀ (ztRoute tm G Γg Q rest) (some (.inr
          (if bitsValue bs = 0 then CallLabel.ztZero else CallLabel.ztPos)))
          v none (decide (bitsValue bs ≠ 0), q) S inp (ofBits bs) [] t g) := by
  have hsplit : 2 * bs.length + 3
      = ((ofBits bs).reverse.length + 1) + (((ofBits bs).length + 1) + 1) := by
    simp only [List.length_reverse, length_ofBits]; omega
  rw [hsplit, Function.iterate_add_apply, Function.iterate_add_apply, Function.iterate_one]
  change (flip Bind.bind (callTM tm (TripleSlot ⊕ G) (prepΓ G Γg) (Bool × Q) eIn eOut p₀
        (prepCont tm G Γg (Bool × Q)
            (ztRoute tm G Γg Q rest))).step)^[(ofBits bs).reverse.length + 1]
    ((flip Bind.bind (callTM tm (TripleSlot ⊕ G) (prepΓ G Γg) (Bool × Q) eIn eOut p₀
        (prepCont tm G Γg (Bool × Q) (ztRoute tm G Γg Q rest))).step)^[(ofBits bs).length + 1]
      ((callTM tm (TripleSlot ⊕ G) (prepΓ G Γg) (Bool × Q) eIn eOut p₀
        (prepCont tm G Γg (Bool × Q) (ztRoute tm G Γg Q rest))).step
        (prepCfg eIn eOut p₀ (ztRoute tm G Γg Q rest) (some (.inr .ztInit)) v temp (seen, q) S
            inp (ofBits bs) [] t g))) = _
  rw [zt_step_init eIn eOut p₀ rest v temp seen q (ofBits bs) [] S t inp g,
    zt_scan eIn eOut p₀ rest (ofBits bs) v none false q [] S t inp g, List.append_nil,
    zt_restore eIn eOut p₀ rest (ofBits bs).reverse v none (false || symsAnyTrue (ofBits bs)) q []
      S t inp g]
  simp [symsAnyTrue_ofBits, any_id_eq]

/-- The certificate, with its count written out. -/
def ztEvals (bs : List Bool) (v : tm.σ) (temp : Option Sym) (seen : Bool) (q : Q)
    (S : ∀ k, List (tm.Γ k)) (t : TripleSlot → List Sym) (inp : List Sym)
    (g : ∀ j : G, List (Γg j)) :
    EvalsToInTime (callTM tm (TripleSlot ⊕ G) (prepΓ G Γg) (Bool × Q) eIn eOut p₀
      (prepCont tm G Γg (Bool × Q) (ztRoute tm G Γg Q rest))).step
      (prepCfg eIn eOut p₀ (ztRoute tm G Γg Q rest) (some (.inr .ztInit)) v temp (seen, q) S inp
          (ofBits bs) [] t g)
      (some (prepCfg eIn eOut p₀ (ztRoute tm G Γg Q rest) (some (.inr
          (if bitsValue bs = 0 then CallLabel.ztZero else CallLabel.ztPos)))
        v none (decide (bitsValue bs ≠ 0), q) S inp (ofBits bs) [] t g))
      (2 * bs.length + 3) where
  steps := 2 * bs.length + 3
  evals_in_steps := zt_trace eIn eOut p₀ rest bs v temp seen q S t inp g
  steps_le_m := le_refl _

@[simp] theorem ztEvals_steps (bs : List Bool) (v : tm.σ) (temp : Option Sym) (seen : Bool) (q : Q)
    (S : ∀ k, List (tm.Γ k)) (t : TripleSlot → List Sym) (inp : List Sym)
    (g : ∀ j : G, List (Γg j)) :
    (ztEvals eIn eOut p₀ rest bs v temp seen q S t inp g).steps = 2 * bs.length + 3 := rfl

end Steps

end

end PCP.Machine
