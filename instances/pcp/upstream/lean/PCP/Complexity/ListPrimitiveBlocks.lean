import PCP.Complexity.PlacedBlock
import PCP.Complexity.BlockExecution
import PCP.Complexity.LangListReverseMachine
import PCP.Complexity.LangListLengthMachine

/-!
# Uniform, placeable list scan blocks

The checked reversal and length machines are repackaged on the compiler's uniform
symbol alphabet. Placement changes only fixed tape indices. Exact local traces
transfer to arbitrary shared storage, preserving every unassigned tape.
-/

namespace PCP.Machine.ListPrimitiveBlocks

open Turing Turing.TM2 StateTransition PCP.Lang FiniteBlocks

variable (F : Type) [DecidableEq F] [Fintype F]

def symbols : ∀ k : MoveSlot ⊕ F, LangListReverse.Alphabet F (fun _ => Sym) k ≃ Sym
  | .inl _ => Equiv.refl Sym
  | .inr _ => Equiv.refl Sym

def tapes (src scratch dst : List Sym) (S : F → List Sym) : MoveSlot ⊕ F → List Sym
  | .inl .src => src
  | .inl .scratch => scratch
  | .inl .dst => dst
  | .inr k => S k

def reverse : Block (MoveSlot ⊕ F) (fun _ => Sym) :=
  relocatedBlock (LangListReverse.machine F (fun _ => Sym))
    (Equiv.refl (MoveSlot ⊕ F)) (symbols F)

def length : Block (MoveSlot ⊕ F) (fun _ => Sym) :=
  relocatedBlock (LangListLength.machine F (fun _ => Sym))
    (Equiv.refl (MoveSlot ⊕ F)) (symbols F)

lemma reverse_cfg (l : Option MovePhase) (src scratch dst : List Sym) (S : F → List Sym) :
    relocateCfg (LangListReverse.machine F (fun _ => Sym)) (Equiv.refl (MoveSlot ⊕ F)) (symbols F)
      (LangListReverse.cfg F (fun _ => Sym) l src scratch dst S) =
      ⟨l, none, tapes F src scratch dst S⟩ := by
  dsimp only [relocateCfg, LangListReverse.cfg]
  congr 1
  funext k
  rcases k with (_ | _ | _) | k <;> change List.map id _ = _
  all_goals exact List.map_id _

lemma length_cfg (l : Option (Fin 3)) (v : Option Sym) (src scratch dst : List Sym)
    (S : F → List Sym) :
    relocateCfg (LangListLength.machine F (fun _ => Sym)) (Equiv.refl (MoveSlot ⊕ F)) (symbols F)
      (LangListLength.cfg F (fun _ => Sym) l v src scratch dst S) =
      ⟨l, v, tapes F src scratch dst S⟩ := by
  dsimp only [relocateCfg, LangListLength.cfg]
  congr 1
  funext k
  rcases k with (_ | _ | _) | k <;> change List.map id _ = _
  all_goals exact List.map_id _

variable {F}

theorem reverse_trace (input output : MoveSlot ⊕ F) (xs : List ℕ) (ys : List Sym)
    (S : F → List Sym) :
    (flip Bind.bind ((reverse F).machine input output).step)^[2 * listSize xs + 1]
      (some ⟨some (reverse F).entry, (reverse F).initial, tapes F (encodeNats xs) [] ys S⟩) =
      some ⟨none, (reverse F).initial, tapes F [] [] (encodeNats xs.reverse ++ ys) S⟩ := by
  have h := iterate_relocatedBlock (LangListReverse.machine F (fun _ => Sym))
    (Equiv.refl (MoveSlot ⊕ F)) (symbols F) input output _ (LangListReverse.trace xs ys S)
  simp only [reverse_cfg, listTape_length] at h
  exact h

theorem length_trace (input output : MoveSlot ⊕ F) (xs : List ℕ) (S : F → List Sym) :
    (flip Bind.bind ((length F).machine input output).step)^[LangListLength.runtime xs 0]
      (some ⟨some (length F).entry, (length F).initial, tapes F (encodeNats xs) [] [] S⟩) =
      some ⟨none, (length F).initial, tapes F [] [] (natTape xs.length) S⟩ := by
  have h := iterate_relocatedBlock (LangListLength.machine F (fun _ => Sym))
    (Equiv.refl (MoveSlot ⊕ F)) (symbols F) input output _ (LangListLength.trace xs 0 none S)
  simp only [length_cfg, Nat.zero_add] at h
  exact h

def workTapes (src scratch dst : List Sym) : MoveSlot → List Sym
  | .src => src
  | .scratch => scratch
  | .dst => dst

variable {K : Type} [DecidableEq K] [Fintype K]

/-- All assigned work tapes are explicit compiler data. -/
def placedReverse (work : MoveSlot → K) : Block K (fun _ => Sym) :=
  StaticTapeLayout.place work (reverse (StaticTapeLayout.Unused work))

def placedLength (work : MoveSlot → K) : Block K (fun _ => Sym) :=
  StaticTapeLayout.place work (length (StaticTapeLayout.Unused work))

omit [DecidableEq K] [Fintype K] in
private theorem tapes_eq_local (work : MoveSlot → K) (a b c : List Sym) (S : K → List Sym) :
    tapes (StaticTapeLayout.Unused work) a b c (fun k => S k.val) =
      StaticTapeLayout.localStacks work (workTapes a b c) S := by
  funext k
  rcases k with (_ | _ | _) | k <;> rfl

/-- Global reversal consumes the source and prepends the reversed list to the destination. -/
theorem reverse_executes (work : MoveSlot → K) (hinj : Function.Injective work)
    (input output : K) (xs : List ℕ) (ys : List Sym) (S T : K → List Sym)
    (hx : ∀ w, S (work w) = workTapes (encodeNats xs) [] ys w)
    (hy : ∀ w, T (work w) = workTapes [] [] (encodeNats xs.reverse ++ ys) w)
    (hframe : ∀ k : StaticTapeLayout.Unused work, T k.val = S k.val) :
    (placedReverse work).Executes input output S T (2 * listSize xs + 1) := by
  have h := reverse_trace (.inl .src) (.inl .dst) xs ys
    (fun k : StaticTapeLayout.Unused work => S k.val)
  simp only [tapes_eq_local] at h
  exact ⟨_, le_rfl, StaticTapeLayout.place_trace work hinj _ (.inl .src) (.inl .dst)
    input output S T (workTapes (encodeNats xs) [] ys)
    (workTapes [] [] (encodeNats xs.reverse ++ ys)) _ _ hx hy hframe h⟩

/-- Global length counting returns a canonical binary numeral and clears its input and scratch. -/
theorem length_executes (work : MoveSlot → K) (hinj : Function.Injective work)
    (input output : K) (xs : List ℕ) (S T : K → List Sym)
    (hx : ∀ w, S (work w) = workTapes (encodeNats xs) [] [] w)
    (hy : ∀ w, T (work w) = workTapes [] [] (natTape xs.length) w)
    (hframe : ∀ k : StaticTapeLayout.Unused work, T k.val = S k.val) :
    (placedLength work).Executes input output S T ((2 * listSize xs + 4) * listSize xs + 1) := by
  have h := length_trace (.inl .src) (.inl .dst) xs
    (fun k : StaticTapeLayout.Unused work => S k.val)
  simp only [tapes_eq_local] at h
  refine ⟨_, (LangListLength.evals xs
    (fun k : StaticTapeLayout.Unused work => S k.val)).steps_le_m, ?_⟩
  exact StaticTapeLayout.place_trace work hinj _ (.inl .src) (.inl .dst)
    input output S T (workTapes (encodeNats xs) [] [])
    (workTapes [] [] (natTape xs.length)) _ _ hx hy hframe h

end PCP.Machine.ListPrimitiveBlocks
