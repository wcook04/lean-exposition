import PCP.Complexity.ListPrimitiveBlocks
import PCP.Complexity.FiniteTransducer

/-!
# Finite-state transducers on arbitrary shared tapes

The streaming and order-restoring passes retain their exact finite-machine trace
under a fixed placement. Unassigned tapes and local control are restored, so the
transducers can be composed with the compiler's other instruction blocks.
-/

namespace PCP.Machine.TransducerBlocks

open Turing Turing.TM2 StateTransition PCP.Lang FiniteBlocks ListPrimitiveBlocks

variable (spec : TransducerSpec) (F : Type) [DecidableEq F] [Fintype F]

def block : Block (MoveSlot ⊕ F) (fun _ => Sym) :=
  relocatedBlock (transducerTM spec F (fun _ => Sym))
    (Equiv.refl (MoveSlot ⊕ F)) (symbols F)

lemma cfg (l : Option MovePhase) (v : spec.State × Option Sym × Bool)
    (src scratch dst : List Sym) (S : F → List Sym) :
    relocateCfg (transducerTM spec F (fun _ => Sym)) (Equiv.refl (MoveSlot ⊕ F)) (symbols F)
      (transducerCfg spec F (fun _ => Sym) l v src scratch dst S) =
      ⟨l, v, tapes F src scratch dst S⟩ := by
  dsimp only [relocateCfg, transducerCfg]
  congr 1
  funext k
  rcases k with (_ | _ | _) | k <;> change List.map id _ = _
  all_goals exact List.map_id _

variable {F}

theorem trace (input output : MoveSlot ⊕ F) (xs : List Sym) (S : F → List Sym) :
    (flip Bind.bind ((block spec F).machine input output).step)^[
        xs.length + (spec.output spec.init xs).length + 2]
      (some ⟨some (block spec F).entry, (block spec F).initial, tapes F xs [] [] S⟩) =
      some ⟨none, (block spec F).initial, tapes F [] [] (spec.output spec.init xs) S⟩ := by
  have h := iterate_relocatedBlock (transducerTM spec F (fun _ => Sym))
    (Equiv.refl (MoveSlot ⊕ F)) (symbols F) input output _ (transducer_trace xs S)
  simp only [cfg] at h
  dsimp only [FinTM2.Cfg, block, Block.machine, relocatedBlock, transducerTM] at h ⊢
  exact h

variable {K : Type} [DecidableEq K] [Fintype K]

def placed (work : MoveSlot → K) : Block K (fun _ => Sym) :=
  StaticTapeLayout.place work (block spec (StaticTapeLayout.Unused work))

omit [DecidableEq K] [Fintype K] in
private theorem tapes_eq_local (work : MoveSlot → K) (a b c : List Sym) (S : K → List Sym) :
    tapes (StaticTapeLayout.Unused work) a b c (fun k => S k.val) =
      StaticTapeLayout.localStacks work (workTapes a b c) S := by
  funext k
  rcases k with (_ | _ | _) | k <;> rfl

/-- The output stream is materialized in its original order within a linear step bound. -/
theorem executes (work : MoveSlot → K) (hinj : Function.Injective work)
    (input output : K) (xs : List Sym) (S T : K → List Sym)
    (hx : ∀ w, S (work w) = workTapes xs [] [] w)
    (hy : ∀ w, T (work w) = workTapes [] [] (spec.output spec.init xs) w)
    (hframe : ∀ k : StaticTapeLayout.Unused work, T k.val = S k.val) :
    (placed spec work).Executes input output S T (2 * xs.length + 2) := by
  have h := trace spec (.inl .src) (.inl .dst) xs
    (fun k : StaticTapeLayout.Unused work => S k.val)
  simp only [tapes_eq_local] at h
  refine ⟨xs.length + (spec.output spec.init xs).length + 2,
    by have := spec.output_length_le xs spec.init; omega, ?_⟩
  exact StaticTapeLayout.place_trace work hinj _ (.inl .src) (.inl .dst)
    input output S T (workTapes xs [] [])
    (workTapes [] [] (spec.output spec.init xs)) _ _ hx hy hframe h

end PCP.Machine.TransducerBlocks
