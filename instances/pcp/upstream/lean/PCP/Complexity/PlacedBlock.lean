import PCP.Complexity.RelocatedBlock
import PCP.Complexity.StaticTapeLayout

/-!
# Executable placement of framed blocks on shared tapes

The code uses only the forward, explicitly assigned tape indices. The inverse of
that fixed layout occurs only in the correctness proof. A local trace that
preserves its complement therefore gives a trace on the original global tape
functions, with exactly the same number of transitions.
-/

namespace PCP.Machine.FiniteBlocks

open Turing Turing.TM2 Turing.TM2.Stmt StateTransition

variable {J K : Type} [DecidableEq J] [Fintype J] [DecidableEq K] [Fintype K]

/-- Rename uniform-symbol tape instructions using an ordinary function. -/
def renameStmt {L V : Type} (positions : J → K) :
    Stmt (fun _ : J => Sym) L V → Stmt (fun _ : K => Sym) L V
  | .push j f q => .push (positions j) f (renameStmt positions q)
  | .peek j f q => .peek (positions j) f (renameStmt positions q)
  | .pop j f q => .pop (positions j) f (renameStmt positions q)
  | .load f q => .load f (renameStmt positions q)
  | .branch f q r => .branch f (renameStmt positions q) (renameStmt positions r)
  | .goto f => .goto f
  | .halt => .halt

/-- The machine construction never evaluates an inverse layout function. -/
def Block.rename (b : Block J (fun _ => Sym)) (positions : J → K) :
    Block K (fun _ => Sym) where
  Label := b.Label
  Control := b.Control
  entry := b.entry
  initial := b.initial
  code l := renameStmt positions (b.code l)

omit [DecidableEq K] [Fintype K] in
/-- A uniform-symbol local block can be viewed at any chosen external ports. -/
lemma renameStmt_eq_relocate (b : Block J (fun _ => Sym)) (localInput localOutput : J)
    (positions : J ≃ K) (q : Stmt (fun _ : J => Sym) b.Label b.Control) :
    renameStmt positions q =
      relocateStmt (b.machine localInput localOutput) positions (fun _ => Equiv.refl Sym) q := by
  induction q with
  | push j f q ih => exact congrArg (Stmt.push (positions j) f) ih
  | peek j f q ih =>
      simp only [renameStmt, relocateStmt]
      have hf : (fun v o => f v (o.map (Equiv.refl Sym).symm)) = f := by
        funext v o; cases o <;> rfl
      rw [hf, ih]
  | pop j f q ih =>
      simp only [renameStmt, relocateStmt]
      have hf : (fun v o => f v (o.map (Equiv.refl Sym).symm)) = f := by
        funext v o; cases o <;> rfl
      rw [hf, ih]
  | load f q ih => exact congrArg (Stmt.load f) ih
  | branch f q r iq ir => simp only [renameStmt, relocateStmt, iq, ir]
  | goto f => rfl
  | halt => rfl

omit [DecidableEq K] [Fintype K] in
/-- Renaming along a bijection is precisely the verified machine relocation. -/
theorem rename_eq_relocated (b : Block J (fun _ => Sym)) (localInput localOutput : J)
    (positions : J ≃ K) :
    b.rename positions = relocatedBlock (b.machine localInput localOutput) positions
      (fun _ => Equiv.refl Sym) := by
  unfold Block.rename relocatedBlock
  congr 1
  funext l
  exact renameStmt_eq_relocate b localInput localOutput positions (b.code l)

omit [DecidableEq K] [Fintype K] in
/-- Pulling a global tape assignment back along the static layout loses no contents. -/
lemma relocatedStacks_pullback (b : Block J (fun _ => Sym)) (localInput localOutput : J)
    (positions : J ≃ K) (S : K → List Sym) :
    relocatedStacks (b.machine localInput localOutput) positions (fun _ => Equiv.refl Sym)
      (fun j => S (positions j)) = S := by
  funext k
  simp only [relocatedStacks, Equiv.apply_symm_apply]
  change List.map id (S k) = S k
  exact List.map_id (S k)

/-- Exact local traces transfer to the original global tape functions. -/
theorem rename_trace (b : Block J (fun _ => Sym)) (localInput localOutput : J)
    (positions : J ≃ K) (input output : K) (S T : K → List Sym) (v : b.Control)
    (n : ℕ)
    (h : (flip Bind.bind (b.machine localInput localOutput).step)^[n]
      (some ⟨some b.entry, b.initial, fun j => S (positions j)⟩) =
      some ⟨none, v, fun j => T (positions j)⟩) :
    (flip Bind.bind ((b.rename positions).machine input output).step)^[n]
      (some ⟨some b.entry, b.initial, S⟩) = some ⟨none, v, T⟩ := by
  have ht := iterate_relocatedBlock (b.machine localInput localOutput) positions
    (fun _ => Equiv.refl Sym) input output n h
  have hs (l : Option b.Label) (v : b.Control) (U : K → List Sym) :
      relocateCfg (b.machine localInput localOutput) positions (fun _ => Equiv.refl Sym)
        ⟨l, v, fun j => U (positions j)⟩ = ⟨l, v, U⟩ := by
    dsimp only [relocateCfg]
    rw [relocatedStacks_pullback]
  simp only [hs] at ht
  have hstep : ((b.rename positions).machine input output).step =
      ((relocatedBlock (b.machine localInput localOutput) positions
        (fun _ => Equiv.refl Sym)).machine input output).step := by
    change TM2.step _ = TM2.step _
    congr 1
    funext l
    exact renameStmt_eq_relocate b localInput localOutput positions (b.code l)
  rw [hstep]
  exact ht

end PCP.Machine.FiniteBlocks

namespace PCP.Machine.StaticTapeLayout

open Turing Turing.TM2 StateTransition FiniteBlocks

variable {W K : Type} [DecidableEq W] [Fintype W] [DecidableEq K] [Fintype K]
  (work : W → K)

/-- Place the assigned work tapes and every untouched caller tape by forward indices. -/
def place (b : Block (W ⊕ Unused work) (fun _ => Sym)) : Block K (fun _ => Sym) :=
  b.rename (position work)

/-- Local framed tape contents, with the global caller frame retained literally. -/
def localStacks (xs : W → List Sym) (S : K → List Sym) : W ⊕ Unused work → List Sym
  | .inl w => xs w
  | .inr k => S k.val

omit [DecidableEq W] [Fintype W] [DecidableEq K] [Fintype K] in
/-- Agreement at the work indices identifies local and global representations. -/
theorem localStacks_eq_pullback (S : K → List Sym) (xs : W → List Sym)
    (h : ∀ w, S (work w) = xs w) :
    localStacks work xs S = fun j => S (position work j) := by
  funext j
  rcases j with w | k
  · exact (h w).symm
  · rfl

/-- A framed operation may change exactly its assigned work tapes. -/
theorem place_trace (hinj : Function.Injective work)
    (b : Block (W ⊕ Unused work) (fun _ => Sym)) (localInput localOutput : W ⊕ Unused work)
    (input output : K) (S T : K → List Sym) (xs ys : W → List Sym) (v : b.Control)
    (n : ℕ) (hx : ∀ w, S (work w) = xs w) (hy : ∀ w, T (work w) = ys w)
    (hframe : ∀ k : Unused work, T k.val = S k.val)
    (h : (flip Bind.bind (b.machine localInput localOutput).step)^[n]
      (some ⟨some b.entry, b.initial, localStacks work xs S⟩) =
      some ⟨none, v, localStacks work ys S⟩) :
    (flip Bind.bind ((place work b).machine input output).step)^[n]
      (some ⟨some b.entry, b.initial, S⟩) = some ⟨none, v, T⟩ := by
  have hy' : localStacks work ys S = fun j => T (position work j) := by
    funext j
    rcases j with w | k
    · exact (hy w).symm
    · exact (hframe k).symm
  rw [localStacks_eq_pullback work S xs hx, hy'] at h
  exact rename_trace b localInput localOutput (equiv work hinj) input output S T v n h

end PCP.Machine.StaticTapeLayout
