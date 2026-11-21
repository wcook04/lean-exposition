import PCP.Complexity.PlacedBlock
import PCP.Complexity.BinaryAdditionMachine
import PCP.Complexity.BinaryComparisonMachine
import PCP.Complexity.BinarySubtractionMachine

/-!
# Binary arithmetic blocks on a uniform compiler alphabet

The synchronous arithmetic machines are repackaged as reset blocks whose caller
frame uses the same materialized symbol alphabet. Every trace exposes the two
operands, scratch, result, and untouched frame. These blocks can consequently be
placed at any injective assignment of compiler work tapes.
-/

namespace PCP.Machine.ArithmeticBlocks

open Turing Turing.TM2 StateTransition PCP.Lang FiniteBlocks

variable (F : Type) [DecidableEq F] [Fintype F]

/-- The source machines permit dependent frame alphabets; the compiler uses `Sym`. -/
def symbols : ∀ k : BinaryZip.Slot ⊕ F, BinaryZip.alphabet F (fun _ => Sym) k ≃ Sym
  | .inl _ => Equiv.refl Sym
  | .inr _ => Equiv.refl Sym

/-- The uniform global contents of the four work ports and caller frame. -/
def tapes (left right scratch result : List Sym) (S : F → List Sym) :
    BinaryZip.Slot ⊕ F → List Sym
  | .inl .left => left
  | .inl .right => right
  | .inl .scratch => scratch
  | .inl .dst => result
  | .inr k => S k

/-- The actual consuming scan, with no changes to the materialized operations. -/
def zip (spec : BinaryZip.Spec) : Block (BinaryZip.Slot ⊕ F) (fun _ => Sym) :=
  relocatedBlock (BinaryZip.machine spec F (fun _ => Sym))
    (Equiv.refl (BinaryZip.Slot ⊕ F)) (symbols F)

/-- The actual consuming borrow scan followed by high-padding/underflow normalization. -/
def filtered (spec : BinaryZip.Spec) (filter : TransducerSpec) :
    Block (BinaryZip.Slot ⊕ F) (fun _ => Sym) :=
  relocatedBlock (FilteredZip.machine spec filter F (fun _ => Sym))
    (Equiv.refl (BinaryZip.Slot ⊕ F)) (symbols F)

lemma zip_cfg (spec : BinaryZip.Spec) (l : Option MovePhase) (s : spec.State)
    (left right scratch result : List Sym) (S : F → List Sym) :
    relocateCfg (BinaryZip.machine spec F (fun _ => Sym))
    (Equiv.refl (BinaryZip.Slot ⊕ F)) (symbols F)
      (BinaryZip.cfg spec F (fun _ => Sym) l s left right scratch result S) =
      ⟨l, (s, none, none), tapes F left right scratch result S⟩ := by
  dsimp only [relocateCfg, BinaryZip.cfg]
  congr 1
  funext k
  rcases k with (_ | _ | _ | _) | k <;>
    change List.map id _ = _
  all_goals exact List.map_id _

lemma filtered_cfg (spec : BinaryZip.Spec) (filter : TransducerSpec)
    (l : Option MovePhase) (s : spec.State) (t : filter.State)
    (left right scratch result : List Sym) (S : F → List Sym) :
    relocateCfg (FilteredZip.machine spec filter F (fun _ => Sym))
    (Equiv.refl (BinaryZip.Slot ⊕ F)) (symbols F)
      (FilteredZip.cfg spec filter F (fun _ => Sym) l s left right scratch result S t) =
      ⟨l, ((s, t), none, none), tapes F left right scratch result S⟩ := by
  dsimp only [relocateCfg, FilteredZip.cfg]
  congr 1
  funext k
  rcases k with (_ | _ | _ | _) | k <;>
    change List.map id _ = _
  all_goals exact List.map_id _

variable {F}

/-- Exact reset trace for arbitrary input words. -/
theorem zip_trace (spec : BinaryZip.Spec) (input output : BinaryZip.Slot ⊕ F)
    (xs ys : List Sym) (S : F → List Sym) :
    (flip Bind.bind ((zip F spec).machine input output).step)^[
        max xs.length ys.length + (spec.output spec.init xs ys).length + 2]
      (some ⟨some (zip F spec).entry, (zip F spec).initial, tapes F xs ys [] [] S⟩) =
      some ⟨none, (zip F spec).initial, tapes F [] [] [] (spec.output spec.init xs ys) S⟩ := by
  have h := iterate_relocatedBlock (BinaryZip.machine spec F (fun _ => Sym))
   
    (Equiv.refl (BinaryZip.Slot ⊕ F)) (symbols F) input output _
    (BinaryZip.trace (spec := spec) xs ys S)
  simp only [zip_cfg] at h
  exact h

/-- The normalizing scan returns with its finite state reset too. -/
theorem filtered_trace (spec : BinaryZip.Spec) (filter : TransducerSpec)
    (input output : BinaryZip.Slot ⊕ F) (xs ys : List Sym) (S : F → List Sym) :
    (flip Bind.bind ((filtered F spec filter).machine input output).step)^[
        max xs.length ys.length + (spec.output spec.init xs ys).length + 2]
      (some ⟨some (filtered F spec filter).entry, (filtered F spec filter).initial,
        tapes F xs ys [] [] S⟩) =
      some ⟨none, (filtered F spec filter).initial,
        tapes F [] [] []
          (filter.output filter.init (spec.output spec.init xs ys).reverse).reverse S⟩ := by
  have h := iterate_relocatedBlock (FilteredZip.machine spec filter F (fun _ => Sym))
   
    (Equiv.refl (BinaryZip.Slot ⊕ F)) (symbols F) input output _
    (FilteredZip.trace (spec := spec) (filter := filter) xs ys S)
  simp only [filtered_cfg] at h
  exact h

/-- Every basic binary arithmetic operation has a finite reset block. -/
inductive BasicOp | add | sub | eq | lt
  deriving DecidableEq, Repr

/-- The natural semantics implemented by the materialized blocks. -/
def BasicOp.eval : BasicOp → ℕ → ℕ → ℕ
  | .add, n, m => n + m
  | .sub, n, m => n - m
  | .eq, n, m => if n = m then 1 else 0
  | .lt, n, m => if n < m then 1 else 0

/-- Selection depends only on the finite program syntax. -/
def BasicOp.block (op : BasicOp) (F : Type) [DecidableEq F] [Fintype F] :
    Block (BinaryZip.Slot ⊕ F) (fun _ => Sym) :=
  match op with
  | .add => zip F BinaryAddition.spec
  | .sub => filtered F BinarySubtraction.spec BinaryNormalize.spec
  | .eq => zip F (BinaryComparison.spec (· == .eq))
  | .lt => zip F (BinaryComparison.spec (· == .lt))

/-- Actual arithmetic work is linear in the two operand bit lengths, including subtraction. -/
theorem BasicOp.evals (op : BasicOp) (input output : BinaryZip.Slot ⊕ F)
    (n m : ℕ) (S : F → List Sym) :
    ∃ steps ≤ 2 * max (Nat.size n) (Nat.size m) + 3,
      (flip Bind.bind ((op.block F).machine input output).step)^[steps]
        (some ⟨some (op.block F).entry, (op.block F).initial,
          tapes F (natTape n) (natTape m) [] [] S⟩) =
        some ⟨none, (op.block F).initial, tapes F [] [] [] (natTape (op.eval n m)) S⟩ := by
  cases op with
  | add =>
      have h := zip_trace BinaryAddition.spec input output (natTape n) (natTape m) S
      have hb := BinaryZip.Spec.output_length_le BinaryAddition.spec (natTape n) (natTape m) false
      simp only [BinaryAddition.output_natTape, natTape_length] at h hb
      exact ⟨_, by omega, h⟩
  | sub =>
      have h := filtered_trace BinarySubtraction.spec BinaryNormalize.spec input output
        (natTape n) (natTape m) S
      have hb := BinaryZip.Spec.output_length_le BinarySubtraction.spec
        (natTape n) (natTape m) false
      simp only [BinarySubtraction.output_natTape, natTape_length] at h hb
      exact ⟨_, by omega, h⟩
  | eq =>
      have h := zip_trace (BinaryComparison.spec (· == .eq)) input output
        (natTape n) (natTape m) S
      have hb := BinaryZip.Spec.output_length_le (BinaryComparison.spec (· == .eq))
        (natTape n) (natTape m) Ordering.eq
      simp only [BinaryComparison.eq_output_natTape, natTape_length] at h hb
      exact ⟨_, by omega, h⟩
  | lt =>
      have h := zip_trace (BinaryComparison.spec (· == .lt)) input output
        (natTape n) (natTape m) S
      have hb := BinaryZip.Spec.output_length_le (BinaryComparison.spec (· == .lt))
        (natTape n) (natTape m) Ordering.eq
      simp only [BinaryComparison.lt_output_natTape, natTape_length] at h hb
      exact ⟨_, by omega, h⟩


/-- Initial and final contents of the four arithmetic work tapes. -/
def workTapes (left right scratch result : List Sym) : BinaryZip.Slot → List Sym
  | .left => left
  | .right => right
  | .scratch => scratch
  | .dst => result

variable {K : Type} [DecidableEq K] [Fintype K]

/-- Materialize a basic operation at statically assigned global work indices. -/
def BasicOp.placed (op : BasicOp) (work : BinaryZip.Slot → K) : Block K (fun _ => Sym) :=
  StaticTapeLayout.place work (op.block (StaticTapeLayout.Unused work))

/-- Global arithmetic trace: consume two operands, produce the canonical result,
clear scratch, and preserve every tape outside the assigned four work slots. -/
theorem BasicOp.placed_evals (op : BasicOp) (work : BinaryZip.Slot → K)
    (hinj : Function.Injective work) (input output : K) (n m : ℕ)
    (S T : K → List Sym)
    (hx : ∀ w, S (work w) = workTapes (natTape n) (natTape m) [] [] w)
    (hy : ∀ w, T (work w) = workTapes [] [] [] (natTape (op.eval n m)) w)
    (hframe : ∀ k : StaticTapeLayout.Unused work, T k.val = S k.val) :
    ∃ steps ≤ 2 * max (Nat.size n) (Nat.size m) + 3,
      (flip Bind.bind ((op.placed work).machine input output).step)^[steps]
        (some ⟨some (op.placed work).entry, (op.placed work).initial, S⟩) =
        some ⟨none, (op.placed work).initial, T⟩ := by
  obtain ⟨steps, hbound, htrace⟩ := op.evals (.inl .left) (.inl .dst) n m
    (fun k : StaticTapeLayout.Unused work => S k.val)
  have he (a b c d : List Sym) :
      tapes (StaticTapeLayout.Unused work) a b c d (fun k => S k.val) =
        StaticTapeLayout.localStacks work (workTapes a b c d) S := by
    funext k
    rcases k with (_ | _ | _ | _) | k <;> rfl
  simp only [he] at htrace
  refine ⟨steps, hbound, ?_⟩
  exact StaticTapeLayout.place_trace work hinj (op.block (StaticTapeLayout.Unused work))
    (.inl .left) (.inl .dst) input output S T
    (workTapes (natTape n) (natTape m) [] [])
    (workTapes [] [] [] (natTape (op.eval n m)))
    (op.block (StaticTapeLayout.Unused work)).initial steps hx hy hframe htrace

end PCP.Machine.ArithmeticBlocks
