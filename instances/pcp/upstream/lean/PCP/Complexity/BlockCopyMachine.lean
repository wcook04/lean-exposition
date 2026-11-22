import PCP.Complexity.FiniteBlockMachine

/-!
# A preserving copy block on explicit shared tape indices

The source is transferred to scratch, then restored while a copy is prepended to
the destination. Both phases are physical scans. The finite controller holds at
most one alphabet symbol; every tape outside the three designated indices is
preserved and scratch is empty at return.
-/

namespace PCP.Machine.BlockCopy

open Turing Turing.TM2 Turing.TM2.Stmt StateTransition FiniteBlocks

variable {K A : Type} [DecidableEq K] [Fintype K] [Fintype A] [Inhabited A]
  (source scratch dest : K)

abbrev block : Block K (fun _ => A) where
  Label := Bool
  Control := Option A
  entry := false
  initial := none
  code := fun
    | false => .pop source (fun _ o => o)
        (.branch Option.isSome
          (.push scratch (fun o => o.getD default)
            (.load (fun _ => none) (.goto (fun _ => false))))
          (.load (fun _ => none) (.goto (fun _ => true))))
    | true => .pop scratch (fun _ o => o)
        (.branch Option.isSome
          (.push source (fun o => o.getD default)
            (.push dest (fun o => o.getD default)
              (.load (fun _ => none) (.goto (fun _ => true)))))
          (.load (fun _ => none) .halt))

/-- Arbitrary caller tapes are overridden only at the three work slots. -/
def tapes (xs tmp ys : List A) (S : K → List A) : K → List A :=
  Function.update (Function.update (Function.update S source xs) scratch tmp) dest ys

variable (input output : K)

def cfg (l : Option Bool) (xs tmp ys : List A) (S : K → List A) :
    ((block source scratch dest : Block K (fun _ => A)).machine input output).Cfg :=
  ⟨l, none, tapes source scratch dest xs tmp ys S⟩

variable (hss : source ≠ scratch) (hsd : source ≠ dest) (htd : scratch ≠ dest)

include hss hsd htd

/-- The first scan removes one source cell and records it on scratch. -/
theorem step_one_cons (c : A) (xs tmp ys : List A) (S : K → List A) :
    ((block source scratch dest).machine input output).step
      (cfg source scratch dest input output (some false) (c :: xs) tmp ys S) =
      some (cfg source scratch dest input output (some false) xs (c :: tmp) ys S) := by
  dsimp only [FinTM2.Cfg, Block.machine, block, FinTM2.step, TM2.step, cfg, TM2.stepAux, tapes]
  simp only [Function.update_of_ne hsd, Function.update_of_ne hss, Function.update_self,
    List.head?_cons, List.tail_cons, Option.isSome, Option.getD_some]
  simp only [Bool.cond_true]
  congr 2
  funext k
  by_cases hs : k = source <;> by_cases ht : k = scratch <;> by_cases hd : k = dest <;>
    simp_all [Function.update]

/-- One transition separates the forward and restoring scans. -/
theorem step_one_nil (tmp ys : List A) (S : K → List A) :
    ((block source scratch dest).machine input output).step
      (cfg source scratch dest input output (some false) [] tmp ys S) =
      some (cfg source scratch dest input output (some true) [] tmp ys S) := by
  dsimp only [FinTM2.Cfg, Block.machine, block, FinTM2.step, TM2.step, cfg, TM2.stepAux, tapes]
  simp only [Function.update_of_ne hsd, Function.update_of_ne hss, Function.update_self,
    List.head?_nil, List.tail_nil, Option.isSome]
  simp only [Bool.cond_false]
  congr 2
  funext k
  by_cases hs : k = source <;> by_cases ht : k = scratch <;> by_cases hd : k = dest <;>
    simp_all [Function.update]

/-- Restoration writes the same physical symbol to source and destination. -/
theorem step_two_cons (c : A) (xs tmp ys : List A) (S : K → List A) :
    ((block source scratch dest).machine input output).step
      (cfg source scratch dest input output (some true) xs (c :: tmp) ys S) =
      some (cfg source scratch dest input output (some true) (c :: xs) tmp (c :: ys) S) := by
  dsimp only [FinTM2.Cfg, Block.machine, block, FinTM2.step, TM2.step, cfg, TM2.stepAux, tapes]
  simp only [Function.update_of_ne htd, Function.update_self,
    Function.update_of_ne hsd, Function.update_of_ne hss, Function.update_of_ne htd.symm,
    Function.update_of_ne hsd.symm, List.head?_cons, List.tail_cons,
    Option.isSome, Option.getD_some]
  simp only [Bool.cond_true]
  congr 2
  funext k
  by_cases hs : k = source <;> by_cases ht : k = scratch <;> by_cases hd : k = dest <;>
    simp_all [Function.update]

/-- Empty scratch halts and resets the only local control. -/
theorem step_two_nil (xs ys : List A) (S : K → List A) :
    ((block source scratch dest).machine input output).step
      (cfg source scratch dest input output (some true) xs [] ys S) =
      some (cfg source scratch dest input output none xs [] ys S) := by
  dsimp only [FinTM2.Cfg, Block.machine, block, FinTM2.step, TM2.step, cfg, TM2.stepAux, tapes]
  simp only [Function.update_of_ne htd, Function.update_self,
    List.head?_nil, List.tail_nil, Option.isSome]
  simp only [Bool.cond_false]
  congr 2
  funext k
  by_cases hs : k = source <;> by_cases ht : k = scratch <;> by_cases hd : k = dest <;>
    simp_all [Function.update]

theorem first_trace (xs tmp ys : List A) (S : K → List A) :
    (flip Bind.bind ((block source scratch dest).machine input output).step)^[
        xs.length + 1]
      (some (cfg source scratch dest input output (some false) xs tmp ys S)) =
      some (cfg source scratch dest input output (some true) [] (xs.reverse ++ tmp) ys S) := by
  induction xs generalizing tmp with
  | nil => exact step_one_nil source scratch dest input output hss hsd htd tmp ys S
  | cons c xs ih =>
      rw [List.length_cons, Function.iterate_succ_apply]
      change (flip Bind.bind ((block source scratch dest).machine input output).step)^[
        xs.length + 1]
        (((block source scratch dest).machine input output).step
          (cfg source scratch dest input output (some false) (c :: xs) tmp ys S)) = _
      rw [step_one_cons source scratch dest input output hss hsd htd, ih]
      simp [List.reverse_cons, List.append_assoc]

theorem second_trace (xs tmp ys : List A) (S : K → List A) :
    (flip Bind.bind ((block source scratch dest).machine input output).step)^[
        tmp.length + 1]
      (some (cfg source scratch dest input output (some true) xs tmp ys S)) =
      some (cfg source scratch dest input output none
        (tmp.reverse ++ xs) [] (tmp.reverse ++ ys) S) := by
  induction tmp generalizing xs ys with
  | nil => exact step_two_nil source scratch dest input output hss hsd htd xs ys S
  | cons c tmp ih =>
      rw [List.length_cons, Function.iterate_succ_apply]
      change (flip Bind.bind ((block source scratch dest).machine input output).step)^[
        tmp.length + 1]
        (((block source scratch dest).machine input output).step
          (cfg source scratch dest input output (some true) xs (c :: tmp) ys S)) = _
      rw [step_two_cons source scratch dest input output hss hsd htd, ih]
      simp [List.reverse_cons, List.append_assoc]

/-- Source retained, scratch cleared, original source prepended in its original order. -/
theorem trace (xs ys : List A) (S : K → List A) :
    (flip Bind.bind ((block source scratch dest).machine input output).step)^[2 * xs.length + 2]
      (some (cfg source scratch dest input output (some false) xs [] ys S)) =
      some (cfg source scratch dest input output none xs [] (xs ++ ys) S) := by
  rw [show 2 * xs.length + 2 = (xs.reverse.length + 1) + (xs.length + 1) by simp; omega,
    Function.iterate_add_apply, first_trace source scratch dest input output hss hsd htd]
  simpa using second_trace source scratch dest input output hss hsd htd [] xs.reverse ys S

/-- An exact linear-time certificate on arbitrary caller storage. -/
def evals (xs ys : List A) (S : K → List A) :
    EvalsToInTime ((block source scratch dest).machine input output).step
      (cfg source scratch dest input output (some false) xs [] ys S)
      (some (cfg source scratch dest input output none xs [] (xs ++ ys) S))
      (2 * xs.length + 2) where
  steps := 2 * xs.length + 2
  evals_in_steps := trace source scratch dest input output hss hsd htd xs ys S
  steps_le_m := le_rfl

end PCP.Machine.BlockCopy
