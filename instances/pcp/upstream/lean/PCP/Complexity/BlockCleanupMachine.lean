import PCP.Complexity.BlockControlMachine

/-!
# Cleaning a fixed collection of materialized machine tapes

One finite block drains one tape, resetting its only control bit at every step.
Static sequencing clears any fixed list of tape indices, preserving all other
tapes. Repeated indices are allowed. The runtime is linear in the total initial
length of the designated tapes and the fixed number of tape indices.
-/

namespace PCP.Machine.BlockCleanup

open Turing Turing.TM2 Turing.TM2.Stmt StateTransition FiniteBlocks

variable {K : Type} [DecidableEq K] [Fintype K] {Γ : K → Type}

/-- A no-op block has one actual halting transition. -/
abbrev empty : Block K Γ where
  Label := Unit
  Control := Unit
  entry := ()
  initial := ()
  code _ := .halt

/-- Drain one tape, retaining only its emptiness flag in finite control. -/
abbrev one (k : K) : Block K Γ where
  Label := Unit
  Control := Bool
  entry := ()
  initial := false
  code _ := .pop k (fun _ o => o.isSome)
    (.branch id (.load (fun _ => false) (.goto (fun _ => ())))
      (.load (fun _ => false) .halt))

/-- Every tape outside the fixed list is untouched. -/
def clear (ks : List K) (S : ∀ k, List (Γ k)) : ∀ k, List (Γ k) :=
  fun k => if k ∈ ks then [] else S k

omit [Fintype K] in
theorem clear_nil (S : ∀ k, List (Γ k)) : clear [] S = S := by
  funext k; simp [clear]

omit [Fintype K] in
theorem clear_cons (k : K) (ks : List K) (S : ∀ k, List (Γ k)) :
    clear (k :: ks) S = clear ks (Function.update S k []) := by
  funext j
  by_cases hj : j = k
  · subst j; simp [clear]
  · simp [clear, hj]

/-- Compose real drain blocks, with no data-dependent change to finite control types. -/
def block : List K → Block K Γ
  | [] => empty
  | k :: ks => BlockControl.sequence (one k) (block ks)

/-- The actual count includes the fixed sequencing transitions. -/
def runtime : List K → (∀ k, List (Γ k)) → ℕ
  | [], _ => 1
  | k :: ks, S => (S k).length + 1 + runtime ks (Function.update S k []) + 3

omit [Fintype K] in
/-- The same tape may appear repeatedly; clearing it never increases subsequent work. -/
theorem runtime_le (ks : List K) (S : ∀ k, List (Γ k)) :
    runtime ks S ≤ (ks.map (fun k => (S k).length)).sum + 4 * ks.length + 1 := by
  induction ks generalizing S with
  | nil => simp [runtime]
  | cons k ks ih =>
      have h := ih (Function.update S k [])
      have hu : (ks.map (fun j => ((Function.update S k []) j).length)).sum ≤
          (ks.map (fun j => (S j).length)).sum := by
        apply List.sum_le_sum
        intro j hj
        by_cases he : j = k
        · subst j; simp
        · simp [Function.update_of_ne he]
      simp only [runtime, List.map_cons, List.sum_cons, List.length_cons] at *
      omega

variable (input output : K) [Fintype (Γ input)]

/-- One physical pop, including the reset, is exactly one transition. -/
theorem one_step_cons (k : K) (S : ∀ k, List (Γ k)) (c : Γ k) (cs : List (Γ k)) :
    ((one k).machine input output).step
      ⟨some (), false, Function.update S k (c :: cs)⟩ =
      some ⟨some (), false, Function.update S k cs⟩ := by
  dsimp only [Block.machine, one, FinTM2.step, TM2.step, TM2.stepAux]
  simp only [Function.update_self, List.head?_cons, Option.isSome, id_eq,
    List.tail_cons, Function.update_idem]
  rfl

theorem one_step_nil (k : K) (S : ∀ k, List (Γ k)) :
    ((one k).machine input output).step
      ⟨some (), false, Function.update S k []⟩ =
      some ⟨none, false, Function.update S k []⟩ := by
  dsimp only [Block.machine, one, FinTM2.step, TM2.step, TM2.stepAux]
  simp only [Function.update_self, List.head?_nil, Option.isSome, id_eq,
    List.tail_nil, Function.update_idem]
  rfl

/-- Draining an arbitrary tape uses one step per cell and one final emptiness test. -/
theorem one_trace (k : K) (S : ∀ k, List (Γ k)) (xs : List (Γ k)) :
    (flip Bind.bind ((one k).machine input output).step)^[xs.length + 1]
      (some ⟨some (), false, Function.update S k xs⟩) =
      some ⟨none, false, Function.update S k []⟩ := by
  induction xs with
  | nil => exact one_step_nil input output k S
  | cons c cs ih =>
      rw [List.length_cons, Function.iterate_succ_apply]
      change (flip Bind.bind ((one k).machine input output).step)^[cs.length + 1]
        (((one k).machine input output).step
          ⟨some (), false, Function.update S k (c :: cs)⟩) = _
      rw [one_step_cons, ih]

/-- The entire fixed cleanup program has canonical initial and final control. -/
theorem trace (ks : List K) (S : ∀ k, List (Γ k)) :
    (flip Bind.bind ((block ks).machine input output).step)^[runtime ks S]
      (some ⟨some (block ks).entry, (block ks).initial, S⟩) =
      some ⟨none, (block ks).initial, clear ks S⟩ := by
  induction ks generalizing S with
  | nil => rw [clear_nil]; rfl
  | cons k ks ih =>
      have ho := one_trace input output k S (S k)
      simp only [Function.update_eq_self] at ho
      have ht := BlockControl.sequence_trace (one k) (block ks) input output
        S (Function.update S k []) (clear ks (Function.update S k []))
        ((S k).length + 1) (runtime ks (Function.update S k [])) ho
        (ih (Function.update S k []))
      rw [clear_cons]
      exact ht

omit [Fintype K] in
/-- A caller may preserve its output tape by omitting it from the fixed cleanup list. -/
theorem clear_apply_of_not_mem (ks : List K) (S : ∀ k, List (Γ k)) (j : K) (h : j ∉ ks) :
    clear ks S j = S j := by simp [clear, h]

omit [Fintype K] in
/-- Every listed tape is empty at the terminal configuration. -/
theorem clear_apply_of_mem (ks : List K) (S : ∀ k, List (Γ k)) (j : K) (h : j ∈ ks) :
    clear ks S j = [] := by simp [clear, h]

/-- Actual machine certificate with a linear bound in the initial tape contents. -/
def evals (ks : List K) (S : ∀ k, List (Γ k)) :
    EvalsToInTime ((block ks).machine input output).step
      ⟨some (block ks).entry, (block ks).initial, S⟩
      (some ⟨none, (block ks).initial, clear ks S⟩)
      ((ks.map (fun k => (S k).length)).sum + 4 * ks.length + 1) where
  steps := runtime ks S
  evals_in_steps := trace input output ks S
  steps_le_m := runtime_le ks S

end PCP.Machine.BlockCleanup
