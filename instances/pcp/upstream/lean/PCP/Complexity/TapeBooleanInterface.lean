import PCP.Complexity.FinTM2TapeSimulation

/-!
# Binary input and output for the marked stack simulator

The initial transition marks the first tape cell. When the simulated machine halts,
one final transition translates its singleton Boolean result to the same symbols used
for binary input. The resulting TM0 starts on a pointwise encoding of the input and
halts with exactly one encoded bit on its complete right-hand tape.

The stack representation reverses input: this wrapper computes the source machine on
the reversed binary word. That reversal is explicit in the theorem's source contract.
-/

namespace PCP.Machine.TMTime.BooleanInterface

open Turing

/-- Initial marker insertion, simulated control, and the final halted state. -/
inductive Control (Q : Type) where
  | start
  | run : Q → Control Q
  | halt
  deriving Fintype

instance {Q : Type} : Inhabited (Control Q) := ⟨.start⟩

variable (tm : FinTM2) (inputBit : Bool → tm.Γ tm.k₀)
variable (outputBit : Bool → tm.Γ tm.k₁) (decodeOutput : tm.Γ tm.k₁ → Bool)

/-- Pointwise binary encoding in the simulator's input track. -/
def cell (b : Bool) : TapeAlphabet tm :=
  (false, Function.update (fun _ => none) tm.k₀ (some (inputBit b)))

theorem cell_injective (h : Function.Injective inputBit) :
    Function.Injective (cell tm inputBit) := by
  intro a b hab
  have hc := congrArg (fun z : TapeAlphabet tm => z.2 tm.k₀) hab
  exact h (Option.some.inj (by simpa only [cell, Function.update_self] using hc))

theorem cell_ne_blank (b : Bool) : cell tm inputBit b ≠ default := by
  intro h
  have hc := congrArg (fun z : TapeAlphabet tm => z.2 tm.k₀) h
  have hb : (default : TapeAlphabet tm).2 tm.k₀ = none := rfl
  simp only [cell, Function.update_self, hb] at hc
  cases hc

/-- A total decoder for the two chosen input symbols, rejecting every other tape symbol. -/
noncomputable def readCell (a : TapeAlphabet tm) : Option Bool := by
  classical
  exact if a = cell tm inputBit false then some false
    else if a = cell tm inputBit true then some true else none

theorem readCell_cell (h : Function.Injective inputBit) (b : Bool) :
    readCell tm inputBit (cell tm inputBit b) = some b := by
  classical
  cases b <;> simp [readCell, (cell_injective tm inputBit h).eq_iff]

theorem readCell_blank : readCell tm inputBit default = none := by
  classical
  simp [readCell, Ne.symm (cell_ne_blank tm inputBit false),
    Ne.symm (cell_ne_blank tm inputBit true)]

/-- Set the permanent bottom marker without changing any stack track. -/
def mark (a : TapeAlphabet tm) : TapeAlphabet tm := (true, a.2)

/-- Translate the output-track symbol into the input alphabet's Boolean convention. -/
def result (a : TapeAlphabet tm) : TapeAlphabet tm :=
  cell tm inputBit (((a.2 tm.k₁).map decodeOutput).getD false)

variable {Q : Type} [Inhabited Q]

/-- The actual TM0 wrapper, with two extra transitions per successful source run. -/
def code (M : TM0.Machine (TapeAlphabet tm) Q) :
    TM0.Machine (TapeAlphabet tm) (Control Q)
  | .start, a => some (.run default, .write (mark tm a))
  | .run q, a => match M q a with
    | none => some (.halt, .write (result tm inputBit decodeOutput a))
    | some (q', action) => some (.run q', action)
  | .halt, _ => none

/-- A source configuration in the simulation phase. -/
def running (a : TM0.Cfg (TapeAlphabet tm) Q) :
    TM0.Cfg (TapeAlphabet tm) (Control Q) := ⟨.run a.q, a.Tape⟩

theorem step_running (M : TM0.Machine (TapeAlphabet tm) Q)
    {a b : TM0.Cfg (TapeAlphabet tm) Q} (h : TM0.step M a = some b) :
    TM0.step (code tm inputBit decodeOutput M) (running tm a) = some (running tm b) := by
  rcases a with ⟨q, T⟩
  cases hM : M q T.head with
  | none => simp [TM0.step, hM] at h
  | some p =>
    rcases p with ⟨q', action⟩
    cases action <;> simp only [TM0.step, hM, Option.map_some, Option.some.injEq] at h <;>
      subst b <;> simp [TM0.step, code, running, hM]

theorem exec_running (M : TM0.Machine (TapeAlphabet tm) Q) (t : ℕ)
    {a b : TM0.Cfg (TapeAlphabet tm) Q} (h : exec (TM0.step M) t a = some b) :
    exec (TM0.step (code tm inputBit decodeOutput M)) t (running tm a) =
      some (running tm b) := by
  induction t generalizing a with
  | zero =>
    simp only [exec, Option.some.injEq] at h
    subst b
    rfl
  | succ t ih =>
    cases hs : TM0.step M a with
    | none => simp [exec, hs] at h
    | some c =>
      have hc : exec (TM0.step M) t c = some b := by simpa [exec, hs] using h
      rw [exec, step_running tm inputBit decodeOutput M hs, Option.bind_some]
      exact ih hc

set_option backward.isDefEq.respectTransparency false in
theorem mark_input (w : List Bool) :
    (Tape.mk₁ (w.map (cell tm inputBit))).write
        (mark tm (Tape.mk₁ (w.map (cell tm inputBit))).head) =
      stackTape tm tm.k₀ (w.reverse.map inputBit) := by
  have hm : (w.map inputBit).map
      (fun a => (false, Function.update (fun _ => none) tm.k₀ (some a))) =
      w.map (cell tm inputBit) := by
    rw [List.map_map]
    rfl
  simp only [stackTape, TM2to1.trInit, ← List.map_reverse, List.reverse_reverse]
  rw [hm]
  cases w <;> rfl

theorem step_start (M : TM0.Machine (TapeAlphabet tm) Q) (w : List Bool) :
    TM0.step (code tm inputBit decodeOutput M) (TM0.init (w.map (cell tm inputBit))) =
      some (running tm (TM0.init (TM2to1.trInit tm.k₀ (w.reverse.map inputBit)))) := by
  change some (⟨.run default, (Tape.mk₁ (w.map (cell tm inputBit))).write
      (mark tm (Tape.mk₁ (w.map (cell tm inputBit))).head)⟩ :
        TM0.Cfg (TapeAlphabet tm) (Control Q)) = _
  rw [mark_input]
  rfl

theorem result_output (hdecode : ∀ b, decodeOutput (outputBit b) = b) (b : Bool) :
    (stackTape tm tm.k₁ [outputBit b]).write
        (result tm inputBit decodeOutput (stackTape tm tm.k₁ [outputBit b]).head) =
      Tape.mk₁ [cell tm inputBit b] := by
  simp [stackTape, TM2to1.trInit, result, Tape.mk₁, Tape.mk₂, Tape.mk', Tape.write,
    List.map, List.headI, List.tail, hdecode]

theorem step_finish (M : TM0.Machine (TapeAlphabet tm) Q)
    (hdecode : ∀ b, decodeOutput (outputBit b) = b) (b : Bool)
    {a : TM0.Cfg (TapeAlphabet tm) Q} (hh : TM0.step M a = none)
    (ho : a.Tape = stackTape tm tm.k₁ [outputBit b]) :
    TM0.step (code tm inputBit decodeOutput M) (running tm a) =
      some ⟨.halt, Tape.mk₁ [cell tm inputBit b]⟩ := by
  have hc : M a.q a.Tape.head = none := by
    simpa only [TM0.step, Option.map_eq_none_iff] using hh
  change (code tm inputBit decodeOutput M (.run a.q) a.Tape.head).map _ = _
  rw [code, hc]
  simp only [Option.map_some]
  apply congrArg some
  rw [show a.Tape.write (result tm inputBit decodeOutput a.Tape.head) =
      Tape.mk₁ [cell tm inputBit b] by
        rw [ho, result_output tm inputBit outputBit decodeOutput hdecode]]

/-- Pointwise binary input and complete singleton binary output, with explicit reversal
and at most two transitions beyond the quantitative stack simulation. -/
theorem outputs (S : TapeSimulation tm)
    (hdecode : ∀ b, decodeOutput (outputBit b) = b)
    (w : List Bool) (b : Bool) (time : ℕ)
    (h : TM2OutputsInTime tm (w.reverse.map inputBit) (some [outputBit b]) time) :
    ∃ u ≤ S.overhead * (w.length + time + 3) ^ 2 + 2,
      ∃ a : TM0.Cfg (TapeAlphabet tm) (Control (Fin (S.states + 1))),
        exec (TM0.step (code tm inputBit decodeOutput S.code)) u
          (TM0.init (w.map (cell tm inputBit))) = some a ∧
        TM0.step (code tm inputBit decodeOutput S.code) a = none ∧
        a.Tape.right₀ = ListBlank.mk [cell tm inputBit b] := by
  obtain ⟨u, hu, a, ha, hh, ho⟩ := S.outputs (w.reverse.map inputBit) [outputBit b] time h
  have hstart : exec (TM0.step (code tm inputBit decodeOutput S.code)) 1
      (TM0.init (w.map (cell tm inputBit))) =
      some (running tm (TM0.init (TM2to1.trInit tm.k₀ (w.reverse.map inputBit)))) := by
    simp only [exec, step_start tm inputBit decodeOutput S.code w, Option.bind_some]
  have hrun := exec_running tm inputBit decodeOutput S.code u ha
  have hfinish : exec (TM0.step (code tm inputBit decodeOutput S.code)) 1 (running tm a) =
      some ⟨.halt, Tape.mk₁ [cell tm inputBit b]⟩ := by
    simp only [exec, step_finish tm inputBit outputBit decodeOutput S.code hdecode b hh ho,
      Option.bind_some]
  refine ⟨1 + u + 1, ?_, ⟨.halt, Tape.mk₁ [cell tm inputBit b]⟩,
    exec_trans (exec_trans hstart hrun) hfinish, rfl, ?_⟩
  · simpa only [List.length_map, List.length_reverse] using (by omega :
      1 + u + 1 ≤ S.overhead * ((w.reverse.map inputBit).length + time + 3) ^ 2 + 2)
  · exact Tape.mk'_right₀ _ _

end PCP.Machine.TMTime.BooleanInterface
