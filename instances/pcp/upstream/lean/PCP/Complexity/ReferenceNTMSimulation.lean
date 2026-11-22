import PCP.Complexity.ReferenceNTMTape

/-!
# Supplied-choice simulation of the reference nondeterministic machine

The execution consumes a finite list of choice bits. Its time bound is therefore
the supplied witness length; no source-machine time-bound function is evaluated.
Every tape uses a finite base-four numeral and a cached head place value.
-/

namespace PCP.ReferenceNTM

open Complexity

variable {k : ℕ} (tm : NTM k)

/-- Tape zero is input, tape one output, and tape `i+2` is work tape `i`. -/
structure Cfg where
  state : tm.Q
  tapes : Fin (k + 2) → Tape

namespace Cfg

variable {tm}

def input (c : Cfg tm) : Tape := c.tapes 0
def output (c : Cfg tm) : Tape := c.tapes 1
def work (c : Cfg tm) (i : Fin k) : Tape := c.tapes ⟨i.val + 2, by omega⟩

def Valid (c : Cfg tm) : Prop := ∀ j, (c.tapes j).Valid

def decode (c : Cfg tm) : Complexity.Cfg k tm.Q :=
  ⟨c.state, c.input.decode, fun i => (c.work i).decode, c.output.decode⟩

def init (tm : NTM k) (x : List Bool) : Cfg tm :=
  ⟨tm.qstart, fun j => if j.val = 0 then Tape.init (x.map Γ.ofBool) else Tape.init []⟩

/-- One simultaneous reference transition, frozen at the halt state. -/
def step (b : Bool) (c : Cfg tm) : Cfg tm :=
  if c.state = tm.qhalt then c
  else
    let (q, ws, os, di, dw, do') :=
      tm.δ b c.state c.input.read (fun i => (c.work i).read) c.output.read
    ⟨q, fun j =>
      if h0 : j.val = 0 then c.input.move di
      else if h1 : j.val = 1 then c.output.writeAndMove os.toΓ do'
      else (c.work ⟨j.val - 2, by omega⟩).writeAndMove
        (ws ⟨j.val - 2, by omega⟩).toΓ (dw ⟨j.val - 2, by omega⟩)⟩

def run : List Bool → Cfg tm → Cfg tm
  | [], c => c
  | b :: bs, c => run bs (step b c)

def accepts (tm : NTM k) (x choices : List Bool) : Bool :=
  let c := run choices (init tm x)
  decide (c.state = tm.qhalt ∧ digit c.output.code 1 = 2)

/-- Number of natural registers holding a complete numeric configuration. -/
abbrev width (k : ℕ) : ℕ := 1 + 3 * (k + 2)

def codeIndex (j : Fin (k + 2)) : Fin (width k) := ⟨1 + 3 * j.val, by dsimp [width]; omega⟩
def headIndex (j : Fin (k + 2)) : Fin (width k) := ⟨2 + 3 * j.val, by dsimp [width]; omega⟩
def powerIndex (j : Fin (k + 2)) : Fin (width k) := ⟨3 + 3 * j.val, by dsimp [width]; omega⟩

/-- State, then code/head/power for input, output, and each work tape. -/
def encode {q : ℕ} (eQ : tm.Q ≃ Fin q) (c : Cfg tm) (r : Fin (width k)) : ℕ :=
  if h : r.val = 0 then (eQ c.state).val
  else
    let j : Fin (k + 2) := ⟨(r.val - 1) / 3, by
      have hr := r.isLt
      dsimp [width] at hr
      omega⟩
    if (r.val - 1) % 3 = 0 then (c.tapes j).code
    else if (r.val - 1) % 3 = 1 then (c.tapes j).head
    else (c.tapes j).power

@[simp] theorem encode_state {q : ℕ} (eQ : tm.Q ≃ Fin q) (c : Cfg tm) :
    encode eQ c 0 = (eQ c.state).val := by simp [encode]

@[simp] theorem encode_code {q : ℕ} (eQ : tm.Q ≃ Fin q) (c : Cfg tm)
    (j : Fin (k + 2)) : encode eQ c (codeIndex j) = (c.tapes j).code := by
  simp [encode, codeIndex]

@[simp] theorem encode_head {q : ℕ} (eQ : tm.Q ≃ Fin q) (c : Cfg tm)
    (j : Fin (k + 2)) : encode eQ c (headIndex j) = (c.tapes j).head := by
  have h : 2 + 3 * j.val - 1 = 1 + 3 * j.val := by omega
  simp [encode, headIndex, h, Nat.add_div, Nat.add_mod]

@[simp] theorem encode_power {q : ℕ} (eQ : tm.Q ≃ Fin q) (c : Cfg tm)
    (j : Fin (k + 2)) : encode eQ c (powerIndex j) = (c.tapes j).power := by
  have h : 3 + 3 * j.val - 1 = 2 + 3 * j.val := by omega
  simp [encode, powerIndex, h, Nat.add_div, Nat.add_mod]

@[simp] theorem valid_init (tm : NTM k) (x : List Bool) : (init tm x).Valid := by
  intro j
  simp only [init]
  split <;> exact Tape.valid_init _

theorem decode_init (tm : NTM k) (x : List Bool) : (init tm x).decode = tm.initCfg x := by
  apply Complexity.Cfg.ext
  · rfl
  · simp [decode, input, init, Tape.decode_init]
  · funext i
    simp [decode, work, init, Tape.decode_init]
  · simp [decode, output, init, Tape.decode_init]

theorem init_input_code_append (tm : NTM k) (x : List Bool) (b : Bool) :
    (init tm (x ++ [b])).input.code = (init tm x).input.code +
      (b.toNat + 1) * 4 ^ (x.length + 1) := by
  simpa [input, init, List.map_append] using
    Tape.init_append_code (x.map Γ.ofBool) (Γ.ofBool b)

theorem Valid.step {c : Cfg tm} (hc : c.Valid) (b : Bool) : (step b c).Valid := by
  by_cases h : c.state = tm.qhalt
  · simpa [Cfg.step, h] using hc
  · intro j
    simp only [Cfg.step, h, ite_false]
    split
    · exact (hc 0).move _
    · split
      · exact ((hc 1).write _).move _
      · exact ((hc _).write _).move _

theorem decode_step (b : Bool) (c : Cfg tm) (hc : c.Valid) :
    (step b c).decode = tm.trace 1 (fun _ => b) c.decode := by
  have hi : c.input.read = c.input.decode.read := Tape.read_decode _ (hc 0)
  have ho : c.output.read = c.output.decode.read := Tape.read_decode _ (hc 1)
  have hw : (fun i => (c.work i).read) = fun i => (c.work i).decode.read := by
    funext i
    exact Tape.read_decode _ (hc _)
  by_cases h : c.state = tm.qhalt
  · simp [step, NTM.trace, decode, h]
  · simp only [step, h, ite_false, NTM.trace, decode, hi, ho, hw]
    apply Complexity.Cfg.ext
    · rfl
    · simp [input, Tape.decode_move]
    · funext i
      simpa [work] using Tape.decode_writeAndMove (c.work i) (hc _) _ _
    · simpa [output] using Tape.decode_writeAndMove c.output (hc 1) _ _

theorem Valid.run {c : Cfg tm} (hc : c.Valid) (choices : List Bool) :
    (run choices c).Valid := by
  induction choices generalizing c with
  | nil => exact hc
  | cons b bs ih => exact ih (hc.step b)

theorem run_halted (c : Cfg tm) (h : c.state = tm.qhalt) (choices : List Bool) :
    run choices c = c := by
  induction choices with
  | nil => rfl
  | cons b bs ih => simpa [run, step, h] using ih

/-- Exact agreement with the unmodified reference trace on every supplied witness. -/
theorem decode_run (choices : List Bool) (c : Cfg tm) (hc : c.Valid) :
    (run choices c).decode =
      tm.trace choices.length (fun i => choices[i.val]'i.isLt) c.decode := by
  induction choices generalizing c with
  | nil => rfl
  | cons b bs ih =>
      by_cases h : c.state = tm.qhalt
      · rw [run_halted c h]
        simp [NTM.trace, decode, h]
      · rw [run, ih (step b c) (hc.step b), decode_step b c hc]
        simp [NTM.trace, decode, h]

/-- The executable Boolean verdict recognizes precisely the supplied accepting path. -/
theorem accepts_iff (tm : NTM k) (x choices : List Bool) :
    accepts tm x choices = true ↔
      let c := tm.trace choices.length (fun i => choices[i.val]'i.isLt) (tm.initCfg x)
      tm.halted c ∧ c.output.cells 1 = Γ.one := by
  have hd := decode_run choices (init tm x) (valid_init tm x)
  rw [decode_init] at hd
  simp only [accepts, decide_eq_true_eq]
  rw [← hd]
  change _ ↔ _ ∧ symbol (digit (run choices (init tm x)).output.code 1) = Γ.one
  have hn : digit (run choices (init tm x)).output.code 1 < 4 := Nat.mod_lt _ (by decide)
  generalize digit (run choices (init tm x)).output.code 1 = a at hn ⊢
  interval_cases a <;> simp [symbol, NTM.halted, Complexity.Cfg.isHalted, decode]

end Cfg
end PCP.ReferenceNTM
