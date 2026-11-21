import PCP.Complexity.LangSpace

/-!
# Operational execution of the costed language

A continuation machine separates control flow from primitive data operations. A `repeat` frame
stores a countdown and the bit width of the count on loop entry; assignments to the source
register cannot change the iteration count or its charge. The countdown denotes one more than
its stored value, so an empty loop exits on entry and there are no uncharged loop-exit steps.

The machine agrees exactly with `Stmt.run`, terminates in at most the charged cost, and bounds
the data in every execution prefix by input size plus total cost. Primitives still operate on
Lean naturals and lists: implementing them on finite-alphabet stacks remains part of COMPILE.
-/

namespace PCP.Lang

variable {R Q : ℕ}

/-- Pending code, or a positive number of remaining loop iterations with a frozen bit width. -/
inductive Frame (R Q : ℕ)
  | exec (s : Stmt R Q)
  | repeat (s : Stmt R Q) (remaining width : ℕ)

/-- The denotation of a single continuation frame. -/
def Frame.run : Frame R Q → State R Q → State R Q × ℕ
  | .exec s, st => s.run st
  | .repeat s n w, st => iterate s.run (w + 1) (n + 1) st

/-- Execute the pending frames in order, adding their costs. -/
def runFrames : List (Frame R Q) → State R Q → State R Q × ℕ
  | [], st => (st, 0)
  | f :: fs, st =>
      let a := f.run st
      let b := runFrames fs a.1
      (b.1, a.2 + b.2)

/-- One control step. Only primitive statements invoke `Stmt.run` here. -/
def Frame.next : Frame R Q → State R Q → List (Frame R Q) × State R Q × ℕ
  | .exec (.seq s t), st => ([.exec s, .exec t], st, 1)
  | .exec (.ite x s t), st =>
      ([.exec (if st.regs x ≠ 0 then s else t)], st, Nat.size (st.regs x) + 1)
  | .exec (.loop x s), st =>
      (match st.regs x with
        | 0 => []
        | n + 1 => [.repeat s n (Nat.size (st.regs x))], st, Nat.size (st.regs x) + 1)
  | .exec s, st => ([], s.run st)
  | .repeat s 0 w, st => ([.exec s], st, w + 1)
  | .repeat s (n + 1) w, st => ([.exec s, .repeat s n w], st, w + 1)

/-- A continuation and the data on which it will operate. -/
structure Config (R Q : ℕ) where
  todo : List (Frame R Q)
  state : State R Q

/-- Halt precisely when no code remains. -/
def Config.step (a : Config R Q) : Option (Config R Q × ℕ) :=
  match a.todo with
  | [] => none
  | f :: fs =>
      let p := f.next a.state
      some (⟨p.1 ++ fs, p.2.1⟩, p.2.2)

/-- The remaining computation, used as a termination measure, not by `step`. -/
def Config.result (a : Config R Q) : State R Q × ℕ := runFrames a.todo a.state

theorem runFrames_append (fs gs : List (Frame R Q)) (st : State R Q) :
    runFrames (fs ++ gs) st =
      let a := runFrames fs st
      let b := runFrames gs a.1
      (b.1, a.2 + b.2) := by
  induction fs generalizing st with
  | nil => simp [runFrames]
  | cons f fs ih => simp [runFrames, ih, Nat.add_assoc]

/-- One operational step preserves the denotation and accounts for exactly its own charge. -/
theorem Frame.run_eq_next (f : Frame R Q) (st : State R Q) :
    f.run st =
      let p := f.next st
      let out := runFrames p.1 p.2.1
      (out.1, p.2.2 + out.2) := by
  cases f with
  | exec s =>
    cases s with
    | seq s t => simp [Frame.run, Frame.next, runFrames, Stmt.run, Nat.add_comm]
    | ite x s t =>
      by_cases h : st.regs x ≠ 0 <;>
        simp [Frame.run, Frame.next, runFrames, Stmt.run, h, Nat.add_comm,
          Nat.add_left_comm]
    | loop x s =>
      cases hn : st.regs x <;>
        simp [Frame.run, Frame.next, runFrames, Stmt.run, hn, iterate, Nat.add_assoc,
          Nat.add_comm, Nat.add_left_comm]
    | _ => rfl
  | «repeat» s n w =>
    cases n <;> simp [Frame.run, Frame.next, runFrames, iterate, Nat.add_assoc]

theorem Frame.next_cost_pos (f : Frame R Q) (st : State R Q) : 0 < (f.next st).2.2 := by
  cases f with
  | exec s =>
    cases s <;> first | exact Stmt.run_cost_pos _ st | simp [Frame.next]
  | «repeat» s n w => cases n <;> simp [Frame.next]

theorem Frame.next_sized (f : Frame R Q) (st : State R Q) {B : ℕ} (h : st.Sized B) :
    (f.next st).2.1.Sized (B + (f.next st).2.2) := by
  cases f with
  | exec s =>
    cases s <;> first | exact Stmt.run_sized _ st B h | exact h.mono (Nat.le_add_right _ _)
  | «repeat» s n w => cases n <;> exact h.mono (Nat.le_add_right _ _)

theorem Config.step_none_iff (a : Config R Q) : a.step = none ↔ a.todo = [] := by
  cases a with | mk todo st => cases todo <;> simp [Config.step]

theorem Config.step_result {a b : Config R Q} {c : ℕ} (h : a.step = some (b, c)) :
    a.result = (b.result.1, c + b.result.2) := by
  cases a with
  | mk todo st =>
    cases todo with
    | nil => simp [Config.step] at h
    | cons f fs =>
      simp only [Config.step, Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩
      rw [Config.result, runFrames, f.run_eq_next st]
      simp [Config.result, runFrames_append, Nat.add_assoc]

theorem Config.step_cost_pos {a b : Config R Q} {c : ℕ} (h : a.step = some (b, c)) :
    0 < c := by
  cases a with
  | mk todo st =>
    cases todo with
    | nil => simp [Config.step] at h
    | cons f fs =>
      simp only [Config.step, Option.some.injEq, Prod.mk.injEq] at h
      exact h.2 ▸ f.next_cost_pos st

theorem Config.step_sized {a b : Config R Q} {c B : ℕ} (h : a.step = some (b, c))
    (hB : a.state.Sized B) : b.state.Sized (B + c) := by
  cases a with
  | mk todo st =>
    cases todo with
    | nil => simp [Config.step] at h
    | cons f fs =>
      simp only [Config.step, Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩
      exact f.next_sized st hB

/-! ## The continuation's counters and length -/

/-- A saved counter fits in `B` bits and its frozen charge width is at most `B`. -/
def Frame.Sized : Frame R Q → ℕ → Prop
  | .exec _, _ => True
  | .repeat _ n w, B => Nat.size (n + 1) ≤ B ∧ w ≤ B

theorem Frame.Sized.mono {f : Frame R Q} {B C : ℕ} (h : f.Sized B) (hBC : B ≤ C) :
    f.Sized C := by
  cases f with
  | exec => trivial
  | «repeat» s n w => exact ⟨Nat.le_trans h.1 hBC, Nat.le_trans h.2 hBC⟩

/-- Include the runtime counters in the configuration's data bound. -/
def Config.Sized (a : Config R Q) (B : ℕ) : Prop :=
  a.state.Sized B ∧ ∀ f ∈ a.todo, f.Sized B

theorem Config.Sized.mono {a : Config R Q} {B C : ℕ} (h : a.Sized B) (hBC : B ≤ C) :
    a.Sized C :=
  ⟨h.1.mono hBC, fun f hf => (h.2 f hf).mono hBC⟩

theorem Frame.next_frames_sized (f : Frame R Q) (st : State R Q) {B : ℕ}
    (hf : f.Sized B) (hB : st.Sized B) : ∀ g ∈ (f.next st).1, g.Sized B := by
  cases f with
  | exec s =>
    cases s with
    | loop x s =>
      cases hn : st.regs x with
      | zero => simp [Frame.next, hn]
      | succ n =>
        have hx : Nat.size (n + 1) ≤ B := by simpa [hn] using hB.1 x
        simpa [Frame.next, hn, Frame.Sized] using hx
    | _ => simp [Frame.next, Frame.Sized]
  | «repeat» s n w =>
    cases n with
    | zero => simp [Frame.next, Frame.Sized]
    | succ n =>
      have hn : Nat.size (n + 1) ≤ B :=
        Nat.le_trans (Nat.size_le_size (by omega : n + 1 ≤ n + 1 + 1)) hf.1
      simp [Frame.next, Frame.Sized, hn, hf.2]

theorem Config.step_config_sized {a b : Config R Q} {c B : ℕ}
    (h : a.step = some (b, c)) (hB : a.Sized B) : b.Sized (B + c) := by
  refine ⟨Config.step_sized h hB.1, ?_⟩
  cases a with
  | mk todo st =>
    cases todo with
    | nil => simp [Config.step] at h
    | cons f fs =>
      simp only [Config.step, Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩
      intro g hg
      rcases List.mem_append.mp hg with hg | hg
      · exact (f.next_frames_sized st (hB.2 f (by simp)) hB.1 g hg).mono
          (Nat.le_add_right _ _)
      · exact (hB.2 g (List.mem_cons_of_mem _ hg)).mono (Nat.le_add_right _ _)

/-- A control step produces at most two replacement frames. -/
theorem Frame.next_length_le (f : Frame R Q) (st : State R Q) : (f.next st).1.length ≤ 2 := by
  cases f with
  | exec s =>
    cases s with
    | loop x s => cases hn : st.regs x <;> simp [Frame.next, hn]
    | _ => simp [Frame.next]
  | «repeat» s n w => cases n <;> simp [Frame.next]

theorem Config.step_length_le {a b : Config R Q} {c : ℕ} (h : a.step = some (b, c)) :
    b.todo.length ≤ a.todo.length + 1 := by
  cases a with
  | mk todo st =>
    cases todo with
    | nil => simp [Config.step] at h
    | cons f fs =>
      simp only [Config.step, Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩
      have := f.next_length_le st
      simp only [List.length_append, List.length_cons]
      omega

/-- A finite operational trace, with both its step count and its accumulated charge. -/
inductive Steps : Config R Q → ℕ → ℕ → Config R Q → Prop
  | refl (a) : Steps a 0 0 a
  | cons {a b d : Config R Q} {c n k : ℕ} (h : a.step = some (b, c))
      (tail : Steps b n k d) : Steps a (n + 1) (c + k) d

theorem Steps.result {a b : Config R Q} {n c : ℕ} (h : Steps a n c b) :
    a.result = (b.result.1, c + b.result.2) := by
  induction h with
  | refl a => simp
  | cons h tail ih => rw [Config.step_result h, ih]; simp [Nat.add_assoc]

/-- Every control step has positive charge. -/
theorem Steps.length_le_cost {a b : Config R Q} {n c : ℕ} (h : Steps a n c b) : n ≤ c := by
  induction h with
  | refl => exact Nat.le_refl _
  | cons h tail ih => have := Config.step_cost_pos h; omega

theorem Steps.cost_le {a b : Config R Q} {n c : ℕ} (h : Steps a n c b) : c ≤ a.result.2 := by
  rw [h.result]
  exact Nat.le_add_right _ _

theorem Steps.sized {a b : Config R Q} {n c B : ℕ} (h : Steps a n c b)
    (hB : a.state.Sized B) : b.state.Sized (B + c) := by
  induction h generalizing B with
  | refl => simpa using hB
  | cons h tail ih =>
    simpa [Nat.add_assoc] using ih (Config.step_sized h hB)

theorem Steps.config_sized {a b : Config R Q} {n c B : ℕ} (h : Steps a n c b)
    (hB : a.Sized B) : b.Sized (B + c) := by
  induction h generalizing B with
  | refl => simpa using hB
  | cons h tail ih =>
    simpa [Nat.add_assoc] using ih (Config.step_config_sized h hB)

theorem Steps.todo_length_le {a b : Config R Q} {n c : ℕ} (h : Steps a n c b) :
    b.todo.length ≤ a.todo.length + n := by
  induction h with
  | refl => exact Nat.le_add_right _ _
  | cons h tail ih => have := Config.step_length_le h; omega

/-- **Operational execution terminates**, with the exact denotational cost and output. -/
theorem Config.terminates (a : Config R Q) :
    ∃ n, Steps a n a.result.2 ⟨[], a.result.1⟩ ∧ n ≤ a.result.2 := by
  generalize hc : a.result.2 = c
  induction c using Nat.strong_induction_on generalizing a with
  | h c ih =>
    cases hs : a.step with
    | none =>
      have ht := a.step_none_iff.mp hs
      have hr : a.result = (a.state, 0) := by simp [Config.result, ht, runFrames]
      have ha : a = ⟨[], a.state⟩ := by cases a; simp_all
      refine ⟨0, ?_, by omega⟩
      simpa [← hc, hr, ← ha] using Steps.refl a
    | some out =>
      rcases out with ⟨b, charge⟩
      have hr := Config.step_result hs
      have hp := Config.step_cost_pos hs
      have he : a.result.2 = charge + b.result.2 := congrArg Prod.snd hr
      obtain ⟨n, hn, hnc⟩ := ih b.result.2 (by omega) b rfl
      refine ⟨n + 1, ?_, by omega⟩
      have ht := Steps.cons hs hn
      simpa [← hc, hr] using ht

/-- The continuation machine starts with precisely the program's body and initial data. -/
def Prog.start (P : Prog) (l : List ℕ) : Config P.R P.Q := ⟨[.exec P.body], P.init l⟩

theorem Prog.start_result (P : Prog) (l : List ℕ) :
    (P.start l).result = P.body.run (P.init l) := by
  simp [Prog.start, Config.result, runFrames, Frame.run]

theorem Prog.start_sized (P : Prog) (l : List ℕ) : (P.start l).Sized (listSize l) := by
  exact ⟨P.init_sized l, by simp [Prog.start, Frame.Sized]⟩

/-- **Every execution prefix** fits the whole program's cost and data-size budget. -/
theorem Prog.prefix_bound (P : Prog) (l : List ℕ) {n c : ℕ} {a : Config P.R P.Q}
    (h : Steps (P.start l) n c a) :
    n ≤ c ∧ c ≤ P.cost l ∧ a.Sized (listSize l + P.cost l) ∧ a.todo.length ≤ 1 + n := by
  have hc : c ≤ P.cost l := by simpa [P.start_result, Prog.cost] using h.cost_le
  exact ⟨h.length_le_cost, hc, (h.config_sized (P.start_sized l)).mono (by omega),
    by simpa [Prog.start] using h.todo_length_le⟩

/-- A complete execution reaches the program's actual output within its charged cost. -/
theorem Prog.execution (P : Prog) (l : List ℕ) :
    ∃ n st, Steps (P.start l) n (P.cost l) ⟨[], st⟩ ∧
      st.lists P.outL = P.run l ∧ n ≤ P.cost l := by
  obtain ⟨n, hn, hc⟩ := (P.start l).terminates
  rw [P.start_result] at hn hc
  exact ⟨n, _, hn, rfl, hc⟩

end PCP.Lang
