import PCP.Complexity.ThreeColorBasePass
import PCP.Complexity.AmplifiedRound

/-! # Two exact passes construct the physical history and compute the base verdict -/

namespace PCP.Lang.ThreeColorBaseBranches

open PCP.Algebraic ThreeColorFullFieldSampling ThreeColorBasePreflight ThreeColorBaseSetup

def discover : Stmt 400 128 := .seq (.copy 122 123) pass

def replay : Stmt 400 128 := .seq (.copy 103 123) pass

def validProgram : Stmt 400 128 := .seq discover replay

def accept : Stmt 400 128 := .seq (.copy 122 103) (.assign 300 (.const 1))

def select : Stmt 400 128 := .ite 357 accept validProgram

def program : Stmt 400 128 := .seq ThreeColorBasePreflight.program select

theorem ready_setHistory {x bits bs : List Bool} {st : State 400 128}
    (hc : Ready x bits bs st) (qs : List ℕ) : Ready x bits bs (setList st 123 qs) := by
  refine ⟨?_, ?_, (fun i => hc.seeds i), ?_, hc.guard⟩
  · rcases hc.data with ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10⟩
    exact ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10⟩
  · exact ⟨hc.cardinal.vertices, hc.cardinal.pairs, hc.cardinal.proper, hc.cardinal.inner,
      hc.cardinal.affine, hc.cardinal.cubic⟩
  · exact ⟨hc.sources.graph, hc.sources.bits, hc.sources.answers, hc.sources.empty⟩

theorem setHistory_context {x bits bs : List Bool} {st : State 400 128}
    (hc : Ready x bits bs st) (qs : List ℕ) : Context x bits bs qs (setList st 123 qs) :=
  ⟨ready_setHistory hc qs, by simp [setList]⟩

theorem copy_then_state (p : Stmt 400 128) (src dst : Fin 128) (st : State 400 128) :
    ((Stmt.seq (.copy src dst) p).run st).1 =
      (p.run (setList st dst (st.lists src))).1 := rfl

theorem discover_state (st : State 400 128) :
    (discover.run st).1 = (pass.run (setList st 123 (st.lists 122))).1 :=
  copy_then_state pass 122 123 st

theorem replay_state (st : State 400 128) :
    (replay.run st).1 = (pass.run (setList st 123 (st.lists 103))).1 :=
  copy_then_state pass 103 123 st

attribute [local irreducible] pass discover replay

theorem discover_run (x bits bs : List Bool)
    (hv : Valid (ThreeColorBaseSeed.sample (ThreeColorEncoding.vertexCount x) bits))
    (st : State 400 128) (hc : Ready x bits bs st) :
    (discover.run st).1.lists 103 = allQueries (ThreeColorEncoding.vertexCount x) x bits hv ∧
    Ready x bits bs (discover.run st).1 := by
  have hs := pass_run x bits bs (st.lists 122) hv (setList st 123 (st.lists 122))
    (setHistory_context hc _)
  exact (congrArg (fun out : State 400 128 =>
    out.lists 103 = allQueries (ThreeColorEncoding.vertexCount x) x bits hv ∧
    Ready x bits bs out) (discover_state st)).mpr ⟨hs.2.1,hs.2.2.ready⟩

theorem replay_run (x bits bs : List Bool)
    (hv : Valid (ThreeColorBaseSeed.sample (ThreeColorEncoding.vertexCount x) bits))
    (st : State 400 128) (hc : Ready x bits bs st)
    (hq : st.lists 103 = allQueries (ThreeColorEncoding.vertexCount x) x bits hv) :
    (replay.run st).1.regs 300 = (allVerdict (ThreeColorEncoding.vertexCount x) x bits hv
      (allQueries (ThreeColorEncoding.vertexCount x) x bits hv) bs).toNat ∧
    (replay.run st).1.lists 103 = allQueries (ThreeColorEncoding.vertexCount x) x bits hv ∧
    Ready x bits bs (replay.run st).1 := by
  have hs := pass_run x bits bs (st.lists 103) hv (setList st 123 (st.lists 103))
    (setHistory_context hc _)
  have hr : (pass.run (setList st 123 (st.lists 103))).1.regs 300 =
      (allVerdict (ThreeColorEncoding.vertexCount x) x bits hv
        (allQueries (ThreeColorEncoding.vertexCount x) x bits hv) bs).toNat :=
    hs.1.trans (congrArg (fun qs => (allVerdict (ThreeColorEncoding.vertexCount x)
      x bits hv qs bs).toNat) hq)
  exact (congrArg (fun out : State 400 128 =>
    out.regs 300 = (allVerdict (ThreeColorEncoding.vertexCount x) x bits hv
      (allQueries (ThreeColorEncoding.vertexCount x) x bits hv) bs).toNat ∧
    out.lists 103 = allQueries (ThreeColorEncoding.vertexCount x) x bits hv ∧
    Ready x bits bs out) (replay_state st)).mpr ⟨hr,hs.2.1,hs.2.2.ready⟩


theorem validProgram_run (x bits bs : List Bool)
    (hv : Valid (ThreeColorBaseSeed.sample (ThreeColorEncoding.vertexCount x) bits))
    (st : State 400 128) (hc : Ready x bits bs st) :
    (validProgram.run st).1.regs 300 = (allVerdict (ThreeColorEncoding.vertexCount x) x bits hv
      (allQueries (ThreeColorEncoding.vertexCount x) x bits hv) bs).toNat ∧
    (validProgram.run st).1.lists 103 = allQueries (ThreeColorEncoding.vertexCount x) x bits hv ∧
    Ready x bits bs (validProgram.run st).1 := by
  have hd := discover_run x bits bs hv st hc
  rw [validProgram, run_seq_fst]
  exact replay_run x bits bs hv _ hd.2 hd.1

attribute [local irreducible] validProgram

theorem select_valid (x bits bs : List Bool)
    (hv : Valid (ThreeColorBaseSeed.sample (ThreeColorEncoding.vertexCount x) bits))
    (st : State 400 128) (hc : Ready x bits bs st) :
    (select.run st).1.regs 300 = (allVerdict (ThreeColorEncoding.vertexCount x) x bits hv
      (allQueries (ThreeColorEncoding.vertexCount x) x bits hv) bs).toNat ∧
    (select.run st).1.lists 103 = allQueries (ThreeColorEncoding.vertexCount x) x bits hv ∧
    Ready x bits bs (select.run st).1 := by
  have hg : st.regs 357 = 0 := by simpa [hv] using hc.guard
  rw [select, run_ite_fst]
  simp only [hg, ne_eq, not_true_eq_false, ↓reduceIte]
  exact validProgram_run x bits bs hv st hc

theorem accept_frame (st : State 400 128) : Frame st (accept.run st).1 := by
  constructor
  · intro i hi
    simp [accept, Stmt.run, setReg, setList,
      Function.update_of_ne (show i ≠ 300 by omega)]
  · intro L hL hn
    simp [accept, Stmt.run, setReg, setList,
      Function.update_of_ne (show L ≠ 103 by omega)]

theorem select_invalid (x bits bs : List Bool)
    (hv : ¬ Valid (ThreeColorBaseSeed.sample (ThreeColorEncoding.vertexCount x) bits))
    (st : State 400 128) (hc : Ready x bits bs st) :
    (select.run st).1.regs 300 = 1 ∧ (select.run st).1.lists 103 = [] ∧
    Ready x bits bs (select.run st).1 := by
  have hg : st.regs 357 = 1 := by simpa [hv] using hc.guard
  rw [select, run_ite_fst]
  simp only [hg]
  refine ⟨?_, ?_, ready_of_frame hc (accept_frame st)⟩
  · simp [accept, Stmt.run, Expr.eval, setReg]
  · simpa [accept, Stmt.run, setReg, setList] using hc.sources.empty

attribute [local irreducible] select ThreeColorBasePreflight.program

theorem program_valid (x bits bs : List Bool)
    (hv : Valid (ThreeColorBaseSeed.sample (ThreeColorEncoding.vertexCount x) bits))
    (st : State 400 128) (hs : Sources x bits bs st) :
    (program.run st).1.regs 300 = (allVerdict (ThreeColorEncoding.vertexCount x) x bits hv
      (allQueries (ThreeColorEncoding.vertexCount x) x bits hv) bs).toNat ∧
    (program.run st).1.lists 103 = allQueries (ThreeColorEncoding.vertexCount x) x bits hv ∧
    Sources x bits bs (program.run st).1 := by
  rw [program, run_seq_fst]
  have hr := select_valid x bits bs hv _ (ThreeColorBasePreflight.program_run x bits bs st hs)
  exact ⟨hr.1, hr.2.1, hr.2.2.sources⟩

theorem program_invalid (x bits bs : List Bool)
    (hv : ¬ Valid (ThreeColorBaseSeed.sample (ThreeColorEncoding.vertexCount x) bits))
    (st : State 400 128) (hs : Sources x bits bs st) :
    (program.run st).1.regs 300 = 1 ∧ (program.run st).1.lists 103 = [] ∧
    Sources x bits bs (program.run st).1 := by
  rw [program, run_seq_fst]
  have hr := select_invalid x bits bs hv _ (ThreeColorBasePreflight.program_run x bits bs st hs)
  exact ⟨hr.1, hr.2.1, hr.2.2.sources⟩

theorem initial_sources (x bits bs : List Bool) : Sources x bits bs
    (AmplifiedWorkspace.initial (x.map Bool.toNat) (bits.map Bool.toNat) (bs.map Bool.toNat)) := by
  constructor <;> simp [AmplifiedWorkspace.initial]

end PCP.Lang.ThreeColorBaseBranches
