import PCP.Complexity.ThreeColorBaseBranchSemantics
import PCP.Complexity.LangTraceSequence

/-! # The fixed seven-way production verifier pass -/

namespace PCP.Lang.ThreeColorBaseBranches

open PCP.Algebraic ThreeColorFullFieldSampling

def step (i : Fin 7) : Stmt 400 128 :=
  .seq (branch i) (.assign 300 (.mul 300 (resultPort i)))

def order : List (Fin 7) := List.ofFn id

def prepare : Stmt 400 128 := .seq (.copy 122 124) (.assign 300 (.const 1))

def finish : Stmt 400 128 := .seq (.rev 124) (.copy 124 103)

def pass : Stmt 400 128 := .seq prepare (.seq (TraceSequence.program step order) finish)

def allQueries (N : ℕ) (x bits : List Bool)
    (hv : Valid (ThreeColorBaseSeed.sample N bits)) : List ℕ :=
  order.flatMap (querySegments N x bits hv)

def allVerdict (N : ℕ) (x bits : List Bool)
    (hv : Valid (ThreeColorBaseSeed.sample N bits)) (qs : List ℕ) (bs : List Bool) : Bool :=
  order.all (verdicts N x bits hv qs bs)

theorem Frame.setReg300 (st : State 400 128) (v : ℕ) : Frame st (setReg st 300 v) := by
  constructor
  · intro i hi
    simp [setReg, Function.update_of_ne (show i ≠ 300 by omega)]
  · intro L hL hn
    rfl

theorem prepare_frame (st : State 400 128) : Frame st (prepare.run st).1 := by
  constructor
  · intro i hi
    simp [prepare, Stmt.run, setReg, setList,
      Function.update_of_ne (show i ≠ 300 by omega)]
  · intro L hL hn
    simp [prepare, Stmt.run, setReg, setList, Function.update_of_ne hn]

theorem finish_frame (st : State 400 128) : Frame st (finish.run st).1 := by
  constructor
  · intro i hi
    rfl
  · intro L hL hn
    simp [finish, Stmt.run, setList, Function.update_of_ne hn,
      Function.update_of_ne (show L ≠ 103 by omega)]

attribute [local irreducible] branch

theorem step_frame (i : Fin 7) (st : State 400 128) : Frame st ((step i).run st).1 := by
  rw [step, run_seq_fst, run_assign_fst]
  exact (branch_frame i st).trans (Frame.setReg300 _ _)

theorem step_run (i : Fin 7) (x bits bs : List Bool) (qs : List ℕ)
    (hv : Valid (ThreeColorBaseSeed.sample (ThreeColorEncoding.vertexCount x) bits))
    (st : State 400 128) (hc : Context x bits bs qs st) :
    ((step i).run st).1.regs 300 = st.regs 300 *
      (verdicts (ThreeColorEncoding.vertexCount x) x bits hv qs bs i).toNat ∧
    ((step i).run st).1.lists 124 =
      (querySegments (ThreeColorEncoding.vertexCount x) x bits hv i).reverse ++ st.lists 124 ∧
    Context x bits bs qs ((step i).run st).1 := by
  have hr := branch_run i x bits bs qs hv st hc
  have hf := hc.of_frame (step_frame i st)
  rw [step, run_seq_fst, run_assign_fst] at hf ⊢
  refine ⟨?_, ?_, hf⟩
  · simp only [Expr.eval, setReg,
      Function.update_self]
    rw [hr.1, branch_accumulator]
  · exact hr.2

theorem prod_toNat {A : Type*} (xs : List A) (f : A → Bool) :
    (xs.map (fun i => (f i).toNat)).prod = (xs.all f).toNat := by
  induction xs with
  | nil => rfl
  | cons a as ih =>
      simp only [List.map_cons, List.prod_cons, List.all_cons, ih]
      cases f a <;> cases as.all f <;> rfl

attribute [local irreducible] step

theorem pass_run (x bits bs : List Bool) (qs : List ℕ)
    (hv : Valid (ThreeColorBaseSeed.sample (ThreeColorEncoding.vertexCount x) bits))
    (st : State 400 128) (hc : Context x bits bs qs st) :
    (pass.run st).1.regs 300 =
      (allVerdict (ThreeColorEncoding.vertexCount x) x bits hv qs bs).toNat ∧
    (pass.run st).1.lists 103 = allQueries (ThreeColorEncoding.vertexCount x) x bits hv ∧
    Context x bits bs qs (pass.run st).1 := by
  have hp := hc.of_frame (prepare_frame st)
  have ha : (prepare.run st).1.regs 300 = 1 := by
    simp [prepare, Stmt.run, setReg, Expr.eval]
  have hl : (prepare.run st).1.lists 124 = [] := by
    simpa [prepare, Stmt.run, setReg, setList] using hc.ready.sources.empty
  have hs := TraceSequence.program_run step (Context x bits bs qs) 300 124
    (fun i => (verdicts (ThreeColorEncoding.vertexCount x) x bits hv qs bs i).toNat)
    (querySegments (ThreeColorEncoding.vertexCount x) x bits hv)
    (fun i s hi => step_run i x bits bs qs hv s hi) order (prepare.run st).1 hp
  rw [ha, hl, one_mul, List.append_nil, prod_toNat] at hs
  rw [pass, run_seq_fst, run_seq_fst]
  refine ⟨?_, ?_, hs.2.2.of_frame (finish_frame _)⟩
  · simpa only [finish, run_seq_fst, run_rev_fst, run_copy_fst, setList, allVerdict] using hs.1
  · simp [finish, Stmt.run, setList, hs.2.1, allQueries]

end PCP.Lang.ThreeColorBaseBranches
