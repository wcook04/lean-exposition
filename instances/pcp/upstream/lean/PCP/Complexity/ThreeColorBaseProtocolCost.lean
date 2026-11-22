import PCP.Complexity.ThreeColorBaseProtocol
import PCP.Complexity.ThreeColorBasePassCost
import PCP.Complexity.ThreeColorBasePreflightCost

/-! # Exact charged bounds for discovery and history replay -/

namespace PCP.Lang.ThreeColorBaseBranches

open PCP.Algebraic ThreeColorFullFieldSampling ThreeColorBasePreflight ThreeColorBaseSetup

theorem copy_then_cost (p : Stmt 400 128) (src dst : Fin 128) (st : State 400 128) :
    ((Stmt.seq (.copy src dst) p).run st).2 =
      listSize (st.lists src)+(p.run (setList st dst (st.lists src))).2+2 := by
  rw [run_seq_snd, run_copy_snd, run_copy_fst]
  omega

theorem discover_charge (st : State 400 128) :
    (discover.run st).2 = listSize (st.lists 122)+
      (pass.run (setList st 123 (st.lists 122))).2+2 :=
  copy_then_cost pass 122 123 st

theorem replay_charge (st : State 400 128) :
    (replay.run st).2 = listSize (st.lists 103)+
      (pass.run (setList st 123 (st.lists 103))).2+2 :=
  copy_then_cost pass 103 123 st

attribute [local irreducible] pass

theorem discover_cost (x bits bs : List Bool)
    (hv : Valid (ThreeColorBaseSeed.sample (ThreeColorEncoding.vertexCount x) bits))
    (B : ℕ) (hB : ∀ i s, Context x bits bs [] s → ((branch i).run s).2 ≤ B)
    (st : State 400 128) (hc : Ready x bits bs st) :
    (discover.run st).2 ≤ 7*(B+6)+2*listSize
      (allQueries (ThreeColorEncoding.vertexCount x) x bits hv)+13 := by
  have hu : Context x bits bs [] (setList st 123 (st.lists 122)) :=
    ⟨ready_setHistory hc _, by simpa [setList] using hc.sources.empty⟩
  have h := pass_cost x bits bs [] hv B hB _ hu
  have hcharge := discover_charge st
  have hsize : listSize (st.lists 122) = 0 := by rw [hc.sources.empty]; rfl
  omega

theorem replay_cost (x bits bs : List Bool)
    (hv : Valid (ThreeColorBaseSeed.sample (ThreeColorEncoding.vertexCount x) bits))
    (B : ℕ) (hB : ∀ i s, Context x bits bs
      (allQueries (ThreeColorEncoding.vertexCount x) x bits hv) s → ((branch i).run s).2 ≤ B)
    (st : State 400 128) (hc : Ready x bits bs st)
    (hq : st.lists 103 = allQueries (ThreeColorEncoding.vertexCount x) x bits hv) :
    (replay.run st).2 ≤ 7*(B+6)+3*listSize
      (allQueries (ThreeColorEncoding.vertexCount x) x bits hv)+13 := by
  have hu : Context x bits bs (allQueries (ThreeColorEncoding.vertexCount x) x bits hv)
      (setList st 123 (st.lists 103)) :=
    ⟨ready_setHistory hc _, by simpa [setList] using hq⟩
  have h := pass_cost x bits bs _ hv B hB _ hu
  have hcharge := replay_charge st
  have hsize := congrArg listSize hq
  omega

attribute [local irreducible] discover replay

theorem validProgram_cost (x bits bs : List Bool)
    (hv : Valid (ThreeColorBaseSeed.sample (ThreeColorEncoding.vertexCount x) bits))
    (B₀ B₁ : ℕ) (h₀ : ∀ i s, Context x bits bs [] s → ((branch i).run s).2 ≤ B₀)
    (h₁ : ∀ i s, Context x bits bs
      (allQueries (ThreeColorEncoding.vertexCount x) x bits hv) s → ((branch i).run s).2 ≤ B₁)
    (st : State 400 128) (hc : Ready x bits bs st) :
    (validProgram.run st).2 ≤ 7*(B₀+B₁)+5*listSize
      (allQueries (ThreeColorEncoding.vertexCount x) x bits hv)+111 := by
  have hd := discover_cost x bits bs hv B₀ h₀ st hc
  have hr := discover_run x bits bs hv st hc
  rw [validProgram, run_seq_snd]
  generalize hu : (discover.run st).1 = u at hr ⊢
  have hh := replay_cost x bits bs hv B₁ h₁ u hr.2 hr.1
  omega

theorem accept_cost (st : State 400 128) (he : st.lists 122 = []) :
    (accept.run st).2 = 5 := by
  simp [accept, Stmt.run, Expr.cost, Expr.readSize, Expr.eval, listSize, he]

attribute [local irreducible] validProgram accept

theorem select_cost (x bits bs : List Bool) (B : ℕ)
    (hB : ∀ (_hv : Valid (ThreeColorBaseSeed.sample (ThreeColorEncoding.vertexCount x) bits))
      s, Ready x bits bs s → (validProgram.run s).2 ≤ B)
    (st : State 400 128) (hc : Ready x bits bs st) :
    (select.run st).2 ≤ B+7 := by
  classical
  by_cases hv : Valid (ThreeColorBaseSeed.sample (ThreeColorEncoding.vertexCount x) bits)
  · have hg : st.regs 357 = 0 := by simpa [hv] using hc.guard
    have h := hB hv st hc
    simp only [select, Stmt.run, hg, ne_eq, not_true_eq_false, ↓reduceIte, Nat.size_zero]
    omega
  · have hg : st.regs 357 = 1 := by simpa [hv] using hc.guard
    have h := accept_cost st hc.sources.empty
    simp only [select, Stmt.run, hg, Nat.size_one]
    change (accept.run st).2+1+1 ≤ B+7
    omega

attribute [local irreducible] select ThreeColorBasePreflight.program

theorem program_cost_bound (x bits bs : List Bool) (B : ℕ)
    (hB : ∀ (_hv : Valid (ThreeColorBaseSeed.sample (ThreeColorEncoding.vertexCount x) bits))
      s, Ready x bits bs s → (validProgram.run s).2 ≤ B)
    (st : State 400 128) (hs : Sources x bits bs st) :
    (program.run st).2 ≤ ThreeColorBasePreflight.costConstant*(x.length+bits.length+1)^84+B+8 := by
  have hp := ThreeColorBasePreflight.program_cost x bits bs st hs
  have hr := ThreeColorBasePreflight.program_run x bits bs st hs
  rw [program, run_seq_snd]
  generalize hu : (ThreeColorBasePreflight.program.run st).1 = u at hr ⊢
  have hc := select_cost x bits bs B hB u hr
  omega

end PCP.Lang.ThreeColorBaseBranches
