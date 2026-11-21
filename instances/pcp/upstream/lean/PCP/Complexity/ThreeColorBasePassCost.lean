import PCP.Complexity.ThreeColorBasePass

/-! # Charged costs of the fixed branch sequence -/

namespace PCP.Lang.ThreeColorBaseBranches

open PCP.Algebraic ThreeColorFullFieldSampling

theorem multiply_bit_cost (r : Fin 400 → ℕ) (i : Fin 400) (b : Bool)
    (h0 : r 300 ≤ 1) (hi : r i = b.toNat) :
    (Expr.mul 300 i).cost r ≤ 4 := by
  have h : r 300 = 0 ∨ r 300 = 1 := by omega
  rcases h with h | h <;> cases b <;> simp [Expr.cost, Expr.readSize, Expr.eval, h, hi]

attribute [local irreducible] branch

theorem step_cost (i : Fin 7) (x bits bs : List Bool) (qs : List ℕ)
    (hv : Valid (ThreeColorBaseSeed.sample (ThreeColorEncoding.vertexCount x) bits))
    (B : ℕ) (st : State 400 128) (hc : Context x bits bs qs st)
    (ha : st.regs 300 ≤ 1) (hb : ((branch i).run st).2 ≤ B) :
    ((step i).run st).2 ≤ B+5 := by
  have hr := branch_run i x bits bs qs hv st hc
  have hz := branch_accumulator i st
  have hm := multiply_bit_cost ((branch i).run st).1.regs (resultPort i) _
    (hz.trans_le ha) hr.1
  rw [step, run_seq_snd]
  change ((branch i).run st).2+(Expr.mul 300 (resultPort i)).cost
    ((branch i).run st).1.regs+1 ≤ B+5
  omega

theorem step_bit (i : Fin 7) (x bits bs : List Bool) (qs : List ℕ)
    (hv : Valid (ThreeColorBaseSeed.sample (ThreeColorEncoding.vertexCount x) bits))
    (st : State 400 128) (hc : Context x bits bs qs st) (ha : st.regs 300 ≤ 1) :
    ((step i).run st).1.regs 300 ≤ 1 := by
  rw [(step_run i x bits bs qs hv st hc).1]
  have hb : (verdicts (ThreeColorEncoding.vertexCount x) x bits hv qs bs i).toNat ≤ 1 := by
    cases verdicts (ThreeColorEncoding.vertexCount x) x bits hv qs bs i <;> decide
  simpa using Nat.mul_le_mul ha hb

theorem prepare_cost (st : State 400 128) (he : st.lists 122 = []) :
    (prepare.run st).2 = 5 := by
  simp [prepare, Stmt.run, Expr.cost, Expr.readSize, Expr.eval, he, listSize]

theorem finish_cost (st : State 400 128) :
    (finish.run st).2 = 2*listSize (st.lists 124)+3 := by
  simp [finish, Stmt.run, setList, listSize_reverse]
  omega

attribute [local irreducible] step prepare finish

theorem pass_cost (x bits bs : List Bool) (qs : List ℕ)
    (hv : Valid (ThreeColorBaseSeed.sample (ThreeColorEncoding.vertexCount x) bits))
    (B : ℕ) (hB : ∀ i st, Context x bits bs qs st → ((branch i).run st).2 ≤ B)
    (st : State 400 128) (hc : Context x bits bs qs st) :
    (pass.run st).2 ≤ 7*(B+6)+2*listSize
      (allQueries (ThreeColorEncoding.vertexCount x) x bits hv)+11 := by
  let Inv := fun s : State 400 128 => Context x bits bs qs s ∧ s.regs 300 ≤ 1
  have hp : Inv (prepare.run st).1 := by
    refine ⟨hc.of_frame (prepare_frame st), ?_⟩
    simp [prepare, Stmt.run, setReg, Expr.eval]
  have hs := TraceSequence.program_cost step Inv (B+5)
    (fun i s hi => ⟨hi.1.of_frame (step_frame i s), step_bit i x bits bs qs hv s hi.1 hi.2⟩)
    (fun i s hi => step_cost i x bits bs qs hv B s hi.1 hi.2 (hB i s hi.1))
    order (prepare.run st).1 hp
  have ht := TraceSequence.program_run step (Context x bits bs qs) 300 124
    (fun i => (verdicts (ThreeColorEncoding.vertexCount x) x bits hv qs bs i).toNat)
    (querySegments (ThreeColorEncoding.vertexCount x) x bits hv)
    (fun i s hi => step_run i x bits bs qs hv s hi) order (prepare.run st).1 hp.1
  have hl : (prepare.run st).1.lists 124 = [] := by
    simpa [prepare, Stmt.run, setReg, setList] using hc.ready.sources.empty
  rw [hl, List.append_nil] at ht
  have hf := finish_cost ((TraceSequence.program step order).run (prepare.run st).1).1
  rw [ht.2.1, listSize_reverse] at hf
  have hprep := prepare_cost st hc.ready.sources.empty
  rw [show order.length = 7 by simp [order]] at hs
  rw [pass, run_seq_snd, run_seq_snd, hprep, hf]
  change _ ≤ 7*(B+6)+2*listSize (order.flatMap _)+11
  omega

end PCP.Lang.ThreeColorBaseBranches
