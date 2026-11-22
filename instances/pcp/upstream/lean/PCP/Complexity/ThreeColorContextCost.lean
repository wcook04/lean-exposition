import PCP.Complexity.ThreeColorContextLang

/-!
# Polynomial charged cost of the production metadata constructor
-/

namespace PCP.Lang.ThreeColorContext

open PCP.Algebraic ThreeColorParameterChoice ThreeColorParameters

def parameterConstant : ℕ :=
  Clog.setup.C * 4 + Clog.body.C * 10 + ThreeColorParameter.setup.C * 12 +
    ThreeColorParameter.passConstant * 33 + 9

def saveConstant : ℕ := saveParameters.C * (saveParameters.width + saveParameters.csize + 1)

theorem parameters_cost (st : State 50 15) :
    (parameters.run st).2 ≤ parameterConstant * (st.regs 0 + 1) ^ 2 := by
  have hc := ThreeColorParameter.program.run_rename_cost parameterRegs parameterLists
    (Fin.castAdd_injective _ _) (Function.injective_of_subsingleton _) st
  change (parameters.run st).2 = _ at hc
  rw [hc]
  exact ThreeColorParameter.program_cost _

theorem saveParameters_cost (N : ℕ) (st : State 50 15)
    (h5 : st.regs 5 = exponent N) (h6 : st.regs 6 = 2 ^ exponent N)
    (h7 : st.regs 7 = volume N) :
    (saveParameters.run st).2 ≤ saveConstant * (32 * (N + 1) + 1) := by
  have hb := ThreeColorParameter.candidate_bound N (exponent N) (exponent_ge_two N) le_rfl
  apply loopFree_cost_le saveParameters (by decide) st
  · intro r hr
    have hr' : r = 5 ∨ r = 6 ∨ r = 7 := by
      simpa [saveParameters, Stmt.uses, Stmt.mustW, Expr.uses] using hr
    rcases hr' with rfl | rfl | rfl
    · rw [h5]
      exact (size_le_self _).trans hb.1
    · rw [h6]
      exact (size_le_self _).trans hb.2.1
    · rw [h7]
      exact (size_le_self _).trans hb.2.2
  · intro L hL
    simp [saveParameters, Stmt.lUses] at hL

def metadataConstant : ℕ := parameterConstant + 33 * saveConstant + 5

theorem metadata_cost (N : ℕ) (st : State 50 15) (hN : st.regs 42 = N) :
    (metadata.run st).2 ≤ metadataConstant * (N + 1) ^ 2 := by
  let s := setReg st 0 N
  have hs0 : s.regs 0 = N := by simp [s]
  have hp := parameters_run s
  have hc := parameters_cost s
  rw [hs0] at hp hc
  simp only [ThreeColorParameter.Represents, State.restrict_regs] at hp
  obtain ⟨_, _, _, h5, h6, h7⟩ := hp
  change (parameters.run s).1.regs 5 = exponent N at h5
  change (parameters.run s).1.regs 6 = 2 ^ exponent N at h6
  change (parameters.run s).1.regs 7 = volume N at h7
  have ht := saveParameters_cost N (parameters.run s).1 h5 h6 h7
  have hn := size_le_self N
  simp only [metadata, run_seq_snd, run_assign_fst, Expr.eval, hN]
  change (Expr.var 42).cost st.regs + ((parameters.run s).2 +
    (saveParameters.run (parameters.run s).1).2 + 1) + 1 ≤ _
  simp only [Expr.cost, Expr.readSize, Expr.eval, hN]
  dsimp only [metadataConstant]
  nlinarith [Nat.zero_le (saveConstant * N * (N + 1)),
    Nat.zero_le (parameterConstant * N * (N + 1))]

end PCP.Lang.ThreeColorContext
