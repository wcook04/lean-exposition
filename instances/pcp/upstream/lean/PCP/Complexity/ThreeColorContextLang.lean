import PCP.Complexity.ThreeColorParameterLang
import PCP.Complexity.ProductionGridLang

/-!
# Preparing the production verifier's stored dimensions

Register 42 contains the decoded public graph order. The exact least admissible
exponent, common grid/dimension size, volume, and field width are stored outside
the arithmetic workspace. No field object is supplied by the caller.
-/

namespace PCP.Lang.ThreeColorContext

open PCP.Algebraic ThreeColorParameterChoice ThreeColorParameters

def parameterRegs : Fin 8 → Fin 50 := Fin.castAdd 42
def parameterLists : Fin 0 → Fin 15 := Fin.elim0

def parameters : Stmt 50 15 :=
  ThreeColorParameter.program.rename parameterRegs parameterLists

def saveParameters : Stmt 50 15 :=
  .seq (.assign 43 (.var 5)) (.seq (.assign 44 (.var 6))
    (.seq (.assign 45 (.var 7)) (.seq (.assign 8 (.const 12))
      (.seq (.assign 9 (.mul 8 43)) (.seq (.assign 10 (.const 32))
        (.seq (.assign 46 (.add 9 10)) (.assign 20 (.var 46))))))))

def metadata : Stmt 50 15 := .seq (.assign 0 (.var 42)) (.seq parameters saveParameters)

/-- Permanent scalar metadata, outside every arithmetic subprogram's allocation. -/
def Metadata (N : ℕ) (st : State 50 15) : Prop :=
  st.regs 42 = N ∧ st.regs 43 = exponent N ∧
    st.regs 44 = size (exponent N) ∧ st.regs 45 = volume N ∧
    st.regs 46 = binaryDimension (exponent N)

theorem parameters_run (st : State 50 15) :
    ThreeColorParameter.Represents (st.regs 0) (exponent (st.regs 0))
      (((parameters.run st).1).restrict parameterRegs parameterLists) := by
  have hp := congrArg Prod.fst (ThreeColorParameter.program.run_rename
    parameterRegs parameterLists (Fin.castAdd_injective _ _)
    (Function.injective_of_subsingleton _) st)
  dsimp only [Prod.fst] at hp
  rw [parameters, hp]
  exact ThreeColorParameter.program_run _

theorem metadata_run (N : ℕ) (st : State 50 15) (hN : st.regs 42 = N) :
    Metadata N (metadata.run st).1 ∧
      (metadata.run st).1.regs 20 = binaryDimension (exponent N) := by
  let s := setReg st 0 N
  have hp := parameters_run s
  have h42 := run_regs_frame parameters 42 (by decide) s
  have hs0 : s.regs 0 = N := by simp [s]
  have hs42 : s.regs 42 = N := by simp [s, Function.update, hN]
  simp only [ThreeColorParameter.Represents, State.restrict_regs, hs0] at hp
  obtain ⟨_, _, _, h5, h6, h7⟩ := hp
  change (parameters.run s).1.regs 5 = exponent N at h5
  change (parameters.run s).1.regs 6 = 2 ^ exponent N at h6
  change (parameters.run s).1.regs 7 = exponent N * 2 ^ exponent N at h7
  rw [hs42] at h42
  simp only [metadata, run_seq_fst, run_assign_fst, Expr.eval, hN]
  change Metadata N (saveParameters.run (parameters.run s).1).1 ∧ _
  generalize hu : (parameters.run s).1 = u at *
  simp [Metadata, saveParameters, Stmt.run, Expr.eval, Function.update,
    h5, h6, h7, h42, size, volume, binaryDimension_eq]

/-- Metadata construction preserves every stored input list. -/
theorem metadata_lists (st : State 50 15) (L : Fin 15) :
    (metadata.run st).1.lists L = st.lists L := by
  apply run_lists_frame
  simp [metadata, parameters, saveParameters, ThreeColorParameter.program,
    ThreeColorParameter.logarithm, ThreeColorParameter.select, ThreeColorParameter.setup,
    ThreeColorParameter.body, Clog.program, Clog.setup, Clog.body, Stmt.listWrites]

end PCP.Lang.ThreeColorContext
