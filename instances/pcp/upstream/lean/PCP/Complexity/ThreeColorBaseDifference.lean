import PCP.Complexity.ThreeColorBaseCardinal
import PCP.Complexity.ThreeColorBaseSeed
import PCP.Complexity.NumericDifferenceCost

/-! # The concrete difference-consistency branch in the complete verifier workspace -/

set_option maxRecDepth 1024

namespace PCP.Lang.ThreeColorBaseDifference

open PCP.Algebraic ThreeColorParameterChoice ThreeColorParameters ThreeColorBaseSetup

def sample (N : ℕ) (bits : List Bool) :
    NumericDifference.Sample (binaryDimension (exponent N)) (size (exponent N)) :=
  ThreeColorBaseSeed.sample N bits 6

def load : Stmt 400 128 :=
  .seq (.assign 100 (.var 324)) (.seq (.assign 101 (.var 322))
  (.seq (.assign 102 (.var 322)) (.seq (.assign 103 (.var 325))
  (.seq (.assign 104 (.var 328)) (.seq (.assign 105 (.var 329))
  (.seq (.assign 106 (.var 332)) (.seq (.assign 107 (.var 333))
  (.seq (.assign 108 (.var 356)) (.seq (.copy 122 32)
  (.seq (.copy 123 33) (.copy 102 34)))))))))))

def branch : Stmt 400 128 := call (by decide) (by decide) NumericDifference.program

def finish : Stmt 400 128 := .seq (.assign 307 (.var 13)) (.revApp 24 124)

def program : Stmt 400 128 := .seq load (.seq branch finish)

attribute [local irreducible] branch NumericDifference.program

theorem load_public (N : ℕ) (qs : List ℕ) (bs : List Bool) (st : State 400 128)
    (hd : Data N st)
    (hc : ThreeColorBaseCardinal.Cardinal (binaryDimension (exponent N))
      (size (exponent N)) st) (hq : st.lists 123 = qs) (hb : st.lists 102 = bs.map Bool.toNat) :
    NumericDifference.Public (t := binaryDimension (exponent N))
      (size (exponent N)) (size (exponent N)) qs bs
      ((load.run st).1.restrict (Fin.castLE (by decide)) (Fin.castLE (by decide))) := by
  constructor
  all_goals dsimp [load, Stmt.run, Expr.eval, Function.update, State.restrict]
  all_goals simp only [hd.width, hd.dimension, hd.card, hd.empty, hc.vertices, hc.pairs,
    hc.affine, hc.cubic, hq, hb]

theorem load_seed (N : ℕ) (bits : List Bool) (st : State 400 128)
    (hs : ThreeColorBaseSeed.Seeds N bits st) :
    (load.run st).1.regs 108 = ((NumericDifference.seedCodec
      (binaryDimension (exponent N)) (size (exponent N))).equiv (sample N bits)).val := by
  have h := hs 6
  change st.regs 356 = _ at h
  have hc : ThreeColorBaseSeed.codes N bits 6 = ((NumericDifference.seedCodec
      (binaryDimension (exponent N)) (size (exponent N))).equiv (sample N bits)).val := rfl
  simpa only [load, run_seq_fst, run_assign_fst, run_copy_fst, Expr.eval, setList_regs,
    setReg_regs, Function.update_self,
    Function.update_of_ne (by decide : (356 : Fin 400) ≠ 100),
    Function.update_of_ne (by decide : (356 : Fin 400) ≠ 101),
    Function.update_of_ne (by decide : (356 : Fin 400) ≠ 102),
    Function.update_of_ne (by decide : (356 : Fin 400) ≠ 103),
    Function.update_of_ne (by decide : (356 : Fin 400) ≠ 104),
    Function.update_of_ne (by decide : (356 : Fin 400) ≠ 105),
    Function.update_of_ne (by decide : (356 : Fin 400) ≠ 106),
    Function.update_of_ne (by decide : (356 : Fin 400) ≠ 107)] using h.trans hc

theorem branch_run (N : ℕ) (bits : List Bool) (qs : List ℕ) (bs : List Bool)
    (st : State 400 128) (hd : Data N st)
    (hc : ThreeColorBaseCardinal.Cardinal (binaryDimension (exponent N))
      (size (exponent N)) st) (hs : ThreeColorBaseSeed.Seeds N bits st)
    (hq : st.lists 123 = qs) (hb : st.lists 102 = bs.map Bool.toNat) :
    (branch.run (load.run st).1).1.lists 24 =
      NumericDifference.queries (size (exponent N)) (sample N bits) ∧
    (branch.run (load.run st).1).1.regs 13 =
      (NumericDifference.verdict (size (exponent N)) (sample N bits) qs bs).toNat := by
  have h := NumericDifference.program_run (sample N bits) qs bs _
    (load_public N qs bs st hd hc hq hb) (load_seed N bits st hs)
  rw [← call_result (by decide) (by decide) NumericDifference.program (load.run st).1] at h
  unfold branch
  exact ⟨h.1, h.2.1⟩

theorem program_run (N : ℕ) (bits : List Bool) (qs : List ℕ) (bs : List Bool)
    (st : State 400 128) (hd : Data N st)
    (hc : ThreeColorBaseCardinal.Cardinal (binaryDimension (exponent N))
      (size (exponent N)) st) (hs : ThreeColorBaseSeed.Seeds N bits st)
    (hq : st.lists 123 = qs) (hb : st.lists 102 = bs.map Bool.toNat) :
    (program.run st).1.regs 307 =
      (NumericDifference.verdict (size (exponent N)) (sample N bits) qs bs).toNat ∧
    (program.run st).1.lists 124 =
      (NumericDifference.queries (size (exponent N)) (sample N bits)).reverse ++ st.lists 124 := by
  have h := NumericDifference.program_run (sample N bits) qs bs _
    (load_public N qs bs st hd hc hq hb) (load_seed N bits st hs)
  rw [← call_result (by decide) (by decide) NumericDifference.program (load.run st).1] at h
  change ((call (by decide) (by decide) NumericDifference.program).run
    (load.run st).1).1.lists 24 = _ ∧
    ((call (by decide) (by decide) NumericDifference.program).run
    (load.run st).1).1.regs 13 = _ ∧ _ at h
  rw [show call (by decide) (by decide) NumericDifference.program = branch by
    unfold branch; rfl] at h
  have h124 : (branch.run (load.run st).1).1.lists 124 = st.lists 124 := by
    unfold branch
    rw [call_list (by decide) (by decide) NumericDifference.program _ 124 (by decide)]
    rfl
  generalize hu : (branch.run (load.run st).1).1 = u at *
  simp [program, hu, finish, Stmt.run, Expr.eval, Function.update, h.1, h.2.1, h124]

theorem program_reg (i : Fin 400) (hi : 300 ≤ i.val) (hne : i ≠ 307) (st : State 400 128) :
    (program.run st).1.regs i = st.regs i := by
  simp only [program, run_seq_fst]
  rw [run_regs_frame finish i (by simp [finish, Stmt.regWrites, hne])]
  rw [show (branch.run (load.run st).1).1.regs i = (load.run st).1.regs i from by
    unfold branch
    exact call_reg (by decide) (by decide) NumericDifference.program _ i (by omega)]
  exact run_regs_frame load i (by simp [load, Stmt.regWrites]; omega) st

theorem program_list (L : Fin 128) (hL : 100 ≤ L.val) (hne : L ≠ 124) (st : State 400 128) :
    (program.run st).1.lists L = st.lists L := by
  simp only [program, run_seq_fst]
  rw [run_lists_frame finish L (by simp [finish, Stmt.listWrites, hne])]
  rw [show (branch.run (load.run st).1).1.lists L = (load.run st).1.lists L from by
    unfold branch
    exact call_list (by decide) (by decide) NumericDifference.program _ L (by omega)]
  exact run_lists_frame load L (by simp [load, Stmt.listWrites]; omega) st

end PCP.Lang.ThreeColorBaseDifference
