/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Complexity.InnerSeedMaterialize

/-! # Assembly of the actual selector context from materialized inner seeds -/

namespace PCP.Lang.InnerSeed

open PCP.Algebraic ThreeColorSeedIndex InterpolationBranch

variable {t n m : ℕ} [NeZero t]

-- The terminal loader is a fixed sequence of scalar and list copies.
set_option maxRecDepth 4096

def finalize : Stmt 140 44 := .seq (.assign 80 (.var 120))
  (.seq (.assign 81 (.var 122))
  (.seq (.assign 82 (.const 0))
  (.seq (.assign 100 (.var 109))
  (.seq (.assign 119 (.var 108))
  (.seq (.assign 83 (.var 123))
  (.seq (.assign 84 (.var 124))
  (.seq (.assign 85 (.var 125))
  (.seq (.assign 86 (.var 126))
  (.seq (.assign 87 (.var 127))
  (.seq (.assign 88 (.var 128))
  (.seq (.assign 89 (.var 129))
  (.seq (.assign 90 (.var 130))
  (.seq (.assign 91 (.var 131))
  (.seq (.assign 110 (.var 123))
  (.seq (.assign 111 (.var 124))
  (.seq (.assign 112 (.var 125))
  (.seq (.assign 113 (.var 126))
  (.seq (.assign 114 (.var 127))
  (.seq (.assign 115 (.var 128))
  (.seq (.assign 116 (.var 129))
  (.seq (.assign 117 (.var 130))
  (.seq (.assign 118 (.var 131))
  (.seq (.copy 40 3)
  (.seq (.copy 41 7)
  ((.copy 42 35))))))))))))))))))))))))))

theorem finalize_frame (st : State 140 44) : Frame st (finalize.run st).1 :=
  frame_of_writes finalize (by decide) (by decide) st

theorem finalize_data (s : InnerBranch.Seed t m) (st : State 140 44) (hd : Data s st) :
    Data s (finalize.run st).1 := by
  intro i
  exact (run_regs_frame finalize (dataPort i) (by
    fin_cases i <;> decide) st).trans (hd i)

omit [NeZero t] in
theorem finalize_stored (s : InnerBranch.Seed t m) (st : State 140 44)
    (hs : Stored s st) (he : st.lists 41 = []) : Stored s (finalize.run st).1 := by
  rcases hs.hadamard with ⟨h20, h56, _, hb, ha, hl, hf⟩
  refine ⟨⟨(run_regs_frame finalize 20 (by decide) st).trans h20,
    (run_regs_frame finalize 56 (by decide) st).trans h56,
    ?_, (run_lists_frame finalize 20 (by decide) st).trans hb,
    (run_lists_frame finalize 21 (by decide) st).trans ha,
    (run_lists_frame finalize 22 (by decide) st).trans hl,
    (run_lists_frame finalize 23 (by decide) st).trans hf⟩,
    (run_lists_frame finalize 32 (by decide) st).trans hs.left,
    (run_lists_frame finalize 33 (by decide) st).trans hs.right,
    (run_lists_frame finalize 34 (by decide) st).trans hs.label⟩
  simpa [finalize, rowState, State.restrict, Stmt.run, Function.update] using he

def selectorState (st : State 140 44) : State 120 40 :=
  st.restrict (Fin.castLE (by decide)) (Fin.castLE (by decide))

theorem finalize_prefix (i : Fin 9) (st : State 140 44) :
    (finalize.run st).1.regs ⟨83+i.val, by omega⟩ = st.regs (prefixPort i) ∧
      (finalize.run st).1.regs ⟨110+i.val, by omega⟩ = st.regs (prefixPort i) := by
  fin_cases i <;> simp [finalize, Stmt.run, Expr.eval, prefixPort, Function.update]

omit [NeZero t] in
theorem location_prefix (site : StandardCorrection.Site (Field t) n) (x : Point t m)
    (i : Fin 9) :
    ((InnerBranch.location site x).payload (t := t) (BinaryFieldCode.fieldEquiv t))
      i.castSucc = site.prefix (BinaryFieldCode.fieldEquiv t)
      (2 ^ BooleanCoefficientIndex.dimension t 1)
      (2 ^ BooleanCoefficientIndex.dimension t 3) m i := by
  cases site <;> fin_cases i <;> rfl

omit [NeZero t] in
theorem location_point (site : StandardCorrection.Site (Field t) n) (x : Point t m) :
    ((InnerBranch.location site x).payload (t := t) (BinaryFieldCode.fieldEquiv t)) 9 =
      (ThreeColorQueryIndex.innerIndex (BinaryFieldCode.fieldEquiv t) m 4 x).val := by
  cases site <;> rfl

set_option maxHeartbeats 800000 in
-- The fixed prefix copies are checked coordinate by coordinate.
theorem finalize_run (a : Fin 5 → Field t) (site : StandardCorrection.Site (Field t) n)
    (s : InnerBranch.Seed t m) (st : State 140 44) (hp : Public m a site st)
    (hd : Data s st) (hs : Stored s st) :
    InnerBranch.Context a site s (selectorState (finalize.run st).1) := by
  have hcoin : st.regs 109 = s.1.toNat := by
    have h := hd 6
    have hb : ∀ b : Bool, (boolCodec.equiv b).val = b.toNat := by
      intro b; cases b <;> rfl
    exact h.trans (hb s.1)
  have hx : st.regs 108 =
      (ThreeColorQueryIndex.innerIndex (BinaryFieldCode.fieldEquiv t) m 4 s.2.1.1).val :=
    (hd 5).trans (pointCode_eq s.2.1.1)
  have hstored := finalize_stored s st hs hp.empty
  constructor
  · simpa [selectorState, State.restrict, finalize, Stmt.run, Expr.eval, Function.update]
      using hcoin
  · exact hstored.hadamard
  · intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · change _ = ((InnerBranch.location site s.2.1.1).payload
        (t := t) (BinaryFieldCode.fieldEquiv t)) 9
      rw [location_point]
      simpa [selectorState, State.restrict, InnerBranch.hadRegs, HadamardRow.payloadReg,
        finalize, Stmt.run, Expr.eval, Function.update] using hx
    · rw [location_prefix]
      have h := (finalize_prefix j st).2.trans (hp.address j)
      fin_cases j <;> exact h
  · refine ⟨?_, ?_, ?_, ?_, ?_, hstored.left, hstored.right, hstored.label, ?_, ?_⟩
    · simpa [selectorState, State.restrict, InnerBranch.interpRegs, finalize,
        Stmt.run, Expr.eval, Function.update] using hp.width
    · simpa [selectorState, State.restrict, InnerBranch.interpRegs, finalize,
        Stmt.run, Expr.eval, Function.update] using hp.card
    · simpa [selectorState, State.restrict, InnerBranch.interpRegs, finalize,
        Stmt.run, Expr.eval, Function.update] using (FieldExpression.code_zero (t := t)).symm
    · simpa [selectorState, State.restrict, finalize, Stmt.run, Function.update] using hp.modulus
    · exact hstored.hadamard.2.2.1
    · simpa [selectorState, State.restrict, finalize, Stmt.run, Function.update] using hp.nodes
    · intro i
      exact (finalize_prefix i st).1.trans (hp.address i)

end PCP.Lang.InnerSeed
