/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Complexity.InnerSeedState

/-! # Exact extraction of the seven actual inner seed cells -/

namespace PCP.Lang.InnerSeed

open PCP.Algebraic ThreeColorSeedIndex InterpolationBranch

variable {t n m : ℕ} [NeZero t]

def prepare : Stmt 140 44 := .seq (.assign 0 (.const 0))
  (.seq (.assign 1 (.var 121)) (.seq (.assign 2 (.const 4))
    (.seq (.assign 3 (.var 120)) (.seq (.assign 15 (.var 132)) (.copy 41 3)))))

def decoder : Stmt 140 44 := call (by decide) (by decide) NestedSeed.inner

def decode : Stmt 140 44 := .seq prepare decoder

theorem prepare_frame (st : State 140 44) : Frame st (prepare.run st).1 :=
  frame_of_writes prepare (by decide) (by decide) st

theorem prepare_context (s : InnerBranch.Seed t m) (st : State 140 44)
    (ht : st.regs 120 = t) (hm : st.regs 121 = m) (he : st.lists 41 = [])
    (hs : st.regs 132 = ((innerCodec (BinaryMaterializedField.coordinates t) m 4).equiv s).val) :
    ComputedSeed.Context 0 m 4 t
      ((innerCodec (BinaryMaterializedField.coordinates t) m 4).equiv s).val
      ((prepare.run st).1.restrict (Fin.castLE (by decide)) (Fin.castLE (by decide))) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i
    fin_cases i <;> simp [prepare, Stmt.run, Expr.eval, Function.update, State.restrict, ht, hm]
  · simpa [prepare, Stmt.run, Expr.eval, Function.update, State.restrict] using hs
  · simpa [prepare, Stmt.run, Expr.eval, Function.update, State.restrict] using he

theorem decode_run (s : InnerBranch.Seed t m) (st : State 140 44)
    (ht : st.regs 120 = t) (hm : st.regs 121 = m) (he : st.lists 41 = [])
    (hs : st.regs 132 = ((innerCodec (BinaryMaterializedField.coordinates t) m 4).equiv s).val) :
    (decode.run st).1.lists 1 = List.ofFn (codes s) := by
  have hc := prepare_context s st ht hm he hs
  have h := NestedSeed.inner_run (BinaryMaterializedField.coordinates t) 0 m 4 s _ hc
  rw [← call_result (by decide) (by decide) NestedSeed.inner (prepare.run st).1] at h
  simpa only [decode, decoder, run_seq_fst, State.restrict_lists,
    show Fin.castLE (by decide : 4 ≤ 44) (1 : Fin 4) = (1 : Fin 44) from rfl,
    codes, List.ofFn_succ, List.ofFn_zero, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Function.comp_def] using h

theorem decode_frame (st : State 140 44) : Frame st (decode.run st).1 :=
  (prepare_frame st).trans (call_frame (by decide) (by decide) NestedSeed.inner _)

def parse : Stmt 140 44 := .seq (.copy 1 39)
  (.seq (.pop 39 103 102) (.seq (.pop 39 104 102) (.seq (.pop 39 105 102)
    (.seq (.pop 39 106 102) (.seq (.pop 39 107 102) (.seq (.pop 39 108 102)
      (.pop 39 109 102)))))))

theorem parse_run (s : InnerBranch.Seed t m) (st : State 140 44)
    (hc : st.lists 1 = List.ofFn (codes s)) : Data s (parse.run st).1 := by
  intro i
  fin_cases i <;> simp [parse, Stmt.run, Function.update, hc, codes, dataPort,
    List.ofFn_succ]

theorem parse_frame (st : State 140 44) : Frame st (parse.run st).1 :=
  frame_of_writes parse (by decide) (by decide) st

def unpack : Stmt 140 44 := .seq decode parse

theorem unpack_run (a : Fin 5 → Field t) (site : StandardCorrection.Site (Field t) n)
    (s : InnerBranch.Seed t m) (st : State 140 44) (hc : Public m a site st)
    (hs : st.regs 132 = ((innerCodec (BinaryMaterializedField.coordinates t) m 4).equiv s).val) :
    Data s (unpack.run st).1 ∧ Public m a site (unpack.run st).1 ∧
      Frame st (unpack.run st).1 := by
  have h := decode_run s st hc.width hc.base hc.empty hs
  have hf := (decode_frame st).trans (parse_frame (decode.run st).1)
  exact ⟨parse_run s _ h, hc.of_frame hf, hf⟩

end PCP.Lang.InnerSeed
