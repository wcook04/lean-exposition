import PCP.Complexity.NumericDifferenceState

/-! # Decode the actual difference sampler into three stored numeric cells -/

namespace PCP.Lang.NumericDifference

open PCP.Algebraic ThreeColorSeedIndex BinaryFieldCode

variable {t n m : ℕ} [NeZero t]

def prepare : Stmt 120 40 := .seq (.assign 0 (.var 101))
  (.seq (.assign 1 (.var 102)) (.seq (.assign 2 (.const 4))
    (.seq (.assign 3 (.var 100)) (.seq (.assign 15 (.var 108)) (.copy 32 3)))))

def decoder : Stmt 120 40 := call (by decide) (by decide) NestedSeed.difference

def decode : Stmt 120 40 := .seq prepare decoder

theorem prepare_frame (st : State 120 40) : Frame st (prepare.run st).1 :=
  frame_of_writes prepare (by decide) (by decide) st

theorem prepare_context (s : Sample t n) (qs : List ℕ) (bs : List Bool)
    (st : State 120 40) (hp : Public (t := t) n m qs bs st)
    (hs : st.regs 108 = ((seedCodec t n).equiv s).val) :
    ComputedSeed.Context n m 4 t ((seedCodec t n).equiv s).val
      ((prepare.run st).1.restrict (Fin.castLE (by decide)) (Fin.castLE (by decide))) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i
    fin_cases i <;> simp [prepare, Stmt.run, Expr.eval, Function.update, State.restrict,
      hp.width, hp.base, hp.dimension]
  · simpa [prepare, Stmt.run, Expr.eval, Function.update, State.restrict] using hs
  · simpa [prepare, Stmt.run, Expr.eval, Function.update, State.restrict] using hp.empty

theorem point_code (p : Fin n → Field t) :
    (((Codec.fin n).function (fieldCodec (BinaryMaterializedField.coordinates t))).equiv p).val =
      (ThreeColorQueryIndex.vertexIndex (fieldEquiv t) n p).val := by
  unfold Codec.function Codec.fin
  rw [UniformDecode.fieldCodec_materialized]
  rfl

theorem decode_run (s : Sample t n) (qs : List ℕ) (bs : List Bool)
    (st : State 120 40) (hp : Public (t := t) n m qs bs st)
    (hs : st.regs 108 = ((seedCodec t n).equiv s).val) :
    (decode.run st).1.lists 1 = List.ofFn (codes s) ++ [0, 0, 0, 0] := by
  have h := NestedSeed.difference_run (BinaryMaterializedField.coordinates t) n m 4 s _
    (prepare_context s qs bs st hp hs)
  rw [← call_result (by decide) (by decide) NestedSeed.difference (prepare.run st).1] at h
  simpa only [decode, decoder, run_seq_fst, State.restrict_lists,
    show Fin.castLE (by decide : 4 ≤ 40) (1 : Fin 4) = (1 : Fin 40) from rfl,
    codes, List.ofFn_succ, List.ofFn_zero, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Function.comp_def, List.cons_append, List.nil_append, point_code] using h

theorem decode_frame (st : State 120 40) : Frame st (decode.run st).1 :=
  (prepare_frame st).trans (call_frame (by decide) (by decide) NestedSeed.difference _)

def parse : Stmt 120 40 := .seq (.copy 1 31)
  (.seq (.pop 31 90 89) (.seq (.pop 31 91 89) (.pop 31 92 89)))

omit [NeZero t] in
theorem parse_run (s : Sample t n) (st : State 120 40)
    (hc : st.lists 1 = List.ofFn (codes s) ++ [0, 0, 0, 0]) : Data s (parse.run st).1 := by
  intro i
  fin_cases i <;> simp [parse, Stmt.run, Function.update, hc, codes, dataPort, List.ofFn_succ]

theorem parse_frame (st : State 120 40) : Frame st (parse.run st).1 :=
  frame_of_writes parse (by decide) (by decide) st

def unpack : Stmt 120 40 := .seq decode parse

theorem unpack_run (s : Sample t n) (qs : List ℕ) (bs : List Bool)
    (st : State 120 40) (hp : Public (t := t) n m qs bs st)
    (hs : st.regs 108 = ((seedCodec t n).equiv s).val) :
    Data s (unpack.run st).1 ∧ Public (t := t) n m qs bs (unpack.run st).1 ∧
      Frame st (unpack.run st).1 := by
  have h := decode_run s qs bs st hp hs
  have hf := (decode_frame st).trans (parse_frame (decode.run st).1)
  exact ⟨parse_run s _ h, hp.of_frame hf, hf⟩

end PCP.Lang.NumericDifference
