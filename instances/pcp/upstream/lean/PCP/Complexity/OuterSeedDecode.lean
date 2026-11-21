import PCP.Complexity.OuterSeedState

/-! # Decode and store the actual seven outer sampler cells -/

set_option maxRecDepth 1024

namespace PCP.Lang.OuterSeed

open PCP.Algebraic ThreeColorSeedIndex BinaryFieldCode OuterBranch

variable {t n m : ℕ} [NeZero t]

def prepare : Stmt 180 80 := .seq (.assign 0 (.var 164))
  (.seq (.assign 1 (.var 161)) (.seq (.assign 2 (.const 4))
    (.seq (.assign 3 (.var 160)) (.seq (.assign 15 (.var 171)) (.copy 65 3)))))

def decoder (k : Kind) : Stmt 180 80 := call (by decide) (by decide) (decodeOuter k)

def decode (k : Kind) : Stmt 180 80 := .seq prepare (decoder k)

theorem prepare_frame (st : State 180 80) : Frame st (prepare.run st).1 :=
  frame_of_writes prepare (by decide) (by decide) st

theorem prepare_context (k : Kind) (a : Fin 5 → Field t) (ζ : Field t)
    (s : Sample k t n m) (qs : List ℕ) (bs : List Bool) (st : State 180 80)
    (hp : Public (n := n) (m := m) k a ζ qs bs st)
    (hs : st.regs 171 = ((seedCodec k t n m).equiv s).val) :
    ComputedSeed.Context (k.dimension n) m 4 t ((seedCodec k t n m).equiv s).val
      ((prepare.run st).1.restrict (Fin.castLE (by decide)) (Fin.castLE (by decide))) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i
    fin_cases i <;> simp [prepare, Stmt.run, Expr.eval, Function.update, State.restrict,
      hp.width, hp.base, hp.dimension]
  · simpa [prepare, Stmt.run, Expr.eval, Function.update, State.restrict] using hs
  · simpa [prepare, Stmt.run, Expr.eval, Function.update, State.restrict] using hp.empty

theorem decode_run (k : Kind) (a : Fin 5 → Field t) (ζ : Field t)
    (s : Sample k t n m) (qs : List ℕ) (bs : List Bool) (st : State 180 80)
    (hp : Public (n := n) (m := m) k a ζ qs bs st)
    (hs : st.regs 171 = ((seedCodec k t n m).equiv s).val) :
    ((decode k).run st).1.lists 1 = List.ofFn (codes k s) := by
  have h := decodeOuter_run k s _ (prepare_context k a ζ s qs bs st hp hs)
  rw [← call_result (by decide) (by decide) (decodeOuter k) (prepare.run st).1] at h
  simpa only [decode, decoder, run_seq_fst, State.restrict_lists,
    show Fin.castLE (by decide : 4 ≤ 80) (1 : Fin 4) = (1 : Fin 80) from rfl,
    codes, List.ofFn_succ, List.ofFn_zero, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Function.comp_def] using h

theorem decode_frame (k : Kind) (st : State 180 80) : Frame st ((decode k).run st).1 :=
  (prepare_frame st).trans (call_frame (by decide) (by decide) (decodeOuter k) _)

def parse : Stmt 180 80 := .seq (.copy 1 63)
  (.seq (.pop 63 150 149) (.seq (.pop 63 151 149) (.seq (.pop 63 152 149)
    (.seq (.pop 63 153 149) (.seq (.pop 63 154 149) (.seq (.pop 63 155 149)
      (.pop 63 156 149)))))))

theorem parse_run (k : Kind) (s : Sample k t n m) (st : State 180 80)
    (hc : st.lists 1 = List.ofFn (codes k s)) : Data k s (parse.run st).1 := by
  intro i
  fin_cases i <;> simp [parse, Stmt.run, Function.update, hc, codes, dataPort,
    List.ofFn_succ]

theorem parse_frame (st : State 180 80) : Frame st (parse.run st).1 :=
  frame_of_writes parse (by decide) (by decide) st

def unpack (k : Kind) : Stmt 180 80 := .seq (decode k) parse

theorem unpack_run (k : Kind) (a : Fin 5 → Field t) (ζ : Field t)
    (s : Sample k t n m) (qs : List ℕ) (bs : List Bool) (st : State 180 80)
    (hp : Public (n := n) (m := m) k a ζ qs bs st)
    (hs : st.regs 171 = ((seedCodec k t n m).equiv s).val) :
    Data k s ((unpack k).run st).1 ∧ Public (n := n) (m := m) k a ζ qs bs ((unpack k).run st).1 ∧
      Frame st ((unpack k).run st).1 := by
  have h := decode_run k a ζ s qs bs st hp hs
  have hf := (decode_frame k st).trans (parse_frame ((decode k).run st).1)
  exact ⟨parse_run k s _ h, hp.of_frame hf, hf⟩

end PCP.Lang.OuterSeed
