import PCP.Complexity.ThreeColorBaseSeed

/-! Extracting the actual whole-field correction parameter before issuing any query. -/

set_option maxRecDepth 1024

namespace PCP.Lang.ThreeColorSeedGuard

open PCP.Algebraic ThreeColorSeedIndex ThreeColorFullFieldSampling ThreeColorBaseSetup

/-- `370` stores the derived branch dimension; the call's point dimension is twice that. -/
def loadCall (src : Fin 400) : Stmt 400 128 :=
  .seq (.assign 310 (.const 2)) (.seq (.assign 0 (.mul 310 370))
    (.seq (.assign 1 (.var 322)) (.seq (.assign 2 (.const 4))
      (.seq (.assign 3 (.var 324)) (.seq (.assign 15 (.var src)) (.copy 122 3))))))

def callDecoder : Stmt 400 128 :=
  ThreeColorBaseSetup.call (by decide) (by decide) NestedSeed.call

def popParameter (dst : Fin 400) : Stmt 400 128 := .seq (.copy 1 99)
  (.seq (.pop 99 319 318) (.seq (.pop 99 319 318) (.pop 99 dst 318)))

def readCall (src dst : Fin 400) : Stmt 400 128 :=
  .seq (loadCall src) (.seq callDecoder (popParameter dst))

attribute [local irreducible] callDecoder NestedSeed.call

variable {F : Type*} [Field F] [Algebra (ZMod 2) F] {t n m : ℕ}

variable (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2))

theorem loadCall_context (s : RawCallSeed F (Fin n ⊕ Fin n) m 4 t)
    (src : Fin 400) (st : State 400 128) (hd : st.regs 370 = n)
    (hm : st.regs 322 = m) (ht : st.regs 324 = t) (he : st.lists 122 = [])
    (hsrc : 350 ≤ src.val)
    (hs : st.regs src = ((callCodec ρ ((Codec.fin n).sum (Codec.fin n)) m 4).equiv s).val) :
    ComputedSeed.Context (n+n) m 4 t
      ((callCodec ρ ((Codec.fin n).sum (Codec.fin n)) m 4).equiv s).val
      (((loadCall src).run st).1.restrict (Fin.castLE (by decide)) (Fin.castLE (by decide))) := by
  have hne : src ≠ 0 ∧ src ≠ 1 ∧ src ≠ 2 ∧ src ≠ 3 ∧ src ≠ 310 := by omega
  refine ⟨?_, ?_, ?_⟩
  · intro i
    fin_cases i <;> simp [loadCall, Stmt.run, Expr.eval, Function.update,
      State.restrict, hd, hm, ht, two_mul]
  · simpa [loadCall, Stmt.run, Expr.eval, Function.update, State.restrict,
      hne.1, hne.2.1, hne.2.2.1, hne.2.2.2.1, hne.2.2.2.2] using hs
  · simpa [loadCall, Stmt.run, Expr.eval, Function.update, State.restrict] using he

theorem popParameter_run (dst : Fin 400) (hd : dst ≠ 318) (a b z : ℕ)
    (rest : List ℕ) (st : State 400 128) (hl : st.lists 1 = a::b::z::rest) :
    ((popParameter dst).run st).1.regs dst = z := by
  simp [popParameter, Stmt.run, Function.update, hl, hd]

theorem readCall_run (s : RawCallSeed F (Fin n ⊕ Fin n) m 4 t)
    (src dst : Fin 400) (st : State 400 128) (hd : st.regs 370 = n)
    (hm : st.regs 322 = m) (ht : st.regs 324 = t) (he : st.lists 122 = [])
    (hsrc : 350 ≤ src.val) (hdst : dst ≠ 318)
    (hs : st.regs src = ((callCodec ρ ((Codec.fin n).sum (Codec.fin n)) m 4).equiv s).val) :
    ((readCall src dst).run st).1.regs dst = ((fieldCodec ρ).equiv s.2.1).val := by
  have h := NestedSeed.call_run ρ ((Codec.fin n).sum (Codec.fin n)) (n+n) m 4 rfl s _
    (loadCall_context ρ s src st hd hm ht he hsrc hs)
  rw [← call_result (by decide) (by decide) NestedSeed.call ((loadCall src).run st).1] at h
  have h' : (callDecoder.run ((loadCall src).run st).1).1.lists 1 =
      [(innerCodec ρ m 4).equiv s.2.2.2 |>.val,
       (innerPointCodec ρ m 4).equiv s.2.2.1 |>.val,
       (fieldCodec ρ).equiv s.2.1 |>.val,
       (((Codec.fin n).sum (Codec.fin n)).function (fieldCodec ρ)).equiv s.1 |>.val, 0, 0, 0] := by
    unfold callDecoder
    exact h
  simp only [readCall, run_seq_fst]
  exact popParameter_run dst hdst _ _ _ _ _ h'

omit [Field F] [Algebra (ZMod 2) F] in
theorem readCall_reg (src dst i : Fin 400) (hi : 320 ≤ i.val) (hne : i ≠ dst)
    (st : State 400 128) : ((readCall src dst).run st).1.regs i = st.regs i := by
  simp only [readCall, run_seq_fst]
  rw [run_regs_frame (popParameter dst) i (by
    simp [popParameter, Stmt.regWrites, hne]
    omega)]
  rw [show (callDecoder.run ((loadCall src).run st).1).1.regs i =
      ((loadCall src).run st).1.regs i from by
    unfold callDecoder
    exact call_reg (by decide) (by decide) NestedSeed.call _ i (by omega)]
  exact run_regs_frame (loadCall src) i (by
    simp [loadCall, Stmt.regWrites]
    omega) st

omit [Field F] [Algebra (ZMod 2) F] in
theorem readCall_list (src dst : Fin 400) (L : Fin 128) (hL : 100 ≤ L.val)
    (st : State 400 128) : ((readCall src dst).run st).1.lists L = st.lists L := by
  simp only [readCall, run_seq_fst]
  rw [run_lists_frame (popParameter dst) L (by simp [popParameter, Stmt.listWrites]; omega)]
  rw [show (callDecoder.run ((loadCall src).run st).1).1.lists L =
      ((loadCall src).run st).1.lists L from by
    unfold callDecoder
    exact call_list (by decide) (by decide) NestedSeed.call _ L (by omega)]
  exact run_lists_frame (loadCall src) L (by simp [loadCall, Stmt.listWrites]; omega) st

end PCP.Lang.ThreeColorSeedGuard
