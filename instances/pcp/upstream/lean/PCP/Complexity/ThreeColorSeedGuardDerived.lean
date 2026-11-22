import PCP.Complexity.ThreeColorSeedGuardCall

/-! Extracting both whole-field parameters from one actual derived-grid seed. -/

set_option maxRecDepth 1024

namespace PCP.Lang.ThreeColorSeedGuard

open PCP.Algebraic ThreeColorSeedIndex ThreeColorFullFieldSampling ThreeColorBaseSetup

def loadDerived (factor : ℕ) (src : Fin 400) : Stmt 400 128 :=
  .seq (.assign 310 (.const factor)) (.seq (.assign 370 (.mul 310 322))
    (.seq (.assign 0 (.var 370)) (.seq (.assign 1 (.var 322))
      (.seq (.assign 2 (.const 4)) (.seq (.assign 3 (.var 324))
        (.seq (.assign 15 (.var src)) (.copy 122 3)))))))

def derivedDecoder : Stmt 400 128 :=
  ThreeColorBaseSetup.call (by decide) (by decide) NestedSeed.derived

def popCalls : Stmt 400 128 := .seq (.copy 1 99)
  (.seq (.pop 99 319 318) (.seq (.pop 99 372 318) (.pop 99 371 318)))

def unpackDerived (factor : ℕ) (src : Fin 400) : Stmt 400 128 :=
  .seq (loadDerived factor src) (.seq derivedDecoder popCalls)

def readDerived (factor : ℕ) (src a b : Fin 400) : Stmt 400 128 :=
  .seq (unpackDerived factor src) (.seq (readCall 371 a) (readCall 372 b))

attribute [local irreducible] derivedDecoder NestedSeed.derived readCall

variable {F : Type*} [Field F] [Algebra (ZMod 2) F] {t n : ℕ}
variable (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2))

theorem loadDerived_context (factor : ℕ)
    (s : RawDerivedSample F (factor * n) n 4 t 3) (src : Fin 400) (st : State 400 128)
    (hn : st.regs 322 = n) (ht : st.regs 324 = t) (he : st.lists 122 = [])
    (hsrc : 350 ≤ src.val) (hsrc' : src.val < 357)
    (hs : st.regs src = ((derivedCodec ρ (factor * n) n 4 3).equiv s).val) :
    ComputedSeed.Context (factor * n) n 4 t ((derivedCodec ρ (factor * n) n 4 3).equiv s).val
      (((loadDerived factor src).run st).1.restrict
        (Fin.castLE (by decide)) (Fin.castLE (by decide))) := by
  have hne : src ≠ 0 ∧ src ≠ 1 ∧ src ≠ 2 ∧ src ≠ 3 ∧ src ≠ 310 ∧ src ≠ 370 := by omega
  refine ⟨?_, ?_, ?_⟩
  · intro i
    fin_cases i <;> simp [loadDerived, Stmt.run, Expr.eval, Function.update,
      State.restrict, hn, ht]
  · simpa [loadDerived, Stmt.run, Expr.eval, Function.update, State.restrict,
      hne.1, hne.2.1, hne.2.2.1, hne.2.2.2.1, hne.2.2.2.2.1, hne.2.2.2.2.2] using hs
  · simpa [loadDerived, Stmt.run, Expr.eval, Function.update, State.restrict] using he

theorem unpackDerived_run (factor : ℕ)
    (s : RawDerivedSample F (factor * n) n 4 t 3) (src : Fin 400) (st : State 400 128)
    (hn : st.regs 322 = n) (ht : st.regs 324 = t) (he : st.lists 122 = [])
    (hsrc : 350 ≤ src.val) (hsrc' : src.val < 357)
    (hs : st.regs src = ((derivedCodec ρ (factor * n) n 4 3).equiv s).val) :
    let out := ((unpackDerived factor src).run st).1
    out.regs 370 = factor * n ∧
    out.regs 371 = ((callCodec ρ ((Codec.fin (factor * n)).sum (Codec.fin (factor * n)))
      n 4).equiv s.2.1.2.1).val ∧
    out.regs 372 = ((callCodec ρ ((Codec.fin (factor * n)).sum (Codec.fin (factor * n)))
      n 4).equiv s.2.1.2.2).val := by
  have h := NestedSeed.derived_run ρ (factor * n) n 4 s _
    (loadDerived_context ρ factor s src st hn ht he hsrc hsrc' hs)
  rw [← call_result (by decide) (by decide) NestedSeed.derived
    ((loadDerived factor src).run st).1] at h
  have hd : (derivedDecoder.run ((loadDerived factor src).run st).1).1.regs 370 =
      factor * n := by
    unfold derivedDecoder
    rw [call_reg (by decide) (by decide) NestedSeed.derived _ 370 (by decide)]
    simp [loadDerived, Stmt.run, Expr.eval, Function.update, hn]
  simp only [State.restrict_lists] at h
  rw [← derivedDecoder] at h
  generalize hu : (derivedDecoder.run ((loadDerived factor src).run st).1).1 = u at *
  change u.lists 1 = _ at h
  simp only [unpackDerived, run_seq_fst, hu]
  simp [popCalls, Stmt.run, Function.update, hd, h]

omit [Field F] [Algebra (ZMod 2) F] in
theorem unpackDerived_reg (factor : ℕ) (src i : Fin 400) (hi : 320 ≤ i.val)
    (h0 : i ≠ 370) (h1 : i ≠ 371) (h2 : i ≠ 372) (st : State 400 128) :
    ((unpackDerived factor src).run st).1.regs i = st.regs i := by
  simp only [unpackDerived, run_seq_fst]
  rw [run_regs_frame popCalls i (by simp [popCalls, Stmt.regWrites, h1, h2]; omega)]
  rw [show (derivedDecoder.run ((loadDerived factor src).run st).1).1.regs i =
      ((loadDerived factor src).run st).1.regs i from by
    unfold derivedDecoder
    exact call_reg (by decide) (by decide) NestedSeed.derived _ i (by omega)]
  exact run_regs_frame (loadDerived factor src) i (by
    simp [loadDerived, Stmt.regWrites, h0]
    omega) st

omit [Field F] [Algebra (ZMod 2) F] in
theorem unpackDerived_list (factor : ℕ) (src : Fin 400) (L : Fin 128)
    (hL : 100 ≤ L.val) (st : State 400 128) :
    ((unpackDerived factor src).run st).1.lists L = st.lists L := by
  simp only [unpackDerived, run_seq_fst]
  rw [run_lists_frame popCalls L (by simp [popCalls, Stmt.listWrites]; omega)]
  rw [show (derivedDecoder.run ((loadDerived factor src).run st).1).1.lists L =
      ((loadDerived factor src).run st).1.lists L from by
    unfold derivedDecoder
    exact call_list (by decide) (by decide) NestedSeed.derived _ L (by omega)]
  exact run_lists_frame (loadDerived factor src) L (by
    simp [loadDerived, Stmt.listWrites]
    omega) st

theorem readDerived_run (factor : ℕ) (s : RawDerivedSample F (factor * n) n 4 t 3)
    (src a b : Fin 400) (st : State 400 128)
    (hn : st.regs 322 = n) (ht : st.regs 324 = t) (he : st.lists 122 = [])
    (hsrc : 350 ≤ src.val) (hsrc' : src.val < 357)
    (ha : 360 ≤ a.val) (ha' : a.val < 364) (hb : 360 ≤ b.val) (hb' : b.val < 364)
    (hab : a ≠ b)
    (hs : st.regs src = ((derivedCodec ρ (factor * n) n 4 3).equiv s).val) :
    ((readDerived factor src a b).run st).1.regs a =
      ((fieldCodec ρ).equiv s.2.1.2.1.2.1).val ∧
    ((readDerived factor src a b).run st).1.regs b =
      ((fieldCodec ρ).equiv s.2.1.2.2.2.1).val := by
  have hu := unpackDerived_run ρ factor s src st hn ht he hsrc hsrc' hs
  have hun := (unpackDerived_reg factor src 322 (by decide) (by decide)
    (by decide) (by decide) st).trans hn
  have hut := (unpackDerived_reg factor src 324 (by decide) (by decide)
    (by decide) (by decide) st).trans ht
  have hue := (unpackDerived_list factor src 122 (by decide) st).trans he
  generalize hU : ((unpackDerived factor src).run st).1 = u at *
  have hv := readCall_run ρ s.2.1.2.1 371 a u hu.1 hun hut hue (by decide) (by omega) hu.2.1
  have hvd := (readCall_reg 371 a 370 (by decide) (by omega) u).trans hu.1
  have hvn := (readCall_reg 371 a 322 (by decide) (by omega) u).trans hun
  have hvt := (readCall_reg 371 a 324 (by decide) (by omega) u).trans hut
  have hve := (readCall_list 371 a 122 (by decide) u).trans hue
  have hvc := (readCall_reg 371 a 372 (by decide) (by omega) u).trans hu.2.2
  generalize hV : ((readCall 371 a).run u).1 = v at *
  have hw := readCall_run ρ s.2.1.2.2 372 b v hvd hvn hvt hve (by decide) (by omega) hvc
  have hwa := (readCall_reg 372 b a (by omega) hab v).trans hv
  simp only [readDerived, run_seq_fst, hU, hV]
  exact ⟨hwa, hw⟩

theorem readDerived_run_dim (factor d : ℕ) (hd : factor * n = d) (s : RawDerivedSample F d n 4 t 3)
    (src a b : Fin 400) (st : State 400 128)
    (hn : st.regs 322 = n) (ht : st.regs 324 = t) (he : st.lists 122 = [])
    (hsrc : 350 ≤ src.val) (hsrc' : src.val < 357)
    (ha : 360 ≤ a.val) (ha' : a.val < 364) (hb : 360 ≤ b.val) (hb' : b.val < 364)
    (hab : a ≠ b)
    (hs : st.regs src = ((derivedCodec ρ d n 4 3).equiv s).val) :
    ((readDerived factor src a b).run st).1.regs a =
      ((fieldCodec ρ).equiv s.2.1.2.1.2.1).val ∧
    ((readDerived factor src a b).run st).1.regs b =
      ((fieldCodec ρ).equiv s.2.1.2.2.2.1).val := by
  subst d
  exact readDerived_run ρ factor s src a b st hn ht he hsrc hsrc' ha ha' hb hb' hab hs

omit [Field F] [Algebra (ZMod 2) F] in
theorem readDerived_reg (factor : ℕ) (src a b i : Fin 400) (hi : 320 ≤ i.val)
    (h0 : i ≠ 370) (h1 : i ≠ 371) (h2 : i ≠ 372) (ha : i ≠ a) (hb : i ≠ b)
    (st : State 400 128) : ((readDerived factor src a b).run st).1.regs i = st.regs i := by
  simp only [readDerived, run_seq_fst, readCall_reg _ _ i hi ha, readCall_reg _ _ i hi hb]
  exact unpackDerived_reg factor src i hi h0 h1 h2 st

omit [Field F] [Algebra (ZMod 2) F] in
theorem readDerived_list (factor : ℕ) (src a b : Fin 400) (L : Fin 128)
    (hL : 100 ≤ L.val) (st : State 400 128) :
    ((readDerived factor src a b).run st).1.lists L = st.lists L := by
  simp only [readDerived, run_seq_fst, readCall_list _ _ L hL,
    unpackDerived_list factor src L hL]

end PCP.Lang.ThreeColorSeedGuard
