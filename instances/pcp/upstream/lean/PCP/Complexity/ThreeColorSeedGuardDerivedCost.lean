import PCP.Complexity.ThreeColorSeedGuardCallCost

/-! Charged cost of the two correction parameters in one derived-grid seed. -/

set_option maxRecDepth 1024

namespace PCP.Lang.ThreeColorSeedGuard

open PCP.Algebraic ThreeColorSeedIndex ThreeColorFullFieldSampling ThreeColorBaseSetup

variable {F : Type*} [Field F] [Algebra (ZMod 2) F] {t n : ℕ}
variable (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2))

omit [Field F] [Algebra (ZMod 2) F] in
theorem popCalls_cost (st : State 400 128) :
    (popCalls.run st).2 ≤ 2 * listSize (st.lists 1) + 7 := by
  generalize h : st.lists 1 = l
  rcases l with _ | ⟨a,l⟩
  · simp [popCalls, Stmt.run, Function.update, h, listSize]
  rcases l with _ | ⟨b,l⟩
  · simp [popCalls, Stmt.run, Function.update, h, listSize]; omega
  rcases l with _ | ⟨c,l⟩
  · simp [popCalls, Stmt.run, Function.update, h, listSize]; omega
  simp [popCalls, Stmt.run, Function.update, h, listSize]
  omega

def derivedLoadConstant (factor : ℕ) (src : Fin 400) : ℕ :=
  (loadDerived factor src).C * ((loadDerived factor src).width + (loadDerived factor src).csize + 1)

def unpackDerivedConstant (factor : ℕ) (src : Fin 400) : ℕ :=
  2 * derivedLoadConstant factor src +
    1156 * ComputedSeed.programConstant NestedSeed.derivedTerms + 42

def readDerivedConstant (factor : ℕ) (src : Fin 400) : ℕ :=
  unpackDerivedConstant factor src + readCallConstant 371 + readCallConstant 372 + 2

attribute [local irreducible] derivedDecoder derivedLoadConstant readCall

theorem unpackDerived_cost (factor : ℕ) (s : RawDerivedSample F (factor * n) n 4 t 3)
    (src : Fin 400) (st : State 400 128) (W : ℕ)
    (hn : st.regs 322 = n) (ht : st.regs 324 = t) (he : st.lists 122 = [])
    (hsrc : 350 ≤ src.val) (hsrc' : src.val < 357)
    (hs : st.regs src = ((derivedCodec ρ (factor * n) n 4 3).equiv s).val)
    (hW : t + 2 * (factor * n) + n + 2 ^ t +
      Nat.size ((derivedCodec ρ (factor * n) n 4 3).equiv s).val + 5 ≤ W) :
    ((unpackDerived factor src).run st).2 ≤ unpackDerivedConstant factor src * W^4 := by
  let code := ((derivedCodec ρ (factor * n) n 4 3).equiv s).val
  have hq := Nat.two_pow_pos t
  have hw : 1 ≤ W := by omega
  have hlin : W ≤ W^2 := Nat.le_pow (by decide)
  have hsq : W^2 ≤ W^4 := Nat.pow_le_pow_right hw (by decide)
  have h4 : 1 ≤ W^4 := Nat.one_le_pow _ _ hw
  have hload : ((loadDerived factor src).run st).2 ≤ derivedLoadConstant factor src * (W + 1) := by
    unfold derivedLoadConstant
    apply loopFree_cost_le (loadDerived factor src) (by simp [loadDerived, Stmt.loopFree]) st W
    · intro i hi
      have hi' : i = 322 ∨ i = 324 ∨ i = src := by
        have hi'' : i = 322 ∨ i = 324 ∨ i = src ∧ i ≠ 310 ∧ i ≠ 370 ∧
            i ≠ 0 ∧ i ≠ 1 ∧ i ≠ 2 ∧ i ≠ 3 := by
          simpa [loadDerived, Stmt.uses, Stmt.mustW, Expr.uses] using hi
        tauto
      rcases hi' with rfl | rfl | rfl
      · rw [hn]; exact (size_le_self _).trans (by omega)
      · rw [ht]; exact (size_le_self _).trans (by omega)
      · rw [hs]; omega
    · intro L hL
      have hl : L = 122 := by simpa [loadDerived, Stmt.lUses] using hL
      rw [hl,he]; exact Nat.zero_le _
  have hparam : ∀ i : Fin 4, Nat.size (![factor * n,n,4,t] i) ≤ W := by
    intro i
    fin_cases i <;> exact (size_le_self _).trans (by dsimp; omega)
  have hterms : ∀ i, (NestedSeed.derivedTerms i).eval ![factor * n,n,4,t] ≤ 32 * W^2 := by
    intro i
    exact (derivedTerms_bound t (factor * n) n i).trans (Nat.mul_le_mul_left _
      (Nat.pow_le_pow_left (by omega) 2))
  have hdec := ComputedSeed.program_cost NestedSeed.derivedTerms
    (factor * n) n 4 t code (32 * W^2) W
    _ (loadDerived_context ρ factor s src st hn ht he hsrc hsrc' hs) hparam hterms
    (by dsimp [code]; omega)
  change (NestedSeed.derived.run _).2 ≤ _ at hdec
  rw [← call_result (by decide) (by decide) NestedSeed.derived, ← derivedDecoder] at hdec
  have harg : 32 * W^2 + W + 1 ≤ 34 * W^2 := by nlinarith only [hlin,hw]
  have hdec' := hdec.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left harg 2))
  have hout := NestedSeed.derived_run ρ (factor * n) n 4 s _
    (loadDerived_context ρ factor s src st hn ht he hsrc hsrc' hs)
  rw [← call_result (by decide) (by decide) NestedSeed.derived] at hout
  have hout' : (derivedDecoder.run ((loadDerived factor src).run st).1).1.lists 1 =
      derivedCodes ρ s := by
    unfold derivedDecoder derivedCodes
    exact hout
  have hp := popCalls_cost (derivedDecoder.run ((loadDerived factor src).run st).1).1
  rw [hout'] at hp
  have hsize := derivedCodes_size ρ s
  have hcode : Nat.size ((derivedCodec ρ (factor * n) n 4 3).equiv s).val ≤ W := by omega
  have hp' : (popCalls.run (derivedDecoder.run ((loadDerived factor src).run st).1).1).2 ≤
      40 * W^4 := by
    nlinarith only [hp,hsize,hcode,hlin,hsq,h4]
  simp only [unpackDerived,run_seq_snd]
  unfold unpackDerivedConstant
  nlinarith only [hload,hdec',hp',hw,hlin,hsq,h4]

theorem readDerived_cost (factor : ℕ) (s : RawDerivedSample F (factor * n) n 4 t 3)
    (src a b : Fin 400) (st : State 400 128) (W : ℕ)
    (hn : st.regs 322 = n) (ht : st.regs 324 = t) (he : st.lists 122 = [])
    (hsrc : 350 ≤ src.val) (hsrc' : src.val < 357)
    (ha : 360 ≤ a.val) (ha' : a.val < 364)
    (hs : st.regs src = ((derivedCodec ρ (factor * n) n 4 3).equiv s).val)
    (hW : t + 2 * (factor * n) + n + 2 ^ t +
      Nat.size ((derivedCodec ρ (factor * n) n 4 3).equiv s).val + 5 ≤ W) :
    ((readDerived factor src a b).run st).2 ≤ readDerivedConstant factor src * W^4 := by
  have huc := unpackDerived_cost ρ factor s src st W hn ht he hsrc hsrc' hs hW
  have hu := unpackDerived_run ρ factor s src st hn ht he hsrc hsrc' hs
  have hun := (unpackDerived_reg factor src 322 (by decide) (by decide)
    (by decide) (by decide) st).trans hn
  have hut := (unpackDerived_reg factor src 324 (by decide) (by decide)
    (by decide) (by decide) st).trans ht
  have hue := (unpackDerived_list factor src 122 (by decide) st).trans he
  have hsize1 := derived_code_size ρ s
    ((callCodec ρ ((Codec.fin (factor * n)).sum (Codec.fin (factor * n))) n 4).equiv
      s.2.1.2.1).val (by simp [derivedCodes])
  have hsize2 := derived_code_size ρ s
    ((callCodec ρ ((Codec.fin (factor * n)).sum (Codec.fin (factor * n))) n 4).equiv
      s.2.1.2.2).val (by simp [derivedCodes])
  generalize hU : ((unpackDerived factor src).run st).1 = u at *
  have hv := readCall_cost ρ s.2.1.2.1 371 a u W hu.1 hun hut hue (by decide) hu.2.1 (by omega)
  have hvd := (readCall_reg 371 a 370 (by decide) (by omega) u).trans hu.1
  have hvn := (readCall_reg 371 a 322 (by decide) (by omega) u).trans hun
  have hvt := (readCall_reg 371 a 324 (by decide) (by omega) u).trans hut
  have hve := (readCall_list 371 a 122 (by decide) u).trans hue
  have hvc := (readCall_reg 371 a 372 (by decide) (by omega) u).trans hu.2.2
  generalize hV : ((readCall 371 a).run u).1 = v at *
  have hw := readCall_cost ρ s.2.1.2.2 372 b v W hvd hvn hvt hve (by decide) hvc (by omega)
  have hq := Nat.two_pow_pos t
  have h4 : 1 ≤ W^4 := Nat.one_le_pow _ _ (by omega)
  simp only [readDerived,run_seq_snd,hU,hV]
  unfold readDerivedConstant
  nlinarith only [huc,hv,hw,h4]

theorem readDerived_cost_dim (factor d : ℕ) (hd : factor * n = d)
    (s : RawDerivedSample F d n 4 t 3) (src a b : Fin 400) (st : State 400 128) (W : ℕ)
    (hn : st.regs 322 = n) (ht : st.regs 324 = t) (he : st.lists 122 = [])
    (hsrc : 350 ≤ src.val) (hsrc' : src.val < 357) (ha : 360 ≤ a.val) (ha' : a.val < 364)
    (hs : st.regs src = ((derivedCodec ρ d n 4 3).equiv s).val)
    (hW : t + 2 * d + n + 2 ^ t + Nat.size ((derivedCodec ρ d n 4 3).equiv s).val + 5 ≤ W) :
    ((readDerived factor src a b).run st).2 ≤ readDerivedConstant factor src * W^4 := by
  subst d
  exact readDerived_cost ρ factor s src a b st W hn ht he hsrc hsrc' ha ha' hs hW

end PCP.Lang.ThreeColorSeedGuard
