import PCP.Complexity.ThreeColorSeedGuardResources

/-! Charged cost of extracting one whole-field correction parameter. -/

set_option maxRecDepth 1024

namespace PCP.Lang.ThreeColorSeedGuard

open PCP.Algebraic ThreeColorSeedIndex ThreeColorFullFieldSampling ThreeColorBaseSetup

variable {F : Type*} [Field F] [Algebra (ZMod 2) F] {t d m : ℕ}
variable (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2))

omit [Field F] [Algebra (ZMod 2) F] in
theorem popParameter_cost (dst : Fin 400) (st : State 400 128) :
    ((popParameter dst).run st).2 ≤ 2 * listSize (st.lists 1) + 7 := by
  generalize h : st.lists 1 = l
  rcases l with _ | ⟨a,l⟩
  · simp [popParameter, Stmt.run, Function.update, h, listSize]
  rcases l with _ | ⟨b,l⟩
  · simp [popParameter, Stmt.run, Function.update, h, listSize]; omega
  rcases l with _ | ⟨c,l⟩
  · simp [popParameter, Stmt.run, Function.update, h, listSize]; omega
  simp [popParameter, Stmt.run, Function.update, h, listSize]
  omega

def callLoadConstant (src : Fin 400) : ℕ :=
  (loadCall src).C * ((loadCall src).width + (loadCall src).csize + 1)

def readCallConstant (src : Fin 400) : ℕ :=
  2 * callLoadConstant src + 1156 * ComputedSeed.programConstant NestedSeed.callTerms + 42

attribute [local irreducible] callDecoder callLoadConstant

/-- Only actual input values are bounded; all decoder and parser work is charged. -/
theorem readCall_cost (s : RawCallSeed F (Fin d ⊕ Fin d) m 4 t)
    (src dst : Fin 400) (st : State 400 128) (W : ℕ)
    (hd : st.regs 370 = d) (hm : st.regs 322 = m) (ht : st.regs 324 = t)
    (he : st.lists 122 = []) (hsrc : 350 ≤ src.val)
    (hs : st.regs src = ((callCodec ρ ((Codec.fin d).sum (Codec.fin d)) m 4).equiv s).val)
    (hW : t + 2 * d + m + 2 ^ t +
      Nat.size ((callCodec ρ ((Codec.fin d).sum (Codec.fin d)) m 4).equiv s).val + 5 ≤ W) :
    ((readCall src dst).run st).2 ≤ readCallConstant src * W^4 := by
  let code := ((callCodec ρ ((Codec.fin d).sum (Codec.fin d)) m 4).equiv s).val
  have hq := Nat.two_pow_pos t
  have hw : 1 ≤ W := by omega
  have hlin : W ≤ W^2 := Nat.le_pow (by decide)
  have hsq : W^2 ≤ W^4 := Nat.pow_le_pow_right hw (by decide)
  have h4 : 1 ≤ W^4 := Nat.one_le_pow _ _ hw
  have hload : ((loadCall src).run st).2 ≤ callLoadConstant src * (W + 1) := by
    unfold callLoadConstant
    apply loopFree_cost_le (loadCall src) (by simp [loadCall, Stmt.loopFree]) st W
    · intro i hi
      have hi' : i = 370 ∨ i = 322 ∨ i = 324 ∨ i = src := by
        have hi'' : i = 370 ∨ i = 322 ∨ i = 324 ∨
            i = src ∧ i ≠ 310 ∧ i ≠ 0 ∧ i ≠ 1 ∧ i ≠ 2 ∧ i ≠ 3 := by
          simpa [loadCall, Stmt.uses, Stmt.mustW, Expr.uses] using hi
        tauto
      rcases hi' with rfl | rfl | rfl | rfl
      · rw [hd]; exact (size_le_self _).trans (by omega)
      · rw [hm]; exact (size_le_self _).trans (by omega)
      · rw [ht]; exact (size_le_self _).trans (by omega)
      · rw [hs]; omega
    · intro L hL
      have hl : L = 122 := by simpa [loadCall, Stmt.lUses] using hL
      rw [hl,he]; exact Nat.zero_le _
  have hparam : ∀ i : Fin 4, Nat.size (![d + d,m,4,t] i) ≤ W := by
    intro i
    fin_cases i
    · exact (size_le_self _).trans (by dsimp; omega)
    · exact (size_le_self _).trans (by dsimp; omega)
    · exact (size_le_self _).trans (by dsimp; omega)
    · exact (size_le_self _).trans (by dsimp; omega)
  have hterms : ∀ i, (NestedSeed.callTerms i).eval ![d + d,m,4,t] ≤ 32 * W^2 := by
    intro i
    exact (callTerms_bound t d m i).trans (Nat.mul_le_mul_left _
      (Nat.pow_le_pow_left (by omega) 2))
  have hdec := ComputedSeed.program_cost NestedSeed.callTerms (d + d) m 4 t code (32 * W^2) W
    _ (loadCall_context ρ s src st hd hm ht he hsrc hs) hparam hterms (by dsimp [code]; omega)
  change (NestedSeed.call.run _).2 ≤ _ at hdec
  rw [← call_result (by decide) (by decide) NestedSeed.call] at hdec
  rw [← callDecoder] at hdec
  have harg : 32 * W^2 + W + 1 ≤ 34 * W^2 := by nlinarith only [hlin,hw]
  have hdec' := hdec.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left harg 2))
  have hout := NestedSeed.call_run ρ ((Codec.fin d).sum (Codec.fin d)) (d + d) m 4 rfl s _
    (loadCall_context ρ s src st hd hm ht he hsrc hs)
  rw [← call_result (by decide) (by decide) NestedSeed.call] at hout
  have hout' : (callDecoder.run ((loadCall src).run st).1).1.lists 1 = callCodes ρ s := by
    unfold callDecoder callCodes
    exact hout
  have hp := popParameter_cost dst (callDecoder.run ((loadCall src).run st).1).1
  rw [hout'] at hp
  have hsize := callCodes_size ρ s
  have hcode : Nat.size ((callCodec ρ ((Codec.fin d).sum (Codec.fin d)) m 4).equiv s).val ≤ W := by
    omega
  have hp' : ((popParameter dst).run (callDecoder.run ((loadCall src).run st).1).1).2 ≤
      40 * W^4 := by
    nlinarith only [hp,hsize,hcode,hlin,hsq,h4]
  simp only [readCall,run_seq_snd]
  unfold readCallConstant
  nlinarith only [hload,hdec',hp',hw,hlin,hsq,h4]

end PCP.Lang.ThreeColorSeedGuard
