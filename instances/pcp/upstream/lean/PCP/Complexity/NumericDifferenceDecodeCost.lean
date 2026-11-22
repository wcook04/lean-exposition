import PCP.Complexity.NumericDifferenceResources

/-! # Charged polynomial cost of actual numeric difference-seed extraction -/

set_option maxRecDepth 1024

namespace PCP.Lang.NumericDifference

open PCP.Algebraic ThreeColorSeedIndex BinaryFieldCode

variable {t n m : ℕ} [NeZero t]

theorem differenceTerms_bound (t n m : ℕ) (i : Fin 7) :
    (NestedSeed.differenceTerms i).eval ![n,m,4,t] ≤ (t+n+m+2^t+1)^2 := by
  have hq := Nat.two_pow_pos t
  fin_cases i <;>
    simp [NestedSeed.differenceTerms, NestedSeed.pointBits_eval, ArithmeticExpression.Term.eval]
  all_goals nlinarith only [hq,Nat.zero_le (t^2),Nat.zero_le (n^2),Nat.zero_le (m^2),
    Nat.zero_le ((2^t)^2),Nat.zero_le (t*n),Nat.zero_le (t*m),Nat.zero_le (t*2^t),
    Nat.zero_le (n*m),Nat.zero_le (n*2^t),Nat.zero_le (m*2^t)]

def unpackConstant : ℕ := fixedConstant prepare +
  4*ComputedSeed.programConstant (NestedSeed.differenceTerms)+30

omit [NeZero t] in
theorem parse_cost (s : Sample t n) (st : State 120 40)
    (hc : st.lists 1 = List.ofFn (codes s) ++ [0, 0, 0, 0]) :
    (parse.run st).2 = 2*listSize (List.ofFn (codes s))+8 := by
  simp [parse, Stmt.run, Function.update, hc, List.ofFn_succ, listSize]
  ring

theorem unpack_cost (s : Sample t n) (qs : List ℕ) (bs : List Bool) (W : ℕ) (st : State 120 40)
    (hp : Public (t := t) n m qs bs st) (hb : SourceBound W st)
    (hs : st.regs 108 = ((seedCodec t n).equiv s).val) :
    ((unpack).run st).2 ≤ unpackConstant*(budget t (n) m W)^4 := by
  have hqpos := Nat.two_pow_pos t
  let A := budget t (n) m W
  have hbasic := budget_basic t (n) m W
  have hA : 1 ≤ A := (by decide : 1 ≤ 20).trans hbasic.1
  have hlin : W+1 ≤ A := hbasic.2.1
  have hprepare := source_cost prepare (by decide) (by decide) (by decide) W st hb
  have hpc := prepare_context s qs bs st hp hs
  have hcode : Nat.size ((seedCodec t n).equiv s).val ≤ W :=
    hs ▸ hb.regs 108 (by decide) (by decide)
  have hparam : ∀ i : Fin 4, Nat.size (![n,m,4,t] i) ≤ W+t+n+m+4 := by
    intro i
    fin_cases i <;> apply (size_le_self _).trans <;> dsimp <;> omega
  have hdecode := ComputedSeed.program_cost (NestedSeed.differenceTerms)
    (n) m 4 t _ ((t+n+m+2^t+1)^2)
    (W+t+n+m+4) _ hpc hparam (differenceTerms_bound t n m)
    (hcode.trans (by omega))
  change ((NestedSeed.difference).run _).2 ≤ _ at hdecode
  rw [← call_result (by decide) (by decide) (NestedSeed.difference)] at hdecode
  change ((decoder).run (prepare.run st).1).2 ≤ _ at hdecode
  have hsmall : t+n+m+2^t+1 ≤ A := by dsimp [A,budget]; omega
  have hrest : W+t+n+m+4+1 ≤ A := by dsimp [A,budget]; omega
  have hA2 : A ≤ A^2 := Nat.le_pow (by decide)
  have harg : (t+n+m+2^t+1)^2+(W+t+n+m+4)+1 ≤ 2*A^2 := by
    have hh := Nat.pow_le_pow_left hsmall 2
    omega
  have hd' := hdecode.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left harg 2))
  have hpow : A ≤ A^4 := Nat.le_pow (by decide)
  have hp' := hprepare.trans (Nat.mul_le_mul_left _ (hlin.trans hpow))
  have houtput := decode_run s qs bs st hp hs
  have hparse := parse_cost s ((decode).run st).1 houtput
  have hls := codes_listSize s W hcode
  have hparse' : (parse.run ((decode).run st).1).2 ≤ 24*A^4 := by
    rw [hparse]
    have h1 : 1 ≤ A^4 := Nat.one_le_pow _ _ hA
    nlinarith only [hls,hlin,hpow,h1]
  have h1 : 1 ≤ A^4 := Nat.one_le_pow _ _ hA
  simp only [unpack,decode,run_seq_snd]
  change _ ≤ unpackConstant*A^4
  dsimp only [decode] at hparse'
  unfold unpackConstant
  nlinarith only [hp',hd',hparse',h1]

end PCP.Lang.NumericDifference
