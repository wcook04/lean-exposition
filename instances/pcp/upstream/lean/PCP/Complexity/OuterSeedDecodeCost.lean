import PCP.Complexity.OuterSeedResources

/-! # Charged polynomial cost of actual numeric outer-seed extraction -/

set_option maxRecDepth 1024

namespace PCP.Lang.OuterSeed

open PCP.Algebraic ThreeColorSeedIndex BinaryFieldCode OuterBranch

variable {t n m : ℕ} [NeZero t]

theorem outerTerms_bound (t d m : ℕ) (b : Bool) (i : Fin 7) :
    (NestedSeed.outerTerms b i).eval ![d,m,4,t] ≤ 16*(t+d+m+2^t+1)^2 := by
  have h2 := Nat.choose_le_two_pow t 2
  have h3 := Nat.choose_le_two_pow t 3
  have hq := Nat.two_pow_pos t
  cases b <;> fin_cases i <;>
    simp [NestedSeed.outerTerms, NestedSeed.innerPointBits_eval, NestedSeed.pointBits_eval,
      NestedSeed.hadamard_eval, NestedSeed.inner_eval, ThreeColorSeedSize.innerBits,
      ThreeColorSeedSize.hadamardBits_one, ThreeColorSeedSize.hadamardBits_three,
      ArithmeticExpression.Term.eval]
  all_goals nlinarith only [h2,h3,hq,Nat.zero_le (t^2),Nat.zero_le (d^2),Nat.zero_le (m^2),
    Nat.zero_le ((2^t)^2),Nat.zero_le (t*d),Nat.zero_le (t*m),Nat.zero_le (t*2^t),
    Nat.zero_le (d*m),Nat.zero_le (d*2^t),Nat.zero_le (m*2^t)]

def unpackConstant (k : Kind) : ℕ := fixedConstant prepare +
  289*ComputedSeed.programConstant (NestedSeed.outerTerms k.cubic)+24

set_option maxRecDepth 1024 in
theorem parse_cost (k : Kind) (s : Sample k t n m) (st : State 180 80)
    (hc : st.lists 1 = List.ofFn (codes k s)) :
    (parse.run st).2 = 2*listSize (List.ofFn (codes k s))+8 := by
  simp [parse, Stmt.run, Function.update, hc, List.ofFn_succ, listSize]
  ring

theorem unpack_cost (k : Kind) (a : Fin 5 → Field t) (ζ : Field t)
    (s : Sample k t n m) (qs : List ℕ) (bs : List Bool) (W : ℕ) (st : State 180 80)
    (hp : Public (n := n) (m := m) k a ζ qs bs st) (hb : SourceBound W st)
    (hs : st.regs 171 = ((seedCodec k t n m).equiv s).val) :
    ((unpack k).run st).2 ≤ unpackConstant k*(budget t (k.dimension n) m W)^4 := by
  have hqpos := Nat.two_pow_pos t
  let A := budget t (k.dimension n) m W
  have hbasic := budget_basic t (k.dimension n) m W
  have hA : 1 ≤ A := (by decide : 1 ≤ 20).trans hbasic.1
  have hlin : W+1 ≤ A := hbasic.2.1
  have hprepare := source_cost prepare (by decide) (by decide) (by decide) W st hb
  have hpc := prepare_context k a ζ s qs bs st hp hs
  have hcode : Nat.size ((seedCodec k t n m).equiv s).val ≤ W :=
    hs ▸ hb.regs 171 (by decide) (by decide)
  have hparam : ∀ i : Fin 4, Nat.size (![k.dimension n,m,4,t] i) ≤ W+t+k.dimension n+m+4 := by
    intro i
    fin_cases i <;> apply (size_le_self _).trans <;> dsimp <;> omega
  have hdecode := ComputedSeed.program_cost (NestedSeed.outerTerms k.cubic)
    (k.dimension n) m 4 t _ (16*(t+k.dimension n+m+2^t+1)^2)
    (W+t+k.dimension n+m+4) _ hpc hparam (outerTerms_bound t (k.dimension n) m k.cubic)
    (hcode.trans (by omega))
  change ((decodeOuter k).run _).2 ≤ _ at hdecode
  rw [← call_result (by decide) (by decide) (decodeOuter k)] at hdecode
  change ((decoder k).run (prepare.run st).1).2 ≤ _ at hdecode
  have hsmall : t+k.dimension n+m+2^t+1 ≤ A := by dsimp [A,budget]; omega
  have hrest : W+t+k.dimension n+m+4+1 ≤ A := by dsimp [A,budget]; omega
  have hA2 : A ≤ A^2 := Nat.le_pow (by decide)
  have harg : 16*(t+k.dimension n+m+2^t+1)^2+(W+t+k.dimension n+m+4)+1 ≤ 17*A^2 := by
    have hh := Nat.pow_le_pow_left hsmall 2
    omega
  have hd' := hdecode.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left harg 2))
  have hpow : A ≤ A^4 := Nat.le_pow (by decide)
  have hp' := hprepare.trans (Nat.mul_le_mul_left _ (hlin.trans hpow))
  have houtput := decode_run k a ζ s qs bs st hp hs
  have hparse := parse_cost k s ((decode k).run st).1 houtput
  have hls := codes_listSize k s W hcode
  have hparse' : (parse.run ((decode k).run st).1).2 ≤ 22*A^4 := by
    rw [hparse]
    have h1 : 1 ≤ A^4 := Nat.one_le_pow _ _ hA
    nlinarith only [hls,hlin,hpow,h1]
  have h1 : 1 ≤ A^4 := Nat.one_le_pow _ _ hA
  simp only [unpack,decode,run_seq_snd]
  change _ ≤ unpackConstant k*A^4
  dsimp only [decode] at hparse'
  unfold unpackConstant
  nlinarith only [hp',hd',hparse',h1]

end PCP.Lang.OuterSeed
