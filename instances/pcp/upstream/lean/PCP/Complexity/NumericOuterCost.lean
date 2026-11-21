import PCP.Complexity.NumericOuterLang
import PCP.Complexity.OuterSeedCost
import PCP.Complexity.OuterStoredBounds

/-! # Full runtime bound from a numeric outer seed, including all branch queries -/

namespace PCP.Lang.NumericOuter

open PCP.Algebraic BinaryFieldCode OuterBranch

variable {t n m : ℕ} [NeZero t] [NeZero m]

attribute [local irreducible] OuterSeed.program OuterBranch.program

def sourceWidth (t n m : ℕ) (qs : List ℕ) (bs : List Bool) : ℕ :=
  storedWidth t n m qs bs []+QueryAddress.width t n m 4

set_option maxRecDepth 8192 in
/-- Seed decoding and branch execution, with all semantic address bounds discharged. -/
theorem program_cost (k : Kind) (a : Fin 5 → Field t) (ζ : Field t)
    (s : Sample k t n m) (qs : List ℕ) (bs : List Bool) (W : ℕ) (st : State 180 80)
    (hp : OuterSeed.Public (n := n) (m := m) k a ζ qs bs st) (hb : OuterSeed.SourceBound W st)
    (hc : st.regs 171 = ((seedCodec k t n m).equiv s).val) :
    ((program k).run st).2 ≤ OuterSeed.costConstant k*(OuterSeed.budget t (k.dimension n) m W)^5+
      OuterBranch.costConstant*(32*(t+4*m+k.dimension n+2^t+sourceWidth t n m qs bs+
        listSize (st.lists 49)+20))^9+1 := by
  have hs := OuterSeed.program_run k a ζ s qs bs st hp hc
  have hcost := OuterSeed.program_cost k a ζ s qs bs W st hp hb hc
  have he := OuterSeed.program_list54 k a ζ s qs bs st hp hc
  have hq := OuterSeed.program_queries k st
  generalize hrun : ((OuterSeed.program k).run st).1 = u at *
  have hstored := hs.1.storedBound k a ζ s qs bs u
  rw [he] at hstored
  have hsbound : StoredBound (sourceWidth t n m qs bs) u := by
    constructor
    · intro i hi hj
      exact (hstored.regs i hi hj).trans (Nat.le_add_right _ _)
    · intro i hi hj hk
      exact (hstored.lists i hi hj hk).trans (Nat.le_add_right _ _)
  have hquery := BranchQueryBounds.outer k a ζ s
    (show QueryAddress.width t n m 4 ≤ sourceWidth t n m qs bs from Nat.le_add_left _ _)
  have hbranch := OuterBranch.program_cost k a ζ s qs bs (sourceWidth t n m qs bs) u hs.1
    hsbound hquery
  unfold OuterBranch.budget at hbranch
  rw [hq] at hbranch
  simp only [program,run_seq_snd,hrun]
  omega

attribute [local irreducible] OuterSeed.costConstant OuterBranch.costConstant
  QueryAddress.widthConstant

def budget (t n m W : ℕ) (qs : List ℕ) (bs : List Bool) (trace : List ℕ) : ℕ :=
  t+n+m+2^t+W+listSize qs+2*bs.length+listSize trace+30

def baseConstant : ℕ := 32*(30+6*QueryAddress.widthConstant)

def costConstant (k : Kind) : ℕ :=
  4^5*OuterSeed.costConstant k+OuterBranch.costConstant*baseConstant^9+1

set_option maxRecDepth 1024 in
/-- A single fixed-degree bound for the full concrete numeric branch. -/
theorem program_cost_uniform (k : Kind) (a : Fin 5 → Field t) (ζ : Field t)
    (s : Sample k t n m) (qs : List ℕ) (bs : List Bool) (W : ℕ) (st : State 180 80)
    (hp : OuterSeed.Public (n := n) (m := m) k a ζ qs bs st) (hb : OuterSeed.SourceBound W st)
    (hc : st.regs 171 = ((seedCodec k t n m).equiv s).val) :
    ((program k).run st).2 ≤ costConstant k*(budget t n m W qs bs (st.lists 49))^18 := by
  have h := program_cost k a ζ s qs bs W st hp hb hc
  let B := budget t n m W qs bs (st.lists 49)
  have hq := Nat.two_pow_pos t
  have hB : 1 ≤ B := by dsimp [B,budget]; omega
  have hB2 : B ≤ B^2 := Nat.le_pow (by decide)
  have hd : k.dimension n ≤ 4*n := by cases k <;> simp [Kind.dimension] <;> omega
  have ht : t+1 ≤ B := by dsimp [B,budget]; omega
  have hnm : n+m ≤ B := by dsimp [B,budget]; omega
  have hmul := Nat.mul_le_mul ht hnm
  have hstored : storedWidth t n m qs bs [] ≤ 21*B^2 := by
    have hsum : 10*t+4*2^t+listSize qs+2*bs.length+30 ≤ 17*B := by
      dsimp [B,budget]; omega
    unfold storedWidth
    simp only [show listSize [] = 0 from rfl,Nat.add_zero]
    nlinarith only [hmul,hsum,hB2]
  have hinput : QueryAddress.inputWidth t n m 4+1 ≤ 5*B^2 := by
    have hsum : 2^t+9 ≤ B := by dsimp [B,budget]; omega
    unfold QueryAddress.inputWidth
    nlinarith only [hmul,hsum,hB2,Nat.zero_le n,Nat.zero_le m]
  have hwidth := Nat.mul_le_mul_left QueryAddress.widthConstant hinput
  change QueryAddress.width t n m 4 ≤ QueryAddress.widthConstant*(5*B^2) at hwidth
  have hswidth : sourceWidth t n m qs bs ≤ (21+5*QueryAddress.widthConstant)*B^2 := by
    unfold sourceWidth
    nlinarith only [hstored,hwidth]
  have hsmall : OuterSeed.budget t (k.dimension n) m W ≤ 4*B := by
    dsimp [OuterSeed.budget,B,budget]; omega
  have hrest : t+4*m+k.dimension n+2^t+listSize (st.lists 49)+20 ≤ 8*B := by
    dsimp [B,budget]; omega
  have hlarge : 32*(t+4*m+k.dimension n+2^t+sourceWidth t n m qs bs+
      listSize (st.lists 49)+20) ≤ baseConstant*B^2 := by
    unfold baseConstant
    nlinarith only [hswidth,hrest,hB2,Nat.zero_le (QueryAddress.widthConstant*B^2)]
  have hs := Nat.mul_le_mul_left (OuterSeed.costConstant k) (Nat.pow_le_pow_left hsmall 5)
  have hl := Nat.mul_le_mul_left OuterBranch.costConstant (Nat.pow_le_pow_left hlarge 9)
  have h518 : B^5 ≤ B^18 := Nat.pow_le_pow_right hB (by decide)
  have hs' : OuterSeed.costConstant k*(OuterSeed.budget t (k.dimension n) m W)^5 ≤
      (4^5*OuterSeed.costConstant k)*B^18 := by
    rw [Nat.mul_pow] at hs
    have hh := Nat.mul_le_mul_left (4^5*OuterSeed.costConstant k) h518
    nlinarith only [hs,hh]
  have hl' : OuterBranch.costConstant*(32*(t+4*m+k.dimension n+2^t+
      sourceWidth t n m qs bs+listSize (st.lists 49)+20))^9 ≤
      (OuterBranch.costConstant*baseConstant^9)*B^18 := by
    simpa only [Nat.mul_pow,← Nat.pow_mul,Nat.mul_assoc] using hl
  have h1 : 1 ≤ B^18 := Nat.one_le_pow _ _ hB
  calc
    _ ≤ _ := h
    _ ≤ (4^5*OuterSeed.costConstant k)*B^18+
        (OuterBranch.costConstant*baseConstant^9)*B^18+B^18 :=
      Nat.add_le_add (Nat.add_le_add hs' hl') h1
    _ = costConstant k*B^18 := by
      unfold costConstant
      ring

end PCP.Lang.NumericOuter
