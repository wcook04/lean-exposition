import PCP.Complexity.OuterSeedTrace
import PCP.Complexity.OuterBranchCost

/-! # The outer encoded-line branch directly from its actual numeric seed -/

namespace PCP.Lang.NumericOuter

open PCP.Algebraic BinaryFieldCode OuterBranch

variable {t n m : ℕ} [NeZero t] [NeZero m]

def program (k : Kind) : Stmt 180 80 := .seq (OuterSeed.program k) OuterBranch.program

attribute [local irreducible] OuterSeed.program OuterBranch.program

set_option maxRecDepth 8192 in
/-- Actual sampler decoding, branch arithmetic, physical queries and history verdict. -/
theorem program_run (k : Kind) (a : Fin 5 → Field t) (ζ : Field t)
    (s : Sample k t n m) (qs : List ℕ) (bs : List Bool) (st : State 180 80)
    (hp : OuterSeed.Public (n := n) (m := m) k a ζ qs bs st)
    (hc : st.regs 171 = ((seedCodec k t n m).equiv s).val) :
    ((program k).run st).1.regs 144 = (OuterBranch.verdict k a ζ s qs bs).toNat ∧
      ((program k).run st).1.lists 49 = (queryCodes k a ζ s).reverse ++ st.lists 49 := by
  have hs := OuterSeed.program_run k a ζ s qs bs st hp hc
  have hv := OuterBranch.program_run k a ζ s qs bs _ hs.1
  have hq := OuterSeed.program_queries k st
  simp only [program, run_seq_fst]
  exact ⟨hv.1, hv.2.1.trans (by rw [hq])⟩

end PCP.Lang.NumericOuter
