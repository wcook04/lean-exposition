import PCP.Complexity.NumericDifferenceResources
import PCP.Complexity.InnerSeedWordCost

/-! # Charged cost of expanding the sampled difference label -/

namespace PCP.Lang.NumericDifference

open PCP.Algebraic ThreeColorSeedIndex BinaryFieldCode

variable {t : ℕ}

attribute [local irreducible] uniform

theorem coordinate_cost (prep : Stmt 120 40) (dst : Fin 40) (st : State 120 40)
    (N base code : ℕ)
    (hN : (prep.run st).1.regs 5 = N) (hb : (prep.run st).1.regs 6 = base)
    (hc : (prep.run st).1.regs 0 = code) (he : (prep.run st).1.lists 2 = []) :
    ((Stmt.seq prep (.seq uniform (.copy 1 dst))).run st).2 ≤
      (prep.run st).2+(MixedRadixDecode.passConstant+24)*
        (N*(Nat.size base+1)+N+Nat.size code+3)^2+N*(Nat.size code+1)+3 := by
  let v := (prep.run st).1.restrict (Fin.castLE (by decide : 7 ≤ 120))
    (Fin.castLE (by decide : 3 ≤ 40))
  have hv : v.lists 2 = [] := he
  have hcost := UniformDecode.program_cost v hv
  have hout := (UniformDecode.program_run v hv).1
  dsimp only [v] at hcost hout
  rw [← call_result (by decide) (by decide) UniformDecode.program] at hcost hout
  rw [show call (by decide) (by decide) UniformDecode.program = uniform by
    unfold uniform; rfl] at hcost hout
  change (uniform.run (prep.run st).1).2 ≤ (MixedRadixDecode.passConstant+24)*
    ((prep.run st).1.regs 5*(Nat.size ((prep.run st).1.regs 6)+1)+
      (prep.run st).1.regs 5+Nat.size ((prep.run st).1.regs 0)+3)^2 at hcost
  change (uniform.run (prep.run st).1).1.lists 1 =
    (MixedRadixDecode.split ((prep.run st).1.regs 0)
      (List.replicate ((prep.run st).1.regs 5) ((prep.run st).1.regs 6))).1 at hout
  rw [hN,hb,hc] at hcost hout
  have hls := MixedRadixDecode.split_listSize code (List.replicate N base)
  rw [List.length_replicate] at hls
  simp only [run_seq_snd,run_copy_snd,hout]
  omega

def bitsConstant : ℕ := fixedConstant bitPrepare+InnerSeed.coordinateConstant

theorem bits_cost (d m W : ℕ) (st : State 120 40)
    (ht : st.regs 100 = t) (he : st.lists 32 = [])
    (hb : SourceBound W st) (hd : DataBound W st) :
    (bits.run st).2 ≤ bitsConstant*(budget t d m W)^4 := by
  have hp := fixed_cost bitPrepare (by decide) (by decide) (by decide) W st hb hd
  have hc := coordinate_cost bitPrepare 17 st t 2 (st.regs 90)
    (by simp [bitPrepare,Stmt.run,Expr.eval,Function.update,ht])
    (by simp [bitPrepare,Stmt.run,Expr.eval,Function.update])
    (by simp [bitPrepare,Stmt.run,Expr.eval,Function.update])
    (by simp [bitPrepare,Stmt.run,Function.update,he])
  have hbasic := budget_basic t d m W
  have hA : 1 ≤ budget t d m W := (by decide : 1 ≤ 20).trans hbasic.1
  have h2 : Nat.size 2 ≤ budget t d m W := by change 2 ≤ _; omega
  have hs : Nat.size (st.regs 90) ≤ W := hd 0
  exact hc.trans (InnerSeed.coordinate_bound _ _ _ _ _ _ hA (by omega) h2
    (hs.trans (by omega)) (hp.trans (Nat.mul_le_mul_left _
      (hbasic.2.1.trans (Nat.le_pow (by decide : 0<4))))))

end PCP.Lang.NumericDifference
