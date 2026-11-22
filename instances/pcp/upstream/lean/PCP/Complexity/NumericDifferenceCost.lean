import PCP.Complexity.NumericDifferenceDecodeCost
import PCP.Complexity.NumericDifferenceWordCost

/-! # Full polynomial charged cost of the numeric difference callback -/

namespace PCP.Lang.NumericDifference

open PCP.Algebraic ThreeColorSeedIndex BinaryFieldCode

variable {t n m : ℕ} [NeZero t]

def WorkBound (W : ℕ) (st : State 120 40) : Prop :=
  ∀ i : Fin 120, 57 ≤ i.val → i.val ≤ 62 → Nat.size (st.regs i) ≤ W

theorem finish_bound (W : ℕ) (st : State 120 40) (hb : SourceBound W st)
    (hd : DataBound W st) : WorkBound W (finish.run st).1 := by
  have h90 : Nat.size (st.regs 91) ≤ W := hd 1
  have h92 : Nat.size (st.regs 92) ≤ W := hd 2
  have h104 := hb.regs 104 (by decide) (by decide)
  have h105 := hb.regs 105 (by decide) (by decide)
  have h106 := hb.regs 106 (by decide) (by decide)
  have h107 := hb.regs 107 (by decide) (by decide)
  intro ⟨i, hi⟩ h1 h2
  interval_cases i <;>
    simp only [finish, Stmt.run, Expr.eval]
  all_goals assumption

attribute [local irreducible] unpack bits branch load

def loadConstant : ℕ := unpackConstant+bitsConstant+fixedConstant finish+2

theorem load_cost (s : Sample t n) (qs : List ℕ) (bs : List Bool) (W : ℕ)
    (st : State 120 40) (hp : Public (t := t) n m qs bs st) (hb : SourceBound W st)
    (hs : st.regs 108 = ((seedCodec t n).equiv s).val) :
    (load.run st).2 ≤ loadConstant*(budget t n m W)^4 ∧ WorkBound W (load.run st).1 := by
  have hu := unpack_cost s qs bs W st hp hb hs
  obtain ⟨hd, hp', hf⟩ := unpack_run s qs bs st hp hs
  have hcode : Nat.size ((seedCodec t n).equiv s).val ≤ W :=
    hs ▸ hb.regs 108 (by decide) (by decide)
  have hdb := hd.bound s W _ hcode
  have hb' := hb.of_frame hf
  have hbc := bits_cost n m W (unpack.run st).1 hp'.width hp'.empty hb' hdb
  have hbf := bits_frame (unpack.run st).1
  have hb'' := hb'.of_frame hbf
  have hdb' : DataBound W (bits.run (unpack.run st).1).1 := by
    intro i
    rw [bits_reg _ (dataPort i) (by simp only [dataPort]; omega)]
    exact hdb i
  have hfc := fixed_cost finish (by decide) (by decide) (by decide)
    W _ hb'' hdb'
  have hwork := finish_bound W _ hb'' hdb'
  have hbas := budget_basic t n m W
  have hpow : budget t n m W ≤ (budget t n m W)^4 := Nat.le_pow (by decide)
  have hfc' := hfc.trans (Nat.mul_le_mul_left _ (hbas.2.1.trans hpow))
  have h1 : 1 ≤ (budget t n m W)^4 := Nat.one_le_pow _ _ ((by decide : 1 ≤ 20).trans hbas.1)
  refine ⟨?_, by simpa only [load, run_seq_fst] using hwork⟩
  simp only [load, run_seq_snd]
  unfold loadConstant
  nlinarith only [hu, hbc, hfc', h1]

def costConstant : ℕ := loadConstant+DifferenceBranch.programConstant+1

attribute [local irreducible] loadConstant DifferenceBranch.programConstant

theorem program_cost (s : Sample t n) (qs : List ℕ) (bs : List Bool) (W : ℕ)
    (st : State 120 40) (hp : Public (t := t) n m qs bs st) (hb : SourceBound W st)
    (hs : st.regs 108 = ((seedCodec t n).equiv s).val) :
    (program.run st).2 ≤ costConstant*(budget t n m W)^8 := by
  obtain ⟨hload, hw⟩ := load_cost s qs bs W st hp hb hs
  obtain ⟨hc, _, _⟩ := load_run s qs bs st hp hs
  have hqs : listSize qs ≤ W := hp.history ▸ hb.lists 33 (by decide) (by decide)
  have hbs : listSize (bs.map Bool.toNat) ≤ W :=
    hp.answers ▸ hb.lists 34 (by decide) (by decide)
  have hbranch := DifferenceBranch.program_cost s.2 qs bs
    ((load.run st).1.restrict (Fin.castLE (by decide)) (Fin.castLE (by decide))) W
    hc.width hc.empty hc.label hc.history hc.answers hqs hbs
    (fun i hi hj => hw (Fin.castLE (by decide) i) hi hj)
  rw [← call_result (by decide) (by decide) DifferenceBranch.program] at hbranch
  rw [show call (by decide) (by decide) DifferenceBranch.program = branch by
    unfold branch; rfl] at hbranch
  have hbas := budget_basic t n m W
  have h1 : 1 ≤ budget t n m W := (by decide : 1 ≤ 20).trans hbas.1
  have harg : 2^t+W+8 ≤ budget t n m W := by have := hbas.2.2.2.2.2; omega
  have hl := hload.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right h1 (by decide : 4 ≤ 8)))
  have hh := hbranch.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left harg 8))
  have hone : 1 ≤ (budget t n m W)^8 := Nat.one_le_pow _ _ h1
  simp only [program, run_seq_snd]
  unfold costConstant
  nlinarith only [hl, hh, hone]

end PCP.Lang.NumericDifference
