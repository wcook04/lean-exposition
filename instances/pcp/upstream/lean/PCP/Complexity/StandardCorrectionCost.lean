import PCP.Complexity.StandardCorrectionLang
import PCP.Complexity.StandardCorrectionQueriesCost

/-!
# Polynomial running cost of the complete standard corrector
-/

namespace PCP.Lang.StandardCorrection

open PCP.Algebraic BinaryFieldCode BinaryPolynomialSpace BooleanCoefficientArithmetic
  BooleanCoefficientIndex

variable {t n m : ℕ} [NeZero t]

attribute [local irreducible] point pass passes prepare generate readParity restore label emit

def labelConstant : ℕ := WordCodec.passConstant * 3 + 30

def costConstant : ℕ := 5*weightConstant + 5*pointConstant + labelConstant + 5*addressConstant +
  8000*(QueryHistory.passConstant+60)+100

/-- The budget uses actual stored history sizes, not the number of possible proof locations. -/
def budget (t m W : ℕ) (st : State 80 26) : ℕ :=
  2^t+t+4*m+W+listSize (st.lists 22)+listSize (st.lists 23)+listSize (st.lists 20)+4

theorem prepare_cost (s : Site (BinaryMaterializedField.Element t) n)
    (ζ : BinaryMaterializedField.Element t)
    (u v : BinaryLocalCorrection.InnerPoint (BinaryMaterializedField.Element t) m 4)
    (w : Fin t → ZMod 2) (st : State 80 26) (hi : Input s ζ u v w st) :
    (prepare.run st).2 ≤ listSize (st.lists 20) + labelConstant*(t+2)^2+4 := by
  let a := setList (setList st 19 (st.lists 20)) 20 (st.lists 7)
  have hw : a.lists 17 = List.ofFn (fun i => (w i).val) := by
    simpa [a, Function.update] using hi.2.2
  have h := label_cost w a hw
  simp only [prepare, run_seq_snd, run_copy_snd, run_copy_fst]
  change listSize (st.lists 20)+1+(listSize (st.lists 7)+1+(label.run a).2+1)+1 ≤ _
  rw [hi.1.2.2.2.2.1]
  change listSize (st.lists 20)+1+(0+1+(label.run a).2+1)+1 ≤ _
  change (label.run a).2 ≤ labelConstant*(t+2)^2 at h
  omega

theorem generate_cost (s : Site (BinaryMaterializedField.Element t) n)
    (ζ : BinaryMaterializedField.Element t)
    (u v : BinaryLocalCorrection.InnerPoint (BinaryMaterializedField.Element t) m 4)
    (w : Fin t → ZMod 2) (W : ℕ) (st : State 80 26) (hi : Input s ζ u v w st)
    (hb : QueryBound s ζ u v w W) (hs : listSize (st.lists 21) ≤ W) :
    (generate.run st).2 ≤ listSize (st.lists 20)+labelConstant*(t+2)^2+
      5*(passBudget t (4*m) W+1)+6 := by
  have hp := prepare_run s ζ u v w st hi
  have hpc := prepare_cost s ζ u v w st hi
  have hsc : listSize ((prepare.run st).1.lists 21) ≤ W := by
    rw [prepare_list st 21 (by decide)]; exact hs
  have hg := passes_cost s ζ u v w 0 5 W (by decide) (prepare.run st).1 hp.1 hb hsc
  rw [generate, run_seq_snd]
  omega

theorem generate_size (s : Site (BinaryMaterializedField.Element t) n)
    (ζ : BinaryMaterializedField.Element t)
    (u v : BinaryLocalCorrection.InnerPoint (BinaryMaterializedField.Element t) m 4)
    (w : Fin t → ZMod 2) (W : ℕ) (st : State 80 26) (hi : Input s ζ u v w st)
    (hb : QueryBound s ζ u v w W) :
    listSize ((generate.run st).1.lists 20) ≤ 5*(W+1) := by
  rw [(generate_run s ζ u v w st hi).1, Site.queries_ofFn]
  simp only [listSize, List.map_reverse, List.sum_reverse, List.map_ofFn, Fin.sum_ofFn]
  calc
    _ ≤ ∑ _i : Fin 5, (W+1) := Finset.sum_le_sum fun i _ =>
      by
        simpa only [queryCode, queryLabel_coe, Function.comp_apply] using
          Nat.add_le_add_right (hb i.val i.isLt).2 1
    _ = _ := by simp

theorem readParity_cost (st : State 80 26) :
    (readParity.run st).2 ≤ (QueryHistory.passConstant+60)*
      (3*(listSize (st.lists 22)+listSize (st.lists 23)+listSize (st.lists 20)+1)+2)^3 := by
  have hp := HistoryParity.parity_cost (st.restrict parityRegs parityLists)
  rw [← congrArg Prod.snd (readParity_result st)] at hp
  exact hp

theorem restore_cost (st : State 80 26) :
    (restore.run st).2 = 3*listSize (st.lists 20)+listSize (st.lists 19)+5 := by
  simp [restore, Stmt.run, listSize, Function.update, List.sum_append]
  omega

/-- All field arithmetic, five physical address computations, history scans, and accumulator
restoration are charged by a single degree-seven bound. -/
theorem program_cost (s : Site (BinaryMaterializedField.Element t) n)
    (ζ : BinaryMaterializedField.Element t)
    (u v : BinaryLocalCorrection.InnerPoint (BinaryMaterializedField.Element t) m 4)
    (w : Fin t → ZMod 2) (W : ℕ) (st : State 80 26) (hi : Input s ζ u v w st)
    (hb : QueryBound s ζ u v w W) (hs : listSize (st.lists 21) ≤ W) :
    (program.run st).2 ≤ costConstant * (budget t m W st)^7 := by
  have hqpos : 0 < 2^t := pow_pos (by decide) _
  let B := budget t m W st
  have hB : 1 ≤ B := by dsimp [B, budget]; omega
  have hlin : B ≤ B^7 := Nat.le_self_pow (by decide) B
  have htwo : B^2 ≤ B^7 := Nat.pow_le_pow_right hB (by decide)
  have hthree : B^3 ≤ B^7 := Nat.pow_le_pow_right hB (by decide)
  have hq : 2^t+4 ≤ B := by dsimp [B, budget]; omega
  have htp : t+4*m+4 ≤ B := by dsimp [B, budget]; omega
  have htl : t+2 ≤ B := by dsimp [B, budget]; omega
  have hW : W+1 ≤ B := by dsimp [B, budget]; omega
  have ho : listSize (st.lists 20) ≤ B := by dsimp [B, budget]; omega
  have hg := generate_cost s ζ u v w W st hi hb hs
  have hsz := generate_size s ζ u v w W st hi hb
  have hgen := generate_run s ζ u v w st hi
  have hr := readParity_cost (generate.run st).1
  have hf := readParity_frame (generate.run st).1
  have hrest := restore_cost (readParity.run (generate.run st).1).1
  rw [generate_list st 22 (by decide) (by decide),
    generate_list st 23 (by decide) (by decide)] at hr
  rw [hf.1, hf.2.2.2, hgen.2.2] at hrest
  have hhist : 3*(listSize (st.lists 22)+listSize (st.lists 23)+
      listSize ((generate.run st).1.lists 20)+1)+2 ≤ 20*B := by
    dsimp [B, budget]; omega
  have hr' := hr.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hhist 3))
  have hr'' : (readParity.run (generate.run st).1).2 ≤
      8000*(QueryHistory.passConstant+60)*B^7 := by
    have hh := Nat.mul_le_mul_left (8000*(QueryHistory.passConstant+60)) hthree
    rw [mul_pow] at hr'
    norm_num at hr'
    nlinarith only [hr', hh]
  have hp : pointConstant*(t+4*m+4)^5 ≤ pointConstant*B^7 :=
    Nat.mul_le_mul_left _ ((Nat.pow_le_pow_left htp 5).trans
      (Nat.pow_le_pow_right hB (by decide)))
  have hw : weightConstant*(2^t+4)^7 ≤ weightConstant*B^7 :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hq 7)
  have hl : labelConstant*(t+2)^2 ≤ labelConstant*B^7 :=
    Nat.mul_le_mul_left _ ((Nat.pow_le_pow_left htl 2).trans htwo)
  have ha : addressConstant*(W+1) ≤ addressConstant*B^7 :=
    Nat.mul_le_mul_left _ (hW.trans hlin)
  have hpos : 1 ≤ B^7 := Nat.one_le_pow _ _ hB
  rw [program_def, run_seq_snd, run_seq_snd]
  change _ ≤ costConstant * B^7
  dsimp only [passBudget] at hg
  dsimp only [costConstant]
  nlinarith only [hg, hr'', hrest, hsz, ho, hW, hp, hw, hl, ha, hlin, hpos]

end PCP.Lang.StandardCorrection
