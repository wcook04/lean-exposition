import PCP.Complexity.OuterSeedResources

/-! # Charged cost of the nested inner-seed materializer -/

set_option maxRecDepth 1024

namespace PCP.Lang.OuterSeed

open PCP.Algebraic ThreeColorSeedIndex BinaryFieldCode OuterBranch

variable {t n m : ℕ} [NeZero t]

attribute [local irreducible] InnerSeed.program innerCall

theorem loadInner_bound (k : Kind) (W : ℕ) (st : State 180 80)
    (hb : SourceBound W st) (hd : DataBound W st) :
    InnerSeed.SourceBound (W+4) (innerState ((loadInner k).run st).1) := by
  have htag0 : Nat.size (4+k.tag) ≤ 4 := by cases k <;> decide
  have htag : Nat.size (4+k.tag) ≤ W+4 := htag0.trans (by omega)
  have hb' (i : Fin 180) (hi : 160 ≤ i.val) (hj : i.val < 172) :
      Nat.size (st.regs i) ≤ W+4 := (hb.regs i hi hj).trans (by omega)
  have hd' (i : Fin 7) : Nat.size (st.regs (dataPort i)) ≤ W+4 := (hd i).trans (by omega)
  constructor
  · intro i hi hj
    have he : i=120 ∨ i=121 ∨ i=122 ∨ i=123 ∨ i=124 ∨ i=125 ∨ i=126 ∨
        i=127 ∨ i=128 ∨ i=129 ∨ i=130 ∨ i=131 ∨ i=132 := by omega
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals
      simp only [innerState, loadInner, run_seq_fst, run_assign_fst, run_copy_fst,
      Expr.eval, State.restrict_regs, setList_regs, setReg_regs, Function.update]
      dsimp
    · exact hb' 160 (by decide) (by decide)
    · exact hb' 161 (by decide) (by decide)
    · exact hb' 162 (by decide) (by decide)
    · exact htag
    · exact hb' 165 (by decide) (by decide)
    · exact hb' 166 (by decide) (by decide)
    · exact hb' 167 (by decide) (by decide)
    · exact hb' 168 (by decide) (by decide)
    · exact hb' 169 (by decide) (by decide)
    · exact hb' 170 (by decide) (by decide)
    · exact hd' 6
    · exact hd' 5
    · exact hd' 0
  · intro i hi hj
    have he : i=40 ∨ i=41 ∨ i=42 := by omega
    rcases he with rfl | rfl | rfl
    all_goals
      simp only [innerState, loadInner, run_seq_fst, run_assign_fst, run_copy_fst,
      State.restrict_lists, setList_lists, setReg_lists, Function.update]
      dsimp
    · exact (hb.lists 64 (by decide) (by decide)).trans (by omega)
    · exact (hb.lists 65 (by decide) (by decide)).trans (by omega)
    · exact (hb.lists 66 (by decide) (by decide)).trans (by omega)

omit [NeZero t] in
theorem saveInner_cost (k : Kind) (s : Sample k t n m) (W : ℕ) (st : State 180 80)
    (hs : InnerSeed.Stored (innerSeed s) (innerState st))
    (hc : st.regs 100 = (innerSeed s).1.toNat)
    (hz : st.regs 104 = (fieldEquiv t (interpolationSeed s).1.2).val)
    (hx : st.regs 119 =
      (ThreeColorQueryIndex.innerIndex (fieldEquiv t) m 4 (innerHadPoint s)).val) :
    (saveInner.run st).2 ≤ 5*fixedConstant saveInner*(budget t (k.dimension n) m W)^5 := by
  let A := budget t (k.dimension n) m W
  have hq := Nat.two_pow_pos t
  have hbasic := budget_basic t (k.dimension n) m W
  have hA : 1 ≤ A := by dsimp [A,budget]; omega
  have ht : t+1 ≤ A := hbasic.2.2.1
  have hm : m ≤ A := hbasic.2.2.2.2.1
  have hqA : 2^t ≤ A := by dsimp [A,budget]; omega
  have hA2 : A ≤ A^2 := Nat.le_pow (by decide)
  have hmixed : (4*m)*(t+1) ≤ 4*A^2 := by
    have hh := Nat.mul_le_mul hm ht
    nlinarith only [hh]
  have hlabels {r : ℕ} (p : BinaryPolynomialSpace.Coefficients t r) :
      listSize (BooleanCoefficientList.encode p) ≤ 4*A^2 :=
    (HadamardLabel.encode_size p).trans (by omega)
  have hscalar (x : Field t) : Nat.size (fieldEquiv t x).val ≤ 4*A^2 :=
    (Nat.size_le.mpr (fieldEquiv t x).isLt).trans (by omega)
  have hpoint : Nat.size (ThreeColorQueryIndex.innerIndex (fieldEquiv t) m 4
      (innerHadPoint s)).val ≤ 4*A^2 := by
    have hh : Nat.size (ThreeColorQueryIndex.innerIndex (fieldEquiv t) m 4
        (innerHadPoint s)).val ≤ t*(4*m) := by
      apply Nat.size_le.mpr
      simpa only [pow_mul] using
        (ThreeColorQueryIndex.innerIndex (fieldEquiv t) m 4 (innerHadPoint s)).isLt
    nlinarith only [hh,hmixed,Nat.zero_le m]
  have hslist (p : Fin (4*m) → Field t) :
      listSize (List.ofFn (fun i => (fieldEquiv t (p i)).val)) ≤ 4*A^2 :=
    (StandardCorrection.fieldCodes_size p).trans hmixed
  rcases hs.hadamard with ⟨_,_,_,hb,ha,hl,hf⟩
  have hleft := hs.left
  have hright := hs.right
  have hbits := hs.label
  change st.lists 20 = _ at hb
  change st.lists 21 = _ at ha
  change st.lists 22 = _ at hl
  change st.lists 23 = _ at hf
  change st.lists 32 = _ at hleft
  change st.lists 33 = _ at hright
  change st.lists 34 = _ at hbits
  have hcost : (saveInner.run st).2 ≤ fixedConstant saveInner*(4*A^2+1) := by
    apply loopFree_cost_le saveInner (by decide) st (4*A^2)
    · intro i hi
      have hh : ∀ j ∈ saveInner.uses, j=100 ∨ j=104 ∨ j=119 := by decide
      have h := hh i hi
      rcases h with rfl | rfl | rfl
      · rw [hc]; exact (InnerBranch.bool_size _).trans (by omega)
      · rw [hz]; exact hscalar _
      · rw [hx]; exact hpoint
    · intro i hi
      have hh : ∀ j ∈ saveInner.lUses,
          j=20 ∨ j=21 ∨ j=22 ∨ j=23 ∨ j=32 ∨ j=33 ∨ j=34 := by decide
      have h := hh i hi
      rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · rw [hb]; exact hlabels _
      · rw [ha]; exact hlabels _
      · rw [hl]; exact hlabels _
      · rw [hf]
        have hh := HadamardRow.factorCodes_size (innerHadSeed s)
        simp only [Nat.sub_self, Nat.zero_mul] at hh
        exact hh.trans (Nat.zero_le (4*A^2))
      · rw [hleft]; exact hslist _
      · rw [hright]; exact hslist _
      · rw [hbits]
        exact (InterpolationBranch.coordinateBits_size _).trans (by omega)
  have hpow : A^2 ≤ A^5 := Nat.pow_le_pow_right hA (by decide)
  have h1 : 1 ≤ A^5 := Nat.one_le_pow _ _ hA
  have hh : 4*A^2+1 ≤ 5*A^5 := by omega
  have hh' := Nat.mul_le_mul_left (fixedConstant saveInner) hh
  exact hcost.trans (by simpa only [Nat.mul_assoc, Nat.mul_left_comm] using hh')

def innerConstant (k : Kind) : ℕ := fixedConstant (loadInner k)+InnerSeed.costConstant+
  5*fixedConstant saveInner+2

theorem inner_cost (k : Kind) (a : Fin 5 → Field t) (ζ : Field t)
    (s : Sample k t n m) (qs : List ℕ) (bs : List Bool) (W : ℕ) (st : State 180 80)
    (hp : Public (n := n) (m := m) k a ζ qs bs st) (hd : Data k s st)
    (hb : SourceBound W st) (hdb : DataBound W st) :
    ((inner k).run st).2 ≤ innerConstant k*(budget t (k.dimension n) m W)^5 := by
  have hl := fixed_cost (loadInner k) (by cases k <;> decide)
    (by cases k <;> decide) (by cases k <;> decide) W st hb hdb
  have hp' := loadInner_public k a ζ s qs bs st hp hd
  have hd' := loadInner_seed k s st hd
  have hi := InnerSeed.program_cost a (k.line s.1) (innerSeed s) (W+4)
    (innerState ((loadInner k).run st).1) hp' (loadInner_bound k W st hb hdb) hd'
  have hr := InnerSeed.program_run a (k.line s.1) (innerSeed s) _ hp' hd'
  have hv := InnerSeed.program_scalars a (k.line s.1) (innerSeed s) _ hp' hd'
  rw [← call_result (by decide) (by decide) InnerSeed.program ((loadInner k).run st).1] at hi hr hv
  rw [show call (by decide) (by decide) InnerSeed.program = innerCall by
    unfold innerCall; rfl] at hi hr hv
  change (innerCall.run ((loadInner k).run st).1).2 ≤ _ at hi
  change _ ∧ InnerSeed.Stored (innerSeed s) (innerState (innerCall.run _).1) ∧ _ at hr
  change (innerCall.run _).1.regs 100 = _ ∧ (innerCall.run _).1.regs 104 = _ ∧
    (innerCall.run _).1.regs 119 = _ at hv
  have hc := saveInner_cost k s W _ hr.2.1 hv.1 hv.2.1 hv.2.2
  have hlin := (budget_basic t (k.dimension n) m W).2.1
  have hA : 1 ≤ budget t (k.dimension n) m W :=
    (by decide : 1 ≤ 20).trans (budget_basic t (k.dimension n) m W).1
  have harg : InnerSeed.budget t m (W+4) ≤ budget t (k.dimension n) m W := by
    unfold InnerSeed.budget budget
    omega
  have hi' := hi.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left harg 5))
  have hl' := hl.trans (Nat.mul_le_mul_left _ (hlin.trans (Nat.le_pow (by decide : 0<5))))
  have h1 := Nat.one_le_pow 5 (budget t (k.dimension n) m W) hA
  simp only [inner,run_seq_snd]
  unfold innerConstant
  nlinarith only [hi',hl',hc,h1]

end PCP.Lang.OuterSeed
