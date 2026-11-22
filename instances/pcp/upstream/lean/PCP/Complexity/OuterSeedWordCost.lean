import PCP.Complexity.OuterSeedResources

/-! # Charged cost of outer coefficient words and uniform-radix coordinate arrays -/

set_option maxRecDepth 1024

namespace PCP.Lang.OuterSeed

open PCP.Algebraic ThreeColorSeedIndex BinaryFieldCode OuterBranch

variable {t n m : ℕ} [NeZero t]

attribute [local irreducible] HadamardSeed.program hadCall uniform

omit [NeZero t] in
theorem hadSave_cost (k : Kind) (s : Sample k t n m) (st : State 180 80)
    (hb : st.lists 20 = BooleanCoefficientList.encode (primarySeed s).base)
    (ha : st.lists 21 = BooleanCoefficientList.encode (primarySeed s).auxiliary)
    (hl : st.lists 22 = BooleanCoefficientList.encode (primarySeed s).linear)
    (hf : st.lists 23 = HadamardRow.factorCodes (primarySeed s)) :
    (hadSave.run st).2 ≤ 10*(2 ^ t+1) := by
  have hb' := HadamardLabel.encode_size (primarySeed s).base
  have ha' := HadamardLabel.encode_size (primarySeed s).auxiliary
  have hl' := HadamardLabel.encode_size (primarySeed s).linear
  have hf' := (HadamardRow.factorCodes_size (primarySeed s)).trans
    (Nat.mul_le_mul_right (2 ^ t+1) (show k.degree-1 ≤ 2 by have := k.degree_le; omega))
  simp only [hadSave,run_seq_snd,run_copy_snd,run_copy_fst,setList_lists,Function.update]
  simp only [show (21 : Fin 80) ≠ 50 by decide, show (22 : Fin 80) ≠ 50 by decide,
    show (22 : Fin 80) ≠ 51 by decide, show (23 : Fin 80) ≠ 50 by decide,
    show (23 : Fin 80) ≠ 51 by decide, show (23 : Fin 80) ≠ 52 by decide,
    ↓reduceDIte, hb,ha,hl,hf]
  omega

def hadConstant : ℕ := fixedConstant hadPrepare+HadamardSeed.seedConstant+12

theorem hadamard_cost (k : Kind) (s : Sample k t n m) (W : ℕ) (st : State 180 80)
    (ht : st.regs 160 = t) (he : st.lists 65 = []) (hd : Data k s st)
    (hb : SourceBound W st) (hdb : DataBound W st) :
    ((hadamard k).run st).2 ≤ hadConstant*(budget t (k.dimension n) m W)^5 := by
  have hp := fixed_cost hadPrepare (by decide) (by decide) (by decide) W st hb hdb
  have hs : st.regs 151 = ((hadamardCodec t k.degree).equiv (primarySeed s)).val := hd 1
  have hh := HadamardSeed.program_cost (primarySeed s)
    ((hadPrepare.run st).1.restrict (Fin.castLE (by decide)) (Fin.castLE (by decide)))
    (by simpa [hadPrepare,Stmt.run,Expr.eval,Function.update,State.restrict] using ht)
    (by simpa [hadPrepare,Stmt.run,Expr.eval,Function.update,State.restrict] using he)
    (by simpa [hadPrepare,Stmt.run,Expr.eval,Function.update,State.restrict] using hs)
  rw [← call_result (by decide) (by decide) (HadamardSeed.program k.degree)] at hh
  rw [show call (by decide) (by decide) (HadamardSeed.program k.degree) = hadCall k by
    unfold hadCall; rfl] at hh
  have h96 : ((hadPrepare.run st).1.restrict (Fin.castLE (by decide : 100 ≤ 180))
      (Fin.castLE (by decide : 32 ≤ 80))).regs 96 = st.regs 151 := by
    simp [hadPrepare,Stmt.run,Expr.eval,Function.update,State.restrict]
  rw [h96] at hh
  have hsem := hadamard_run k s st ht he hd
  generalize hu : ((hadCall k).run (hadPrepare.run st).1).1 = u at *
  have hsaved := hadSave_cost k s u
    (by simpa [hadamard,run_seq_fst,hu,hadSave,Stmt.run,Function.update] using hsem.base)
    (by simpa [hadamard,run_seq_fst,hu,hadSave,Stmt.run,Function.update] using hsem.auxiliary)
    (by simpa [hadamard,run_seq_fst,hu,hadSave,Stmt.run,Function.update] using hsem.linear)
    (by simpa [hadamard,run_seq_fst,hu,hadSave,Stmt.run,Function.update] using hsem.factors)
  have hcode : Nat.size (st.regs 151) ≤ W := hdb 1
  have hbasic := budget_basic t (k.dimension n) m W
  have harg : 2 ^ t+k.degree+Nat.size (st.regs 151)+5 ≤ budget t (k.dimension n) m W := by
    have := k.degree_le
    omega
  have hA : 1 ≤ budget t (k.dimension n) m W := (by decide : 1 ≤ 20).trans hbasic.1
  have hpow : budget t (k.dimension n) m W ≤ (budget t (k.dimension n) m W)^5 :=
    Nat.le_pow (by decide)
  have hp' := hp.trans (Nat.mul_le_mul_left _ (hbasic.2.1.trans hpow))
  have hh' := hh.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left harg 5))
  have hc' : (hadSave.run u).2 ≤ 10*(budget t (k.dimension n) m W)^5 := by
    exact hsaved.trans (Nat.mul_le_mul_left _ ((by omega : 2 ^ t+1 ≤ budget t
      (k.dimension n) m W).trans hpow))
  have h1 := Nat.one_le_pow 5 (budget t (k.dimension n) m W) hA
  simp only [hadamard,run_seq_snd,hu]
  unfold hadConstant
  nlinarith only [hp',hh',hc',h1]

theorem coordinate_cost (prep : Stmt 180 80) (dst : Fin 80) (st : State 180 80)
    (N base code : ℕ)
    (hN : (prep.run st).1.regs 5 = N) (hb : (prep.run st).1.regs 6 = base)
    (hc : (prep.run st).1.regs 0 = code) (he : (prep.run st).1.lists 2 = []) :
    ((Stmt.seq prep (.seq uniform (.copy 1 dst))).run st).2 ≤
      (prep.run st).2+(MixedRadixDecode.passConstant+24)*
        (N*(Nat.size base+1)+N+Nat.size code+3)^2+N*(Nat.size code+1)+3 := by
  let v := (prep.run st).1.restrict (Fin.castLE (by decide : 7 ≤ 180))
    (Fin.castLE (by decide : 3 ≤ 80))
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

def pointConstant (src : Fin 180) : ℕ :=
  fixedConstant (pointPrepare src 164)+InnerSeed.coordinateConstant

omit [NeZero t] in
theorem point_cost (src : Fin 180) (hsrc : 150 ≤ src.val ∧ src.val < 157)
    (dst : Fin 80) (d W : ℕ) (st : State 180 80)
    (hn : st.regs 164 = d) (hq : st.regs 162 = 2 ^ t) (he : st.lists 65 = [])
    (hb : SourceBound W st) (hd : DataBound W st) :
    ((point src 164 dst).run st).2 ≤ pointConstant src*(budget t d m W)^4 := by
  have hp := fixed_cost (pointPrepare src 164) (by simp [pointPrepare,Stmt.loopFree])
    (by
      intro i hi
      change i ∈ [src,164,162] at hi
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl | rfl | rfl
      · exact Or.inr hsrc
      · exact Or.inl ⟨by decide,by decide⟩
      · exact Or.inl ⟨by decide,by decide⟩)
    (by simp only [pointPrepare,Stmt.lUses]; decide) W st hb hd
  have hc := coordinate_cost (pointPrepare src 164) dst st d (2 ^ t) (st.regs src)
    (by simp [pointPrepare,Stmt.run,Expr.eval,Function.update,hn])
    (by simp [pointPrepare,Stmt.run,Expr.eval,Function.update,hq])
    (by simp [pointPrepare,Stmt.run,Expr.eval,Function.update])
    (by simp [pointPrepare,Stmt.run,Function.update,he])
  have hbasic := budget_basic t d m W
  have hA : 1 ≤ budget t d m W := (by decide : 1 ≤ 20).trans hbasic.1
  have hqsize : Nat.size (2 ^ t) ≤ budget t d m W := by
    simpa only [Nat.size_pow] using hbasic.2.2.1
  have hs : Nat.size (st.regs src) ≤ W := by
    have hi : dataPort ⟨src.val-150,by omega⟩ = src := by
      apply Fin.ext; simp only [dataPort]; omega
    rw [← hi]; exact hd _
  exact hc.trans (InnerSeed.coordinate_bound _ _ _ _ _ _ hA (by omega) hqsize
    (hs.trans (by omega)) (hp.trans (Nat.mul_le_mul_left _
      (hbasic.2.1.trans (Nat.le_pow (by decide : 0<4))))))


def directionConstant : ℕ := fixedConstant directionPrepare+InnerSeed.coordinateConstant

omit [NeZero t] in
theorem direction_cost (d W : ℕ) (st : State 180 80)
    (hm : st.regs 161 = m) (hq : st.regs 162 = 2 ^ t) (he : st.lists 65 = [])
    (hb : SourceBound W st) (hd : DataBound W st) :
    (direction.run st).2 ≤ directionConstant*(budget t d m W)^4 := by
  have hp := fixed_cost directionPrepare (by decide) (by decide) (by decide) W st hb hd
  have hc := coordinate_cost directionPrepare 44 st (4*m) (2 ^ t) (st.regs 153)
    (by simp [directionPrepare,Stmt.run,Expr.eval,Function.update,hm])
    (by simp [directionPrepare,Stmt.run,Expr.eval,Function.update,hq])
    (by simp [directionPrepare,Stmt.run,Expr.eval,Function.update])
    (by simp [directionPrepare,Stmt.run,Function.update,he])
  have hbasic := budget_basic t d m W
  have hA : 1 ≤ budget t d m W := (by decide : 1 ≤ 20).trans hbasic.1
  have hqsize : Nat.size (2 ^ t) ≤ budget t d m W := by
    simpa only [Nat.size_pow] using hbasic.2.2.1
  have hs : Nat.size (st.regs 153) ≤ W := hd 3
  exact hc.trans (InnerSeed.coordinate_bound _ _ _ _ _ _ hA
    (Nat.mul_le_mul_left 4 hbasic.2.2.2.2.1) hqsize (hs.trans (by omega))
    (hp.trans (Nat.mul_le_mul_left _ (hbasic.2.1.trans (Nat.le_pow (by decide : 0<4))))))

def bitsConstant : ℕ := fixedConstant bitPrepare+InnerSeed.coordinateConstant

omit [NeZero t] in
theorem bits_cost (d m W : ℕ) (st : State 180 80)
    (ht : st.regs 160 = t) (he : st.lists 65 = [])
    (hb : SourceBound W st) (hd : DataBound W st) :
    (bits.run st).2 ≤ bitsConstant*(budget t d m W)^4 := by
  have hp := fixed_cost bitPrepare (by decide) (by decide) (by decide) W st hb hd
  have hc := coordinate_cost bitPrepare 45 st t 2 (st.regs 152)
    (by simp [bitPrepare,Stmt.run,Expr.eval,Function.update,ht])
    (by simp [bitPrepare,Stmt.run,Expr.eval,Function.update])
    (by simp [bitPrepare,Stmt.run,Expr.eval,Function.update])
    (by simp [bitPrepare,Stmt.run,Function.update,he])
  have hbasic := budget_basic t d m W
  have hA : 1 ≤ budget t d m W := (by decide : 1 ≤ 20).trans hbasic.1
  have h2 : Nat.size 2 ≤ budget t d m W := by change 2 ≤ _; omega
  have hs : Nat.size (st.regs 152) ≤ W := hd 2
  exact hc.trans (InnerSeed.coordinate_bound _ _ _ _ _ _ hA (by omega) h2
    (hs.trans (by omega)) (hp.trans (Nat.mul_le_mul_left _
      (hbasic.2.1.trans (Nat.le_pow (by decide : 0<4))))))

end PCP.Lang.OuterSeed
