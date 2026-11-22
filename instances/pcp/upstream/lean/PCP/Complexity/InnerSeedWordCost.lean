/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Complexity.InnerSeedResources

/-! # Charged costs of materializing the inner seed's stored words -/

namespace PCP.Lang.InnerSeed

open PCP.Algebraic ThreeColorSeedIndex InterpolationBranch

variable {t n m : ℕ} [NeZero t]

attribute [local irreducible] HadamardSeed.program hadCall

def hadConstant : ℕ := fixedConstant hadPrepare + HadamardSeed.seedConstant + 1

theorem hadamard_cost (s : InnerBranch.Seed t m) (W : ℕ) (st : State 140 44)
    (ht : st.regs 120 = t) (he : st.lists 41 = []) (hd : Data s st)
    (hb : SourceBound W st) (hdb : DataBound W st) :
    (hadamard.run st).2 ≤ hadConstant * (budget t m W) ^ 5 := by
  have hp := fixed_cost hadPrepare (by decide) (by decide) (by decide) W st hb hdb
  have hs : st.regs 107 = ((hadamardCodec t 1).equiv s.2.1.2).val := hd 4
  have hh := HadamardSeed.program_cost s.2.1.2
    ((hadPrepare.run st).1.restrict (Fin.castLE (by decide)) (Fin.castLE (by decide)))
    (by simpa [hadPrepare, Stmt.run, Expr.eval, Function.update, State.restrict] using ht)
    (by simpa [hadPrepare, Stmt.run, Expr.eval, Function.update, State.restrict] using he)
    (by simpa [hadPrepare, Stmt.run, Expr.eval, Function.update, State.restrict] using hs)
  rw [← call_result (by decide) (by decide) (HadamardSeed.program 1)] at hh
  rw [show call (by decide) (by decide) (HadamardSeed.program 1) = hadCall by
    unfold hadCall; rfl] at hh
  have h96 : ((hadPrepare.run st).1.restrict (Fin.castLE (by decide : 100 ≤ 140))
      (Fin.castLE (by decide : 32 ≤ 44))).regs 96 = st.regs 107 := by
    simp [hadPrepare, Stmt.run, Expr.eval, Function.update, State.restrict]
  rw [h96] at hh
  have h107 : Nat.size (st.regs 107) ≤ W := hdb 4
  have hbasic := budget_basic t m W
  have hlin : W + 1 ≤ budget t m W := hbasic.2.1
  have harg : 2 ^ t + 1 + Nat.size (st.regs 107) + 5 ≤ budget t m W := by
    have hh := hbasic.2.2.2.2.1
    omega
  have hp' := hp.trans (Nat.mul_le_mul_left _
    (hlin.trans (Nat.le_pow (by decide : 0 < 5))))
  have hh' := hh.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left harg 5))
  have h1 : 1 ≤ (budget t m W) ^ 5 := Nat.one_le_pow _ _ ((by decide : 1 ≤ 10).trans hbasic.1)
  simp only [hadamard, run_seq_snd]
  unfold hadConstant
  nlinarith only [hp', hh', h1]

attribute [local irreducible] uniform

/-- The copy after decoding is charged for the complete materialized digit list. -/
theorem coordinate_cost (prep : Stmt 140 44) (dst : Fin 44) (st : State 140 44)
    (N base code : ℕ)
    (hN : (prep.run st).1.regs 5 = N) (hbase : (prep.run st).1.regs 6 = base)
    (hcode : (prep.run st).1.regs 0 = code) (he : (prep.run st).1.lists 7 = []) :
    ((Stmt.seq prep (.seq (call (by decide) (by decide) uniform) (.copy 1 dst))).run st).2 ≤
      (prep.run st).2 + (MixedRadixDecode.passConstant + 24) *
        (N * (Nat.size base + 1) + N + Nat.size code + 3) ^ 2 +
          N * (Nat.size code + 1) + 3 := by
  let v := (prep.run st).1.restrict (Fin.castLE (by decide : 7 ≤ 140))
    ((Fin.castLE (by decide : 8 ≤ 44)) ∘ uniformLists)
  have hv : v.lists 2 = [] := he
  have hc := UniformDecode.program_cost v hv
  have hout := (UniformDecode.program_run v hv).1
  dsimp only [v] at hc hout
  rw [← uniform_result] at hc hout
  change ((call (by decide) (by decide) uniform).run (prep.run st).1).2 ≤
    (MixedRadixDecode.passConstant + 24) *
      ((prep.run st).1.regs 5 * (Nat.size ((prep.run st).1.regs 6) + 1) +
        (prep.run st).1.regs 5 + Nat.size ((prep.run st).1.regs 0) + 3) ^ 2 at hc
  change ((call (by decide) (by decide) uniform).run (prep.run st).1).1.lists 1 =
    (MixedRadixDecode.split ((prep.run st).1.regs 0)
      (List.replicate ((prep.run st).1.regs 5) ((prep.run st).1.regs 6))).1 at hout
  rw [hN, hbase, hcode] at hc hout
  have hls := MixedRadixDecode.split_listSize code (List.replicate N base)
  rw [List.length_replicate] at hls
  simp only [run_seq_snd, run_copy_snd, hout]
  omega

def coordinateConstant : ℕ := 256 * (MixedRadixDecode.passConstant + 24) + 11

theorem coordinate_bound (P N base code A C : ℕ) (hA : 1 ≤ A)
    (hN : N ≤ 4 * A) (hb : Nat.size base ≤ A) (hc : Nat.size code ≤ A)
    (hP : P ≤ C * A ^ 4) :
    P + (MixedRadixDecode.passConstant + 24) *
      (N * (Nat.size base + 1) + N + Nat.size code + 3) ^ 2 +
        N * (Nat.size code + 1) + 3 ≤ (C + coordinateConstant) * A ^ 4 := by
  have hA2 : A ≤ A ^ 2 := Nat.le_pow (by decide)
  have hA4 : A ^ 2 ≤ A ^ 4 := Nat.pow_le_pow_right hA (by decide)
  have hmul := Nat.mul_le_mul hN (Nat.add_le_add_right hb 1)
  have harg : N * (Nat.size base + 1) + N + Nat.size code + 3 ≤ 16 * A ^ 2 := by
    nlinarith only [hmul, hN, hc, hA, hA2]
  have hs := Nat.pow_le_pow_left harg 2
  have hterm := Nat.mul_le_mul_left (MixedRadixDecode.passConstant + 24) hs
  have hcopy := Nat.mul_le_mul hN (Nat.add_le_add_right hc 1)
  unfold coordinateConstant
  nlinarith only [hP, hterm, hcopy, hA, hA2, hA4]

def pointConstant (src : Fin 140) : ℕ := fixedConstant (pointPrepare src) + coordinateConstant

omit [NeZero t] in
theorem point_cost (src : Fin 140) (hsrc : 103 ≤ src.val ∧ src.val < 110)
    (dst : Fin 44) (W : ℕ) (st : State 140 44)
    (hm : st.regs 121 = m) (hq : st.regs 122 = 2 ^ t) (he : st.lists 41 = [])
    (hb : SourceBound W st) (hd : DataBound W st) :
    ((point src dst).run st).2 ≤ pointConstant src * (budget t m W) ^ 4 := by
  have hp := fixed_cost (pointPrepare src) (by simp [pointPrepare, Stmt.loopFree])
    (by
      intro i hi
      change i ∈ [src, 121, 122] at hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl
      · exact Or.inr hsrc
      · exact Or.inl ⟨by decide, by decide⟩
      · exact Or.inl ⟨by decide, by decide⟩)
    (by simp only [pointPrepare, Stmt.lUses]; decide) W st hb hd
  have hc := coordinate_cost (pointPrepare src) dst st (4 * m) (2 ^ t) (st.regs src)
    (by simp [pointPrepare, Stmt.run, Expr.eval, Function.update, hm])
    (by simp [pointPrepare, Stmt.run, Expr.eval, Function.update, hq])
    (by simp [pointPrepare, Stmt.run, Expr.eval, Function.update])
    (by simp [pointPrepare, Stmt.run, Function.update, he])
  have hbasic := budget_basic t m W
  have hA : 1 ≤ budget t m W := (by decide : 1 ≤ 10).trans hbasic.1
  have hqsize : Nat.size (2 ^ t) ≤ budget t m W := by
    simpa only [Nat.size_pow] using hbasic.2.2.2.2.2.1
  have hsrcsize : Nat.size (st.regs src) ≤ W := by
    have heq : dataPort ⟨src.val - 103, by omega⟩ = src := by
      apply Fin.ext; simp only [dataPort]; omega
    rw [← heq]
    exact hd _
  exact hc.trans (coordinate_bound _ _ _ _ _ _ hA
    (Nat.mul_le_mul_left 4 hbasic.2.2.2.2.2.2) hqsize
    (hsrcsize.trans (Nat.le_succ W |>.trans hbasic.2.1))
    (hp.trans (Nat.mul_le_mul_left _
      (hbasic.2.1.trans (Nat.le_pow (by decide : 0 < 4))))))

def bitsConstant : ℕ := fixedConstant bitPrepare + coordinateConstant

omit [NeZero t] in
theorem bits_cost (W : ℕ) (st : State 140 44)
    (ht : st.regs 120 = t) (he : st.lists 41 = [])
    (hb : SourceBound W st) (hd : DataBound W st) :
    (bits.run st).2 ≤ bitsConstant * (budget t m W) ^ 4 := by
  have hp := fixed_cost bitPrepare (by decide) (by decide) (by decide) W st hb hd
  have hc := coordinate_cost bitPrepare 34 st t 2 (st.regs 103)
    (by simp [bitPrepare, Stmt.run, Expr.eval, Function.update, ht])
    (by simp [bitPrepare, Stmt.run, Expr.eval, Function.update])
    (by simp [bitPrepare, Stmt.run, Expr.eval, Function.update])
    (by simp [bitPrepare, Stmt.run, Function.update, he])
  have hbasic := budget_basic t m W
  have hA : 1 ≤ budget t m W := (by decide : 1 ≤ 10).trans hbasic.1
  have hN : t ≤ 4 * budget t m W := by
    have hh := hbasic.2.2.2.2.2.1
    omega
  have hcode : Nat.size (st.regs 103) ≤ budget t m W :=
    (hd 0).trans ((Nat.le_succ W).trans hbasic.2.1)
  exact hc.trans (coordinate_bound _ _ _ _ _ _ hA hN
    ((by decide : Nat.size 2 ≤ 10).trans hbasic.1) hcode
    (hp.trans (Nat.mul_le_mul_left _
      (hbasic.2.1.trans (Nat.le_pow (by decide : 0 < 4))))))

end PCP.Lang.InnerSeed
