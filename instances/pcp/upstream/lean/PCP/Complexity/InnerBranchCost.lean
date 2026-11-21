/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Complexity.InnerBranchHadamardCost
import PCP.Complexity.InnerBranchFrame

/-!
# Polynomial charged cost of the complete inner selector

Only sizes of actual physical addresses and their public payloads are bounded.
The program and its correctness are concrete; there is no callback premise.
-/

namespace PCP.Lang.InnerBranch

open PCP.Algebraic InterpolationBranch

variable {t n m : ℕ} [NeZero t]

attribute [local irreducible] interpCall hadamard interpolate

structure Bounds (a : Fin 5 → Field t) (site : StandardCorrection.Site (Field t) n)
    (s : Seed t m) (W : ℕ) : Prop where
  payload : ∀ i, Nat.size ((location site s.2.1.1).payload (t := t)
    (BinaryFieldCode.fieldEquiv t) i) ≤ W
  hadamard : ∀ p ∈ ComputableHadamardTest.queries (le_refl 1) s.2.1.2,
    Nat.size (address site s.2.1.1 p) ≤ W
  interpolation : QueryBound a 0 s.2.2.1.1.1 s.2.2.1.1.2 s.2.2.2 site W

theorem interpolate_cost (a : Fin 5 → Field t) (z : Field t) (u v : Point t m)
    (w : Fin t → ZMod 2) (site : StandardCorrection.Site (Field t) n)
    (qs : List ℕ) (bs : List Bool) (W : ℕ) (st : State 120 40)
    (hc : InterpolationBranch.Context a z u v w site (st.restrict interpRegs id))
    (hq : st.lists 36 = qs) (hb : st.lists 37 = bs.map Bool.toNat)
    (hbound : QueryBound a z u v w site W) :
    (interpolate.run st).2 ≤ (InterpolationBranch.costConstant + 20) * budget t m W st ^ 9 := by
  let B := budget t m W st
  have h := InterpolationBranch.program_cost a z u v w site W
    (st.restrict interpRegs id) hc hbound
  have ho := InterpolationBranch.program_run a z u v w site qs bs
    (st.restrict interpRegs id) hc hq hb
  rw [← interpCall_result] at h ho
  change (interpCall.run st).2 ≤ InterpolationBranch.costConstant *
    (InterpolationBranch.budget t m W (st.restrict interpRegs id)) ^ 7 at h
  have hbase : InterpolationBranch.budget t m W (st.restrict interpRegs id) ≤ B := by
    dsimp only [B, budget, InterpolationBranch.budget, State.restrict_lists, id_eq]
    omega
  have hB : 1 ≤ B := Nat.succ_le_succ (Nat.zero_le _)
  have hpow := (Nat.pow_le_pow_left hbase 7).trans
    (Nat.pow_le_pow_right hB (by decide : 7 ≤ 9))
  have hc' := h.trans (Nat.mul_le_mul_left _ hpow)
  have hs := queryCodes_size a z u v w site W hbound
  have hf := bool_size (check a z u v w site qs bs)
  have hWP : W + 1 ≤ B ^ 9 := by
    have arith : ∀ t m q W h b : ℕ, W + 1 ≤ t + 4 * m + q + W + h + b + 10 := by
      intros
      omega
    exact (arith _ _ _ _ _ _).trans (Nat.le_pow (by decide))
  simp only [interpolate, run_seq_snd]
  generalize hout : (interpCall.run st).1 = out at *
  change out.lists 20 = _ ∧ out.regs 11 = _ at ho
  simp only [run_copy_snd, run_copy_fst]
  change (interpCall.run st).2 + (listSize (out.lists 20) + 1 +
    (Nat.size (out.regs 11) + Nat.size (out.regs 11) + 1) + 1) + 1 ≤ _
  rw [ho.1, ho.2]
  have sumBound : ∀ C P x q f W : ℕ, x ≤ C * P → q ≤ 6 * (W + 1) →
      f ≤ 1 → W + 1 ≤ P →
      x + (q + 1 + (f + f + 1) + 1) + 1 ≤ (C + 20) * P := by
    intros
    nlinarith
  exact sumBound _ _ _ _ _ _ hc' hs hf hWP

def costConstant : ℕ := HadamardRow.branchConstant + InterpolationBranch.costConstant + 60

private theorem ite_cost {R Q : ℕ} (x : Fin R) (P Q' : Stmt R Q) (st : State R Q) :
    ((Stmt.ite x P Q').run st).2 =
      (if st.regs x ≠ 0 then (P.run st).2 else (Q'.run st).2) + Nat.size (st.regs x) + 1 := by
  simp only [Stmt.run]
  split_ifs <;> rfl

theorem program_cost (a : Fin 5 → Field t) (site : StandardCorrection.Site (Field t) n)
    (s : Seed t m) (qs : List ℕ) (bs : List Bool) (W : ℕ) (st : State 120 40)
    (hc : Context a site s st) (hq : st.lists 36 = qs) (hb : st.lists 37 = bs.map Bool.toNat)
    (hbound : Bounds a site s W) :
    (program.run st).2 ≤ costConstant * budget t m W st ^ 9 := by
  have hpos : 1 ≤ budget t m W st ^ 9 :=
    Nat.one_le_pow _ _ (Nat.succ_le_succ (Nat.zero_le _))
  cases hcoin : s.1 with
  | false =>
      have hz : st.regs 100 = 0 := hc.coin.trans (congrArg Bool.toNat hcoin)
      have h := hadamard_cost site s.2.1.1 s.2.1.2 qs bs W st hc.hadamard hc.payload
        hq hb hbound.payload hbound.hadamard
      have sumBound : ∀ A B P x : ℕ, x ≤ (A + 30) * P → 1 ≤ P →
          x + 1 ≤ (A + B + 60) * P := by
        intros
        nlinarith
      calc
        _ = (hadamard.run st).2 + 1 := by rw [program, ite_cost, hz]; rfl
        _ ≤ _ := sumBound _ _ _ _ h hpos
  | true =>
      have hz : st.regs 100 = 1 := hc.coin.trans (congrArg Bool.toNat hcoin)
      have h := interpolate_cost a _ _ _ _ site qs bs W st hc.interpolation hq hb
        hbound.interpolation
      have sumBound : ∀ A B P x : ℕ, x ≤ (B + 20) * P → 1 ≤ P →
          x + 2 ≤ (A + B + 60) * P := by
        intros
        nlinarith
      calc
        _ = (interpolate.run st).2 + 2 := by
          rw [program, ite_cost, hz]
          simp only [ne_eq, one_ne_zero, not_false_eq_true, ↓reduceIte]
          rfl
        _ ≤ _ := sumBound _ _ _ _ h hpos

end PCP.Lang.InnerBranch
