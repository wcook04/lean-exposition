/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Complexity.BinaryRootPredicateLang

/-!
# Charged cost of the concrete cube-root predicate
-/

namespace PCP.Lang.BinaryRootPredicate

open PCP.Algebraic BinaryField BinaryFieldWordCode

theorem serialize_cost (st : State 36 11) (he : st.lists 7 = []) :
    (serialize.run st).2 ≤ 100 * (st.regs 20 + Nat.size (st.regs 33) + 1) ^ 2 := by
  rw [serialize, Stmt.run_rename_cost _ id serialLists Function.injective_id serialLists_injective]
  exact BinaryPolynomialSelector.materialize_cost _ he

theorem power36_cost {t : ℕ} [NeZero t] (st : State 36 11)
    (w : BinaryWordMaterialization.Word t) (p : ℕ)
    (hm : st.lists 3 = encode (BinaryWordMaterialization.modulus t))
    (hw : st.lists 8 = encode w) (hp : st.lists 9 = p.bits.map Bool.toNat)
    (he : st.lists 7 = []) :
    (power36.run st).2 ≤ 15000 * (t + p.bits.length + 1) ^ 4 := by
  rw [power36, Stmt.run_rename_cost BinaryFieldPower.power powerRegs id
    (show Function.Injective powerRegs from Fin.castLE_injective _) Function.injective_id]
  exact BinaryFieldPower.power_cost (Nat.pos_of_ne_zero (NeZero.ne t)) _ _ w p.bits hm hw hp he

theorem decode36_cost (st : State 36 11) (hb : Bits (st.lists 1)) :
    (decode36.run st).2 ≤ (WordCodec.passConstant * 3 + 20) * ((st.lists 1).length + 1) ^ 2 := by
  rw [decode36, Stmt.run_rename_cost WordCodec.decode decodeRegs decodeLists
    (show Function.Injective decodeRegs from Fin.castLE_injective _)
    (Function.injective_of_subsingleton _)]
  exact WordCodec.decode_cost _ hb

theorem exponent_cost (st : State 36 11) (he : st.lists 7 = []) :
    ((exponent).run st).2 ≤ 30 := by
  simp [exponent, Stmt.run, Expr.cost, Expr.readSize, Expr.eval,
    Function.update, he, listSize, show Nat.size 1 = 1 from rfl]

theorem rootPower_cost {t : ℕ} [NeZero t] (st : State 36 11)
    (i : Fin (2 ^ t)) (h20 : st.regs 20 = t) (h33 : st.regs 33 = i.val)
    (hm : st.lists 3 = encode (BinaryWordMaterialization.modulus t)) (he : st.lists 7 = []) :
    ((rootPower).run st).2 ≤ 20000 * (t + 4) ^ 4 := by
  have hserial := serialize_cost st he
  have hsize : Nat.size i.val ≤ t := Nat.size_le.mpr i.isLt
  have hserial' : (serialize.run st).2 ≤ 100 * (2 * t + 1) ^ 2 := by
    rw [h20, h33] at hserial
    exact hserial.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2))
  have hs8 := serialize_run st he
  rw [h20, h33, ← encode_word] at hs8
  have hs3 := run_lists_frame serialize 3 (by decide) st
  have hs7 := run_lists_frame serialize 7 (by decide) st
  simp only [rootPower, run_seq_snd]
  generalize hs : (serialize.run st).1 = s at *
  have hexp := exponent_cost s (hs7.trans he)
  have hu9 := exponent_run s (hs7.trans he)
  have hu3 := run_lists_frame (exponent) 3 (by decide) s
  have hu7 := run_lists_frame (exponent) 7 (by decide) s
  have hu8 := run_lists_frame (exponent) 8 (by decide) s
  generalize hu : ((exponent).run s).1 = u at *
  have hpow := power36_cost u (word t i) (3) (hu3.trans (hs3.trans hm))
    (hu8.trans hs8) hu9 (hu7.trans (hs7.trans he))
  have hlen : (3 : ℕ).bits.length ≤ 3 := by decide
  have hpow' : (power36.run u).2 ≤ 15000 * (t + 4) ^ 4 :=
    hpow.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 4))
  nlinarith [Nat.zero_le (t ^ 4), Nat.zero_le (t ^ 3), Nat.zero_le (t ^ 2)]

theorem rootTail_cost (st : State 36 11) (t : ℕ)
    (h1 : Nat.size (st.regs 1) ≤ t) (h33 : Nat.size (st.regs 33) ≤ t) :
    (rootTail.run st).2 ≤ 10000000 * (t + 1) := by
  have hc := loopFree_cost_le rootTail (by decide) st t
    (by
      intro r hr
      have hu : rootTail.uses = [1, 33] := rfl
      rw [hu] at hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact h1
      · exact h33)
    (by simp [rootTail, Stmt.lUses])
  have hC : rootTail.C * (rootTail.width + rootTail.csize + 1) ≤ 10000000 := by decide
  exact hc.trans (Nat.mul_le_mul_right _ hC)

/-- A root predicate is evaluated by an actual program at quartic cost in word width. -/
theorem testRoot_cost {t : ℕ} [NeZero t] (st : State 36 11)
    (i : Fin (2 ^ t)) (h20 : st.regs 20 = t) (h33 : st.regs 33 = i.val)
    (hm : st.lists 3 = encode (BinaryWordMaterialization.modulus t)) (he : st.lists 7 = []) :
    ((testRoot).run st).2 ≤ 100000000 * (t + 4) ^ 4 := by
  have hpower := rootPower_cost st i h20 h33 hm he
  have hs1 := rootPower_run st i h20 h33 hm he
  have hs33 := run_regs_frame (rootPower) 33 (by decide) st
  simp only [testRoot, run_seq_snd]
  generalize hs : ((rootPower).run st).1 = s at *
  have hdecode := decode36_cost s (by rw [hs1]; exact encode_bits _)
  have hdecode' : (decode36.run s).2 ≤ 10000000 * (t + 1) ^ 2 := by
    rw [hs1, encode_length] at hdecode
    exact hdecode.trans (Nat.mul_le_mul_right _ (by decide))
  have hu1 := decode36_run s
  rw [hs1] at hu1
  have hu33 := run_regs_frame decode36 33 (by decide) s
  rw [hs33, h33] at hu33
  generalize hu : (decode36.run s).1 = u at *
  have h1 : Nat.size (u.regs 1) ≤ t := by
    rw [hu1]
    apply Nat.size_le.mpr
    simpa using WordCodec.value_lt (encode_bits
      (BinaryWordMaterialization.fieldPower (word t i) (3)))
  have htail := rootTail_cost u t h1 (by rw [hu33]; exact Nat.size_le.mpr i.isLt)
  nlinarith [Nat.zero_le (t ^ 4), Nat.zero_le (t ^ 3), Nat.zero_le (t ^ 2)]

end PCP.Lang.BinaryRootPredicate
