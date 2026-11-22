/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Complexity.BinaryPolynomialMaskScan

/-!
# Cost of the joint-mask factor scan
-/

namespace PCP.Lang.BinaryPolynomialMaskScan

open BinaryPolynomialCoefficient BinaryPolynomialFactor BooleanLoops

theorem factor32_cost (st : State 32 2) (t : ℕ)
    (ht : st.regs 20 = t) (hcode : st.regs 21 < 2 ^ t)
    (hd : st.regs 8 ≤ t) (he : st.regs 9 ≤ t)
    (hj : st.regs 10 < 2 ^ st.regs 8) (hk : st.regs 11 < 2 ^ st.regs 9) :
    (factor32.run st).2 ≤ 240000 * (2 ^ t + 1) ^ 4 := by
  rw [factor32, Stmt.run_rename_cost matchProduct factorEmbedding id
    (show Function.Injective factorEmbedding from Fin.castLE_injective _)
    Function.injective_id]
  exact matchProduct_cost _ t ht hcode hd he hj hk

theorem maskPrepare_cost (st : State 32 2) (q : ℕ)
    (hn : st.regs 25 ≤ q) (hw : st.regs 29 ≤ q) :
    (maskPrepare.run st).2 ≤ 800 * (q + 1) := by
  have hc := loopFree_cost_le maskPrepare (by decide) st q
    (by
      intro r hr
      have hu : maskPrepare.uses = [25, 29, 25, 29] := rfl
      rw [hu] at hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact (size_le_self _).trans hn
      · exact (size_le_self _).trans hw
      · exact (size_le_self _).trans hn
      · exact (size_le_self _).trans hw)
    (by simp [maskPrepare, Stmt.lUses])
  have hC : maskPrepare.C * (maskPrepare.width + maskPrepare.csize + 1) ≤ 800 := by decide
  exact hc.trans (Nat.mul_le_mul_right _ hC)

theorem maskTail_cost (st : State 32 2) (q : ℕ)
    (h30 : st.regs 30 = 1) (h22 : st.regs 22 < 2)
    (h27 : st.regs 27 < 2) (h25 : st.regs 25 ≤ q) :
    (maskTail.run st).2 ≤ 5000 * (q + 2) := by
  have hc := loopFree_cost_le maskTail (by decide) st (q + 1)
    (by
      intro r hr
      have hu : maskTail.uses = [30, 22, 27, 25, 30] := rfl
      rw [hu] at hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · rw [h30]; exact (show Nat.size 1 = 1 from rfl).le.trans (by omega)
      · exact (size_le_self _).trans (by omega)
      · exact (size_le_self _).trans (by omega)
      · exact (size_le_self _).trans (by omega)
      · rw [h30]; exact (show Nat.size 1 = 1 from rfl).le.trans (by omega))
    (by simp [maskTail, Stmt.lUses])
  have hC : maskTail.C * (maskTail.width + maskTail.csize + 1) ≤ 5000 := by decide
  exact hc.trans (by simpa only [Nat.add_assoc] using Nat.mul_le_mul_right (q + 1 + 1) hC)

theorem maskBody_cost (t code d : ℕ) (st : State 32 2) (hd : d ≤ t)
    (hcode : code < 2 ^ t) (hc : Context t code d (t - d) (2 ^ t) (2 ^ d) st)
    (hn : st.regs 25 < 2 ^ t) (hf : st.regs 27 < 2) :
    (maskBody.run st).2 ≤ 260000 * (2 ^ t + 1) ^ 4 := by
  have hwidth : 2 ^ d ≤ 2 ^ t := Nat.pow_le_pow_right (by decide) hd
  have hprep := maskPrepare_cost st (2 ^ t) hn.le (by rw [hc.2.2.2.2.2.1]; exact hwidth)
  let p := setReg (setReg st 10 (st.regs 25 % st.regs 29)) 11
    (st.regs 25 / st.regs 29)
  have hp : (maskPrepare.run st).1 = p := rfl
  have hpow : 2 ^ t = 2 ^ d * 2 ^ (t - d) := by rw [← pow_add, Nat.add_sub_of_le hd]
  have hk : st.regs 25 / 2 ^ d < 2 ^ (t - d) := by
    apply (Nat.div_lt_iff_lt_mul (by positivity)).mpr
    simpa only [Nat.mul_comm] using hpow ▸ hn
  have hfac := factor32_cost p t
    (by simpa [p, Function.update] using hc.1)
    (by simpa [p, Function.update, hc.2.1] using hcode)
    (by simpa [p, Function.update, hc.2.2.1] using hd)
    (by simp [p, Function.update, hc.2.2.2.1])
    (by simpa [p, Function.update, hc.2.2.1, hc.2.2.2.2.2.1] using
      Nat.mod_lt (st.regs 25) (by positivity : 0 < 2 ^ d))
    (by simpa [p, Function.update, hc.2.2.2.1, hc.2.2.2.2.2.1] using hk)
  have hs30 := run_regs_frame factor32 30 (by decide) p
  have hs25 := run_regs_frame factor32 25 (by decide) p
  have hs27 := run_regs_frame factor32 27 (by decide) p
  have hs22 := factor32_run p
  simp only [p, setReg_regs, Function.update, Fin.reduceEq, dite_false] at hs30 hs25 hs27
  simp only [maskBody, run_seq_snd, hp]
  generalize hs : (factor32.run p).1 = s at *
  have htail := maskTail_cost s (2 ^ t) (hs30.trans hc.2.2.2.2.2.2)
    (by rw [hs22]; exact truth_lt_two _) (by simpa only [hs27] using hf)
    (by simpa only [hs25] using hn.le)
  nlinarith [Nat.zero_le ((2 ^ t) ^ 4), Nat.zero_le ((2 ^ t) ^ 3),
    Nat.zero_le ((2 ^ t) ^ 2)]

theorem maskScan_cost (t code d : ℕ) (st : State 32 2) (hd : d ≤ t)
    (hcode : code < 2 ^ t) (hc : Context t code d (t - d) (2 ^ t) (2 ^ d) st)
    (hf : st.regs 27 < 2) :
    (maskScan.run st).2 ≤ 270000 * (2 ^ t + 1) ^ 5 := by
  let q := 2 ^ t
  let s := setReg st 25 0
  have hi : Context t code d (t - d) q (2 ^ d) s := by
    simpa [Context, s, q, Function.update] using hc
  have hit := iterate_all_cost maskBody.run (Nat.size q + 1) q
    (260000 * (q + 1) ^ 4) 25 27 (Context t code d (t - d) q (2 ^ d))
    (NoFactor t code d (t - d) (2 ^ d))
    (by
      intro n u _ hu hn
      obtain ⟨hh, hj⟩ := maskBody_step u hu.2.2.2.2.2.2
      refine ⟨maskBody_context _ _ _ _ _ _ u hu, hj.trans (by rw [hn]), ?_⟩
      simpa only [hu.1, hu.2.1, hu.2.2.1, hu.2.2.2.1,
        hu.2.2.2.2.2.1, hn] using hh)
    (by
      intro n u hn hu hi hf
      exact maskBody_cost t code d u hd hcode hu (hi ▸ hn) hf)
    s hi (by simp [s]) (by simpa [s, Function.update] using hf)
  have hsize : Nat.size q ≤ q := size_le_self _
  simp only [maskScan, run_seq_snd, run_assign_fst, Expr.eval, run_loop_snd,
    setReg_regs, Function.update_of_ne (by decide : (28 : Fin 32) ≠ 25), hc.2.2.2.2.1]
  change (Expr.const 0).cost st.regs +
    ((iterate maskBody.run (Nat.size q + 1) q s).2 + Nat.size q + 1) + 1 ≤ _
  simp only [Expr.cost, Expr.readSize, Expr.eval, Nat.size_zero]
  change _ ≤ 270000 * (q + 1) ^ 5
  have hb : q * (Nat.size q + 1 + 260000 * (q + 1) ^ 4) ≤
      q * (q + 1 + 260000 * (q + 1) ^ 4) := Nat.mul_le_mul_left _ (by omega)
  have hb' := hit.trans hb
  nlinarith [Nat.zero_le (q ^ 5), Nat.zero_le (q ^ 4), Nat.zero_le (q ^ 3),
    Nat.zero_le (q ^ 2)]

end PCP.Lang.BinaryPolynomialMaskScan
