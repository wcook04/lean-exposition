/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Complexity.InnerSeedResources

/-! # Polynomial charged cost of extracting the actual inner seed cells -/

namespace PCP.Lang.InnerSeed

open PCP.Algebraic ThreeColorSeedIndex InterpolationBranch

variable {t n m : ℕ} [NeZero t]

theorem innerTerms_bound (t m : ℕ) (i : Fin 7) :
    (NestedSeed.innerTerms i).eval ![0, m, 4, t] ≤ 4 * (t + m + 1) ^ 2 := by
  fin_cases i <;> simp [NestedSeed.innerTerms, NestedSeed.innerPointBits_eval,
    NestedSeed.hadamard_eval,
    ThreeColorSeedSize.hadamardBits_one, ArithmeticExpression.Term.eval]
  all_goals nlinarith [Nat.zero_le (t ^ 2), Nat.zero_le (m ^ 2), Nat.zero_le (t * m)]

def unpackConstant : ℕ := fixedConstant prepare +
  25 * ComputedSeed.programConstant NestedSeed.innerTerms + 24

theorem parse_cost (s : InnerBranch.Seed t m) (st : State 140 44)
    (hc : st.lists 1 = List.ofFn (codes s)) :
    (parse.run st).2 = 2 * listSize (List.ofFn (codes s)) + 8 := by
  simp [parse, Stmt.run, Function.update, hc, List.ofFn_succ, listSize]
  ring

theorem unpack_cost (a : Fin 5 → Field t) (site : StandardCorrection.Site (Field t) n)
    (s : InnerBranch.Seed t m) (W : ℕ) (st : State 140 44) (hc : Public m a site st)
    (hb : SourceBound W st)
    (hs : st.regs 132 = ((innerCodec (BinaryMaterializedField.coordinates t) m 4).equiv s).val) :
    (unpack.run st).2 ≤ unpackConstant * (budget t m W) ^ 4 := by
  let A := budget t m W
  have hbasic := budget_basic t m W
  have hA : 1 ≤ A := (by decide : 1 ≤ 10).trans hbasic.1
  have hlin : W + 1 ≤ A := hbasic.2.1
  have hp := source_cost prepare (by decide) (by decide) (by decide) W st hb
  have hpc := prepare_context s st hc.width hc.base hc.empty hs
  have hcode :
      Nat.size ((innerCodec (BinaryMaterializedField.coordinates t) m 4).equiv s).val ≤ W :=
    hs ▸ hb.regs 132 (by decide) (by decide)
  have hparam : ∀ i : Fin 4, Nat.size (![0, m, 4, t] i) ≤ W + t + m + 4 := by
    intro i
    fin_cases i <;> apply (size_le_self _).trans <;> dsimp <;> omega
  have hd := ComputedSeed.program_cost NestedSeed.innerTerms 0 m 4 t _
    (4 * (t + m + 1) ^ 2) (W + t + m + 4) _ hpc hparam (innerTerms_bound t m)
    (hcode.trans (by omega))
  change (NestedSeed.inner.run _).2 ≤ _ at hd
  rw [← call_result (by decide) (by decide) NestedSeed.inner] at hd
  change (decoder.run (prepare.run st).1).2 ≤ _ at hd
  have hsmall : t + m + 1 ≤ A := hbasic.2.2.1
  have hrest : W + t + m + 4 + 1 ≤ A := by
    simpa only [Nat.add_assoc] using hbasic.2.2.2.1
  have hA2 : A ≤ A ^ 2 := Nat.le_pow (by decide)
  have harg : 4 * (t + m + 1) ^ 2 + (W + t + m + 4) + 1 ≤ 5 * A ^ 2 := by
    have hh := Nat.pow_le_pow_left hsmall 2
    omega
  have hd' := hd.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left harg 2))
  have hpow : A ≤ A ^ 4 := Nat.le_pow (by decide)
  have hp' := hp.trans (Nat.mul_le_mul_left _ (hlin.trans hpow))
  have houtput := decode_run s st hc.width hc.base hc.empty hs
  have hparse := parse_cost s (decode.run st).1 houtput
  have hls := codes_listSize s W hcode
  have hparse' : (parse.run (decode.run st).1).2 ≤ 22 * A ^ 4 := by
    rw [hparse]
    have h1 : 1 ≤ A ^ 4 := Nat.one_le_pow _ _ hA
    nlinarith only [hls, hlin, hpow, h1]
  have h1 : 1 ≤ A ^ 4 := Nat.one_le_pow _ _ hA
  simp only [unpack, decode, run_seq_snd]
  change _ ≤ unpackConstant * A ^ 4
  dsimp only [decode] at hparse'
  unfold unpackConstant
  nlinarith only [hp', hd', hparse', h1]

end PCP.Lang.InnerSeed
