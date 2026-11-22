/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Complexity.CorrectionSeedSplitCost
import PCP.Complexity.CorrectionSeedVectorCost

/-! # Complete polynomial charged cost of correction-seed materialization -/

namespace PCP.Lang.CorrectionSeed

open PCP.Algebraic ThreeColorSeedIndex ThreeColorFullFieldSampling BinaryFieldCode

variable {t m : ℕ} [NeZero t] {σ : Type*}

attribute [local irreducible] splitSeed vector

theorem dimension_cost (W : ℕ) (st : State 220 96) (hb : SourceBound W st) :
    (dimension.run st).2 ≤ fixedConstant dimension * (W + 1) := by
  apply loopFree_cost_le dimension (by decide)
  · intro i hi
    change i ∈ [201] at hi
    simp only [List.mem_singleton] at hi
    subst i
    exact hb 1
  · intro L hL
    simp [dimension, Stmt.lUses] at hL

def costConstant : ℕ := splitConstant + fixedConstant dimension +
  vectorConstant 207 202 + vectorConstant 205 211 + 3

/-- The exponent bound describes the explicit radix formulas only. -/
theorem program_cost_bound (σc : Codec σ)
    (s : RawCallSeed (BinaryMaterializedField.Element t) σ m 4 t) (B W : ℕ)
    (st : State 220 96) (hc : Input σc s st) (hb : SourceBound W st)
    (hB : ∀ i, (NestedSeed.callTerms i).eval ![σc.size, m, 4, t] ≤ B) :
    (program.run st).2 ≤ costConstant * (σc.size + 4 * m + t + B + W + 10) ^ 4 := by
  let A := σc.size + 4 * m + t + B + W + 10
  have hcode :
      Nat.size ((callCodec (BinaryMaterializedField.coordinates t) σc m 4).equiv s).val ≤ W :=
    hc.seed ▸ hb 3
  have hsc := splitSeed_cost σc s B W st hc hb hB
  have hd := splitSeed_run σc s st hc
  have hc' := hc.split
  have hb' := hb.split
  simp only [program, run_seq_snd]
  generalize hu : (splitSeed.run st).1 = u at *
  have hdim := dimension_run σc s u hc' hd
  have hdimc := dimension_cost W u hb'
  generalize hv : (dimension.run u).1 = v at *
  have hdb := hdim.2.1.bound W hcode
  have houter := vector_cost t σc.size W 207 202 81 (by decide) v
    hdim.1.dimension hdim.1.card (hdb 3) hdim.1.empty
  have hvc := hdim.1.vector 207 202 81 (by decide)
  have hvd := hdim.2.1.vector 207 202 81
  have hvn := (vector_reg 207 202 211 81 (by decide) v).trans hdim.2.2
  generalize hw : ((vector 207 202 81).run v).1 = w at *
  have hinner := vector_cost t (4 * m) W 205 211 82 (by decide) w
    hvn hvc.card (hvd.bound W hcode 1) hvc.empty
  have hA : 1 ≤ A := by dsimp [A]; omega
  have hsmall : B + W + 5 ≤ A := by dsimp [A]; omega
  have hpow : A ^ 2 ≤ A ^ 4 := Nat.pow_le_pow_right hA (by decide)
  have hs' := hsc.trans (Nat.mul_le_mul_left _
    ((Nat.pow_le_pow_left hsmall 2).trans hpow))
  have hdim' := hdimc.trans (Nat.mul_le_mul_left _
    ((show W + 1 ≤ A by dsimp [A]; omega).trans (Nat.le_pow (by decide : 0 < 4))))
  have ho' := houter.trans (Nat.mul_le_mul_left _
    (Nat.pow_le_pow_left (show σc.size + t + W + 3 ≤ A by dsimp [A]; omega) 4))
  have hi' := hinner.trans (Nat.mul_le_mul_left _
    (Nat.pow_le_pow_left (show 4 * m + t + W + 3 ≤ A by dsimp [A]; omega) 4))
  have h1 : 1 ≤ A ^ 4 := Nat.one_le_pow _ _ hA
  change _ ≤ costConstant * A ^ 4
  unfold costConstant
  nlinarith only [hs', hdim', ho', hi', h1]

/-- A concrete quadratic expression dominates every actual component radix exponent. -/
def radixBound (d m t : ℕ) : ℕ :=
  ThreeColorSeedSize.innerBits m 4 t + t * (4 * m) + t * d + t + 1

theorem callTerms_bound (d m t : ℕ) (i : Fin 7) :
    (NestedSeed.callTerms i).eval ![d, m, 4, t] ≤ radixBound d m t := by
  unfold radixBound
  fin_cases i <;> simp [NestedSeed.callTerms, NestedSeed.inner_eval,
    NestedSeed.innerPointBits_eval, NestedSeed.pointBits_eval, ArithmeticExpression.Term.eval]
  all_goals omega

/-- No callback or runtime assumption remains: the bound is an explicit polynomial expression. -/
theorem program_cost (σc : Codec σ)
    (s : RawCallSeed (BinaryMaterializedField.Element t) σ m 4 t) (W : ℕ)
    (st : State 220 96) (hc : Input σc s st) (hb : SourceBound W st) :
    (program.run st).2 ≤ costConstant *
      (σc.size + 4 * m + t + radixBound σc.size m t + W + 10) ^ 4 :=
  program_cost_bound σc s _ W st hc hb (callTerms_bound σc.size m t)

/-- Unconditional polynomial bound in dimensions and the stored raw-code bit size. -/
theorem program_cost_self (σc : Codec σ)
    (s : RawCallSeed (BinaryMaterializedField.Element t) σ m 4 t)
    (st : State 220 96) (hc : Input σc s st) :
    (program.run st).2 ≤ costConstant *
      (σc.size + 4 * m + t + radixBound σc.size m t +
        (t + m + σc.size + Nat.size (st.regs 203) + 3) + 10) ^ 4 :=
  program_cost σc s _ st hc hc.sourceBound

/-- All genuine decoded components satisfy the same source bit bound. -/
theorem program_dataBound (σc : Codec σ)
    (s : RawCallSeed (BinaryMaterializedField.Element t) σ m 4 t) (W : ℕ)
    (st : State 220 96) (hc : Input σc s st) (hb : SourceBound W st) :
    DataBound W (program.run st).1 :=
  (program_run σc s st hc).2.1.bound W (hc.seed ▸ hb 3)

end PCP.Lang.CorrectionSeed
