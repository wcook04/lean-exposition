/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Complexity.DerivedSeedResources

/-! # Charged cost of complete correction-seed radix construction and decomposition -/

namespace PCP.Lang.DerivedSeed

open PCP.Algebraic ThreeColorSeedIndex ThreeColorFullFieldSampling BinaryFieldCode

open LocalCorrection DerivedGrid

variable {t n m : ℕ} [NeZero t]

theorem prepare_cost (W : ℕ) (st : State 300 112) (hb : InputBound W st)
    (he : st.lists 100 = []) : (prepare.run st).2 ≤ fixedConstant prepare * (W + 1) := by
  apply loopFree_cost_le prepare (by decide)
  · intro i hi
    change i ∈ [256, 241, 240, 257] at hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl
    · exact hb 2
    · exact hb 1
    · exact hb 0
    · exact hb 3
  · intro L hL
    change L ∈ [100] at hL
    simp only [List.mem_singleton] at hL
    subst L
    simp [he, listSize]

theorem prepare_context (k : Certificate)
    (s : DerivedGrid.RawSample k t n m) (st : State 300 112)
    (hc : Input k s st) :
    ComputedSeed.Context (baseDimension k n) m 4 t
      ((derivedCodec (BinaryMaterializedField.coordinates t) (baseDimension k n) m 4 3).equiv s).val
      (DerivedCall.view (by decide) (by decide) (prepare.run st).1) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i
    fin_cases i <;> simp [prepare, Stmt.run, Expr.eval, Function.update,
      DerivedCall.view, State.restrict, hc.width, hc.base, hc.dimension]
  · simp [prepare, Stmt.run, Expr.eval, Function.update, DerivedCall.view, State.restrict, hc.seed]
  · simp [prepare, Stmt.run, Function.update, DerivedCall.view, State.restrict, hc.empty]

attribute [local irreducible] decode NestedSeed.derived

theorem decode_output (k : Certificate)
    (s : DerivedGrid.RawSample k t n m) (st : State 300 112)
    (hc : Input k s st) :
    (decode.run (prepare.run st).1).1.lists 1 = List.ofFn (components k s) ++ [0, 0] := by
  have h := NestedSeed.derived_run (BinaryMaterializedField.coordinates t) (baseDimension k n) m 4
    s _ (prepare_context k s st hc)
  rw [← DerivedCall.call_result (by decide) (by decide) NestedSeed.derived] at h
  rw [show DerivedCall.call (by decide) (by decide) NestedSeed.derived = decode by
    unfold decode; rfl] at h
  generalize hu : (decode.run (prepare.run st).1).1 = u at *
  change u.lists 1 = _ at h
  simp only [components, List.ofFn_succ, List.ofFn_zero, Matrix.cons_val_zero,
    Matrix.cons_val_succ, List.cons_append, List.nil_append]
  exact h

theorem decode_cost (k : Certificate)
    (s : DerivedGrid.RawSample k t n m) (B W : ℕ)
    (st : State 300 112) (hc : Input k s st) (hb : InputBound W st)
    (hB : ∀ i, (NestedSeed.derivedTerms i).eval ![(baseDimension k n), m, 4, t] ≤ B) :
    (decode.run (prepare.run st).1).2 ≤
      ComputedSeed.programConstant NestedSeed.derivedTerms * (B + W + 5) ^ 2 := by
  have hcode :
      Nat.size ((derivedCodec (BinaryMaterializedField.coordinates t)
        (baseDimension k n) m 4 3).equiv s).val ≤ W :=
    hc.seed ▸ hb 3
  have hp : ∀ i : Fin 4, Nat.size (![(baseDimension k n), m, 4, t] i) ≤ W + 4 := by
    intro i
    fin_cases i
    · exact (hc.dimension ▸ hb 2).trans (by omega)
    · exact (hc.base ▸ hb 1).trans (by omega)
    · exact (by decide : Nat.size 4 ≤ 4).trans (Nat.le_add_left 4 W)
    · exact (hc.width ▸ hb 0).trans (by omega)
  have h := ComputedSeed.program_cost NestedSeed.derivedTerms (baseDimension k n) m 4 t _ B (W + 4)
    _ (prepare_context k s st hc) hp hB (hcode.trans (by omega))
  rw [show ComputedSeed.program NestedSeed.derivedTerms = NestedSeed.derived by
    unfold NestedSeed.derived; rfl] at h
  rw [← DerivedCall.call_result (by decide) (by decide) NestedSeed.derived] at h
  rw [show DerivedCall.call (by decide) (by decide) NestedSeed.derived = decode by
    unfold decode; rfl] at h
  simpa only [Nat.add_assoc] using h

theorem unpack_cost (k : Certificate)
    (s : DerivedGrid.RawSample k t n m) (W : ℕ) (st : State 300 112)
    (h0 : st.lists 1 = List.ofFn (components k s) ++ [0, 0])
    (hW : Nat.size ((derivedCodec (BinaryMaterializedField.coordinates t)
        (baseDimension k n) m 4 3).equiv s).val ≤ W) :
    (unpack.run st).2 ≤ 5 * W + 9 := by
  have h0 := h0
  have h1 := (component_size k s 0).trans hW
  have h2 := (component_size k s 1).trans hW
  have h3 := (component_size k s 2).trans hW
  have h4 := (component_size k s 3).trans hW
  have h5 := (component_size k s 4).trans hW
  simp only [List.ofFn_succ, List.ofFn_zero, List.cons_append, List.nil_append] at h0
  simp [unpack, Stmt.run, Function.update, h0]
  omega

def splitConstant : ℕ := fixedConstant prepare +
  ComputedSeed.programConstant NestedSeed.derivedTerms + 10

theorem split_cost_bound (k : Certificate)
    (s : DerivedGrid.RawSample k t n m) (B W : ℕ)
    (st : State 300 112) (hc : Input k s st) (hb : InputBound W st)
    (hB : ∀ i, (NestedSeed.derivedTerms i).eval ![(baseDimension k n), m, 4, t] ≤ B) :
    (split.run st).2 ≤ splitConstant * (B + W + 5) ^ 2 := by
  have hp := prepare_cost W st hb hc.empty
  have hd := decode_cost k s B W st hc hb hB
  have hout := decode_output k s st hc
  have hcsize :
      Nat.size ((derivedCodec (BinaryMaterializedField.coordinates t)
        (baseDimension k n) m 4 3).equiv s).val ≤ W :=
    hc.seed ▸ hb 3
  have hu := unpack_cost k s W _ hout hcsize
  have hpow : B + W + 5 ≤ (B + W + 5) ^ 2 := Nat.le_pow (by decide)
  have hp' := hp.trans (Nat.mul_le_mul_left _ ((show W + 1 ≤ B + W + 5 by omega).trans hpow))
  have h1 : 1 ≤ (B + W + 5) ^ 2 := Nat.one_le_pow _ _ (by omega)
  simp only [split, run_seq_snd]
  unfold splitConstant
  nlinarith only [hp', hd, hu, hpow, h1]

def radixBound (d m t : ℕ) : ℕ :=
  2^t + 2*t*d + t + t*(4*m) + ThreeColorSeedSize.innerBits m 4 t + 1

theorem derivedTerms_bound (d m t : ℕ) (i : Fin 7) :
    (NestedSeed.derivedTerms i).eval ![d,m,4,t] ≤ radixBound d m t := by
  have hcoeff : ThreeColorSeedSize.coefficientBits t 3 ≤ 2^t := by
    have h := BooleanCoefficientTransform.masks_length_le t 3
    rw [BooleanMask.masks_length] at h
    exact h
  have hcall : NestedSeed.callBits.eval ![d,m,4,t] =
      2*(t*d)+t+t*(4*m)+ThreeColorSeedSize.innerBits m 4 t := by
    change 2*(NestedSeed.pointBits.eval ![d,m,4,t])+t+
      NestedSeed.innerPointBits.eval ![d,m,4,t]+SeedArithmetic.inner.eval ![d,m,4,t] = _
    rw [NestedSeed.pointBits_eval, NestedSeed.innerPointBits_eval, NestedSeed.inner_eval]
  rw [ThreeColorSeedSize.coefficientBits_three] at hcoeff
  unfold radixBound
  fin_cases i <;> simp [NestedSeed.derivedTerms, NestedSeed.coefficientThree_eval, hcall,
    NestedSeed.pointBits_eval, ArithmeticExpression.Term.eval]
  all_goals nlinarith only [hcoeff, Nat.zero_le (2^t), Nat.zero_le (t*d),
    Nat.zero_le t, Nat.zero_le (t*(4*m)), Nat.zero_le (ThreeColorSeedSize.innerBits m 4 t)]

/-- The actual radix formulas discharge the intermediate numeric exponent bound. -/
theorem split_cost (k : Certificate) (s : DerivedGrid.RawSample k t n m) (W : ℕ)
    (st : State 300 112) (hc : Input k s st) (hb : InputBound W st) :
    (split.run st).2 ≤ splitConstant * (radixBound (baseDimension k n) m t + W + 5)^2 :=
  split_cost_bound k s _ W st hc hb (derivedTerms_bound (baseDimension k n) m t)

end PCP.Lang.DerivedSeed
