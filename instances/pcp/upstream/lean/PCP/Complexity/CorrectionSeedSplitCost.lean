/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Complexity.CorrectionSeedResources

/-! # Charged cost of complete correction-seed radix construction and decomposition -/

namespace PCP.Lang.CorrectionSeed

open PCP.Algebraic ThreeColorSeedIndex ThreeColorFullFieldSampling BinaryFieldCode

variable {t m : ℕ} [NeZero t] {σ : Type*}

def fixedConstant (p : Stmt 220 96) : ℕ := p.C * (p.width + p.csize + 1)

theorem prepare_cost (W : ℕ) (st : State 220 96) (hb : SourceBound W st)
    (he : st.lists 80 = []) : (prepare.run st).2 ≤ fixedConstant prepare * (W + 1) := by
  apply loopFree_cost_le prepare (by decide)
  · intro i hi
    change i ∈ [202, 201, 200, 203] at hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl
    · exact hb 2
    · exact hb 1
    · exact hb 0
    · exact hb 3
  · intro L hL
    change L ∈ [80] at hL
    simp only [List.mem_singleton] at hL
    subst L
    simp [he, listSize]

theorem prepare_context (σc : Codec σ)
    (s : RawCallSeed (BinaryMaterializedField.Element t) σ m 4 t) (st : State 220 96)
    (hc : Input σc s st) :
    ComputedSeed.Context σc.size m 4 t
      ((callCodec (BinaryMaterializedField.coordinates t) σc m 4).equiv s).val
      ((prepare.run st).1.restrict (Fin.castLE (by decide)) (Fin.castLE (by decide))) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i
    fin_cases i <;> simp [prepare, Stmt.run, Expr.eval, Function.update,
      State.restrict, hc.width, hc.base, hc.dimension]
  · simp [prepare, Stmt.run, Expr.eval, Function.update, State.restrict, hc.seed]
  · simp [prepare, Stmt.run, Function.update, State.restrict, hc.empty]

attribute [local irreducible] decode NestedSeed.call

theorem decode_output (σc : Codec σ)
    (s : RawCallSeed (BinaryMaterializedField.Element t) σ m 4 t) (st : State 220 96)
    (hc : Input σc s st) :
    (decode.run (prepare.run st).1).1.lists 1 = List.ofFn (components σc s) ++ [0, 0, 0] := by
  have h := NestedSeed.call_run (BinaryMaterializedField.coordinates t) σc σc.size m 4
    rfl s _ (prepare_context σc s st hc)
  rw [← call_result (by decide) (by decide) NestedSeed.call] at h
  rw [show call (by decide) (by decide) NestedSeed.call = decode by unfold decode; rfl] at h
  generalize hu : (decode.run (prepare.run st).1).1 = u at *
  change u.lists 1 = _ at h
  simp only [components, List.ofFn_succ, List.ofFn_zero, Matrix.cons_val_zero,
    Matrix.cons_val_succ, List.cons_append, List.nil_append]
  simp only [UniformDecode.fieldCodec_materialized] at h
  exact h

theorem decode_cost (σc : Codec σ)
    (s : RawCallSeed (BinaryMaterializedField.Element t) σ m 4 t) (B W : ℕ)
    (st : State 220 96) (hc : Input σc s st) (hb : SourceBound W st)
    (hB : ∀ i, (NestedSeed.callTerms i).eval ![σc.size, m, 4, t] ≤ B) :
    (decode.run (prepare.run st).1).2 ≤
      ComputedSeed.programConstant NestedSeed.callTerms * (B + W + 5) ^ 2 := by
  have hcode :
      Nat.size ((callCodec (BinaryMaterializedField.coordinates t) σc m 4).equiv s).val ≤ W :=
    hc.seed ▸ hb 3
  have hp : ∀ i : Fin 4, Nat.size (![σc.size, m, 4, t] i) ≤ W + 4 := by
    intro i
    fin_cases i
    · exact (hc.dimension ▸ hb 2).trans (by omega)
    · exact (hc.base ▸ hb 1).trans (by omega)
    · exact (by decide : Nat.size 4 ≤ 4).trans (Nat.le_add_left 4 W)
    · exact (hc.width ▸ hb 0).trans (by omega)
  have h := ComputedSeed.program_cost NestedSeed.callTerms σc.size m 4 t _ B (W + 4)
    _ (prepare_context σc s st hc) hp hB (hcode.trans (by omega))
  rw [show ComputedSeed.program NestedSeed.callTerms = NestedSeed.call by
    unfold NestedSeed.call; rfl] at h
  rw [← call_result (by decide) (by decide) NestedSeed.call] at h
  rw [show call (by decide) (by decide) NestedSeed.call = decode by unfold decode; rfl] at h
  simpa only [Nat.add_assoc] using h

theorem unpack_cost (σc : Codec σ)
    (s : RawCallSeed (BinaryMaterializedField.Element t) σ m 4 t) (W : ℕ) (st : State 220 96)
    (h0 : st.lists 1 = List.ofFn (components σc s) ++ [0, 0, 0])
    (hW : Nat.size ((callCodec (BinaryMaterializedField.coordinates t) σc m 4).equiv s).val ≤ W) :
    (unpack.run st).2 ≤ 4 * W + 7 := by
  have h0 := h0
  have h1 := (component_size σc s 0).trans hW
  have h2 := (component_size σc s 1).trans hW
  have h3 := (component_size σc s 2).trans hW
  have h4 := (component_size σc s 3).trans hW
  simp only [List.ofFn_succ, List.ofFn_zero, List.cons_append, List.nil_append] at h0
  simp [unpack, Stmt.run, Function.update, h0]
  omega

def splitConstant : ℕ := fixedConstant prepare +
  ComputedSeed.programConstant NestedSeed.callTerms + 10

theorem splitSeed_cost (σc : Codec σ)
    (s : RawCallSeed (BinaryMaterializedField.Element t) σ m 4 t) (B W : ℕ)
    (st : State 220 96) (hc : Input σc s st) (hb : SourceBound W st)
    (hB : ∀ i, (NestedSeed.callTerms i).eval ![σc.size, m, 4, t] ≤ B) :
    (splitSeed.run st).2 ≤ splitConstant * (B + W + 5) ^ 2 := by
  have hp := prepare_cost W st hb hc.empty
  have hd := decode_cost σc s B W st hc hb hB
  have hout := decode_output σc s st hc
  have hcsize :
      Nat.size ((callCodec (BinaryMaterializedField.coordinates t) σc m 4).equiv s).val ≤ W :=
    hc.seed ▸ hb 3
  have hu := unpack_cost σc s W _ hout hcsize
  have hpow : B + W + 5 ≤ (B + W + 5) ^ 2 := Nat.le_pow (by decide)
  have hp' := hp.trans (Nat.mul_le_mul_left _ ((show W + 1 ≤ B + W + 5 by omega).trans hpow))
  have h1 : 1 ≤ (B + W + 5) ^ 2 := Nat.one_le_pow _ _ (by omega)
  simp only [splitSeed, run_seq_snd]
  unfold splitConstant
  nlinarith only [hp', hd, hu, hpow, h1]

end PCP.Lang.CorrectionSeed
