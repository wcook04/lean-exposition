/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Complexity.HadamardLabelCost

/-!
# Compositional specifications for the concrete Hadamard row

The row seed is held in protected source arrays. Query-producing stages prepend
their numeric labels to a work accumulator; the final reversal restores the
semantic query order. Specifications compose with the actual sequence cost.
-/

namespace PCP.Lang.HadamardRow

open PCP.Algebraic BinaryPolynomialSpace Hadamard BooleanCoefficientList HadamardLabel

variable {t r : ℕ}

def factorCodes (s : TestRandomness t r) : List ℕ :=
  List.ofFn fun k => code (s.factor k)

def Context (s : TestRandomness t r) (st : State 80 32) : Prop :=
  st.regs 20 = t ∧ st.regs 56 = r ∧ st.lists 7 = [] ∧
    st.lists 20 = encode s.base ∧ st.lists 21 = encode s.auxiliary ∧
    st.lists 22 = encode s.linear ∧ st.lists 23 = factorCodes s

/-- The protected seed inputs are disjoint from every query-producing work slot. -/
def Stable (P : Stmt 80 32) : Prop :=
  20 ∉ P.regWrites ∧ 56 ∉ P.regWrites ∧ 7 ∉ P.listWrites ∧
    20 ∉ P.listWrites ∧ 21 ∉ P.listWrites ∧ 22 ∉ P.listWrites ∧ 23 ∉ P.listWrites

instance (P : Stmt 80 32) : Decidable (Stable P) := by unfold Stable; infer_instance

theorem context_frame (P : Stmt 80 32) (hs : Stable P) (s : TestRandomness t r)
    (st : State 80 32) (hc : Context s st) : Context s (P.run st).1 := by
  unfold Context at hc ⊢
  rw [run_regs_frame P 20 hs.1 st, run_regs_frame P 56 hs.2.1 st,
    run_lists_frame P 7 hs.2.2.1 st, run_lists_frame P 20 hs.2.2.2.1 st,
    run_lists_frame P 21 hs.2.2.2.2.1 st, run_lists_frame P 22 hs.2.2.2.2.2.1 st,
    run_lists_frame P 23 hs.2.2.2.2.2.2 st]
  exact hc

/-- Exact outputs and charged cost, with no condition on initial scratch contents. -/
structure Spec (s : TestRandomness t r) (P : Stmt 80 32) (qs : List ℕ) (bound : ℕ) : Prop where
  context : ∀ st, Context s st → Context s (P.run st).1
  output : ∀ st, Context s st → (P.run st).1.lists 24 = qs.reverse ++ st.lists 24
  cost : ∀ st, Context s st → (P.run st).2 ≤ bound

theorem Spec.seq {s : TestRandomness t r} {P Q : Stmt 80 32} {xs ys : List ℕ} {A B : ℕ}
    (hp : Spec s P xs A) (hq : Spec s Q ys B) :
    Spec s (.seq P Q) (xs ++ ys) (A + B + 1) where
  context st hc := by rw [run_seq_fst]; exact hq.context _ (hp.context st hc)
  output st hc := by
    rw [run_seq_fst, hq.output _ (hp.context st hc), hp.output st hc,
      List.reverse_append, List.append_assoc]
  cost st hc := by
    rw [run_seq_snd]
    have h1 := hp.cost st hc
    have h2 := hq.cost (P.run st).1 (hp.context st hc)
    omega

theorem Spec.mono {s : TestRandomness t r} {P : Stmt 80 32} {qs : List ℕ} {A B : ℕ}
    (h : Spec s P qs A) (hab : A ≤ B) : Spec s P qs B where
  context := h.context
  output := h.output
  cost st hc := (h.cost st hc).trans hab

theorem emit_spec (s : TestRandomness t r) (L : Fin 32) (p : Coefficients t r)
    (hsource : ∀ st, Context s st → st.lists L = encode p) (hstable : Stable (emit L)) :
    Spec s (emit L) [code p] ((WordCodec.passConstant * 3 + 30) * (2 ^ t + 1) ^ 2) where
  context := fun st hc => context_frame _ hstable s st hc
  output st hc := by simpa using emit_run L p st (hsource st hc)
  cost st hc := emit_cost L p st (hsource st hc)

theorem emitSum_spec (s : TestRandomness t r) (L K : Fin 32) (hK : K ≠ 28)
    (p q : Coefficients t r)
    (hleft : ∀ st, Context s st → st.lists L = encode p)
    (hright : ∀ st, Context s st → st.lists K = encode q)
    (hstable : Stable (emitSum L K)) :
    Spec s (emitSum L K) [code (p + q)]
      ((WordCodec.passConstant * 3 + 101) * (2 ^ t + 1) ^ 2) where
  context := fun st hc => context_frame _ hstable s st hc
  output st hc := by
    simpa using emitSum_run L K hK p q st (hleft st hc) (hright st hc) hc.2.2.1
  cost st hc := emitSum_cost L K hK p q st (hleft st hc) (hright st hc) hc.2.2.1

end PCP.Lang.HadamardRow
