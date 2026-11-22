import PCP.Complexity.OuterBranchSeedIndex
import PCP.Complexity.DerivedSeedEdge
import PCP.Complexity.DerivedSeedPoints

/-! # Public stored inputs and physical payload for each derived-grid branch -/

set_option maxRecDepth 1024

namespace PCP.Lang.DerivedSeed

open PCP.Algebraic ThreeColorSeedIndex ThreeColorFullFieldSampling BinaryFieldCode
open LocalCorrection DerivedGrid

variable {t n m : ℕ} [NeZero t]

structure Public (nodes : Fin 5 → OuterBranch.Field t) (ζ : OuterBranch.Field t)
    (h : ℕ) (x : List Bool) (qs : List ℕ) (bs : List Bool) (st : State 300 112) : Prop where
  root : st.regs 244 = (fieldEquiv t ζ).val
  vertices : st.regs 250 = (2^t)^n
  pairs : st.regs 251 = (2^t)^(n+n)
  proper : st.regs 252 = (2^t)^((n+n)+(n+n))
  inner : st.regs 253 = (2^t)^(4*m)
  affineLabels : st.regs 254 = 2^BooleanCoefficientIndex.dimension t 1
  cubicLabels : st.regs 255 = 2^BooleanCoefficientIndex.dimension t 3
  count : st.regs 279 = h
  dimension : st.regs 280 = n
  modulus : st.lists 101 = BinaryField.encode (BinaryWordMaterialization.modulus t)
  nodes : st.lists 102 = List.ofFn (fun i => (fieldEquiv t (nodes i)).val)
  history : st.lists 107 = qs
  answers : st.lists 108 = bs.map Bool.toNat
  graph : st.lists 111 = x.map Bool.toNat

def publicRegs : List (Fin 300) := [244,250,251,252,253,254,255,279,280]
def publicLists : List (Fin 112) := [101,102,107,108,111]

theorem Public.of_eq {nodes : Fin 5 → OuterBranch.Field t} {ζ : OuterBranch.Field t}
    {h : ℕ} {x : List Bool} {qs : List ℕ} {bs : List Bool} {st out : State 300 112}
    (hp : Public (n := n) (m := m) nodes ζ h x qs bs st)
    (hr : ∀ i ∈ publicRegs, out.regs i = st.regs i)
    (hl : ∀ L ∈ publicLists, out.lists L = st.lists L) :
    Public (n := n) (m := m) nodes ζ h x qs bs out := by
  constructor
  · exact (hr 244 (by decide)).trans hp.root
  · exact (hr 250 (by decide)).trans hp.vertices
  · exact (hr 251 (by decide)).trans hp.pairs
  · exact (hr 252 (by decide)).trans hp.proper
  · exact (hr 253 (by decide)).trans hp.inner
  · exact (hr 254 (by decide)).trans hp.affineLabels
  · exact (hr 255 (by decide)).trans hp.cubicLabels
  · exact (hr 279 (by decide)).trans hp.count
  · exact (hr 280 (by decide)).trans hp.dimension
  · exact (hl 101 (by decide)).trans hp.modulus
  · exact (hl 102 (by decide)).trans hp.nodes
  · exact (hl 107 (by decide)).trans hp.history
  · exact (hl 108 (by decide)).trans hp.answers
  · exact (hl 111 (by decide)).trans hp.graph

def payload (k : Certificate) : Stmt 300 112 :=
  .seq (.assign 242 (.add 256 256)) (
  .seq (.assign 260 (.const (match k with | .valid => 0 | .proper => 2))) (
  .seq (.assign 261 (.var 250)) (
  .seq (.assign 262 (.var 251)) (
  .seq (.assign 263 (.var 252)) (
  .seq (.assign 264 (.var 253)) (
  .seq (.assign 265 (.var 254)) (
  .seq (.assign 266 (.var 255)) (
  .seq (.assign 267 (.var 259)) (
  .seq (.assign 268 (.const 0)) (.assign 269 (.const 0)))))))))))

theorem payload_reg (k : Certificate) (st : State 300 112) (i : Fin 300)
    (h2 : i ≠ 242) (hi : i.val < 260 ∨ 270 ≤ i.val) :
    ((payload k).run st).1.regs i = st.regs i := by
  apply run_regs_frame
  have hw : ∀ j ∈ (payload k).regWrites, j = 242 ∨ (260 ≤ j.val ∧ j.val < 270) := by
    intro j hj
    simp only [payload, Stmt.regWrites, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      norm_num
  intro hm
  rcases hw i hm with h | h
  · exact h2 h
  · omega

theorem payload_list (k : Certificate) (st : State 300 112) (L : Fin 112) :
    ((payload k).run st).1.lists L = st.lists L :=
  run_lists_frame _ _ (by simp [payload, Stmt.listWrites]) st

theorem pointCode_materialized (k : Certificate)
    (x : Fin (baseDimension k n) → OuterBranch.Field t) :
    (((Codec.fin (baseDimension k n)).function
      (fieldCodec (BinaryMaterializedField.coordinates t))).equiv x).val =
      ((primaryLocation (m := m) k x).payload (t := t) (fieldEquiv t)) 7 := by
  cases k with
  | valid => exact OuterBranch.Kind.codec_point .color x
  | proper =>
      have hc := OuterBranch.Kind.codec_point .color x
      refine hc.trans ?_
      change (finFunctionFinEquiv (fun i : Fin (n+n) => fieldEquiv t (x i))).val =
        (finFunctionFinEquiv (fun i : Fin (n+n) =>
          fieldEquiv t (x (finSumFinEquiv (finSumFinEquiv.symm i))))).val
      simp only [Equiv.apply_symm_apply]

theorem payload_run (k : Certificate) (s : DerivedGrid.RawSample k t n m)
    (nodes : Fin 5 → OuterBranch.Field t) (ζ : OuterBranch.Field t) (h : ℕ)
    (x : List Bool) (qs : List ℕ) (bs : List Bool) (st : State 300 112)
    (hi : Input k s st) (hd : Data k s st) (hp : Public (n := n) (m := m) nodes ζ h x qs bs st) :
    ((payload k).run st).1.regs 242 = k.outer.dimension n ∧
    ∀ i, ((payload k).run st).1.regs (DerivedCall.payloadPort i) =
      ((primaryLocation (m := m) k s.1).payload (t := t) (fieldEquiv t)) i := by
  constructor
  · cases k <;> simp [payload, Stmt.run, Expr.eval, Function.update, hi.dimension,
      baseDimension, Certificate.outer, OuterBranch.Kind.dimension]
  · intro i
    have hc := pointCode_materialized (m := m) k s.1
    rw [← hd.point] at hc
    cases k <;> fin_cases i
    all_goals first
      | solve | simp [payload, Stmt.run, Expr.eval, Function.update, DerivedCall.payloadPort,
          primaryLocation, HadamardRow.Location.payload, HadamardRow.Location.query,
          QueryAddress.inputs, hp.vertices, hp.pairs, hp.proper, hp.inner,
          hp.affineLabels, hp.cubicLabels]
      | solve | simpa [payload, Stmt.run, Expr.eval, Function.update, DerivedCall.payloadPort,
          primaryLocation, HadamardRow.Location.payload, HadamardRow.Location.query,
          QueryAddress.inputs] using hc

end PCP.Lang.DerivedSeed
