import PCP.Complexity.ThreeColorNestedSeedSemantics
import PCP.Complexity.LangSeedMaterialization
import PCP.Complexity.LangUniformDecodeCost

/-!
# Numeric correction-seed decomposition and coordinate materialization

The actual mixed-radix seed is split into its inner seed, inner direction, field
parameter and outer direction. Both coordinate vectors are then materialized in
the production codec order. A zero parameter remains visible for the caller's
whole-field rejection guard.
-/

-- The fixed port proofs range over 220 registers.
set_option maxRecDepth 1024

namespace PCP.Lang.CorrectionSeed

open PCP.Algebraic ThreeColorSeedIndex ThreeColorFullFieldSampling BinaryFieldCode

variable {t m : ℕ} [NeZero t]

def call {R Q : ℕ} (hR : R ≤ 180) (hQ : Q ≤ 80) (p : Stmt R Q) : Stmt 220 96 :=
  p.rename (Fin.castLE (hR.trans (by decide))) (Fin.castLE (hQ.trans (by decide)))

theorem call_result {R Q : ℕ} (hR : R ≤ 180) (hQ : Q ≤ 80) (p : Stmt R Q)
    (st : State 220 96) :
    (((call hR hQ p).run st).1.restrict (Fin.castLE (hR.trans (by decide)))
      (Fin.castLE (hQ.trans (by decide))), ((call hR hQ p).run st).2) =
    p.run (st.restrict (Fin.castLE (hR.trans (by decide)))
      (Fin.castLE (hQ.trans (by decide)))) :=
  p.run_rename _ _ (Fin.castLE_injective _) (Fin.castLE_injective _) st

structure Input {σ : Type*} (σc : Codec σ)
    (s : RawCallSeed (BinaryMaterializedField.Element t) σ m 4 t) (st : State 220 96) : Prop where
  width : st.regs 200 = t
  base : st.regs 201 = m
  dimension : st.regs 202 = σc.size
  seed : st.regs 203 = ((callCodec (BinaryMaterializedField.coordinates t) σc m 4).equiv s).val
  card : st.regs 208 = 2^t
  empty : st.lists 80 = []

structure Data {σ : Type*} (σc : Codec σ)
    (s : RawCallSeed (BinaryMaterializedField.Element t) σ m 4 t) (st : State 220 96) : Prop where
  inner : st.regs 204 = ((innerCodec (BinaryMaterializedField.coordinates t) m 4).equiv s.2.2.2).val
  direction : st.regs 205 =
    ((innerPointCodec (BinaryMaterializedField.coordinates t) m 4).equiv s.2.2.1).val
  param : st.regs 206 = (fieldEquiv t s.2.1).val
  outer : st.regs 207 =
    ((σc.function (fieldCodec (BinaryMaterializedField.coordinates t))).equiv s.1).val

def prepare : Stmt 220 96 := .seq (.copy 80 3)
  (.seq (.assign 0 (.var 202)) (.seq (.assign 1 (.var 201))
    (.seq (.assign 2 (.const 4)) (.seq (.assign 3 (.var 200)) (.assign 15 (.var 203))))))

def decode : Stmt 220 96 := call (by decide) (by decide) NestedSeed.call

def unpack : Stmt 220 96 := .seq (.pop 1 204 209)
  (.seq (.pop 1 205 209) (.seq (.pop 1 206 209) (.pop 1 207 209)))

def splitSeed : Stmt 220 96 := .seq prepare (.seq decode unpack)

attribute [local irreducible] decode NestedSeed.call

theorem splitSeed_run {σ : Type*} (σc : Codec σ)
    (s : RawCallSeed (BinaryMaterializedField.Element t) σ m 4 t) (st : State 220 96)
    (hc : Input σc s st) : Data σc s (splitSeed.run st).1 := by
  have hi : ComputedSeed.Context σc.size m 4 t
      ((callCodec (BinaryMaterializedField.coordinates t) σc m 4).equiv s).val
      ((prepare.run st).1.restrict (Fin.castLE (by decide)) (Fin.castLE (by decide))) := by
    refine ⟨?_, ?_, ?_⟩
    · intro i
      fin_cases i <;> simp [prepare, Stmt.run, Expr.eval, Function.update,
        State.restrict, hc.width, hc.base, hc.dimension]
    · simp [prepare, Stmt.run, Expr.eval, Function.update, State.restrict, hc.seed]
    · simp [prepare, Stmt.run, Function.update, State.restrict, hc.empty]
  have hd := NestedSeed.call_run (BinaryMaterializedField.coordinates t) σc σc.size m 4 rfl s _ hi
  rw [← call_result (by decide) (by decide) NestedSeed.call (prepare.run st).1] at hd
  have hd' : (decode.run (prepare.run st).1).1.lists 1 =
      [((innerCodec (BinaryMaterializedField.coordinates t) m 4).equiv s.2.2.2).val,
       ((innerPointCodec (BinaryMaterializedField.coordinates t) m 4).equiv s.2.2.1).val,
       (fieldEquiv t s.2.1).val,
       ((σc.function (fieldCodec (BinaryMaterializedField.coordinates t))).equiv s.1).val,
       0, 0, 0] := by
    simp only [State.restrict_lists,
      show Fin.castLE (by decide : 4 ≤ 96) (1 : Fin 4) = (1 : Fin 96) from rfl,
      UniformDecode.fieldCodec_materialized] at hd
    convert hd using 1
    · unfold decode
      rfl
  simp only [splitSeed, run_seq_fst]
  generalize hu : (decode.run (prepare.run st).1).1 = u at *
  constructor <;> simp [unpack, Stmt.run, Function.update, hd']

theorem call_reg {R Q : ℕ} (hR : R ≤ 180) (hQ : Q ≤ 80) (p : Stmt R Q)
    (st : State 220 96) (i : Fin 220) (hi : 180 ≤ i.val) :
    ((call hR hQ p).run st).1.regs i = st.regs i := by
  apply Stmt.run_rename_reg_outside
  intro j hj
  have := congrArg Fin.val hj
  simp only [Fin.val_castLE] at this
  omega

theorem call_list {R Q : ℕ} (hR : R ≤ 180) (hQ : Q ≤ 80) (p : Stmt R Q)
    (st : State 220 96) (i : Fin 96) (hi : 80 ≤ i.val) :
    ((call hR hQ p).run st).1.lists i = st.lists i := by
  apply Stmt.run_rename_list_outside
  intro j hj
  have := congrArg Fin.val hj
  simp only [Fin.val_castLE] at this
  omega

theorem splitSeed_reg (st : State 220 96) (i : Fin 220) (hi : 200 ≤ i.val)
    (h4 : i ≠ 204) (h5 : i ≠ 205) (h6 : i ≠ 206) (h7 : i ≠ 207) (h9 : i ≠ 209) :
    (splitSeed.run st).1.regs i = st.regs i := by
  have hu : ∀ s : State 220 96, (unpack.run s).1.regs i = s.regs i := by
    intro s
    apply run_regs_frame
    simp [unpack, Stmt.regWrites, h4, h5, h6, h7, h9]
  have hp : (prepare.run st).1.regs i = st.regs i := by
    apply run_regs_frame
    have hb : ∀ j ∈ prepare.regWrites, j.val < 180 := by decide
    intro hm
    have := hb i hm
    omega
  have hd := call_reg (by decide) (by decide) NestedSeed.call (prepare.run st).1 i (by omega)
  simpa only [splitSeed, run_seq_fst, hu, decode] using hd.trans hp

theorem splitSeed_list (st : State 220 96) (i : Fin 96) (hi : 80 ≤ i.val) :
    (splitSeed.run st).1.lists i = st.lists i := by
  have hu : ∀ s : State 220 96, (unpack.run s).1.lists i = s.lists i := by
    intro s
    apply run_lists_frame
    have hb : ∀ j ∈ unpack.listWrites, j.val < 80 := by decide
    intro hm
    have := hb i hm
    omega
  have hp : (prepare.run st).1.lists i = st.lists i := by
    apply run_lists_frame
    have hb : ∀ j ∈ prepare.listWrites, j.val < 80 := by decide
    intro hm
    have := hb i hm
    omega
  have hd := call_list (by decide) (by decide) NestedSeed.call (prepare.run st).1 i hi
  simpa only [splitSeed, run_seq_fst, hu, decode] using hd.trans hp

theorem Input.split {σ : Type*} {σc : Codec σ}
    {s : RawCallSeed (BinaryMaterializedField.Element t) σ m 4 t} {st : State 220 96}
    (hc : Input σc s st) : Input σc s (splitSeed.run st).1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (splitSeed_reg st 200 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)).trans hc.width
  · exact (splitSeed_reg st 201 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)).trans hc.base
  · exact (splitSeed_reg st 202 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)).trans hc.dimension
  · exact (splitSeed_reg st 203 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)).trans hc.seed
  · exact (splitSeed_reg st 208 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)).trans hc.card
  · exact (splitSeed_list st 80 (by decide)).trans hc.empty

def vectorPrepare (src len : Fin 220) : Stmt 220 96 := .seq (.copy 80 2)
  (.seq (.assign 0 (.var src)) (.seq (.assign 5 (.var len)) (.assign 6 (.var 208))))

def vectorDecode : Stmt 220 96 := call (by decide) (by decide) UniformDecode.program

def vector (src len : Fin 220) (dst : Fin 96) : Stmt 220 96 :=
  .seq (vectorPrepare src len) (.seq vectorDecode (.copy 1 dst))

theorem vector_run {σ : Type*} (σc : Codec σ)
    (p : σ → BinaryMaterializedField.Element t) (src len : Fin 220) (dst : Fin 96)
    (hlen : 180 ≤ len.val) (st : State 220 96)
    (hc : st.regs src =
      ((σc.function (fieldCodec (BinaryMaterializedField.coordinates t))).equiv p).val)
    (hn : st.regs len = σc.size) (hb : st.regs 208 = 2 ^ t) (he : st.lists 80 = []) :
    ((vector src len dst).run st).1.lists dst =
      List.ofFn (fun i => (fieldEquiv t (p (σc.equiv.symm i))).val) := by
  have hlen0 : len ≠ 0 := by intro h; subst len; norm_num at hlen
  have hp := UniformDecode.program_fieldPoint σc p
    (((vectorPrepare src len).run st).1.restrict
      (Fin.castLE (by decide)) (Fin.castLE (by decide)))
    (by simpa [vectorPrepare, Stmt.run, Expr.eval, Function.update, State.restrict] using hc)
    (by simpa [vectorPrepare, Stmt.run, Expr.eval, Function.update, State.restrict, hlen0] using hn)
    (by simpa [vectorPrepare, Stmt.run, Expr.eval, Function.update, State.restrict] using hb)
    (by simpa [vectorPrepare, Stmt.run, Expr.eval, Function.update, State.restrict] using he)
  rw [← call_result (by decide) (by decide) UniformDecode.program
    (vectorPrepare src len |>.run st).1] at hp
  simpa only [vector, run_seq_fst, run_copy_fst, setList_lists, Function.update_self,
    vectorDecode, call, State.restrict_lists,
    show Fin.castLE (by decide : 3 ≤ 96) (1 : Fin 3) = (1 : Fin 96) from rfl] using hp

theorem vector_reg (src len i : Fin 220) (dst : Fin 96) (hi : 180 ≤ i.val)
    (st : State 220 96) : ((vector src len dst).run st).1.regs i = st.regs i := by
  have hp : ((vectorPrepare src len).run st).1.regs i = st.regs i := by
    apply run_regs_frame
    have hb : ∀ j ∈ (vectorPrepare src len).regWrites, j.val < 180 := by
      simp [vectorPrepare, Stmt.regWrites]
    intro hm
    have := hb i hm
    omega
  have hd := call_reg (by decide) (by decide) UniformDecode.program
    ((vectorPrepare src len).run st).1 i hi
  simpa only [vector, run_seq_fst, run_copy_fst, setList_regs, vectorDecode] using hd.trans hp

theorem vector_list (src len : Fin 220) (dst i : Fin 96) (hi : 80 ≤ i.val) (hne : i ≠ dst)
    (st : State 220 96) : ((vector src len dst).run st).1.lists i = st.lists i := by
  have hp : ((vectorPrepare src len).run st).1.lists i = st.lists i := by
    apply run_lists_frame
    have hb : ∀ j ∈ (vectorPrepare src len).listWrites, j.val < 80 := by
      simp [vectorPrepare, Stmt.listWrites]
    intro hm
    have := hb i hm
    omega
  have hd := call_list (by decide) (by decide) UniformDecode.program
    ((vectorPrepare src len).run st).1 i hi
  simpa only [vector, run_seq_fst, run_copy_fst, setList_lists,
    Function.update_of_ne hne, vectorDecode] using hd.trans hp

theorem Input.vector {σ : Type*} {σc : Codec σ}
    {s : RawCallSeed (BinaryMaterializedField.Element t) σ m 4 t} {st : State 220 96}
    (hc : Input σc s st) (src len : Fin 220) (dst : Fin 96) (hne : (80 : Fin 96) ≠ dst) :
    Input σc s ((vector src len dst).run st).1 :=
  ⟨(vector_reg src len 200 dst (by decide) st).trans hc.width,
    (vector_reg src len 201 dst (by decide) st).trans hc.base,
    (vector_reg src len 202 dst (by decide) st).trans hc.dimension,
    (vector_reg src len 203 dst (by decide) st).trans hc.seed,
    (vector_reg src len 208 dst (by decide) st).trans hc.card,
    (vector_list src len dst 80 (by decide) hne st).trans hc.empty⟩

theorem Data.vector {σ : Type*} {σc : Codec σ}
    {s : RawCallSeed (BinaryMaterializedField.Element t) σ m 4 t} {st : State 220 96}
    (hd : Data σc s st) (src len : Fin 220) (dst : Fin 96) :
    Data σc s ((vector src len dst).run st).1 :=
  ⟨(vector_reg src len 204 dst (by decide) st).trans hd.inner,
    (vector_reg src len 205 dst (by decide) st).trans hd.direction,
    (vector_reg src len 206 dst (by decide) st).trans hd.param,
    (vector_reg src len 207 dst (by decide) st).trans hd.outer⟩

def dimension : Stmt 220 96 := .seq (.assign 210 (.const 4)) (.assign 211 (.mul 210 201))

def program : Stmt 220 96 := .seq splitSeed (.seq dimension
  (.seq (vector 207 202 81) (vector 205 211 82)))

theorem dimension_run {σ : Type*} (σc : Codec σ)
    (s : RawCallSeed (BinaryMaterializedField.Element t) σ m 4 t) (st : State 220 96)
    (hc : Input σc s st) (hd : Data σc s st) :
    Input σc s (dimension.run st).1 ∧ Data σc s (dimension.run st).1 ∧
    (dimension.run st).1.regs 211 = 4*m := by
  refine ⟨?_, ?_, ?_⟩
  · constructor <;> simp [dimension, Stmt.run, Expr.eval, Function.update, hc.width,
      hc.base, hc.dimension, hc.seed, hc.card, hc.empty]
  · constructor <;> simp [dimension, Stmt.run, Expr.eval, Function.update,
      hd.inner, hd.direction, hd.param, hd.outer]
  · simp [dimension, Stmt.run, Expr.eval, Function.update, hc.base]

attribute [local irreducible] splitSeed vector

theorem program_run {σ : Type*} (σc : Codec σ)
    (s : RawCallSeed (BinaryMaterializedField.Element t) σ m 4 t) (st : State 220 96)
    (hc : Input σc s st) :
    Input σc s (program.run st).1 ∧ Data σc s (program.run st).1 ∧
    (program.run st).1.lists 81 = List.ofFn (fun i => (fieldEquiv t (s.1 (σc.equiv.symm i))).val) ∧
    (program.run st).1.lists 82 = List.ofFn (fun i : Fin (4*m) =>
      (fieldEquiv t (s.2.2.1 (finProdFinEquiv.symm i))).val) := by
  have hd := splitSeed_run σc s st hc
  have hc' := hc.split
  generalize hu : (splitSeed.run st).1 = u at *
  have hdim := dimension_run σc s u hc' hd
  generalize hv : (dimension.run u).1 = v at *
  have hb := vector_run σc s.1 207 202 81 (by decide) v
    hdim.2.1.outer hdim.1.dimension hdim.1.card hdim.1.empty
  have hcB := hdim.1.vector 207 202 81 (by decide)
  have hdB := hdim.2.1.vector 207 202 81
  have hnB := (vector_reg 207 202 211 81 (by decide) v).trans hdim.2.2
  generalize hB : ((vector 207 202 81).run v).1 = b at *
  have hi := vector_run ((Codec.fin 4).prod (Codec.fin m)) s.2.2.1 205 211 82 (by decide) b
    hdB.direction hnB hcB.card hcB.empty
  have hfinal := (vector_list 205 211 82 81 (by decide) (by decide) b).trans hb
  simp only [program, run_seq_fst, hu, hv, hB]
  exact ⟨hcB.vector 205 211 82 (by decide), hdB.vector 205 211 82, hfinal, hi⟩

/-- The caller's remaining metadata registers survive complete raw-seed materialization. -/
theorem program_reg (st : State 220 96) (i : Fin 220) (hi : 212 ≤ i.val) :
    (program.run st).1.regs i = st.regs i := by
  have hd : ∀ u : State 220 96, (dimension.run u).1.regs i = u.regs i := by
    intro u
    apply run_regs_frame
    simp only [dimension, Stmt.regWrites, List.mem_append, List.mem_singleton, not_or]
    constructor <;> intro h <;> have hh := congrArg Fin.val h <;> simp at hh <;> omega
  simp only [program, run_seq_fst]
  exact (vector_reg 205 211 i 82 (by omega) _).trans
    ((vector_reg 207 202 i 81 (by omega) _).trans
      ((hd _).trans (splitSeed_reg st i (by omega)
        (by intro h; subst i; norm_num at hi) (by intro h; subst i; norm_num at hi)
        (by intro h; subst i; norm_num at hi) (by intro h; subst i; norm_num at hi)
        (by intro h; subst i; norm_num at hi))))

/-- Source arrays beyond the two output vectors are retained verbatim. -/
theorem program_list (st : State 220 96) (L : Fin 96) (hL : 83 ≤ L.val) :
    (program.run st).1.lists L = st.lists L := by
  have hd : ∀ u : State 220 96, (dimension.run u).1.lists L = u.lists L := by
    intro u
    apply run_lists_frame
    simp [dimension, Stmt.listWrites]
  simp only [program, run_seq_fst]
  exact (vector_list 205 211 82 L (by omega)
    (by intro h; subst L; norm_num at hL) _).trans
    ((vector_list 207 202 81 L (by omega)
      (by intro h; subst L; norm_num at hL) _).trans
      ((hd _).trans (splitSeed_list st L (by omega))))

end PCP.Lang.CorrectionSeed
