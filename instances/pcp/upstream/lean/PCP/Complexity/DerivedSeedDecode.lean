import PCP.Complexity.DerivedGridSite
import PCP.Complexity.ThreeColorNestedSeedSemantics

/-! # Decomposing the actual raw derived-grid seed into its five numeric components -/

-- Fixed port arithmetic uses 300 registers.
set_option maxRecDepth 1024

namespace PCP.Lang.DerivedSeed

open PCP.Algebraic ThreeColorSeedIndex ThreeColorFullFieldSampling BinaryFieldCode
open LocalCorrection DerivedGrid

variable {t n m : ℕ} [NeZero t]

structure Input (k : Certificate) (s : DerivedGrid.RawSample k t n m)
    (st : State 300 112) : Prop where
  width : st.regs 240 = t
  base : st.regs 241 = m
  dimension : st.regs 256 = baseDimension k n
  seed : st.regs 257 = ((derivedCodec (BinaryMaterializedField.coordinates t)
    (baseDimension k n) m 4 3).equiv s).val
  card : st.regs 243 = 2^t
  empty : st.lists 100 = []

structure Data (k : Certificate) (s : DerivedGrid.RawSample k t n m)
    (st : State 300 112) : Prop where
  mask : st.regs 277 = ((coefficientCodec t 3).equiv s.2.2).val
  first : st.regs 248 = ((callCodec (BinaryMaterializedField.coordinates t)
    ((Codec.fin (baseDimension k n)).sum (Codec.fin (baseDimension k n))) m 4).equiv s.2.1.2.1).val
  second : st.regs 249 = ((callCodec (BinaryMaterializedField.coordinates t)
    ((Codec.fin (baseDimension k n)).sum (Codec.fin (baseDimension k n))) m 4).equiv s.2.1.2.2).val
  label : st.regs 258 = ((bitsCodec t).equiv s.2.1.1).val
  point : st.regs 259 = (((Codec.fin (baseDimension k n)).function
    (fieldCodec (BinaryMaterializedField.coordinates t))).equiv s.1).val

def prepare : Stmt 300 112 := .seq (.copy 100 3)
  (.seq (.assign 0 (.var 256)) (.seq (.assign 1 (.var 241))
    (.seq (.assign 2 (.const 4)) (.seq (.assign 3 (.var 240)) (.assign 15 (.var 257))))))

def decode : Stmt 300 112 := DerivedCall.call (by decide) (by decide) NestedSeed.derived

def unpack : Stmt 300 112 := .seq (.pop 1 277 278) (.seq (.pop 1 249 278)
  (.seq (.pop 1 248 278) (.seq (.pop 1 258 278) (.pop 1 259 278))))

def split : Stmt 300 112 := .seq prepare (.seq decode unpack)

attribute [local irreducible] decode NestedSeed.derived

/-- All five output integers are the exact structural component codes. -/
theorem split_run (k : Certificate) (s : DerivedGrid.RawSample k t n m) (st : State 300 112)
    (hc : Input k s st) : Data k s (split.run st).1 := by
  have hi : ComputedSeed.Context (baseDimension k n) m 4 t
      ((derivedCodec (BinaryMaterializedField.coordinates t)
        (baseDimension k n) m 4 3).equiv s).val
      (DerivedCall.view (by decide) (by decide)
        (prepare.run st).1) := by
    refine ⟨?_, ?_, ?_⟩
    · intro i
      fin_cases i <;> simp [prepare, Stmt.run, Expr.eval, Function.update,
        DerivedCall.view, State.restrict, hc.width, hc.base, hc.dimension]
    · simp [prepare, Stmt.run, Expr.eval, Function.update, DerivedCall.view,
        State.restrict, hc.seed]
    · simp [prepare, Stmt.run, Function.update, DerivedCall.view, State.restrict, hc.empty]
  have h := NestedSeed.derived_run (BinaryMaterializedField.coordinates t)
    (baseDimension k n) m 4 s _ hi
  rw [← DerivedCall.call_result (by decide) (by decide) NestedSeed.derived (prepare.run st).1] at h
  rw [show DerivedCall.call (by decide) (by decide) NestedSeed.derived = decode by
    unfold decode; rfl] at h
  change (decode.run (prepare.run st).1).1.lists 1 = _ at h
  generalize hu : (decode.run (prepare.run st).1).1 = u at *
  simp only [split, run_seq_fst, hu]
  constructor <;> simp [unpack, Stmt.run, Function.update, h]

theorem split_reg (st : State 300 112) (i : Fin 300) (hi : 240 ≤ i.val)
    (h1 : i ≠ 248) (h2 : i ≠ 249) (h3 : i ≠ 258) (h4 : i ≠ 259)
    (h5 : i ≠ 277) (h6 : i ≠ 278) : (split.run st).1.regs i = st.regs i := by
  have hu : ∀ s : State 300 112, (unpack.run s).1.regs i = s.regs i := by
    intro s
    apply run_regs_frame
    simp [unpack, Stmt.regWrites, h1, h2, h3, h4, h5, h6]
  have hp : (prepare.run st).1.regs i = st.regs i := by
    apply run_regs_frame
    have hb : ∀ j ∈ prepare.regWrites, j.val < 220 := by decide
    intro hm
    have := hb i hm
    omega
  have hd := DerivedCall.call_reg (by decide) (by decide)
    NestedSeed.derived (prepare.run st).1 i (by omega)
  simpa only [split, run_seq_fst, hu, decode] using hd.trans hp

theorem split_list (st : State 300 112) (L : Fin 112) (hL : 96 ≤ L.val) :
    (split.run st).1.lists L = st.lists L := by
  have hu : ∀ s : State 300 112, (unpack.run s).1.lists L = s.lists L := by
    intro s
    apply run_lists_frame
    have hb : ∀ j ∈ unpack.listWrites, j.val < 96 := by decide
    intro hm
    have := hb L hm
    omega
  have hp : (prepare.run st).1.lists L = st.lists L := by
    apply run_lists_frame
    have hb : ∀ j ∈ prepare.listWrites, j.val < 96 := by decide
    intro hm
    have := hb L hm
    omega
  have hd := DerivedCall.call_list (by decide) (by decide)
    NestedSeed.derived (prepare.run st).1 L hL
  simpa only [split, run_seq_fst, hu, decode] using hd.trans hp

theorem Input.split {k : Certificate} {s : DerivedGrid.RawSample k t n m}
    {st : State 300 112} (h : Input k s st) : Input k s (split.run st).1 := by
  constructor
  · exact (split_reg st 240 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)).trans h.width
  · exact (split_reg st 241 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)).trans h.base
  · exact (split_reg st 256 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)).trans h.dimension
  · exact (split_reg st 257 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)).trans h.seed
  · exact (split_reg st 243 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)).trans h.card
  · exact (split_list st 100 (by decide)).trans h.empty

end PCP.Lang.DerivedSeed
