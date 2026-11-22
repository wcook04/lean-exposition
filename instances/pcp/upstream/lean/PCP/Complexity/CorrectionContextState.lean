import PCP.Complexity.CorrectionSeedMaterialization
import PCP.Complexity.InnerSeedLang
import PCP.Complexity.LocalCorrectionSemantics

/-!
# Stored sources for correction calls decoded from numeric seeds

The numeric seed and its coordinate materialization occupy the last registers.
Field metadata, requested point, homogeneous label and global history remain
protected while the inner seed loader constructs both actual selector arms.
-/

namespace PCP.Lang.CorrectionContext

open PCP.Algebraic ThreeColorSeedIndex ThreeColorFullFieldSampling BinaryFieldCode
open LocalCorrection

variable {t n m : ℕ} [NeZero t]

def coordinateCodec (k : Certificate) (n : ℕ) : Codec (k.outer.Coordinates n) :=
  ⟨k.outer.dimension n, k.outer.coordinateEquiv n⟩

theorem pointCode_eq (k : Certificate) (p : k.Point t n) :
    (((coordinateCodec k n).function (fieldCodec (BinaryMaterializedField.coordinates t))).equiv
      p).val = k.outer.pointCode (fieldEquiv t) p := by
  change (finFunctionFinEquiv (fun i =>
    (fieldCodec (BinaryMaterializedField.coordinates t)).equiv
      (p ((k.outer.coordinateEquiv n).symm i)))).val = _
  rw [UniformDecode.fieldCodec_materialized]
  rfl

structure Public (k : Certificate) (nodes : Fin 5 → OuterBranch.Field t)
    (ζ : OuterBranch.Field t) (a : k.Point t n) (w : Fin t → ZMod 2)
    (qs : List ℕ) (bs : List Bool) (st : State 220 96) : Prop where
  vertices : st.regs 212 = (2^t)^n
  pairs : st.regs 213 = (2^t)^(n+n)
  proper : st.regs 214 = (2^t)^((n+n)+(n+n))
  inner : st.regs 215 = (2^t)^(4*m)
  affineLabels : st.regs 216 = 2^BooleanCoefficientIndex.dimension t 1
  cubicLabels : st.regs 217 = 2^BooleanCoefficientIndex.dimension t 3
  root : st.regs 218 = (fieldEquiv t ζ).val
  pointCode : st.regs 219 = k.outer.pointCode (fieldEquiv t) a
  point : st.lists 83 = List.ofFn (fun i => (fieldEquiv t (k.outer.vector a i)).val)
  label : st.lists 84 = List.ofFn (fun i => (w i).val)
  modulus : st.lists 85 = BinaryField.encode (BinaryWordMaterialization.modulus t)
  nodes : st.lists 86 = List.ofFn (fun i => (fieldEquiv t (nodes i)).val)
  history : st.lists 87 = qs
  answers : st.lists 88 = bs.map Bool.toNat

structure Loaded (k : Certificate) (s : k.Seed t n m) (st : State 220 96) : Prop where
  input : CorrectionSeed.Input (coordinateCodec k n) (padCall s) st
  data : CorrectionSeed.Data (coordinateCodec k n) (padCall s) st
  outer : st.lists 81 = List.ofFn (fun i => (fieldEquiv t (k.outer.vector s.1 i)).val)
  direction : st.lists 82 = List.ofFn (fun i =>
    (fieldEquiv t (StandardCorrection.vector s.2.2.1 i)).val)

structure Frame (st out : State 220 96) : Prop where
  regs : ∀ i : Fin 220, 180 ≤ i.val → out.regs i = st.regs i
  lists : ∀ L : Fin 96, 80 ≤ L.val → out.lists L = st.lists L

theorem Frame.trans {st u v : State 220 96} (h : Frame st u) (g : Frame u v) : Frame st v :=
  ⟨fun i hi => (g.regs i hi).trans (h.regs i hi),
    fun L hL => (g.lists L hL).trans (h.lists L hL)⟩

theorem Public.of_frame {k : Certificate} {nodes : Fin 5 → OuterBranch.Field t}
    {ζ : OuterBranch.Field t} {a : k.Point t n} {w : Fin t → ZMod 2}
    {qs : List ℕ} {bs : List Bool} {st out : State 220 96}
    (h : Public (m := m) k nodes ζ a w qs bs st) (hf : Frame st out) :
    Public (m := m) k nodes ζ a w qs bs out := by
  constructor
  all_goals first
    | exact (hf.regs _ (by decide)).trans h.vertices
    | exact (hf.regs _ (by decide)).trans h.pairs
    | exact (hf.regs _ (by decide)).trans h.proper
    | exact (hf.regs _ (by decide)).trans h.inner
    | exact (hf.regs _ (by decide)).trans h.affineLabels
    | exact (hf.regs _ (by decide)).trans h.cubicLabels
    | exact (hf.regs _ (by decide)).trans h.root
    | exact (hf.regs _ (by decide)).trans h.pointCode
    | exact (hf.lists _ (by decide)).trans h.point
    | exact (hf.lists _ (by decide)).trans h.label
    | exact (hf.lists _ (by decide)).trans h.modulus
    | exact (hf.lists _ (by decide)).trans h.nodes
    | exact (hf.lists _ (by decide)).trans h.history
    | exact (hf.lists _ (by decide)).trans h.answers

theorem Loaded.of_frame {k : Certificate} {s : k.Seed t n m} {st out : State 220 96}
    (h : Loaded k s st) (hf : Frame st out) : Loaded k s out := by
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  all_goals first
    | exact (hf.regs _ (by decide)).trans h.input.width
    | exact (hf.regs _ (by decide)).trans h.input.base
    | exact (hf.regs _ (by decide)).trans h.input.dimension
    | exact (hf.regs _ (by decide)).trans h.input.seed
    | exact (hf.regs _ (by decide)).trans h.input.card
    | exact (hf.lists _ (by decide)).trans h.input.empty
    | exact (hf.regs _ (by decide)).trans h.data.inner
    | exact (hf.regs _ (by decide)).trans h.data.direction
    | exact (hf.regs _ (by decide)).trans h.data.param
    | exact (hf.regs _ (by decide)).trans h.data.outer
    | exact (hf.lists _ (by decide)).trans h.outer
    | exact (hf.lists _ (by decide)).trans h.direction

def innerState (st : State 220 96) : State 140 44 :=
  st.restrict (Fin.castLE (by decide)) (Fin.castLE (by decide))

def outerState (st : State 220 96) : State 180 80 :=
  st.restrict (Fin.castLE (by decide)) (Fin.castLE (by decide))

theorem frame_of_writes (p : Stmt 220 96)
    (hr : ∀ i ∈ p.regWrites, i.val < 180) (hl : ∀ L ∈ p.listWrites, L.val < 80)
    (st : State 220 96) : Frame st (p.run st).1 := by
  constructor
  · intro i hi
    apply run_regs_frame
    intro h
    have := hr i h
    omega
  · intro L hL
    apply run_lists_frame
    intro h
    have := hl L h
    omega

end PCP.Lang.CorrectionContext
