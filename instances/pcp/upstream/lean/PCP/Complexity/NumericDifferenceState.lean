import PCP.Complexity.LangDifferenceBranchCost
import PCP.Complexity.ThreeColorNestedSeedSemantics
import PCP.Complexity.LangSeedMaterialization

/-!
# Public numeric inputs of the difference consistency branch

The state has 120 scalar and 40 list cells. Sources are width100, dimension101,
inner base102, field cardinality103, vertex/pair cardinalities104/105, affine/cubic
label cardinalities106/107, and numeric seed108. Lists32/33/34 are empty/query
history/answer history. Every work cell is initialized by the program.
-/

namespace PCP.Lang.NumericDifference

open PCP.Algebraic ThreeColorSeedIndex BinaryFieldCode

abbrev Field (t : ℕ) := BinaryMaterializedField.Element t
abbrev Sample (t n : ℕ) := ((Fin n → Field t) × (Fin n → Field t)) × (Fin t → ZMod 2)

def seedCodec (t n : ℕ) [NeZero t] : Codec (Sample t n) :=
  (((Codec.fin n).function (fieldCodec (BinaryMaterializedField.coordinates t))).prod
    ((Codec.fin n).function (fieldCodec (BinaryMaterializedField.coordinates t)))).prod
    (bitsCodec t)

variable {t n m : ℕ} [NeZero t]

structure Public (n m : ℕ) (qs : List ℕ) (bs : List Bool) (st : State 120 40) : Prop where
  width : st.regs 100 = t
  dimension : st.regs 101 = n
  base : st.regs 102 = m
  card : st.regs 103 = 2^t
  vertices : st.regs 104 = (2^t)^n
  pairs : st.regs 105 = (2^t)^(n+n)
  affineLabels : st.regs 106 = 2^BooleanCoefficientIndex.dimension t 1
  cubicLabels : st.regs 107 = 2^BooleanCoefficientIndex.dimension t 3
  empty : st.lists 32 = []
  history : st.lists 33 = qs
  answers : st.lists 34 = bs.map Bool.toNat

structure Frame (st out : State 120 40) : Prop where
  regs : ∀ i : Fin 120, 100 ≤ i.val → out.regs i = st.regs i
  lists : ∀ i : Fin 40, 32 ≤ i.val → out.lists i = st.lists i

theorem Frame.trans {st u v : State 120 40} (h : Frame st u) (g : Frame u v) : Frame st v :=
  ⟨fun i hi => (g.regs i hi).trans (h.regs i hi),
    fun i hi => (g.lists i hi).trans (h.lists i hi)⟩

omit [NeZero t] in
theorem Public.of_frame {qs : List ℕ} {bs : List Bool} {st out : State 120 40}
    (h : Public (t := t) n m qs bs st) (hf : Frame st out) : Public (t := t) n m qs bs out :=
  ⟨(hf.regs 100 (by decide)).trans h.width, (hf.regs 101 (by decide)).trans h.dimension,
    (hf.regs 102 (by decide)).trans h.base, (hf.regs 103 (by decide)).trans h.card,
    (hf.regs 104 (by decide)).trans h.vertices, (hf.regs 105 (by decide)).trans h.pairs,
    (hf.regs 106 (by decide)).trans h.affineLabels, (hf.regs 107 (by decide)).trans h.cubicLabels,
    (hf.lists 32 (by decide)).trans h.empty, (hf.lists 33 (by decide)).trans h.history,
    (hf.lists 34 (by decide)).trans h.answers⟩

def call {R Q : ℕ} (hR : R ≤ 90) (hQ : Q ≤ 32) (p : Stmt R Q) : Stmt 120 40 :=
  p.rename (Fin.castLE (hR.trans (by decide))) (Fin.castLE (hQ.trans (by decide)))

theorem call_result {R Q : ℕ} (hR : R ≤ 90) (hQ : Q ≤ 32) (p : Stmt R Q) (st : State 120 40) :
    (((call hR hQ p).run st).1.restrict (Fin.castLE (hR.trans (by decide)))
      (Fin.castLE (hQ.trans (by decide))), ((call hR hQ p).run st).2) =
    p.run (st.restrict (Fin.castLE (hR.trans (by decide)))
      (Fin.castLE (hQ.trans (by decide)))) :=
  p.run_rename _ _ (Fin.castLE_injective _) (Fin.castLE_injective _) st

theorem call_reg {R Q : ℕ} (hR : R ≤ 90) (hQ : Q ≤ 32) (p : Stmt R Q)
    (st : State 120 40) (i : Fin 120) (hi : R ≤ i.val) :
    ((call hR hQ p).run st).1.regs i = st.regs i := by
  apply Stmt.run_rename_reg_outside
  intro j hj
  have := congrArg Fin.val hj
  simp only [Fin.val_castLE] at this
  omega

theorem call_list {R Q : ℕ} (hR : R ≤ 90) (hQ : Q ≤ 32) (p : Stmt R Q)
    (st : State 120 40) (i : Fin 40) (hi : Q ≤ i.val) :
    ((call hR hQ p).run st).1.lists i = st.lists i := by
  apply Stmt.run_rename_list_outside
  intro j hj
  have := congrArg Fin.val hj
  simp only [Fin.val_castLE] at this
  omega

theorem call_frame {R Q : ℕ} (hR : R ≤ 90) (hQ : Q ≤ 32) (p : Stmt R Q)
    (st : State 120 40) : Frame st ((call hR hQ p).run st).1 :=
  ⟨fun i hi => call_reg hR hQ p st i (by omega),
    fun i hi => call_list hR hQ p st i (by omega)⟩

theorem frame_of_writes (p : Stmt 120 40)
    (hr : ∀ i ∈ p.regWrites, i.val < 100) (hl : ∀ i ∈ p.listWrites, i.val < 32)
    (st : State 120 40) : Frame st (p.run st).1 := by
  constructor
  · intro i hi
    apply run_regs_frame
    intro h
    have := hr i h
    omega
  · intro i hi
    apply run_lists_frame
    intro h
    have := hl i h
    omega

def codes (s : Sample t n) : Fin 3 → ℕ :=
  ![((bitsCodec t).equiv s.2).val,
    (ThreeColorQueryIndex.vertexIndex (fieldEquiv t) n s.1.2).val,
    (ThreeColorQueryIndex.vertexIndex (fieldEquiv t) n s.1.1).val]

def dataPort (i : Fin 3) : Fin 120 := ⟨90+i.val,by omega⟩

def Data (s : Sample t n) (st : State 120 40) : Prop :=
  ∀ i, st.regs (dataPort i) = codes s i

end PCP.Lang.NumericDifference
