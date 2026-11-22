import PCP.Complexity.OuterBranchSeedIndex

/-!
# Protected public sources of the numeric outer-seed loader

Registers 160–170 store the field, dimension and table cardinalities; register
171 contains the actual outer sampler code. Lists 64–68 store the modulus,
empty list, interpolation nodes, physical query history and answer history.
- Each call uses at most the first 140 registers and 44 lists.
- Decoded sampler cells occupy registers 150–156.
-/

set_option maxRecDepth 1024

namespace PCP.Lang.OuterSeed

open PCP.Algebraic ThreeColorSeedIndex BinaryFieldCode OuterBranch

variable {t n m : ℕ} [NeZero t]

structure Public (k : Kind) (a : Fin 5 → Field t) (ζ : Field t)
    (qs : List ℕ) (bs : List Bool) (st : State 180 80) : Prop where
  width : st.regs 160 = t
  base : st.regs 161 = m
  card : st.regs 162 = 2^t
  root : st.regs 163 = (fieldEquiv t ζ).val
  dimension : st.regs 164 = k.dimension n
  vertices : st.regs 165 = (2^t)^n
  pairs : st.regs 166 = (2^t)^(n+n)
  proper : st.regs 167 = (2^t)^((n+n)+(n+n))
  inner : st.regs 168 = (2^t)^(4*m)
  affineLabels : st.regs 169 = 2^BooleanCoefficientIndex.dimension t 1
  cubicLabels : st.regs 170 = 2^BooleanCoefficientIndex.dimension t 3
  modulus : st.lists 64 = BinaryField.encode (BinaryWordMaterialization.modulus t)
  empty : st.lists 65 = []
  nodes : st.lists 66 = List.ofFn (fun i => (fieldEquiv t (a i)).val)
  history : st.lists 67 = qs
  answers : st.lists 68 = bs.map Bool.toNat

structure Frame (st out : State 180 80) : Prop where
  regs : ∀ i : Fin 180, 160 ≤ i.val → out.regs i = st.regs i
  lists : ∀ i : Fin 80, 64 ≤ i.val → out.lists i = st.lists i

theorem Frame.refl (st : State 180 80) : Frame st st :=
  ⟨fun _ _ => rfl, fun _ _ => rfl⟩

theorem Frame.trans {st u v : State 180 80} (h : Frame st u) (g : Frame u v) : Frame st v :=
  ⟨fun i hi => (g.regs i hi).trans (h.regs i hi),
    fun i hi => (g.lists i hi).trans (h.lists i hi)⟩

theorem Public.of_frame {k : Kind} {a : Fin 5 → Field t} {ζ : Field t}
    {qs : List ℕ} {bs : List Bool} {st out : State 180 80}
    (h : Public (n := n) (m := m) k a ζ qs bs st) (hf : Frame st out) :
    Public (n := n) (m := m) k a ζ qs bs out :=
  ⟨(hf.regs 160 (by decide)).trans h.width, (hf.regs 161 (by decide)).trans h.base,
    (hf.regs 162 (by decide)).trans h.card, (hf.regs 163 (by decide)).trans h.root,
    (hf.regs 164 (by decide)).trans h.dimension, (hf.regs 165 (by decide)).trans h.vertices,
    (hf.regs 166 (by decide)).trans h.pairs, (hf.regs 167 (by decide)).trans h.proper,
    (hf.regs 168 (by decide)).trans h.inner, (hf.regs 169 (by decide)).trans h.affineLabels,
    (hf.regs 170 (by decide)).trans h.cubicLabels,
    (hf.lists 64 (by decide)).trans h.modulus, (hf.lists 65 (by decide)).trans h.empty,
    (hf.lists 66 (by decide)).trans h.nodes, (hf.lists 67 (by decide)).trans h.history,
    (hf.lists 68 (by decide)).trans h.answers⟩

def call {R Q : ℕ} (hR : R ≤ 140) (hQ : Q ≤ 44) (p : Stmt R Q) : Stmt 180 80 :=
  p.rename (Fin.castLE (hR.trans (by decide))) (Fin.castLE (hQ.trans (by decide)))

theorem call_result {R Q : ℕ} (hR : R ≤ 140) (hQ : Q ≤ 44) (p : Stmt R Q)
    (st : State 180 80) :
    (((call hR hQ p).run st).1.restrict (Fin.castLE (hR.trans (by decide)))
      (Fin.castLE (hQ.trans (by decide))), ((call hR hQ p).run st).2) =
    p.run (st.restrict (Fin.castLE (hR.trans (by decide)))
      (Fin.castLE (hQ.trans (by decide)))) :=
  p.run_rename _ _ (Fin.castLE_injective _) (Fin.castLE_injective _) st

theorem call_reg {R Q : ℕ} (hR : R ≤ 140) (hQ : Q ≤ 44) (p : Stmt R Q)
    (st : State 180 80) (i : Fin 180) (hi : R ≤ i.val) :
    ((call hR hQ p).run st).1.regs i = st.regs i := by
  apply Stmt.run_rename_reg_outside
  intro j hj
  have := congrArg Fin.val hj
  simp only [Fin.val_castLE] at this
  omega

theorem call_list {R Q : ℕ} (hR : R ≤ 140) (hQ : Q ≤ 44) (p : Stmt R Q)
    (st : State 180 80) (i : Fin 80) (hi : Q ≤ i.val) :
    ((call hR hQ p).run st).1.lists i = st.lists i := by
  apply Stmt.run_rename_list_outside
  intro j hj
  have := congrArg Fin.val hj
  simp only [Fin.val_castLE] at this
  omega

theorem call_frame {R Q : ℕ} (hR : R ≤ 140) (hQ : Q ≤ 44) (p : Stmt R Q)
    (st : State 180 80) : Frame st ((call hR hQ p).run st).1 :=
  ⟨fun i hi => call_reg hR hQ p st i (by omega),
    fun i hi => call_list hR hQ p st i (by omega)⟩

theorem frame_of_writes (p : Stmt 180 80)
    (hr : ∀ i ∈ p.regWrites, i.val < 160) (hl : ∀ i ∈ p.listWrites, i.val < 64)
    (st : State 180 80) : Frame st (p.run st).1 := by
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

def codes (k : Kind) (s : Sample k t n m) : Fin 7 → ℕ :=
  ![((innerCodec (BinaryMaterializedField.coordinates t) m 4).equiv (innerSeed s)).val,
    ((hadamardCodec t k.degree).equiv (primarySeed s)).val,
    ((bitsCodec t).equiv s.2.2.1.2).val,
    (ThreeColorQueryIndex.innerIndex (fieldEquiv t) m 4 s.2.2.1.1).val,
    (fieldEquiv t s.2.1).val,
    k.pointCode (fieldEquiv t) s.1.2,
    k.pointCode (fieldEquiv t) s.1.1]

def dataPort (i : Fin 7) : Fin 180 := ⟨150+i.val, by omega⟩

def Data (k : Kind) (s : Sample k t n m) (st : State 180 80) : Prop :=
  ∀ i, st.regs (dataPort i) = codes k s i

end PCP.Lang.OuterSeed
