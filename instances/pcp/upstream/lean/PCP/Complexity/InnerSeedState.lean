/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Complexity.InnerBranchCost
import PCP.Complexity.HadamardSeedCost
import PCP.Complexity.LangSeedMaterialization
import PCP.Complexity.ThreeColorNestedSeedSemantics

/-!
# Public stored inputs for numeric inner-seed materialization

The loader uses 140 natural and 44 list registers. Public source registers start
at 120: width, inner base, field cardinality, nine physical site-prefix entries,
then the actual inner seed code at 132. Lists 40/41/42 hold modulus/empty/nodes.
It constructs the complete selector context in the first 120/40 cells.
-/

namespace PCP.Lang.InnerSeed

open PCP.Algebraic ThreeColorSeedIndex InterpolationBranch

variable {t n m : ℕ} [NeZero t]

def prefixPort (i : Fin 9) : Fin 140 := ⟨123 + i.val, by omega⟩

structure Public (m : ℕ) (a : Fin 5 → Field t) (site : StandardCorrection.Site (Field t) n)
    (st : State 140 44) : Prop where
  width : st.regs 120 = t
  base : st.regs 121 = m
  card : st.regs 122 = 2 ^ t
  address : ∀ i, st.regs (prefixPort i) = site.prefix (BinaryFieldCode.fieldEquiv t)
    (2 ^ BooleanCoefficientIndex.dimension t 1) (2 ^ BooleanCoefficientIndex.dimension t 3) m i
  modulus : st.lists 40 = BinaryField.encode (BinaryWordMaterialization.modulus t)
  empty : st.lists 41 = []
  nodes : st.lists 42 = List.ofFn (fun i => (BinaryFieldCode.fieldEquiv t (a i)).val)

structure Frame (st out : State 140 44) : Prop where
  regs : ∀ i : Fin 140, 120 ≤ i.val → out.regs i = st.regs i
  lists : ∀ L : Fin 44, 40 ≤ L.val → out.lists L = st.lists L

theorem Frame.refl (st : State 140 44) : Frame st st :=
  ⟨fun _ _ => rfl, fun _ _ => rfl⟩

theorem Frame.trans {st u v : State 140 44} (h : Frame st u) (g : Frame u v) : Frame st v :=
  ⟨fun i hi => (g.regs i hi).trans (h.regs i hi),
    fun L hL => (g.lists L hL).trans (h.lists L hL)⟩

theorem Public.of_frame {a : Fin 5 → Field t} {site : StandardCorrection.Site (Field t) n}
    {st out : State 140 44} (h : Public m a site st) (hf : Frame st out) : Public m a site out :=
  ⟨(hf.regs 120 (by decide)).trans h.width, (hf.regs 121 (by decide)).trans h.base,
    (hf.regs 122 (by decide)).trans h.card,
    fun i => (hf.regs (prefixPort i) (by simp only [prefixPort]; omega)).trans (h.address i),
    (hf.lists 40 (by decide)).trans h.modulus, (hf.lists 41 (by decide)).trans h.empty,
    (hf.lists 42 (by decide)).trans h.nodes⟩

def call {R Q : ℕ} (hR : R ≤ 120) (hQ : Q ≤ 40) (p : Stmt R Q) : Stmt 140 44 :=
  p.rename (Fin.castLE (hR.trans (by decide))) (Fin.castLE (hQ.trans (by decide)))

theorem call_result {R Q : ℕ} (hR : R ≤ 120) (hQ : Q ≤ 40) (p : Stmt R Q)
    (st : State 140 44) :
    (((call hR hQ p).run st).1.restrict (Fin.castLE (hR.trans (by decide)))
      (Fin.castLE (hQ.trans (by decide))), ((call hR hQ p).run st).2) =
    p.run (st.restrict (Fin.castLE (hR.trans (by decide)))
      (Fin.castLE (hQ.trans (by decide)))) :=
  p.run_rename _ _ (Fin.castLE_injective _) (Fin.castLE_injective _) st

theorem call_reg {R Q : ℕ} (hR : R ≤ 120) (hQ : Q ≤ 40) (p : Stmt R Q)
    (st : State 140 44) (i : Fin 140) (hi : R ≤ i.val) :
    ((call hR hQ p).run st).1.regs i = st.regs i := by
  apply Stmt.run_rename_reg_outside
  intro j hj
  have := congrArg Fin.val hj
  simp only [Fin.val_castLE] at this
  omega

theorem call_list {R Q : ℕ} (hR : R ≤ 120) (hQ : Q ≤ 40) (p : Stmt R Q)
    (st : State 140 44) (L : Fin 44) (hL : Q ≤ L.val) :
    ((call hR hQ p).run st).1.lists L = st.lists L := by
  apply Stmt.run_rename_list_outside
  intro j hj
  have := congrArg Fin.val hj
  simp only [Fin.val_castLE] at this
  omega

theorem call_frame {R Q : ℕ} (hR : R ≤ 120) (hQ : Q ≤ 40) (p : Stmt R Q)
    (st : State 140 44) : Frame st ((call hR hQ p).run st).1 :=
  ⟨fun i hi => call_reg hR hQ p st i (hR.trans hi),
    fun L hL => call_list hR hQ p st L (hQ.trans hL)⟩

theorem frame_of_writes (p : Stmt 140 44)
    (hr : ∀ i ∈ p.regWrites, i.val < 120) (hl : ∀ L ∈ p.listWrites, L.val < 40)
    (st : State 140 44) : Frame st (p.run st).1 := by
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

/-- The actual structural code of an inner point is already its physical point code. -/
theorem pointCode_eq (p : Point t m) :
    ((innerPointCodec (BinaryMaterializedField.coordinates t) m 4).equiv p).val =
      (ThreeColorQueryIndex.innerIndex (BinaryFieldCode.fieldEquiv t) m 4 p).val := by
  change (finFunctionFinEquiv (fun i : Fin (4 * m) =>
    (fieldCodec (BinaryMaterializedField.coordinates t)).equiv
      (p (finProdFinEquiv.symm i)))).val = _
  rw [UniformDecode.fieldCodec_materialized]
  rfl

def codes (s : InnerBranch.Seed t m) : Fin 7 → ℕ :=
  ![((bitsCodec t).equiv s.2.2.2).val,
    ((fieldCodec (BinaryMaterializedField.coordinates t)).equiv s.2.2.1.2).val,
    ((innerPointCodec (BinaryMaterializedField.coordinates t) m 4).equiv s.2.2.1.1.2).val,
    ((innerPointCodec (BinaryMaterializedField.coordinates t) m 4).equiv s.2.2.1.1.1).val,
    ((hadamardCodec t 1).equiv s.2.1.2).val,
    ((innerPointCodec (BinaryMaterializedField.coordinates t) m 4).equiv s.2.1.1).val,
    (boolCodec.equiv s.1).val]

def dataPort (i : Fin 7) : Fin 140 := ⟨103 + i.val, by omega⟩

def Data (s : InnerBranch.Seed t m) (st : State 140 44) : Prop :=
  ∀ i, st.regs (dataPort i) = codes s i

end PCP.Lang.InnerSeed
