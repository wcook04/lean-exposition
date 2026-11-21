import PCP.Complexity.InterpolationWeightLoadCost
import PCP.Complexity.StandardCorrectionFrame
import PCP.Complexity.StandardCorrectionAddressLang
import PCP.Complexity.BinaryLabelScaleCost
import PCP.Complexity.LangHistoryParityOracle

/-!
# Stored context for the interpolation branch

Read-only sources are placed outside the arithmetic subroutines. The branch
uses the shared production point, coefficient, and physical address codecs.
-/

namespace PCP.Lang.InterpolationBranch

open PCP.Algebraic BinaryFieldCode BinaryPolynomialSpace

variable {t n m : ℕ} [NeZero t]

abbrev Field (t : ℕ) := BinaryMaterializedField.Element t
abbrev Point (t m : ℕ) := BinaryLocalCorrection.InnerPoint (Field t) m 4

def prefixPort (i : Fin 9) : Fin 100 := ⟨83+i.val, by omega⟩

structure Context (a : Fin 5 → Field t) (z : Field t) (u v : Point t m)
    (w : Fin t → ZMod 2) (site : StandardCorrection.Site (Field t) n)
    (st : State 100 40) : Prop where
  width : st.regs 80 = t
  card : st.regs 81 = 2^t
  param : st.regs 82 = (fieldEquiv t z).val
  modulus : st.lists 3 = BinaryField.encode (BinaryWordMaterialization.modulus t)
  empty : st.lists 7 = []
  left : st.lists 32 = List.ofFn (fun i => (fieldEquiv t (StandardCorrection.vector u i)).val)
  right : st.lists 33 = List.ofFn (fun i => (fieldEquiv t (StandardCorrection.vector v i)).val)
  label : st.lists 34 = List.ofFn (fun i => (w i).val)
  nodes : st.lists 35 = List.ofFn (fun i => (fieldEquiv t (a i)).val)
  address : ∀ i, st.regs (prefixPort i) = site.prefix (fieldEquiv t)
    (2^BooleanCoefficientIndex.dimension t 1) (2^BooleanCoefficientIndex.dimension t 3) m i

/-- All semantic sources live outside the scratch region. -/
structure Frame (st out : State 100 40) : Prop where
  regs : ∀ i : Fin 100, 80 ≤ i.val → i.val < 92 → out.regs i = st.regs i
  lists : ∀ i : Fin 40, 32 ≤ i.val → out.lists i = st.lists i
  modulus : out.lists 3 = st.lists 3
  empty : out.lists 7 = st.lists 7

theorem Frame.refl (st : State 100 40) : Frame st st :=
  ⟨fun _ _ _ => rfl, fun _ _ => rfl, rfl, rfl⟩

theorem Frame.trans {s u v : State 100 40} (h : Frame s u) (k : Frame u v) : Frame s v :=
  ⟨fun i hi hj => (k.regs i hi hj).trans (h.regs i hi hj),
    fun i hi => (k.lists i hi).trans (h.lists i hi),
    k.modulus.trans h.modulus, k.empty.trans h.empty⟩

theorem Context.of_frame {a : Fin 5 → Field t} {z : Field t} {u v : Point t m}
    {w : Fin t → ZMod 2} {site : StandardCorrection.Site (Field t) n}
    {st out : State 100 40} (hc : Context a z u v w site st) (hf : Frame st out) :
    Context a z u v w site out :=
  ⟨(hf.regs 80 (by decide) (by decide)).trans hc.width,
    (hf.regs 81 (by decide) (by decide)).trans hc.card,
    (hf.regs 82 (by decide) (by decide)).trans hc.param, hf.modulus.trans hc.modulus,
    hf.empty.trans hc.empty, (hf.lists 32 (by decide)).trans hc.left,
    (hf.lists 33 (by decide)).trans hc.right, (hf.lists 34 (by decide)).trans hc.label,
    (hf.lists 35 (by decide)).trans hc.nodes,
    fun i => (hf.regs (prefixPort i) (by simp only [prefixPort]; omega)
      (by simp only [prefixPort]; omega)).trans (hc.address i)⟩

/-- All fixed arithmetic routines use the same prefix embedding. -/
def call {R Q : ℕ} (hR : R ≤ 80) (hQ : Q ≤ 32) (p : Stmt R Q) : Stmt 100 40 :=
  p.rename (Fin.castLE (hR.trans (by decide))) (Fin.castLE (hQ.trans (by decide)))

theorem call_result {R Q : ℕ} (hR : R ≤ 80) (hQ : Q ≤ 32) (p : Stmt R Q)
    (st : State 100 40) :
    (((call hR hQ p).run st).1.restrict (Fin.castLE (hR.trans (by decide)))
      (Fin.castLE (hQ.trans (by decide))), ((call hR hQ p).run st).2) =
    p.run (st.restrict (Fin.castLE (hR.trans (by decide)))
      (Fin.castLE (hQ.trans (by decide)))) :=
  p.run_rename _ _ (Fin.castLE_injective _) (Fin.castLE_injective _) st

theorem call_reg {R Q : ℕ} (hR : R ≤ 80) (hQ : Q ≤ 32) (p : Stmt R Q)
    (st : State 100 40) (i : Fin 100) (hi : 80 ≤ i.val) :
    ((call hR hQ p).run st).1.regs i = st.regs i := by
  apply Stmt.run_rename_reg_outside
  intro j hj
  have h := congrArg Fin.val hj
  simp only [Fin.val_castLE] at h
  omega

theorem call_list {R Q : ℕ} (hR : R ≤ 80) (hQ : Q ≤ 32) (p : Stmt R Q)
    (st : State 100 40) (i : Fin 40) (hi : Q ≤ i.val) :
    ((call hR hQ p).run st).1.lists i = st.lists i := by
  apply Stmt.run_rename_list_outside
  intro j hj
  have h := congrArg Fin.val hj
  simp only [Fin.val_castLE] at h
  omega

theorem Frame.assign (st : State 100 40) (i : Fin 100) (hi : i.val < 80 ∨ 92 ≤ i.val) (v : ℕ) :
    Frame st (setReg st i v) := by
  refine ⟨?_, fun _ _ => rfl, rfl, rfl⟩
  intro j hj hk
  simp only [setReg_regs, Function.update_of_ne (show j ≠ i by
    intro h; subst j; omega)]

theorem Frame.copy (st : State 100 40) (src dst : Fin 40)
    (hd : dst.val < 32) (h3 : dst ≠ 3) (h7 : dst ≠ 7) :
    Frame st (setList st dst (st.lists src)) := by
  refine ⟨fun _ _ _ => rfl, ?_, ?_, ?_⟩
  · intro j hj
    simp only [setList_lists, Function.update_of_ne (show j ≠ dst by
      intro h; subst j; omega)]
  · simp only [setList_lists, Function.update_of_ne h3.symm]
  · simp only [setList_lists, Function.update_of_ne h7.symm]

theorem frame_of_writes (p : Stmt 100 40)
    (hr : ∀ i ∈ p.regWrites, i.val < 80 ∨ 92 ≤ i.val)
    (hl : ∀ L ∈ p.listWrites, L.val < 32 ∧ L ≠ 3 ∧ L ≠ 7) (st : State 100 40) :
    Frame st (p.run st).1 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i hi hj
    apply run_regs_frame
    intro h
    have := hr i h
    omega
  · intro L hL
    apply run_lists_frame
    intro h
    have := (hl L h).1
    omega
  · apply run_lists_frame
    intro h
    exact (hl 3 h).2.1 rfl
  · apply run_lists_frame
    intro h
    exact (hl 7 h).2.2 rfl

end PCP.Lang.InterpolationBranch
