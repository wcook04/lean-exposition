import PCP.Complexity.DerivedPrimaryLabels
import PCP.Complexity.HadamardRowPhysical
import PCP.Complexity.LangHistoryParityOracle

/-!
# Both actual derived-primary proof reads

A computed cubic label is corrected using the sampled fresh mask. Numeric label
serialization, physical table-address construction and shared-history parity are
all executed, and both query occurrences are retained in their original order.
-/

namespace PCP.Lang.DerivedPrimary

open PCP.Algebraic BinaryPolynomialSpace BinaryFieldCode

variable {t : ℕ} [NeZero t]

def parityLists : Fin 6 → Fin 32 := ![30, 31, 28, 29, 26, 27]

def parity : Stmt 100 32 :=
  HistoryParity.parity.rename (Fin.castLE (by decide)) parityLists

theorem parity_result (st : State 100 32) :
    ((parity.run st).1.restrict (Fin.castLE (by decide)) parityLists, (parity.run st).2) =
      HistoryParity.parity.run (st.restrict (Fin.castLE (by decide)) parityLists) :=
  HistoryParity.parity.run_rename _ _ (Fin.castLE_injective _) (by decide) st

theorem parity_run (qs xs : List ℕ) (bs : List Bool) (st : State 100 32)
    (hq : st.lists 30 = qs) (hb : st.lists 31 = bs.map Bool.toNat)
    (hx : st.lists 26 = xs) :
    (parity.run st).1.regs 8 = ((xs.map (fun a => BinarySeedPadding.boolEquiv
      (QueryTree.answersOracle qs bs a))).sum).val ∧
    (parity.run st).1.lists 26 = xs := by
  have h := HistoryParity.parity_oracle qs xs bs
    (st.restrict (Fin.castLE (by decide)) parityLists) hq hb hx
  have hf := (HistoryParity.parity_run
    (st.restrict (Fin.castLE (by decide)) parityLists)).2.2.2
  rw [← parity_result] at h hf
  refine ⟨?_, ?_⟩
  · simpa only [State.restrict_regs,
      show Fin.castLE (by decide : 12 ≤ 100) (8 : Fin 12) = (8 : Fin 100) from rfl] using h
  · exact hf.trans hx

def finish : Stmt 100 32 := .seq (.copy 23 7) (.seq HadamardRow.physicalQueries parity)

theorem finish_run (payload : Fin 10 → ℕ) (zs qs : List ℕ) (bs : List Bool)
    (st : State 100 32) (hp : HadamardRow.Payload payload st)
    (hz : st.lists 24 = zs) (he : st.lists 23 = [])
    (hq : st.lists 30 = qs) (hb : st.lists 31 = bs.map Bool.toNat) :
    (finish.run st).1.lists 26 = zs.map (HadamardRow.address payload) ∧
    (finish.run st).1.regs 8 = (((zs.map (HadamardRow.address payload)).map
      (fun a => BinarySeedPadding.boolEquiv (QueryTree.answersOracle qs bs a))).sum).val := by
  let s := setList st 7 []
  have hph := HadamardRow.physicalQueries_run payload zs s hp
    (by simpa [s, Function.update] using hz) (by simp [s])
  have hframe := HadamardRow.physicalQueries_frame s
  have hq' : (HadamardRow.physicalQueries.run s).1.lists 30 = qs :=
    hframe.2.1.trans (by simpa [s, Function.update] using hq)
  have hb' : (HadamardRow.physicalQueries.run s).1.lists 31 = bs.map Bool.toNat :=
    hframe.2.2.trans (by simpa [s, Function.update] using hb)
  have hh := parity_run qs _ bs (HadamardRow.physicalQueries.run s).1 hq' hb' hph.2
  simpa only [finish, run_seq_fst, run_copy_fst, he] using And.intro hh.2 hh.1

def program (weighted : Bool) : Stmt 100 32 := .seq (labels weighted) finish

attribute [local irreducible] labels finish

theorem program_run (weighted : Bool) (w : BinaryMaterializedField.Element t)
    (v : Fin t → ZMod 2) (mask : Coefficients t 3) (payload : Fin 10 → ℕ)
    (qs : List ℕ) (bs : List Bool) (st : State 100 32)
    (hc : Context w v mask st) (hp : HadamardRow.Payload payload st)
    (hq : st.lists 30 = qs) (hb : st.lists 31 = bs.map Bool.toNat) :
    let label := BinaryCubicQueryLang.translated weighted w
      (BooleanCoefficientArithmetic.homogeneousIndex (le_refl 1) v)
    let addresses := [HadamardRow.address payload (HadamardLabel.code (label + mask)),
      HadamardRow.address payload (HadamardLabel.code mask)]
    ((program weighted).run st).1.lists 26 = addresses ∧
    ((program weighted).run st).1.regs 8 = ((addresses.map (fun a =>
      BinarySeedPadding.boolEquiv (QueryTree.answersOracle qs bs a))).sum).val := by
  have hl := labels_run weighted w v mask st hc
  have hp' : HadamardRow.Payload payload ((labels weighted).run st).1 := by
    intro i
    have hi : 80 ≤ (HadamardRow.payloadReg i).val := by
      simp [HadamardRow.payloadReg]
    have h96 : HadamardRow.payloadReg i ≠ 96 := by
      intro h; have := congrArg Fin.val h; simp [HadamardRow.payloadReg] at this; omega
    have h97 : HadamardRow.payloadReg i ≠ 97 := by
      intro h; have := congrArg Fin.val h; simp [HadamardRow.payloadReg] at this; omega
    exact (labels_reg weighted st _ hi h96 h97).trans (hp i)
  have he' := (labels_list weighted st 23 (by decide) (by decide)).trans hc.empty
  have hq' := (labels_list weighted st 30 (by decide) (by decide)).trans hq
  have hb' := (labels_list weighted st 31 (by decide) (by decide)).trans hb
  have hf := finish_run payload _ qs bs ((labels weighted).run st).1 hp' hl he' hq' hb'
  simpa only [program, run_seq_fst, List.map_cons, List.map_nil] using hf

/-- The two physical reads compute the named self-correction with the original fresh mask. -/
theorem program_location {n m : ℕ} (weighted : Bool)
    (w : BinaryMaterializedField.Element t) (v : Fin t → ZMod 2)
    (mask : Coefficients t 3)
    (loc : HadamardRow.Location (BinaryMaterializedField.Element t) n m 4 3)
    (qs : List ℕ) (bs : List Bool) (st : State 100 32)
    (hc : Context w v mask st)
    (hp : HadamardRow.Payload (loc.payload (t := t) (fieldEquiv t)) st)
    (hq : st.lists 30 = qs) (hb : st.lists 31 = bs.map Bool.toNat) :
    let label := BinaryCubicQueryLang.translated weighted w
      (BooleanCoefficientArithmetic.homogeneousIndex (le_refl 1) v)
    let index := fun p : Coefficients t 3 =>
      (ThreeColorQueryIndex.equiv (fieldEquiv t) (BooleanCoefficientIndex.coefficientEquiv t 1)
        (BooleanCoefficientIndex.coefficientEquiv t 3) (loc.query p)).val
    ((program weighted).run st).1.lists 26 = [index (label + mask), index mask] ∧
    ((program weighted).run st).1.regs 8 =
      (Hadamard.selfCorrect (fun p => BinarySeedPadding.boolEquiv
        (QueryTree.answersOracle qs bs (index p))) label mask).val := by
  have h := program_run weighted w v mask (loc.payload (t := t) (fieldEquiv t))
    qs bs st hc hp hq hb
  dsimp only at h ⊢
  simpa only [HadamardRow.Location.address_eq, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, add_zero, Hadamard.selfCorrect,
    sub_eq_add_neg, ZMod.neg_eq_self_mod_two] using h

end PCP.Lang.DerivedPrimary
