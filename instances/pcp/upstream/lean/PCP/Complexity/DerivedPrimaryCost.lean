import PCP.Complexity.DerivedPrimaryLang
import PCP.Complexity.DerivedPrimaryLabelCost
import PCP.Complexity.HadamardRowPhysicalCost

/-! # Polynomial cost of both materialized derived-primary proof reads -/

namespace PCP.Lang.DerivedPrimary

open PCP.Algebraic BinaryPolynomialSpace BinaryFieldCode

variable {t : ℕ} [NeZero t]

def finishConstant : ℕ := HadamardRow.addressConstant + 30 +
  216*(QueryHistory.passConstant+60)

omit [NeZero t] in
theorem finish_cost (payload : Fin 10 → ℕ) (zs : List ℕ) (W : ℕ)
    (st : State 100 32) (hp : HadamardRow.Payload payload st)
    (hz : st.lists 24 = zs) (hlen : zs.length = 2) (he : st.lists 23 = [])
    (hps : ∀ i, Nat.size (payload i) ≤ W)
    (hzs : ∀ z ∈ zs, Nat.size z ≤ 2 ^ t)
    (hs : listSize (st.lists 27) ≤ W)
    (ha : ∀ z ∈ zs, Nat.size (HadamardRow.address payload z) ≤ W) :
    (finish.run st).2 ≤ finishConstant *
      (2^t+W+listSize (st.lists 30)+listSize (st.lists 31)+10)^3 := by
  have htq : t < 2^t := Nat.lt_two_pow_self
  let s := setList st 7 []
  have hphys := HadamardRow.physicalQueries_cost payload zs (2^t+W) s hp
    (by simpa [s, Function.update] using hz) (by simp [s])
    (fun i => (hps i).trans (by omega))
    (fun z hz => (hzs z hz).trans (by omega))
    (by simpa [s, Function.update] using hs.trans (by omega : W ≤ 2^t+W))
    (fun z hz => (ha z hz).trans (by omega))
  have htrace := HadamardRow.physicalQueries_run payload zs s hp
    (by simpa [s, Function.update] using hz) (by simp [s])
  have hf := HadamardRow.physicalQueries_frame s
  generalize hu : (HadamardRow.physicalQueries.run s).1 = u at *
  have hq : u.lists 30 = st.lists 30 := hf.2.1
  have hb : u.lists 31 = st.lists 31 := hf.2.2
  have hsize : listSize (u.lists 26) ≤ 2*(W+1) := by
    rw [htrace.2]
    have h := HadamardRow.listSize_bounded (zs.map (HadamardRow.address payload)) W (by
      intro z hz
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hz
      exact ha y hy)
    simpa only [List.length_map, hlen] using h
  have hc := HistoryParity.parity_cost (u.restrict (Fin.castLE (by decide)) parityLists)
  rw [← parity_result] at hc
  change (parity.run u).2 ≤ (QueryHistory.passConstant+60)*
    (3*(listSize (u.lists 30)+listSize (u.lists 31)+listSize (u.lists 26)+1)+2)^3 at hc
  rw [hq, hb] at hc
  let N := 2^t+W+listSize (st.lists 30)+listSize (st.lists 31)+10
  have hparbase : 3*(listSize (st.lists 30)+listSize (st.lists 31)+
      listSize (u.lists 26)+1)+2 ≤ 6*N := by dsimp [N]; omega
  have hpar := hc.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hparbase 3))
  have hpar' : (parity.run u).2 ≤ 216*(QueryHistory.passConstant+60)*N^3 := by
    nlinarith only [hpar]
  have hphysbase : zs.length+(2^t+W)+1 ≤ N := by dsimp [N]; omega
  have hpow : (zs.length+(2^t+W)+1)^2 ≤ N^3 :=
    (Nat.pow_le_pow_left hphysbase 2).trans (Nat.pow_le_pow_right (by dsimp [N]; omega) (by decide))
  have hphys' := hphys.trans (Nat.mul_le_mul_left _ hpow)
  have hpos : 1 ≤ N^3 := Nat.one_le_pow _ _ (by dsimp [N]; omega)
  simp only [finish, run_seq_snd, run_copy_snd, run_copy_fst, he,
    show listSize [] = 0 from rfl]
  change 1 + ((HadamardRow.physicalQueries.run s).2 +
    (parity.run (HadamardRow.physicalQueries.run s).1).2+1)+1 ≤ finishConstant*N^3
  rw [hu]
  unfold finishConstant
  nlinarith only [hphys', hpar', hpos]

def programConstant : ℕ := labelsConstant + finishConstant + 1

attribute [local irreducible] labels finish

theorem program_cost (weighted : Bool) (w : BinaryMaterializedField.Element t)
    (v : Fin t → ZMod 2) (mask : Coefficients t 3) (payload : Fin 10 → ℕ)
    (W : ℕ) (st : State 100 32) (hc : Context w v mask st)
    (hp : HadamardRow.Payload payload st) (hps : ∀ i, Nat.size (payload i) ≤ W)
    (hs : listSize (st.lists 27) ≤ W)
    (ha : ∀ p ∈ [BinaryCubicQueryLang.translated weighted w
        (BooleanCoefficientArithmetic.homogeneousIndex (le_refl 1) v) + mask, mask],
      Nat.size (HadamardRow.address payload (HadamardLabel.code p)) ≤ W) :
    ((program weighted).run st).2 ≤ programConstant *
      (2^t+W+listSize (st.lists 30)+listSize (st.lists 31)+10)^8 := by
  have htq : t < 2^t := Nat.lt_two_pow_self
  have cl := labels_cost weighted w v mask st hc
  have hl := labels_run weighted w v mask st hc
  have hp' : HadamardRow.Payload payload ((labels weighted).run st).1 := by
    intro i
    have hi : 80 ≤ (HadamardRow.payloadReg i).val := by simp [HadamardRow.payloadReg]
    have h96 : HadamardRow.payloadReg i ≠ 96 := by
      intro h; have := congrArg Fin.val h; simp [HadamardRow.payloadReg] at this; omega
    have h97 : HadamardRow.payloadReg i ≠ 97 := by
      intro h; have := congrArg Fin.val h; simp [HadamardRow.payloadReg] at this; omega
    exact (labels_reg weighted st _ hi h96 h97).trans (hp i)
  have he := (labels_list weighted st 23 (by decide) (by decide)).trans hc.empty
  have hstack := (labels_list weighted st 27 (by decide) (by decide)) ▸ hs
  have cf := finish_cost (t := t) payload _ W ((labels weighted).run st).1 hp' hl rfl he hps
    (by intro z hz; simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
        rcases hz with rfl | rfl <;> exact HadamardLabel.code_size _) hstack
    (by intro z hz; simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
        rcases hz with rfl | rfl
        · exact ha _ (by simp)
        · exact ha _ (by simp))
  rw [labels_list weighted st 30 (by decide) (by decide),
    labels_list weighted st 31 (by decide) (by decide)] at cf
  let N := 2^t+W+listSize (st.lists 30)+listSize (st.lists 31)+10
  have hcl := cl.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left
    (by dsimp [N]; omega : 2^t+7 ≤ N) 8))
  have hcf := cf.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right
    (by dsimp [N]; omega : 1 ≤ N) (by decide : 3 ≤ 8)))
  have hpos : 1 ≤ N^8 := Nat.one_le_pow _ _ (by dsimp [N]; omega)
  rw [program, run_seq_snd]
  change _ ≤ programConstant*N^8
  unfold programConstant
  nlinarith only [hcl, hcf, hpos]

end PCP.Lang.DerivedPrimary
