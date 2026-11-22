/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Complexity.InnerBranchLang

/-! # Cost of the inner Hadamard arm with physical shared-history reads -/

namespace PCP.Lang.InnerBranch

open PCP.Algebraic BinaryPolynomialSpace InterpolationBranch

variable {t n m : ℕ} [NeZero t]

attribute [local irreducible] hadCall

def budget (t m W : ℕ) (st : State 120 40) : ℕ :=
  t + 4 * m + 2 ^ t + W + listSize (st.lists 36) + listSize (st.lists 37) + 10

theorem bool_size (b : Bool) : Nat.size b.toNat ≤ 1 := by cases b <;> decide

theorem prepareHad_cost (st : State 120 40) (he : st.lists 7 = []) :
    (prepareHad.run st).2 = listSize (st.lists 36) + listSize (st.lists 37) + 5 := by
  simp [prepareHad, Stmt.run, Function.update, he, listSize]
  omega

omit [NeZero t] in
theorem hadCodes_size (site : StandardCorrection.Site (Field t) n) (x : Point t m)
    (s : Hadamard.TestRandomness t 1) (W : ℕ)
    (hb : ∀ p ∈ ComputableHadamardTest.queries (le_refl 1) s,
      Nat.size (address site x p) ≤ W) :
    listSize ((ComputableHadamardTest.queries (le_refl 1) s).map (address site x)) ≤
      6 * (W + 1) := by
  have h := HadamardRow.listSize_bounded
    ((ComputableHadamardTest.queries (le_refl 1) s).map (address site x)) W (by
      intro z hz
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hz
      exact hb p hp)
  simpa only [List.length_map, ComputableHadamardTest.queries_eq,
    Hadamard.testQueries_length] using h

omit [NeZero t] in
theorem hadCall_cost (site : StandardCorrection.Site (Field t) n) (x : Point t m)
    (s : Hadamard.TestRandomness t 1) (qs : List ℕ) (bs : List Bool)
    (W : ℕ) (st : State 120 40)
    (hc : HadamardRow.Sources s (st.restrict hadRegs hadLists))
    (hp : HadamardRow.Payload ((location site x).payload (t := t) (BinaryFieldCode.fieldEquiv t))
      (st.restrict hadRegs hadLists))
    (hq : st.lists 30 = qs) (hb : st.lists 31 = bs.map Bool.toNat)
    (hpayload : ∀ i, Nat.size ((location site x).payload (t := t)
      (BinaryFieldCode.fieldEquiv t) i) ≤ W)
    (hstack : listSize (st.lists 27) ≤ W)
    (hhq : listSize qs ≤ W) (hhb : listSize (bs.map Bool.toNat) ≤ W)
    (haddr : ∀ p ∈ ComputableHadamardTest.queries (le_refl 1) s,
      Nat.size (address site x p) ≤ W) :
    (hadCall.run st).2 ≤ HadamardRow.branchConstant * (2 ^ t + 3 + W + 5) ^ 9 := by
  have h := HadamardRow.branch_cost (le_refl 1) s _ qs bs W
    (st.restrict hadRegs hadLists) hc hp hq hb hpayload hstack hhq hhb (by
      intro p hp
      rw [HadamardRow.Location.address_eq, location_query]
      exact haddr p hp)
  rw [← hadCall_result] at h
  exact h

omit [NeZero t] in
theorem hadamard_cost (site : StandardCorrection.Site (Field t) n) (x : Point t m)
    (s : Hadamard.TestRandomness t 1) (qs : List ℕ) (bs : List Bool)
    (W : ℕ) (st : State 120 40)
    (hc : HadamardRow.Sources s (st.restrict hadRegs hadLists))
    (hp : HadamardRow.Payload ((location site x).payload (t := t) (BinaryFieldCode.fieldEquiv t))
      (st.restrict hadRegs hadLists))
    (hq : st.lists 36 = qs) (hb : st.lists 37 = bs.map Bool.toNat)
    (hpayload : ∀ i, Nat.size ((location site x).payload (t := t)
      (BinaryFieldCode.fieldEquiv t) i) ≤ W)
    (haddr : ∀ p ∈ ComputableHadamardTest.queries (le_refl 1) s,
      Nat.size (address site x p) ≤ W) :
    (hadamard.run st).2 ≤ (HadamardRow.branchConstant + 30) * budget t m W st ^ 9 := by
  let B := budget t m W st
  let W' := W + listSize qs + listSize (bs.map Bool.toNat)
  have he : st.lists 7 = [] := hc.2.2.1
  have hprep := prepareHad_cost st he
  have hs := prepareHad_sources s st hc
  have hp' := prepareHad_payload _ st hp
  have hh := prepareHad_histories st
  have hsem := hadCall_run site x s qs bs (prepareHad.run st).1 hs hp'
    (hh.1.trans hq) (hh.2.1.trans hb)
  have hcost := hadCall_cost site x s qs bs W' (prepareHad.run st).1 hs hp'
    (hh.1.trans hq) (hh.2.1.trans hb)
    (fun i => (hpayload i).trans (by dsimp [W']; omega))
    (by rw [hh.2.2, he]; exact Nat.zero_le _)
    (by dsimp [W']; omega) (by dsimp [W']; omega)
    (fun p hp => (haddr p hp).trans (by dsimp [W']; omega))
  have hsize := hadCodes_size site x s W haddr
  have hflag := bool_size (ComputableHadamardTest.test (le_refl 1) (oracle site qs bs x) s)
  have hB : 1 ≤ B := Nat.succ_le_succ (Nat.zero_le _)
  have hbase : 2 ^ t + 3 + W' + 5 ≤ B := by
    dsimp [B, budget, W']
    rw [hq, hb]
    omega
  have hcost' := hcost.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hbase 9))
  have hlow : B ≤ B ^ 9 := Nat.le_pow (by decide)
  simp only [hadamard, run_seq_snd]
  generalize hu : (prepareHad.run st).1 = u at *
  generalize hv : (hadCall.run u).1 = v at *
  simp only [run_copy_snd, run_copy_fst]
  change _ + ((hadCall.run u).2 +
    (listSize (v.lists 26) + 1 + (Nat.size (v.regs 63) + Nat.size (v.regs 63) + 1) + 1) + 1) + 1 ≤ _
  rw [hsem.1, hsem.2]
  have hhist : listSize (st.lists 36) + listSize (st.lists 37) + W + 10 ≤ B := by
    have arith : ∀ t m q W h b : ℕ,
        h + b + W + 10 ≤ t + 4 * m + q + W + h + b + 10 := by
      intros
      omega
    exact arith _ _ _ _ _ _
  have sumBound : ∀ C P x y h q w f : ℕ, x = h + 5 → y ≤ C * P →
      q ≤ 6 * (w + 1) → f ≤ 1 → h + w + 10 ≤ P →
      x + (y + (q + 1 + (f + f + 1) + 1) + 1) + 1 ≤ (C + 30) * P := by
    intros
    nlinarith
  exact sumBound _ _ _ _ _ _ _ _ hprep hcost' hsize hflag (hhist.trans hlow)

end PCP.Lang.InnerBranch
