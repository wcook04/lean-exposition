/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Complexity.HadamardRowBranch
import PCP.Complexity.HadamardRowAcceptanceCost

/-!
# Polynomial charged cost of the complete physical Hadamard branch

The bound counts all label arithmetic, physical address construction, shared-history
scans, and the final verdict. `W` bounds the stored public payload and history sizes
and the physical address bit length; no work-register bound is assumed.
-/

set_option maxRecDepth 4096

namespace PCP.Lang.HadamardRow

open PCP.Algebraic BinaryPolynomialSpace Hadamard HadamardLabel

variable {t r : ℕ}

def branchConstant : ℕ := queryConstant + addressConstant + answerBodyConstant + 600

theorem labels_cost (hr : 1 ≤ r) (s : TestRandomness t r) (st : State 100 32)
    (hc : Sources s st) :
    (labels.run st).2 ≤ queryConstant * factorSize t r ^ 9 := by
  rw [labels, Stmt.run_rename_cost queries rowRegs id
    (show Function.Injective rowRegs from Fin.castLE_injective _) Function.injective_id]
  exact queries_cost hr s (st.restrict rowRegs id) hc

theorem branch_cost (hr : 1 ≤ r) (s : TestRandomness t r) (p : Fin 10 → ℕ)
    (hs : List ℕ) (bs : List Bool) (W : ℕ) (st : State 100 32)
    (hc : Sources s st) (hp : Payload p st)
    (hq : st.lists 30 = hs) (hb : st.lists 31 = bs.map Bool.toNat)
    (hpayload : ∀ i, Nat.size (p i) ≤ W) (hstack : listSize (st.lists 27) ≤ W)
    (hhq : listSize hs ≤ W) (hhb : listSize (bs.map Bool.toNat) ≤ W)
    (haddr : ∀ z ∈ ComputableHadamardTest.queries hr s, Nat.size (address p (code z)) ≤ W) :
    (branch.run st).2 ≤ branchConstant * (2 ^ t + 3 * r + W + 5) ^ 9 := by
  let zs := (ComputableHadamardTest.queries hr s).map code
  have hzlen : zs.length = 2 * r + 4 := by
    simp only [zs, List.length_map, ComputableHadamardTest.queries_eq, testQueries_length]
  have hcodes : ∀ z ∈ zs, Nat.size z ≤ 2 ^ t + W := by
    intro z hz
    obtain ⟨y, _, rfl⟩ := List.mem_map.mp hz
    exact (code_size y).trans (Nat.le_add_right _ _)
  have haddresses : ∀ z ∈ zs, Nat.size (address p z) ≤ W := by
    intro z hz
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hz
    exact haddr y hy
  have hl := labels_run hr s st hc
  have hlc := labels_cost hr s st hc
  have hlp := labels_payload p st hp
  have hlf := labels_frame st
  simp only [branch, run_seq_snd]
  generalize hu : (labels.run st).1 = u at *
  have he : u.lists 7 = [] := hl.1.2.2.1
  have hphys := physicalQueries_run p zs u hlp hl.2 he
  have hpc := physicalQueries_cost p zs (2 ^ t + W) u hlp hl.2 he
    (fun i => (hpayload i).trans (Nat.le_add_left _ _)) hcodes
    ((hlf.1 ▸ hstack).trans (Nat.le_add_left _ _))
    (fun z hz => (haddresses z hz).trans (Nat.le_add_left _ _))
  have hpf := physicalQueries_frame u
  have hpr := run_regs_frame physicalQueries 56 (by decide) u
  have hpe := run_lists_frame physicalQueries 7 (by decide) u
  generalize hv : (physicalQueries.run u).1 = v at *
  have hvq : v.lists 30 = hs := hpf.2.1.trans (hlf.2.1.trans hq)
  have hvb : v.lists 31 = bs.map Bool.toNat := hpf.2.2.trans (hlf.2.2.trans hb)
  have hans := collectAnswers_bool (zs.map (address p)) hs bs v hphys.2
    (hpe.trans he) hvq hvb
  have hcc := collectAnswers_cost (zs.map (address p)) W v hphys.2 (hpe.trans he)
    (by
      intro z hz
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hz
      exact haddresses y hy) (hvq ▸ hhq) (hvb ▸ hhb)
  have hcr := run_regs_frame collectAnswers 56 (by decide) v
  generalize hw : (collectAnswers.run v).1 = w at *
  have htrace : w.lists 29 = (ComputableHadamardTest.queries hr s).map
      (fun z => (receivedOracle p hs bs z).val) := by
    simpa only [zs, List.map_map, Function.comp_def, receivedOracle_val] using hans
  have hdegree : w.regs 56 = r := hcr.trans (hpr.trans hl.1.2.1)
  have hcheck := checkAnswers_received_cost hr (receivedOracle p hs bs) s w hdegree htrace
  have hnumeric : factorSize t r ^ 9 ≤ (2 ^ t + 3 * r + W + 5) ^ 9 :=
    Nat.pow_le_pow_left (by unfold factorSize; omega) _
  have hphysical : (zs.length + (2 ^ t + W) + 1) ^ 2 ≤
      (2 ^ t + 3 * r + W + 5) ^ 9 :=
    (Nat.pow_le_pow_left (by rw [hzlen]; omega) 2).trans
      (Nat.pow_le_pow_right (Nat.succ_le_succ (Nat.zero_le _)) (by decide))
  have hhistory : ((zs.map (address p)).length + W + 1) ^ 3 ≤
      (2 ^ t + 3 * r + W + 5) ^ 9 := by
    have hbase : (zs.map (address p)).length + W + 1 ≤ 2 ^ t + 3 * r + W + 5 := by
      rw [List.length_map, hzlen]
      exact (by omega : 2 * r + 4 + W + 1 ≤ 3 * r + W + 5).trans
        (Nat.add_le_add_right (Nat.add_le_add_right (Nat.le_add_left _ _) W) 5)
    exact (Nat.pow_le_pow_left hbase 3).trans
      (Nat.pow_le_pow_right (Nat.succ_le_succ (Nat.zero_le _)) (by decide))
  have hsmall : (r + 1) ^ 2 ≤ (2 ^ t + 3 * r + W + 5) ^ 9 := by
    have hbase : r + 1 ≤ 2 ^ t + 3 * r + W + 5 :=
      (by omega : r + 1 ≤ 3 * r + W + 5).trans
        (Nat.add_le_add_right (Nat.add_le_add_right (Nat.le_add_left _ _) W) 5)
    exact (Nat.pow_le_pow_left hbase 2).trans
      (Nat.pow_le_pow_right (Nat.succ_le_succ (Nat.zero_le _)) (by decide))
  have h1 := hlc.trans (Nat.mul_le_mul_left _ hnumeric)
  have h2 := hpc.trans (Nat.mul_le_mul_left _ hphysical)
  have h3 := hcc.trans (Nat.mul_le_mul_left _ hhistory)
  have h4 := hcheck.trans (Nat.mul_le_mul_left _ hsmall)
  have hpos : 1 ≤ (2 ^ t + 3 * r + W + 5) ^ 9 := Nat.one_le_pow _ _ (Nat.succ_pos _)
  have sumBound : ∀ A B C P x y z v : ℕ,
      x ≤ A * P → y ≤ (B + 20) * P → z ≤ (C + 20) * P → v ≤ 500 * P → 1 ≤ P →
      x + (y + (z + v + 1) + 1) + 1 ≤ (A + B + C + 600) * P := by
    intro A B C P x y z v hx hy hz hv hP
    nlinarith only [hx, hy, hz, hv, hP]
  exact sumBound queryConstant addressConstant answerBodyConstant _ _ _ _ _
    h1 h2 h3 h4 hpos

end PCP.Lang.HadamardRow
