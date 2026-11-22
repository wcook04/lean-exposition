/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Complexity.HadamardRowAcceptance
import PCP.Complexity.HadamardRowVerdictCost
import PCP.Complexity.HadamardRowHistoryCost

/-!
# Charged cost of the entire Hadamard received-answer checker

The checker traverses only the stored answer trace. Its cost is quadratic in the
row degree, independently of all initial work-register contents.
-/

namespace PCP.Lang.HadamardRow

open PCP.Algebraic BinaryPolynomialSpace Hadamard

variable {t r : ℕ}

theorem readPrefix_cost (b a z u lp l : ℕ) (rest : List ℕ) (st : State 100 32)
    (h : st.lists 25 = b :: a :: z :: u :: lp :: l :: rest)
    (hb : b ≤ 1) (ha : a ≤ 1) (hz : z ≤ 1) (hu : u ≤ 1) (hp : lp ≤ 1) (hl : l ≤ 1) :
    (readPrefix.run st).2 ≤ 20 := by
  have hbs := (size_le_self b).trans hb
  have has := (size_le_self a).trans ha
  have hzs := (size_le_self z).trans hz
  have hus := (size_le_self u).trans hu
  have hps := (size_le_self lp).trans hp
  have hls := (size_le_self l).trans hl
  simp [readPrefix, Stmt.run, Function.update, h]
  omega

theorem pairAnswers_length (ps : List (ℕ × ℕ)) : (pairAnswers ps).length = 2 * ps.length := by
  induction ps with
  | nil => rfl
  | cons p ps ih => simp [pairAnswers] at ih ⊢; omega

theorem pairAnswers_bound (ps : List (ℕ × ℕ))
    (hp : ∀ x ∈ ps, x.1 ≤ 1 ∧ x.2 ≤ 1) : ∀ z ∈ pairAnswers ps, z ≤ 1 := by
  intro z hz
  obtain ⟨x, hx, hz⟩ := List.mem_flatMap.mp hz
  have hh := hp x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with rfl | rfl
  · exact hh.1
  · exact hh.2

theorem checkSetup_cost (b a z u lp l : ℕ) (ps : List (ℕ × ℕ)) (st : State 100 32)
    (h : st.lists 29 = b :: a :: z :: u :: lp :: l :: pairAnswers ps)
    (hb : b ≤ 1) (ha : a ≤ 1) (hz : z ≤ 1) (hu : u ≤ 1) (hlp : lp ≤ 1) (hl : l ≤ 1)
    (hp : ∀ x ∈ ps, x.1 ≤ 1 ∧ x.2 ≤ 1) :
    (checkSetup.run st).2 ≤ 4 * ps.length + 200 := by
  let v := setList st 25 (st.lists 29)
  have hh := readPrefix_run b a z u lp l (pairAnswers ps) v (by simpa [v] using h)
  have hc := readPrefix_cost b a z u lp l (pairAnswers ps) v
    (by simpa [v] using h) hb ha hz hu hlp hl
  dsimp only [v] at hh hc
  simp only [checkSetup, run_seq_snd, run_copy_snd, run_copy_fst]
  generalize hv : (readPrefix.run (setList st 25 (st.lists 29))).1 = v at *
  have hpref := prefixCheck_cost v (hh.1 ▸ hb) (hh.2.1 ▸ ha) (hh.2.2.1 ▸ hz)
    (hh.2.2.2.1 ▸ hu) (hh.2.2.2.2.1 ▸ hlp) (hh.2.2.2.2.2.1 ▸ hl)
  have hsize : listSize (st.lists 29) ≤ 2 * (6 + 2 * ps.length) := by
    have hbnds : ∀ x ∈ st.lists 29, Nat.size x ≤ 1 := by
      rw [h]
      intro x hx
      have hx' : x ≤ 1 := by
        simp only [List.mem_cons] at hx
        rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | hx
        · exact hb
        · exact ha
        · exact hz
        · exact hu
        · exact hlp
        · exact hl
        · exact pairAnswers_bound ps hp x hx
      exact (size_le_self _).trans hx'
    have hs := listSize_bounded (st.lists 29) 1 hbnds
    have hlen : (st.lists 29).length = 6 + 2 * ps.length := by
      rw [h]
      simp only [List.length_cons, pairAnswers_length]
      omega
    rw [hlen] at hs
    omega
  omega

/-- Complete bit-trace checker, allowing arbitrary scratch data. -/
theorem checkAnswers_cost (b a z u lp l : ℕ) (ps : List (ℕ × ℕ)) (st : State 100 32)
    (h : st.lists 29 = b :: a :: z :: u :: lp :: l :: pairAnswers ps)
    (hr : st.regs 56 = r) (hlen : ps.length = r - 1)
    (hb : b ≤ 1) (ha : a ≤ 1) (hz : z ≤ 1) (hu : u ≤ 1) (hlp : lp ≤ 1) (hl : l ≤ 1)
    (hp : ∀ x ∈ ps, x.1 ≤ 1 ∧ x.2 ≤ 1) :
    (checkAnswers.run st).2 ≤ 500 * (r + 1) ^ 2 := by
  have hs := checkSetup_run b a z u lp l ps st h
  have hc := checkSetup_cost b a z u lp l ps st h hb ha hz hu hlp hl hp
  simp only [checkAnswers, run_seq_snd]
  generalize hv : (checkSetup.run st).1 = v at *
  let w := setReg v 58 (v.regs 56 - v.regs 61)
  have hcounter : w.regs 58 = ps.length := by
    simp [w, hs.2.2.2.1, hs.2.2.2.2.2.1, hr, hlen]
  have hbase : w.regs 74 ≤ 1 := by simpa [w, Function.update, hs.2.1] using hb
  have hdelta : w.regs 69 ≤ 1 := by
    simp only [w, setReg_regs, Function.update_of_ne (by decide : (69 : Fin 100) ≠ 58),
      hs.2.2.1]
    omega
  have hacc : w.regs 63 ≤ 1 := by
    simpa [w, Function.update, hs.1] using prefixVerdict_le b a z u lp l
  have hit := factorCheck_iterate_cost ps (Nat.size ps.length + 1) w hs.2.2.2.2.2.2
    (by simpa [w, Function.update] using hs.2.2.2.2.1) hbase hdelta hacc hp
  simp only [run_assign_fst, Expr.eval, run_loop_snd]
  change (checkSetup.run st).2 + ((Expr.sub 56 61).cost v.regs +
    ((iterate factorCheck.run (Nat.size (w.regs 58) + 1) (w.regs 58) w).2 +
      Nat.size (w.regs 58) + 1) + 1) + 1 ≤ _
  rw [hcounter]
  simp only [Expr.cost, Expr.readSize, Expr.eval, hs.2.2.2.1,
    hs.2.2.2.2.2.1, hr, Nat.size_one]
  have hsr := size_le_self r
  have hsp : Nat.size ps.length ≤ r := (size_le_self _).trans (by omega)
  have hsn : Nat.size (r - 1) ≤ r := (size_le_self _).trans (Nat.sub_le _ _)
  have hn : ps.length ≤ r := by omega
  have hmult := Nat.mul_le_mul hn (Nat.add_le_add_right hsp 101)
  nlinarith only [hc, hit, hsr, hsp, hsn, hn, hmult]

theorem checkAnswers_received_cost (hr : 1 ≤ r) (H : Coefficients t r → ZMod 2)
    (s : TestRandomness t r) (st : State 100 32) (hrg : st.regs 56 = r)
    (h : st.lists 29 = (ComputableHadamardTest.queries hr s).map (fun p => (H p).val)) :
    (checkAnswers.run st).2 ≤ 500 * (r + 1) ^ 2 := by
  rw [received_trace hr H s] at h
  have hb (x : ZMod 2) : x.val ≤ 1 := by have hh := x.val_lt; omega
  apply checkAnswers_cost _ _ _ _ _ _ _ st h hrg
    (by simp [receivedPairs]) (hb _) (hb _) (hb _) (hb _) (hb _) (hb _)
  intro x hx
  obtain ⟨y, _, rfl⟩ := List.mem_map.mp hx
  exact ⟨hb _, hb _⟩

end PCP.Lang.HadamardRow
