import PCP.Complexity.GridRecoveryPoints

/-! # Charged cost of both actual certificate-point lists -/

namespace PCP.Lang.GridRecovery

open PCP.Algebraic BinaryFieldCode

variable {t : ℕ} [NeZero t]

theorem iterate_push_cost {R Q : ℕ} (r : Fin R) (L : Fin Q) (c n : ℕ) (st : State R Q) :
    (iterate (Stmt.push L r).run c n st).2 = n * (c + Nat.size (st.regs r) + 1) := by
  induction n generalizing st with
  | zero => simp [iterate]
  | succ n ih =>
      change c + ((Stmt.push L r).run st).2 +
        (iterate (Stmt.push L r).run c n ((Stmt.push L r).run st).1).2 = _
      rw [ih]
      simp only [run_push_snd, run_push_fst, setList_regs]
      ring

theorem assemble_cost (st : State 41 17) (he : st.lists 7 = []) :
    (assemble.run st).2 ≤ 8 * (listSize (st.lists 12) + (st.lists 12).length + 2) ^ 2 := by
  have hs := size_le_self (st.lists 12).length
  have ha (s : State 41 17) : ((Stmt.assign 40 (.const 0)).run s).2 = 1 := rfl
  have heq : (assemble.run st).2 = 5 * listSize (st.lists 12) +
      (st.lists 12).length * (Nat.size (st.lists 12).length + 2) +
      2 * Nat.size (st.lists 12).length + 15 := by
    simp [assemble, run_seq_snd, run_copy_snd, run_copy_fst,
      run_assign_fst, ha, Expr.eval,
      run_len_fst, run_len_snd, run_loop_snd, run_loop_fst, iterate_push,
      iterate_push_cost, run_rev_fst, run_rev_snd, run_revApp_fst, run_revApp_snd,
      Function.update, he, listSize]
    ring
  rw [heq]
  have hn := Nat.mul_le_mul_left (st.lists 12).length hs
  nlinarith

theorem points_cost (h : ℕ) (hh : h ≤ 2 ^ t)
    (xs : List (BinaryMaterializedField.Element t)) (st : State 41 17)
    (hc : Context t h st) (hx : st.lists 12 = codes xs) :
    (points.run st).2 ≤ 100001000 * (h + t + xs.length + 1) ^ 6 := by
  have hp := program_cost h hh xs st hc hx
  have hr := program_run h hh xs st hc hx
  have ha := assemble_cost (program.run st).1 hr.2.1.2.2.2
  rw [hr.2.2, hx] at ha
  simp only [codes, List.length_map] at ha
  have hs := codes_size xs
  let N := h + t + xs.length + 1
  have hN : 1 ≤ N := by dsimp [N]; omega
  have hn : xs.length ≤ N := by dsimp [N]; omega
  have ht : t + 1 ≤ N := by dsimp [N]; omega
  have hsize : listSize (codes xs) ≤ N ^ 2 := by
    exact hs.trans ((Nat.mul_le_mul hn ht).trans_eq (pow_two N).symm)
  have hlin : N ≤ N ^ 2 := Nat.le_self_pow (by decide) _
  have hbase : listSize (codes xs) + xs.length + 2 ≤ 4 * N ^ 2 := by
    nlinarith
  change _ ≤ 8 * (listSize (codes xs) + xs.length + 2) ^ 2 at ha
  have hasq := Nat.pow_le_pow_left hbase 2
  have h46 : N ^ 4 ≤ N ^ 6 := Nat.pow_le_pow_right hN (by decide)
  have ha' : (assemble.run (program.run st).1).2 ≤ 128 * N ^ 6 := by
    have hh := ha.trans (Nat.mul_le_mul_left 8 hasq)
    nlinarith only [hh, h46]
  have hpos : 1 ≤ N ^ 6 := Nat.one_le_pow _ _ hN
  simp only [points, run_seq_snd]
  change _ ≤ 100001000 * N ^ 6
  change (program.run st).2 ≤ 100000000 * N ^ 6 at hp
  nlinarith only [hp, ha', hpos]

end PCP.Lang.GridRecovery
