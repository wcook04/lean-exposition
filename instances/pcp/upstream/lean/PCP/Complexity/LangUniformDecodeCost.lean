import PCP.Complexity.LangUniformDecode

/-!
# Polynomial charged cost of materializing radix coordinates
-/

namespace PCP.Lang.UniformDecode

theorem repeat_cost (n c : ℕ) (st : State 7 3) :
    (iterate (Stmt.push 0 6).run c n st).2 = n * (c + Nat.size (st.regs 6) + 1) := by
  induction n generalizing st with
  | zero => simp [iterate]
  | succ n ih =>
      simp only [iterate, run_push_fst, run_push_snd, ih, setList_regs]
      ring

theorem prepare_cost (st : State 7 3) (he : st.lists 2 = []) :
    (prepare.run st).2 = st.regs 5 * (Nat.size (st.regs 5) + Nat.size (st.regs 6) + 2) +
      Nat.size (st.regs 5) + 5 := by
  simp [prepare, run_seq_snd, run_copy_snd, run_copy_fst, run_loop_snd, repeat_cost,
    he, listSize, Function.update]
  ring

/-- The bound counts both creating the radix list and actual successive divisions. -/
theorem program_cost (st : State 7 3) (he : st.lists 2 = []) :
    (program.run st).2 ≤ (MixedRadixDecode.passConstant + 24) *
      (st.regs 5 * (Nat.size (st.regs 6) + 1) + st.regs 5 + Nat.size (st.regs 0) + 3) ^ 2 := by
  have hp := prepare_run st he
  have hpc := prepare_cost st he
  generalize hs : (prepare.run st).1 = s at *
  have hd := MixedRadixDecode.program_cost
    (s.restrict (Fin.castLE (by decide)) (Fin.castLE (by decide)))
  rw [← decoder_result s] at hd
  simp only [State.restrict_regs, State.restrict_lists,
    show Fin.castLE (by decide : 5 ≤ 7) (0 : Fin 5) = (0 : Fin 7) from rfl,
    show Fin.castLE (by decide : 2 ≤ 3) (0 : Fin 2) = (0 : Fin 3) from rfl,
    show Fin.castLE (by decide : 2 ≤ 3) (1 : Fin 2) = (1 : Fin 3) from rfl,
    hp.1, hp.2.1, hp.2.2.1, listSize, List.map_replicate, List.sum_replicate,
    List.map_nil, List.sum_nil, Nat.add_zero] at hd
  have hdec := hd.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left
    (show st.regs 5 * (Nat.size (st.regs 6) + 1) + Nat.size (st.regs 0) + 2 ≤
      st.regs 5 * (Nat.size (st.regs 6) + 1) + st.regs 5 + Nat.size (st.regs 0) + 3 by omega) 2))
  have hsize := size_le_self (st.regs 5)
  let X := st.regs 5 * (Nat.size (st.regs 6) + 1) + st.regs 5 +
    Nat.size (st.regs 0) + 3
  have hn : st.regs 5 ≤ X := by dsimp [X]; omega
  have hb : st.regs 5 * Nat.size (st.regs 6) ≤ X := by dsimp [X]; nlinarith
  have hmul := Nat.mul_le_mul_left (st.regs 5) hsize
  have hn2 : st.regs 5 * st.regs 5 ≤ X ^ 2 := by
    simpa [pow_two] using Nat.pow_le_pow_left hn 2
  have hX : X ≤ X ^ 2 := Nat.le_pow (by decide)
  have hX1 : 1 ≤ X ^ 2 := Nat.one_le_pow _ _ (by dsimp [X]; omega)
  have hprep : (prepare.run st).2 + 1 ≤ 12 * X ^ 2 := by
    rw [hpc]
    nlinarith only [hsize, hn, hb, hmul, hn2, hX, hX1]
  simp only [program, run_seq_snd, hs]
  change (prepare.run st).2 + (decoder.run s).2 + 1 ≤
    (MixedRadixDecode.passConstant + 24) * X ^ 2
  change (decoder.run s).2 ≤ (MixedRadixDecode.passConstant + 12) * X ^ 2 at hdec
  nlinarith only [hprep, hdec]

end PCP.Lang.UniformDecode
