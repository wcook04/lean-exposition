import PCP.Complexity.ThreeColorRawSeedSemantics

/-!
# Charged cost of the complete structural sampler decoder
-/

set_option maxRecDepth 4096

namespace PCP.Lang.RawSeed

open SeedArithmetic

def programConstant : ℕ := 7 * SeedRadices.emitConstant + 40 +
  256 * (MixedRadixDecode.passConstant + 12) + 10

theorem radices_cost (n m c t B W : ℕ) (st : State 16 4)
    (hc : ∀ i : Fin 4, st.regs (i.castAdd 12) = ![n, m, c, t] i)
    (he : st.lists 0 = []) (hs : ∀ i : Fin 4, Nat.size (![n, m, c, t] i) ≤ W)
    (hb : ∀ i, branchBits n m c t i ≤ B) :
    (radices.run st).2 ≤ (7 * SeedRadices.emitConstant + 40) * (B + W + 1) ^ 2 := by
  have h := SeedRadices.program_cost n m c t B W
    (st.restrict (Fin.castAdd 1) (Fin.castAdd 2)) hc he hs hb
  rw [← radices_result st] at h
  exact h

/-- Bound parameters concern numeric sizes alone; the entire radix construction is charged. -/
theorem program_cost (n m c t code B W : ℕ) (st : State 16 4)
    (hc : Context n m c t code st) (hs : ∀ i : Fin 4, Nat.size (![n, m, c, t] i) ≤ W)
    (hb : ∀ i, branchBits n m c t i ≤ B) (hcode : Nat.size code ≤ W) :
    (program.run st).2 ≤ programConstant * (B + W + 1) ^ 2 := by
  let s := setList st 0 []
  have hr := radices_run n m c t s hc.1 (by simp [s])
  have hrc := radices_cost n m c t B W s hc.1 (by simp [s]) hs hb
  have h15 := (radices_reg s).trans hc.2.1
  have h3 : (radices.run s).1.lists 3 = [] :=
    (radices_empty s).trans (by simpa [s, Function.update] using hc.2.2)
  generalize hu : (radices.run s).1 = u at *
  let v := setList (setReg u 0 code) 1 []
  have hd := MixedRadixDecode.program_cost
    (v.restrict (Fin.castLE (by decide)) (Fin.castLE (by decide)))
  rw [← decoder_result v] at hd
  have hv0 : v.regs 0 = code := by simp [v]
  have hvL0 : v.lists 0 = List.ofFn (fun i => 2 ^ branchBits n m c t i) := by
    simpa [v, Function.update] using hr
  have hvL1 : v.lists 1 = [] := by simp [v]
  change (decoder.run v).2 ≤ (MixedRadixDecode.passConstant + 12) *
    (listSize (v.lists 0) + listSize (v.lists 1) + Nat.size (v.regs 0) + 2) ^ 2 at hd
  rw [hv0, hvL0, hvL1, show listSize [] = 0 from rfl, Nat.add_zero] at hd
  have hls : listSize (List.ofFn (fun i => 2 ^ branchBits n m c t i)) ≤ 7 * (B + 2) := by
    simpa only [List.length_finRange, ← List.ofFn_eq_map] using
      SeedRadices.radices_size (List.finRange 7) n m c t B hb
  have hbound : listSize (List.ofFn (fun i => 2 ^ branchBits n m c t i)) + Nat.size code + 2 ≤
      16 * (B + W + 1) := by omega
  have hdsq := Nat.pow_le_pow_left hbound 2
  have hdc : (decoder.run v).2 ≤
      256 * (MixedRadixDecode.passConstant + 12) * (B + W + 1) ^ 2 := by
    have h := hd.trans (Nat.mul_le_mul_left _ hdsq)
    nlinarith only [h]
  have hsq : B + W + 1 ≤ (B + W + 1) ^ 2 := Nat.le_pow (by decide)
  have hpos : 1 ≤ (B + W + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  simp only [program, run_seq_snd, run_copy_snd, run_copy_fst, hc.2.2,
    show listSize [] = 0 from rfl, Nat.zero_add]
  dsimp only [s] at hu hrc
  rw [hu, run_assign_fst, Expr.eval, h15, setReg_lists, h3]
  change 1 + ((radices.run (setList st 0 [])).2 + ((Expr.var 15).cost u.regs +
    (1 + (decoder.run v).2 + 1) + 1) + 1) + 1 ≤ _
  simp only [Expr.cost, Expr.readSize, Expr.eval, h15]
  unfold programConstant
  nlinarith only [hrc, hdc, hcode, hsq, hpos]

end PCP.Lang.RawSeed
