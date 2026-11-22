import PCP.Complexity.ThreeColorSeedBitsLang

/-!
# Charged bound for complete bit-list seed decoding
-/

set_option maxRecDepth 4096

namespace PCP.Lang.SeedBits

open SeedArithmetic

theorem word_cost (bits : List Bool) (st : State 21 4)
    (hb : st.lists 2 = bits.map Bool.toNat) :
    (word.run st).2 ≤ (WordCodec.passConstant * 3 + 20) * (bits.length + 1) ^ 2 := by
  have h := WordCodec.decode_cost (st.restrict (Fin.natAdd 16) (fun _ => 2)) (by
    change BinaryField.Bits (st.lists 2)
    rw [hb]
    intro x hx
    obtain ⟨b, _, rfl⟩ := List.mem_map.mp hx
    cases b <;> decide)
  rw [← word_result st] at h
  change (word.run st).2 ≤ (WordCodec.passConstant * 3 + 20) * ((st.lists 2).length + 1) ^ 2 at h
  simpa only [hb, List.length_map] using h

def programConstant : ℕ := RawSeed.programConstant + WordCodec.passConstant * 3 + 25

/-- Every stage is included: word reading, bitcount arithmetic, powers and divisions. -/
theorem program_cost (n m c t B W : ℕ) (bits : List Bool) (st : State 21 4)
    (hc : Context n m c t bits st) (hs : ∀ i : Fin 4, Nat.size (![n, m, c, t] i) ≤ W)
    (hb : ∀ i, branchBits n m c t i ≤ B) (hlen : bits.length ≤ W) :
    (program.run st).2 ≤ programConstant * (B + W + 1) ^ 2 := by
  let s := setReg (word.run st).1 15 ((word.run st).1.regs 17)
  have hcode : Nat.size (Machine.bitsValue bits) ≤ W :=
    (Nat.size_le.mpr (Machine.bitsValue_lt bits)).trans hlen
  have hraw := RawSeed.program_cost n m c t (Machine.bitsValue bits) B W
    (s.restrict (Fin.castAdd 5) id) (raw_context n m c t bits st hc) hs hb hcode
  rw [← raw_result s] at hraw
  have hw := word_cost bits st hc.2.1
  have hw' := hw.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left
    (show bits.length + 1 ≤ B + W + 1 by omega) 2))
  have hvalue := word_run bits st hc.2.1
  have hsq : B + W + 1 ≤ (B + W + 1) ^ 2 := Nat.le_pow (by decide)
  have hpos : 1 ≤ (B + W + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  simp only [program, run_seq_snd, run_assign_fst, Expr.eval]
  change (word.run st).2 + ((Expr.var 17).cost (word.run st).1.regs + (raw.run s).2 + 1) + 1 ≤ _
  simp only [Expr.cost, Expr.readSize, Expr.eval, hvalue]
  unfold programConstant
  nlinarith only [hraw, hw', hcode, hsq, hpos]

end PCP.Lang.SeedBits
