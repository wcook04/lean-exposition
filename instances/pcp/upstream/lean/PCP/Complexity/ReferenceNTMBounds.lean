import PCP.Complexity.ReferenceNTMSimulation

/-!
# Linear bit-storage bound for bounded reference traces

After the supplied number of choices, every head and base-four tape numeral has
bit size linear in the input length plus that number of choices. This bounds the
actual arithmetic representation, including its cached head place values.
-/

namespace PCP.ReferenceNTM.Cfg

open Complexity

variable {k : ℕ} {tm : NTM k}

def Bounded (B : ℕ) (c : Cfg tm) : Prop :=
  ∀ j, (c.tapes j).head < B ∧ (c.tapes j).code < 4 ^ B

theorem bounded_init (tm : NTM k) (x : List Bool) : Bounded (x.length + 1) (init tm x) := by
  intro j
  constructor
  · simp only [init]
    split <;> simp [Tape.init]
  · simp only [init]
    split
    · simpa using Tape.init_code_lt (x.map Γ.ofBool)
    · have h := Tape.init_code_lt []
      exact h.trans_le (Nat.pow_le_pow_right (by decide) (by simp))

theorem Bounded.mono {B C : ℕ} {c : Cfg tm} (hc : Bounded B c) (hBC : B ≤ C) :
    Bounded C c := by
  intro j
  exact ⟨(hc j).1.trans_le hBC,
    (hc j).2.trans_le (Nat.pow_le_pow_right (by decide) hBC)⟩

private theorem move_bounded (t : Tape) (d : Dir3) (B : ℕ)
    (hh : t.head < B) (hb : t.code < 4 ^ B) :
    (t.move d).head < B + 1 ∧ (t.move d).code < 4 ^ (B + 1) := by
  refine ⟨?_, ?_⟩
  · have h := Tape.head_move_le t d
    omega
  · rw [Tape.move_code]
    exact hb.trans_le (Nat.pow_le_pow_right (by decide) (by omega))

private theorem writeAndMove_bounded (t : Tape) (ht : t.Valid) (s : Γ)
    (d : Dir3) (B : ℕ) (hh : t.head < B) (hb : t.code < 4 ^ B) :
    (t.writeAndMove s d).head < B + 1 ∧ (t.writeAndMove s d).code < 4 ^ (B + 1) := by
  apply move_bounded (t.write s) d B
  · simpa using hh
  · exact Tape.write_code_lt t ht s B hb hh

theorem Bounded.step {B : ℕ} {c : Cfg tm} (hb : Bounded B c) (hc : c.Valid)
    (b : Bool) : Bounded (B + 1) (step b c) := by
  by_cases h : c.state = tm.qhalt
  · simpa [Cfg.step, h] using hb.mono (Nat.le_succ B)
  · intro j
    simp only [Cfg.step, h, ite_false]
    split
    · exact move_bounded c.input _ B (hb 0).1 (hb 0).2
    · split
      · exact writeAndMove_bounded c.output (hc 1) _ _ B (hb 1).1 (hb 1).2
      · exact writeAndMove_bounded (c.work _) (hc _) _ _ B (hb _).1 (hb _).2

theorem Bounded.run {B : ℕ} {c : Cfg tm} (hb : Bounded B c) (hc : c.Valid)
    (choices : List Bool) : Bounded (B + choices.length) (run choices c) := by
  induction choices generalizing B c with
  | nil => simpa [Cfg.run] using hb
  | cons b bs ih =>
      simpa [Cfg.run, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        ih (hb.step hc b) (hc.step b)

theorem Bounded.code_size {B : ℕ} {c : Cfg tm} (hb : Bounded B c) (j : Fin (k + 2)) :
    Nat.size (c.tapes j).code ≤ 2 * B := size_le_of_lt_four_pow _ B (hb j).2

theorem Bounded.head_size {B : ℕ} {c : Cfg tm} (hb : Bounded B c) (j : Fin (k + 2)) :
    Nat.size (c.tapes j).head ≤ B :=
  (Nat.size_le.mpr Nat.lt_two_pow_self).trans (hb j).1.le

theorem Bounded.power_size {B : ℕ} {c : Cfg tm} (hb : Bounded B c) (hc : c.Valid)
    (j : Fin (k + 2)) : Nat.size (c.tapes j).power ≤ 2 * B := by
  apply size_le_of_lt_four_pow
  rw [show (c.tapes j).power = 4 ^ (c.tapes j).head from hc j]
  exact Nat.pow_lt_pow_right (by decide) (hb j).1

theorem Bounded.encode_size {B q : ℕ} {c : Cfg tm} (hb : Bounded B c) (hc : c.Valid)
    (eQ : tm.Q ≃ Fin q) (r : Fin (width k)) : Nat.size (encode eQ c r) ≤ Nat.size q + 2 * B := by
  simp only [encode]
  split
  · have h := Nat.size_le_size (eQ c.state).isLt.le
    omega
  · split
    · exact (hb.code_size _).trans (Nat.le_add_left _ _)
    · split
      · apply (hb.head_size _).trans
        omega
      · exact (hb.power_size hc _).trans (Nat.le_add_left _ _)

/-- Every numeric register has linear bit size throughout the witness simulation. -/
theorem run_encode_size (tm : NTM k) {q : ℕ} (eQ : tm.Q ≃ Fin q)
    (x choices : List Bool) (r : Fin (width k)) :
    Nat.size (encode eQ (run choices (init tm x)) r) ≤
      Nat.size q + 2 * (x.length + choices.length + 1) := by
  have hb := (bounded_init tm x).run (valid_init tm x) choices
  have hc := (valid_init tm x).run choices
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hb.encode_size hc eQ r

end PCP.ReferenceNTM.Cfg
