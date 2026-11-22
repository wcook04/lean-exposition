/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.Containments.Internal.ConfigCount
public import Complexitylib.Asymptotics

/-!
# The configuration graph of a log-space machine is polynomially sized

⚠️ Unreviewed by Bolton

A machine using `O(log n)` space has only polynomially many configurations: each of the
`4 ^ O(log n)` tape contents is `n ^ O(1)`, and the head positions contribute a further
polynomial factor. This is what turns the graph reachability of
`Complexitylib.Classes.Containments.Internal.ConfigGraph` into a polynomial-time search.

## Main results

- `exists_log_bound` — an `O(log n)` bound holds everywhere after adding a constant
- `four_pow_log_le` — `4 ^ (C · log₂ n + D)` is polynomially bounded
- `exists_config_bound` — the configuration count is `A · (n + 1) ^ B`
-/

@[expose] public section

namespace Complexity

/-- An asymptotic logarithmic bound becomes an everywhere bound after adding a constant: the
finitely many exceptional inputs are absorbed into it. -/
theorem exists_log_bound {f : ℕ → ℕ} (hf : f =O (fun n => Nat.log 2 n)) :
    ∃ C D : ℕ, ∀ n, f n ≤ C * Nat.log 2 n + D := by
  rw [BigO, Asymptotics.isBigO_iff] at hf
  obtain ⟨c, hc⟩ := hf
  rw [Filter.eventually_atTop] at hc
  obtain ⟨N, hN⟩ := hc
  refine ⟨⌈c⌉₊, (Finset.range N).sup f, fun n => ?_⟩
  by_cases hn : n < N
  · have : f n ≤ (Finset.range N).sup f := Finset.le_sup (Finset.mem_range.mpr hn)
    omega
  · have hb := hN n (by omega)
    simp only [Real.norm_natCast] at hb
    have hcle : c ≤ (⌈c⌉₊ : ℝ) := Nat.le_ceil c
    have hlog : (0 : ℝ) ≤ ((Nat.log 2 n : ℕ) : ℝ) := by positivity
    have : (f n : ℝ) ≤ (⌈c⌉₊ : ℝ) * ((Nat.log 2 n : ℕ) : ℝ) :=
      le_trans hb (mul_le_mul_of_nonneg_right hcle hlog)
    have hnat : f n ≤ ⌈c⌉₊ * Nat.log 2 n := by exact_mod_cast this
    omega

/-- Four to a logarithmic power is polynomial. -/
theorem four_pow_log_le (C D n : ℕ) :
    4 ^ (C * Nat.log 2 n + D) ≤ 4 ^ D * (n + 1) ^ (2 * C) := by
  rw [pow_add, Nat.mul_comm (4 ^ (C * Nat.log 2 n)) (4 ^ D)]
  refine Nat.mul_le_mul_left _ ?_
  have hbase : (4 : ℕ) ^ (C * Nat.log 2 n) = (2 ^ Nat.log 2 n) ^ (2 * C) := by
    rw [show (4 : ℕ) = 2 ^ 2 from rfl, ← pow_mul, ← pow_mul]
    ring_nf
  rw [hbase]
  refine Nat.pow_le_pow_left ?_ _
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · exact le_trans (Nat.pow_log_le_self 2 (by omega)) (by omega)

/-- Bounded by a constant times a power of `n + 1`. -/
def PolyBounded (g : ℕ → ℕ) : Prop := ∃ A B : ℕ, ∀ n, g n ≤ A * (n + 1) ^ B

theorem PolyBounded.const (c : ℕ) : PolyBounded fun _ => c := ⟨c, 0, fun _ => by simp⟩

/-- Transfer along a pointwise bound. -/
theorem PolyBounded.mono {g h : ℕ → ℕ} (hg : PolyBounded g) (hle : ∀ n, h n ≤ g n) :
    PolyBounded h := by
  obtain ⟨A, B, hA⟩ := hg
  exact ⟨A, B, fun n => le_trans (hle n) (hA n)⟩

theorem PolyBounded.mul {g h : ℕ → ℕ} (hg : PolyBounded g)
    (hh : PolyBounded h) : PolyBounded fun n => g n * h n := by
  obtain ⟨A₁, B₁, h₁⟩ := hg
  obtain ⟨A₂, B₂, h₂⟩ := hh
  refine ⟨A₁ * A₂, B₁ + B₂, fun n => ?_⟩
  calc g n * h n ≤ (A₁ * (n + 1) ^ B₁) * (A₂ * (n + 1) ^ B₂) :=
        Nat.mul_le_mul (h₁ n) (h₂ n)
    _ = A₁ * A₂ * (n + 1) ^ (B₁ + B₂) := by rw [pow_add]; ring

theorem PolyBounded.add {g h : ℕ → ℕ} (hg : PolyBounded g)
    (hh : PolyBounded h) : PolyBounded fun n => g n + h n := by
  obtain ⟨A₁, B₁, h₁⟩ := hg
  obtain ⟨A₂, B₂, h₂⟩ := hh
  refine ⟨A₁ + A₂, max B₁ B₂, fun n => ?_⟩
  have e₁ : (n + 1) ^ B₁ ≤ (n + 1) ^ max B₁ B₂ :=
    Nat.pow_le_pow_right (by omega) (le_max_left _ _)
  have e₂ : (n + 1) ^ B₂ ≤ (n + 1) ^ max B₁ B₂ :=
    Nat.pow_le_pow_right (by omega) (le_max_right _ _)
  calc g n + h n ≤ A₁ * (n + 1) ^ B₁ + A₂ * (n + 1) ^ B₂ := Nat.add_le_add (h₁ n) (h₂ n)
    _ ≤ A₁ * (n + 1) ^ max B₁ B₂ + A₂ * (n + 1) ^ max B₁ B₂ :=
        Nat.add_le_add (Nat.mul_le_mul_left _ e₁) (Nat.mul_le_mul_left _ e₂)
    _ = (A₁ + A₂) * (n + 1) ^ max B₁ B₂ := by ring

theorem PolyBounded.pow {g : ℕ → ℕ} (hg : PolyBounded g) (m : ℕ) :
    PolyBounded fun n => g n ^ m := by
  induction m with
  | zero => exact (PolyBounded.const 1).mono fun n => by simp
  | succ m ih => exact (ih.mul hg).mono fun n => by rw [pow_succ]

theorem PolyBounded.id : PolyBounded fun n => n := ⟨1, 1, fun n => by simp⟩

/-- A log-space bound is polynomially bounded, as is four to its power. -/
theorem PolyBounded.of_log {f : ℕ → ℕ} (hf : f =O (fun n => Nat.log 2 n)) : PolyBounded f := by
  obtain ⟨C, D, hCD⟩ := exists_log_bound hf
  refine ⟨C + D, 1, fun n => ?_⟩
  have h1 : Nat.log 2 n ≤ n := Nat.log_le_self 2 n
  have := hCD n
  nlinarith [Nat.zero_le C, Nat.zero_le D]

theorem PolyBounded.four_pow {f : ℕ → ℕ} (hf : f =O (fun n => Nat.log 2 n)) (m : ℕ) :
    PolyBounded fun n => 4 ^ (f n + m) := by
  obtain ⟨C, D, hCD⟩ := exists_log_bound hf
  refine ⟨4 ^ (D + m), 2 * C, fun n => ?_⟩
  calc 4 ^ (f n + m) ≤ 4 ^ (C * Nat.log 2 n + (D + m)) := by
        refine Nat.pow_le_pow_right (by norm_num) ?_
        have := hCD n
        omega
    _ ≤ 4 ^ (D + m) * (n + 1) ^ (2 * C) := four_pow_log_le C (D + m) n

/-- **The configuration count of a log-space machine is polynomial.** -/
theorem exists_config_bound {k : ℕ} (Q : Type) [Fintype Q] {f : ℕ → ℕ}
    (hf : f =O (fun n => Nat.log 2 n)) :
    PolyBounded fun n => Fintype.card (Code Q k n (f n)) := by
  have hf' := PolyBounded.of_log hf
  have key : PolyBounded fun n =>
      Fintype.card Q *
        ((n + f n + 2) * (((f n + 1) * 4 ^ (f n + 1)) ^ k * ((f n + 2) * 4 ^ (f n + 2)))) := by
    refine (PolyBounded.const _).mul (((PolyBounded.id.add hf').add (PolyBounded.const 2)).mul ?_)
    refine PolyBounded.mul ?_ ?_
    · exact ((hf'.add (PolyBounded.const 1)).mul (PolyBounded.four_pow hf 1)).pow k
    · exact (hf'.add (PolyBounded.const 2)).mul (PolyBounded.four_pow hf 2)
  exact key.mono fun n => by rw [card_Code]

end Complexity
