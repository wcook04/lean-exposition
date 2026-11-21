/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Models.TuringMachine.SpaceTime.Defs
public import Mathlib.Tactic.Ring

/-!
# Counting the configurations inside a space bound

⚠️ Unreviewed by Bolton

`Cfg.WithinDecisionSpace` bounds head *positions*, but counting configurations also needs to know
the tape *contents* are pinned down. A head that never leaves its window can never write outside
it, so every cell beyond still holds what it started with — that is `Windowed`, and it is what
makes the configuration space finite.

Nothing here mentions a machine: the counting is the same for deterministic and nondeterministic
configurations, and both `PSPACE ⊆ EXP` and the log-space graph arguments use it.

## Main definitions

- `Windowed` — the tapes agree with their initial contents outside the window
- `cfgCode` — a total code for configurations, injective inside the space bound
- `instDecidableEqCode` — codes have decidable equality

## Main results

- `Windowed.mono`, `Cfg.WithinDecisionSpace.mono` — enlarging the window is harmless
- `cfgCode_inj` — two windowed configurations inside the bound with the same code are equal
- `card_Code` — the number of codes
- `card_Code_le_two_pow` — the count is at most `2` to a linear-in-`S` exponent
-/

@[expose] public section

namespace Complexity

variable {k : ℕ} {Q : Type}

/-- Outside the space window every tape still holds what it started with: the input tape is
read-only, and the work and output tapes are blank beyond the reach of their heads. -/
structure Windowed (x : List Bool) (S : ℕ) (c : Cfg k Q) : Prop where
  /-- The input tape is never written. -/
  input : c.input.cells = (Tape.init (x.map Γ.ofBool)).cells
  /-- Work cells beyond the window are blank. -/
  work : ∀ (i : Fin k) (p : ℕ), S < p → (c.work i).cells p = Γ.blank
  /-- Output cells beyond the window are blank. -/
  output : ∀ p : ℕ, S + 1 < p → c.output.cells p = Γ.blank

/-- The initial configuration is windowed. -/
theorem windowed_init (q : Q) (x : List Bool) (S : ℕ) :
    Windowed (k := k) x S (Cfg.init q x) where
  input := rfl
  work := by
    intro i p hp
    show (Tape.init ([] : List Γ)).cells p = Γ.blank
    obtain ⟨r, rfl⟩ : ∃ r, p = r + 1 := ⟨p - 1, by omega⟩
    simp
  output := by
    intro p hp
    show (Tape.init ([] : List Γ)).cells p = Γ.blank
    obtain ⟨r, rfl⟩ : ∃ r, p = r + 1 := ⟨p - 1, by omega⟩
    simp

/-- Enlarging the window preserves the invariant: what is blank beyond `S` is blank beyond any
larger `S'` too. -/
theorem Windowed.mono {x : List Bool} {S S' : ℕ} {c : Cfg k Q}
    (h : Windowed x S c) (hS : S ≤ S') : Windowed x S' c where
  input := h.input
  work := fun i p hp => h.work i p (by omega)
  output := fun p hp => h.output p (by omega)

/-- Enlarging the space budget preserves a decision-space bound. -/
theorem Cfg.WithinDecisionSpace.mono {n S S' : ℕ} {c : Cfg k Q}
    (h : c.WithinDecisionSpace n S) (hS : S ≤ S') : c.WithinDecisionSpace n S' :=
  ⟨⟨fun i => (h.1.1 i).trans hS, by have := h.1.2; omega⟩, by have := h.2; omega⟩

/-- Writing at the head leaves every other cell alone. -/
theorem cells_writeAndMove_of_ne (t : Tape) (s : Γ) (d : Dir3) {p : ℕ} (hp : p ≠ t.head) :
    (t.writeAndMove s d).cells p = t.cells p := by
  show ((t.write s).move d).cells p = t.cells p
  have : (t.write s).cells p = t.cells p := by
    rw [Tape.write]
    split
    · rfl
    · exact Function.update_of_ne hp _ _
  cases d <;> exact this

/-- A finite code for configurations inside the space window: the state, the three head
positions clamped into range, and the tape contents restricted to the window. -/
abbrev Code (Q : Type) (k nn S : ℕ) : Type :=
  Q × Fin (nn + S + 2) × (Fin k → Fin (S + 1) × (Fin (S + 1) → Γ)) ×
    (Fin (S + 2) × (Fin (S + 2) → Γ))

/-- Codes have decidable equality: the search of
`Complexitylib.Classes.Containments.Internal.CodeSearch` stores them in a `Finset`. The instance
is spelled out because the default synthesis size limit stops short of this nesting depth. -/
instance instDecidableEqCode (Q : Type) [DecidableEq Q] (k nn S : ℕ) :
    DecidableEq (Code Q k nn S) := by
  set_option synthInstance.maxSize 400 in infer_instance

/-- The code of a configuration. Clamping keeps this total; on configurations that respect the
space bound the clamps are inert. -/
def cfgCode (nn S : ℕ) (c : Cfg k Q) : Code Q k nn S :=
  (c.state,
   ⟨min c.input.head (nn + S + 1), by omega⟩,
   fun i => (⟨min (c.work i).head S, by omega⟩, fun p => (c.work i).cells p.val),
   (⟨min c.output.head (S + 1), by omega⟩, fun p => c.output.cells p.val))

/-- Two windowed configurations inside the space bound with the same code are equal. -/
theorem cfgCode_inj {x : List Bool} {S : ℕ} {c₁ c₂ : Cfg k Q}
    (h₁ : Windowed x S c₁) (hs₁ : c₁.WithinDecisionSpace x.length S)
    (h₂ : Windowed x S c₂) (hs₂ : c₂.WithinDecisionSpace x.length S)
    (h : cfgCode x.length S c₁ = cfgCode x.length S c₂) : c₁ = c₂ := by
  simp only [cfgCode, Prod.mk.injEq] at h
  obtain ⟨hst, hin, hwk, hout⟩ := h
  refine Cfg.ext hst ?_ ?_ ?_
  · refine Tape.ext ?_ (h₁.input.trans h₂.input.symm)
    have b₁ : c₁.input.head ≤ x.length + S + 1 := hs₁.1.2
    have b₂ : c₂.input.head ≤ x.length + S + 1 := hs₂.1.2
    have := congrArg Fin.val hin
    simp only [] at this
    omega
  · funext i
    have hi := congrFun hwk i
    rw [Prod.mk.injEq] at hi
    have bh₁ : (c₁.work i).head ≤ S := hs₁.1.1 i
    have bh₂ : (c₂.work i).head ≤ S := hs₂.1.1 i
    refine Tape.ext ?_ ?_
    · have := congrArg Fin.val hi.1
      simp only [] at this
      omega
    · funext p
      rcases Nat.lt_or_ge S p with hp | hp
      · rw [h₁.work i p hp, h₂.work i p hp]
      · exact congrFun hi.2 ⟨p, by omega⟩
  · have bh₁ : c₁.output.head ≤ S + 1 := hs₁.2
    have bh₂ : c₂.output.head ≤ S + 1 := hs₂.2
    refine Tape.ext ?_ ?_
    · have := congrArg Fin.val hout.1
      simp only [] at this
      omega
    · funext p
      rcases Nat.lt_or_ge (S + 1) p with hp | hp
      · rw [h₁.output p hp, h₂.output p hp]
      · exact congrFun hout.2 ⟨p, by omega⟩

/-- The number of codes. -/
theorem card_Code (Q : Type) [Fintype Q] (k nn S : ℕ) :
    Fintype.card (Code Q k nn S)
      = Fintype.card Q *
        ((nn + S + 2) * (((S + 1) * 4 ^ (S + 1)) ^ k * ((S + 2) * 4 ^ (S + 2)))) := by
  simp [Code, Fintype.card_prod, Γ.card]

/-- **The configuration count is at most exponential in the space bound.** Both `PSPACE ⊆ EXP`
and Savitch's theorem read the count this way: as `2` to something linear in the space bound. -/
theorem card_Code_le_two_pow (Q : Type) [Fintype Q] (k nn S : ℕ) :
    Fintype.card (Code Q k nn S)
      ≤ 2 ^ (Fintype.card Q + (nn + S + 2) + 3 * k * (S + 1) + 3 * (S + 2)) := by
  have key : ∀ m : ℕ, (m + 1) * 4 ^ (m + 1) ≤ 2 ^ (3 * (m + 1)) := by
    intro m
    calc (m + 1) * 4 ^ (m + 1)
        ≤ 2 ^ (m + 1) * 4 ^ (m + 1) := Nat.mul_le_mul_right _ (Nat.lt_two_pow_self).le
      _ = 2 ^ (m + 1) * 2 ^ (2 * (m + 1)) := by
          rw [show (4 : ℕ) = 2 ^ 2 from rfl, ← pow_mul, Nat.mul_comm 2 (m + 1)]
      _ = 2 ^ (3 * (m + 1)) := by rw [← pow_add]; ring_nf
  have e1 : Fintype.card Q ≤ 2 ^ Fintype.card Q := (Nat.lt_two_pow_self).le
  have e2 : nn + S + 2 ≤ 2 ^ (nn + S + 2) := (Nat.lt_two_pow_self).le
  have e3 : ((S + 1) * 4 ^ (S + 1)) ^ k ≤ 2 ^ (3 * k * (S + 1)) := by
    calc ((S + 1) * 4 ^ (S + 1)) ^ k
        ≤ (2 ^ (3 * (S + 1))) ^ k := Nat.pow_le_pow_left (key S) k
      _ = 2 ^ (3 * k * (S + 1)) := by rw [← pow_mul]; ring_nf
  have e4 : (S + 2) * 4 ^ (S + 2) ≤ 2 ^ (3 * (S + 2)) := by
    have := key (S + 1)
    rw [show S + 1 + 1 = S + 2 from rfl] at this
    exact this
  rw [card_Code]
  calc Fintype.card Q * ((nn + S + 2) * (((S + 1) * 4 ^ (S + 1)) ^ k * ((S + 2) * 4 ^ (S + 2))))
      ≤ 2 ^ Fintype.card Q *
        (2 ^ (nn + S + 2) * (2 ^ (3 * k * (S + 1)) * 2 ^ (3 * (S + 2)))) :=
        Nat.mul_le_mul e1 (Nat.mul_le_mul e2 (Nat.mul_le_mul e3 e4))
    _ = 2 ^ (Fintype.card Q + (nn + S + 2) + 3 * k * (S + 1) + 3 * (S + 2)) := by
        rw [← pow_add, ← pow_add, ← pow_add]
        ring_nf

end Complexity
