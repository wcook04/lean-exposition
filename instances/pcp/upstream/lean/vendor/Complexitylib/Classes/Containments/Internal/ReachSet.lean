/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.Containments.Internal.ConfigGraph
public import Mathlib.Data.Set.Card

/-!
# Reachability as a bounded fixpoint

⚠️ Unreviewed by Bolton

Breadth-first search closes a set of configurations under the successor relation. `reachSet`
is that closure after a fixed number of rounds, and the theorem below says a *polynomial* number
of rounds already suffices: the rounds strictly grow until they stabilize, and they cannot grow
past the number of configurations available.

This is the specification a polynomial-time search has to implement — the counting it needs comes
from `Complexitylib.Classes.Containments.Internal.LogSpaceBound`.

`reachSet` itself is defined in `Complexitylib.Classes.Containments.Defs`.

## Main results

- `NTM.reachSet_mono`, `NTM.reachSet_stabilizes` — the rounds grow and then stop
- `NTM.reachSet_finite` — each round is a finite set
- `NTM.exists_stabilizing_round` — they stop within the number of configuration codes
- `NTM.reachesCfg_iff_mem_reachSet` — enough rounds compute exactly reachability
- `NTM.reachesCfg_iff_mem_reachSet` — with enough rounds the fixpoint is exactly reachability
-/

@[expose] public section

namespace Complexity

namespace NTM

variable {k : ℕ} {tm : NTM k}

theorem reachSet_succ (tm : NTM k) (c₀ : Cfg k tm.Q) (t : ℕ) :
    reachSet tm c₀ (t + 1) = reachSet tm c₀ t ∪ {c' | ∃ c ∈ reachSet tm c₀ t, tm.Succ c c'} :=
  rfl

theorem reachSet_subset_succ (tm : NTM k) (c₀ : Cfg k tm.Q) (t : ℕ) :
    reachSet tm c₀ t ⊆ reachSet tm c₀ (t + 1) := fun _ h => Or.inl h

theorem reachSet_mono (tm : NTM k) (c₀ : Cfg k tm.Q) {s t : ℕ} (h : s ≤ t) :
    reachSet tm c₀ s ⊆ reachSet tm c₀ t := by
  induction t with
  | zero => rw [Nat.le_zero.mp h]
  | succ t ih =>
      rcases Nat.lt_or_ge s (t + 1) with hlt | hge
      · exact (ih (by omega)).trans (reachSet_subset_succ tm c₀ t)
      · rw [show s = t + 1 from by omega]

/-- Every element of a round is reachable. -/
theorem reachesCfg_of_mem_reachSet (tm : NTM k) (c₀ : Cfg k tm.Q) :
    ∀ (t : ℕ) {c}, c ∈ reachSet tm c₀ t → tm.ReachesCfg c₀ c
  | 0, c, hc => by rw [Set.mem_singleton_iff.mp hc]; exact reachesCfg_refl tm c₀
  | t + 1, c, hc => by
      rcases hc with hc | ⟨c', hc', hstep⟩
      · exact reachesCfg_of_mem_reachSet tm c₀ t hc
      · exact Relation.ReflTransGen.tail (reachesCfg_of_mem_reachSet tm c₀ t hc') hstep

/-- Reachability in `t` steps lands in round `t`. -/
theorem mem_reachSet_of_reachesCfg {c₀ c : Cfg k tm.Q} (h : tm.ReachesCfg c₀ c) :
    ∃ t, c ∈ reachSet tm c₀ t := by
  induction h with
  | refl => exact ⟨0, rfl⟩
  | tail _ hstep ih =>
      obtain ⟨t, ht⟩ := ih
      exact ⟨t + 1, Or.inr ⟨_, ht, hstep⟩⟩

/-- Once a round adds nothing, no later round does either. -/
theorem reachSet_stabilizes (tm : NTM k) (c₀ : Cfg k tm.Q) {s : ℕ}
    (h : reachSet tm c₀ (s + 1) ⊆ reachSet tm c₀ s) :
    ∀ m, reachSet tm c₀ (s + m) = reachSet tm c₀ s := by
  intro m
  induction m with
  | zero => rfl
  | succ m ih =>
      have hs : s + (m + 1) = (s + m) + 1 := by omega
      rw [hs, reachSet_succ]
      refine subset_antisymm (fun c hc => ?_) (fun c hc => Or.inl (by rw [ih]; exact hc))
      rcases hc with hc | ⟨c', hc', hst⟩
      · rw [ih] at hc
        exact hc
      · rw [ih] at hc'
        exact h (Or.inr ⟨c', hc', hst⟩)

/-- Each round is a finite set: it starts as a singleton and each round adds at most two
successors per member. -/
theorem reachSet_finite (tm : NTM k) (c₀ : Cfg k tm.Q) : ∀ t, (reachSet tm c₀ t).Finite
  | 0 => Set.finite_singleton c₀
  | t + 1 => by
      refine (reachSet_finite tm c₀ t).union (Set.Finite.subset
        (((reachSet_finite tm c₀ t).image (tm.stepCfg false)).union
          ((reachSet_finite tm c₀ t).image (tm.stepCfg true))) ?_)
      rintro c' ⟨c, hc, -, b, rfl⟩
      cases b
      · exact Or.inl ⟨c, hc, rfl⟩
      · exact Or.inr ⟨c, hc, rfl⟩

/-! ## The rounds stabilize within the configuration count -/

section Finite

variable {α : Type} [Fintype α]

/-- The image of a round under a coding map. -/
private def reachImage (tm : NTM k) (c₀ : Cfg k tm.Q) (g : Cfg k tm.Q → α) (t : ℕ) : Set α :=
  g '' reachSet tm c₀ t

omit [Fintype α] in
private theorem reachImage_mono (tm : NTM k) (c₀ : Cfg k tm.Q) (g : Cfg k tm.Q → α) (t : ℕ) :
    reachImage tm c₀ g t ⊆ reachImage tm c₀ g (t + 1) :=
  Set.image_mono (reachSet_subset_succ tm c₀ t)

omit [Fintype α] in
/-- A round that adds a genuinely new configuration adds a new code too, provided the coding
map separates reachable configurations. -/
private theorem reachImage_ssubset (tm : NTM k) (c₀ : Cfg k tm.Q) (g : Cfg k tm.Q → α)
    (hinj : ∀ {c c' : Cfg k tm.Q}, tm.ReachesCfg c₀ c → tm.ReachesCfg c₀ c' → g c = g c' → c = c')
    {t : ℕ} (h : ¬ reachSet tm c₀ (t + 1) ⊆ reachSet tm c₀ t) :
    reachImage tm c₀ g t ⊂ reachImage tm c₀ g (t + 1) := by
  obtain ⟨c, hc, hcn⟩ := Set.not_subset.mp h
  refine ⟨reachImage_mono tm c₀ g t, fun hsub => hcn ?_⟩
  obtain ⟨c', hc', hgc⟩ := hsub ⟨c, hc, rfl⟩
  have := hinj (reachesCfg_of_mem_reachSet tm c₀ (t + 1) hc)
    (reachesCfg_of_mem_reachSet tm c₀ t hc') hgc.symm
  rwa [this]

/-- **The rounds stabilize by the number of codes.** As long as the rounds keep growing they
consume a fresh code each time, and there are only `Fintype.card α` of those. -/
theorem exists_stabilizing_round (tm : NTM k) (c₀ : Cfg k tm.Q) (g : Cfg k tm.Q → α)
    (hinj : ∀ {c c' : Cfg k tm.Q}, tm.ReachesCfg c₀ c → tm.ReachesCfg c₀ c' → g c = g c' → c = c') :
    ∃ s ≤ Fintype.card α, reachSet tm c₀ (s + 1) ⊆ reachSet tm c₀ s := by
  by_contra hcon
  have hcon' : ∀ t ≤ Fintype.card α, ¬ reachSet tm c₀ (t + 1) ⊆ reachSet tm c₀ t :=
    fun t ht hsub => hcon ⟨t, ht, hsub⟩
  have grow : ∀ t ≤ Fintype.card α, t + 1 ≤ (reachImage tm c₀ g t).ncard := by
    intro t
    induction t with
    | zero =>
        intro _
        have : reachImage tm c₀ g 0 = {g c₀} := by
          simp [reachImage, reachSet]
        rw [this, Set.ncard_singleton]
    | succ t ih =>
        intro ht
        have hss := reachImage_ssubset tm c₀ g hinj (hcon' t (by omega))
        have hlt := Set.ncard_lt_ncard hss (Set.toFinite _)
        have := ih (by omega)
        omega
  have hle : (reachImage tm c₀ g (Fintype.card α)).ncard ≤ Fintype.card α := by
    have := Set.ncard_le_ncard (Set.subset_univ (reachImage tm c₀ g (Fintype.card α)))
      (Set.finite_univ)
    rwa [Set.ncard_univ, Nat.card_eq_fintype_card] at this
  have := grow (Fintype.card α) le_rfl
  omega

/-- **With enough rounds the fixpoint is exactly reachability.** The number of rounds needed is
the number of codes, so a polynomial code count makes this a polynomial-round search. -/
theorem reachesCfg_iff_mem_reachSet' (tm : NTM k) (c₀ : Cfg k tm.Q) (g : Cfg k tm.Q → α)
    (hinj : ∀ {c c' : Cfg k tm.Q}, tm.ReachesCfg c₀ c → tm.ReachesCfg c₀ c' → g c = g c' → c = c')
    (c : Cfg k tm.Q) :
    tm.ReachesCfg c₀ c ↔ c ∈ reachSet tm c₀ (Fintype.card α) := by
  refine ⟨fun h => ?_, reachesCfg_of_mem_reachSet tm c₀ _⟩
  obtain ⟨t, ht⟩ := mem_reachSet_of_reachesCfg h
  obtain ⟨s, hsN, hstab⟩ := exists_stabilizing_round tm c₀ g hinj
  rcases Nat.lt_or_ge t (Fintype.card α) with hlt | hge
  · exact reachSet_mono tm c₀ hlt.le ht
  · have : reachSet tm c₀ t = reachSet tm c₀ s := by
      have := reachSet_stabilizes tm c₀ hstab (t - s)
      rwa [show s + (t - s) = t from by omega] at this
    rw [this] at ht
    exact reachSet_mono tm c₀ hsN ht

/-- **Running extra rounds is harmless.** An implementation computes a round count it can
evaluate rather than the exact number of codes; any count that reaches the bound is correct. -/
theorem reachesCfg_iff_mem_reachSet (tm : NTM k) (c₀ : Cfg k tm.Q) (g : Cfg k tm.Q → α)
    (hinj : ∀ {c c' : Cfg k tm.Q}, tm.ReachesCfg c₀ c → tm.ReachesCfg c₀ c' → g c = g c' → c = c')
    {N : ℕ} (hN : Fintype.card α ≤ N) (c : Cfg k tm.Q) :
    tm.ReachesCfg c₀ c ↔ c ∈ reachSet tm c₀ N :=
  ⟨fun h => reachSet_mono tm c₀ hN
      ((reachesCfg_iff_mem_reachSet' tm c₀ g hinj c).mp h),
   reachesCfg_of_mem_reachSet tm c₀ N⟩

end Finite

end NTM

end Complexity
