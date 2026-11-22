/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Algebraic.CandidateCrossing
import PCP.Algebraic.BivariateCleanRectangle

/-!
# Probabilistic assembly for candidate crossing rigidity

Five actual mean errors bound the probability of disagreement at a crossing.
An additional endpoint estimate identifies a seed-independent column value.
The seed distributions may be correlated arbitrarily.
-/

namespace PCP.Algebraic.CandidateCrossing

open Finset AffineLineSampling PointedLineSampling
open scoped BigOperators

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The two global, two transverse, and selected-row own errors. -/
noncomputable def errors (M : F × F → F) (R C : F → Polynomial F) (y₀ z₀ : F) :
    Fin 5 → ℚ :=
  ![relativeDistance M (fun yz => (R yz.1).eval yz.2),
    relativeDistance M (fun yz => (C yz.2).eval yz.1),
    relativeDistance (fun z => M (y₀, z)) (fun z => (C z).eval y₀),
    relativeDistance (fun y => M (y, z₀)) (fun y => (R y).eval z₀),
    relativeDistance (fun z => M (y₀, z)) (R y₀).eval]

theorem errors_nonneg (M : F × F → F) (R C : F → Polynomial F) (y₀ z₀ : F) (j : Fin 5) :
    0 ≤ errors M R C y₀ z₀ j := by
  fin_cases j <;> exact relativeDistance_nonneg _ _

/-- Markov and a union bound control failure of the candidate crossing identity. -/
theorem fraction_disagreement_le {S : Type*} [Fintype S] {d : ℕ}
    (hd : 0 < d) (hq : 1000 * d ^ 3 ≤ Fintype.card F)
    (M : S → F × F → F) (R C : S → F → Polynomial F)
    (hR : ∀ s y, (R s y).natDegree ≤ d) (hC : ∀ s z, (C s z).natDegree ≤ d)
    (y₀ z₀ : F) {ε : ℚ} (hεpos : 0 < ε) (hε : ε ≤ 1 / 100)
    (hmin : ∀ s (p : Polynomial F), p.natDegree ≤ d →
      relativeDistance (fun y => M s (y, z₀)) (C s z₀).eval ≤
        relativeDistance (fun y => M s (y, z₀)) p.eval)
    (hsmall : 6 * ε + 2 * ((d : ℚ) / Fintype.card F) < 1 / 2)
    (β : Fin 5 → ℚ) (hmean : ∀ j, (𝔼 s, errors (M s) (R s) (C s) y₀ z₀ j) ≤ β j) :
    fraction (fun s => (R s y₀).eval z₀ ≠ (C s z₀).eval y₀) ≤ (∑ j, β j) / ε := by
  classical
  let E : Fin 5 → S → Prop := fun j s => ε ≤ errors (M s) (R s) (C s) y₀ z₀ j
  have hbad : ∀ s, (R s y₀).eval z₀ ≠ (C s z₀).eval y₀ →
      ∃ j ∈ (univ : Finset (Fin 5)), E j s := by
    intro s hs
    by_contra hn
    have hall (j : Fin 5) : errors (M s) (R s) (C s) y₀ z₀ j ≤ ε := by
      have h : ¬ E j s := fun hj => hn ⟨j, mem_univ j, hj⟩
      exact (lt_of_not_ge h).le
    exact hs (crossing_eq hd hq (M s) (R s) (C s) (hR s) (hC s) y₀ z₀ hε
      (hall 0) (hall 1) (hall 2) (hall 3) (hall 4) (hmin s) hsmall)
  have hmarkov (j : Fin 5) : fraction (E j) ≤ β j / ε := by
    apply (fraction_ge_le (fun s => errors (M s) (R s) (C s) y₀ z₀ j)
      (fun s => errors_nonneg _ _ _ _ _ _) ε hεpos).trans
    exact div_le_div_of_nonneg_right (hmean j) hεpos.le
  calc
    _ ≤ fraction (fun s => ∃ j ∈ (univ : Finset (Fin 5)), E j s) := fraction_mono _ _ hbad
    _ ≤ ∑ j, fraction (E j) := BivariateCleanRectangle.fraction_exists_mem_le univ E
    _ ≤ ∑ j, β j / ε := sum_le_sum (fun j _ => hmarkov j)
    _ = _ := (sum_div ..).symm

/-- A seed-independent column value is identified by a positive-probability
intersection of good crossings and correct candidate endpoint predictions. -/
theorem value_eq_of_mean_errors {S : Type*} [Fintype S] [Nonempty S] {d : ℕ}
    (hd : 0 < d) (hq : 1000 * d ^ 3 ≤ Fintype.card F)
    (M : S → F × F → F) (R C : S → F → Polynomial F)
    (hR : ∀ s y, (R s y).natDegree ≤ d) (hC : ∀ s z, (C s z).natDegree ≤ d)
    (y₀ z₀ : F) {ε γ : ℚ} (hεpos : 0 < ε) (hε : ε ≤ 1 / 100)
    (hmin : ∀ s (p : Polynomial F), p.natDegree ≤ d →
      relativeDistance (fun y => M s (y, z₀)) (C s z₀).eval ≤
        relativeDistance (fun y => M s (y, z₀)) p.eval)
    (hsmall : 6 * ε + 2 * ((d : ℚ) / Fintype.card F) < 1 / 2)
    (β : Fin 5 → ℚ) (hmean : ∀ j, (𝔼 s, errors (M s) (R s) (C s) y₀ z₀ j) ≤ β j)
    (a b : F) (hb : ∀ s, (C s z₀).eval y₀ = b)
    (hpoint : fraction (fun s => (R s y₀).eval z₀ ≠ a) ≤ γ)
    (hbudget : (∑ j, β j) / ε + γ < 1) : b = a := by
  have hcross := fraction_disagreement_le hd hq M R C hR hC y₀ z₀ hεpos hε
    hmin hsmall β hmean
  simp only [fraction_ne_eq_relativeDistance, hb] at hcross hpoint
  by_contra hne
  have ht := relativeDistance_triangle (fun _ : S => b) (fun s => (R s y₀).eval z₀)
    (fun _ => a)
  rw [relativeDistance_const, ite_eq_right hne,
    relativeDistance_comm (fun _ : S => b) (fun s => (R s y₀).eval z₀)] at ht
  linarith

end PCP.Algebraic.CandidateCrossing
