module

public import QuarticQuery.LowerBound.Planted.ZeroSearch

/-!
# Heavy columns (equation 20)

A column is heavy on a run if the run makes more than `L` queries in total to its
strings `A_{i,1}, …, A_{i,r}`. A run of `G` queries has at most `G / L` heavy
columns, and `I` is independent of the run. The bound holds run by run.
-/

@[expose] public section

open Finset

namespace QuarticQuery

variable {κ : Type} [DecidableEq κ] {ℓ r S : ℕ}

/-- Queries of the location list `l` to the strings of column `i`. -/
def aQueries (i : Column ℓ) (l : List (BitLoc ℓ r S κ)) : ℕ :=
  l.countP fun q => (aTarget i q).isSome

/-- Each query is charged to at most one column. -/
theorem sum_aQueries_le (l : List (BitLoc ℓ r S κ)) : ∑ i : Column ℓ, aQueries i l ≤ l.length := by
  refine sum_countP_le_length (γ := Column ℓ)
    (fun i (q : BitLoc ℓ r S κ) => (aTarget i q).isSome) (fun a b q ha hb => ?_) l
  rcases q with q | ⟨c, h, q⟩ | q
  · simp [aTarget] at ha
  · have h1 : c = a := by
      by_contra hne
      simp [aTarget, hne] at ha
    have h2 : c = b := by
      by_contra hne
      simp [aTarget, hne] at hb
    exact h1.symm.trans h2
  · simp [aTarget] at ha

/-- Ledger: eq-20. `Pr(I is heavy) ≤ G / (m L)`, for a fixed run of length at most
`G`. -/
theorem avg_heavy_le {L G : ℕ} (hL : 1 ≤ L) (l : List (BitLoc ℓ r S κ)) (hl : l.length ≤ G) :
    avg (unif ℓ) (fun I => ind (L < aQueries I l)) ≤
      (G : ℝ) / (((2 ^ ℓ : ℕ) : ℝ) * (L : ℝ)) := by
  have hm := colCard_pos ℓ
  have hL0 : (0 : ℝ) < L := by exact_mod_cast hL
  have hcount : (L : ℝ) * ∑ I : Column ℓ, ind (L < aQueries I l) ≤ (G : ℝ) := by
    rw [mul_sum]
    calc ∑ I : Column ℓ, (L : ℝ) * ind (L < aQueries I l)
        ≤ ∑ I : Column ℓ, (aQueries I l : ℝ) := sum_le_sum fun I _ => by
          by_cases h : L < aQueries I l
          · rw [ind_true h, mul_one]
            exact_mod_cast h.le
          · rw [ind_false h, mul_zero]
            positivity
      _ ≤ (G : ℝ) := by
          have : (∑ I : Column ℓ, aQueries I l : ℕ) ≤ G := (sum_aQueries_le l).trans hl
          exact_mod_cast this
  rw [avg_unif, le_div_iff₀ (by positivity)]
  set M : ℝ := ((2 ^ ℓ : ℕ) : ℝ)
  have : 1 / M * ∑ I : Column ℓ, ind (L < aQueries I l) * (M * (L : ℝ)) =
      1 / M * ∑ I : Column ℓ, ind (L < aQueries I l) * (M * (L : ℝ)) := rfl
  calc 1 / M * (∑ I : Column ℓ, ind (L < aQueries I l)) * (M * (L : ℝ))
      = (L : ℝ) * ∑ I : Column ℓ, ind (L < aQueries I l) := by field_simp
    _ ≤ (G : ℝ) := hcount

end QuarticQuery
