module

public import QuarticQuery.LowerBound.RealizedCaps

/-!
# Exact finite pushforward of an external random seed

Compiled as part of the `QuarticQuery` library target.
This module proves algebraic pushforward results for *finite* seed spaces. The
arbitrary measurable seed case requires the measurable finite-table compiler
and a measure-theoretic identification of its fiber weights; that latter
bridge is proved in the ordinary note but NOT established by this Lean file.
-/

@[expose] public section

open Finset

namespace QuarticQuery

/-- The exact mass of the fiber of a map from a finite source to a finite
behavior table. Source weights need not be rational or independent factors. -/
noncomputable def finitePushforwardWeight {Ω S : Type}
    [Fintype Ω] [Fintype S] [DecidableEq S]
    (w : Ω → ℝ) (φ : Ω → S) (s : S) : ℝ :=
  ∑ ω, if φ ω = s then w ω else 0

/-- Exact disjoint-fiber partition identity. -/
theorem finitePushforward_sum {Ω S : Type}
    [Fintype Ω] [Fintype S] [DecidableEq S]
    (w : Ω → ℝ) (φ : Ω → S) :
    ∑ s, finitePushforwardWeight w φ s = ∑ ω, w ω := by
  classical
  simp only [finitePushforwardWeight]
  rw [sum_comm]
  simp

/-- Fiber weights are nonnegative when the source weights are. -/
theorem finitePushforward_nonneg {Ω S : Type}
    [Fintype Ω] [Fintype S] [DecidableEq S]
    (w : Ω → ℝ) (φ : Ω → S) (hw : ∀ ω, 0 ≤ w ω)
    (s : S) : 0 ≤ finitePushforwardWeight w φ s := by
  unfold finitePushforwardWeight
  exact sum_nonneg fun ω _ => by split_ifs <;> [exact hw ω; exact le_refl 0]

/-- The output law after identifying seed values with the same finite
behavior is preserved *exactly*, without approximate mixture weights. -/
theorem finitePushforward_expectation {Ω S : Type}
    [Fintype Ω] [Fintype S] [DecidableEq S]
    (w : Ω → ℝ) (φ : Ω → S) (F : S → ℝ) :
    ∑ ω, w ω * F (φ ω) =
      ∑ s, finitePushforwardWeight w φ s * F s := by
  classical
  simp only [finitePushforwardWeight, sum_mul]
  rw [sum_comm]
  apply sum_congr rfl
  intro ω _
  simp

end QuarticQuery
