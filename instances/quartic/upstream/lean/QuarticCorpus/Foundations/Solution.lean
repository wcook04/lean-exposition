module

public import QuarticQuery.Statement
import QuarticQuery.Model.Quantum

/-!
# Foundations bundle

The complexities are attained minima with the expected order, renaming coordinates
is free, and a lower bound on `R` is exactly the absence of a program at that
budget. Everything later rests on these facts about `sInf`.
-/

public section

namespace QuarticQuery.Checked

-- CHALLENGE-BEGIN
theorem R_le_iff {ι : Type} [Fintype ι] (f : PartialBool ι) (t : ℕ) : R f ≤ t ↔ RLe f t := by
  -- proof
  exact QuarticQuery.R_le_iff

theorem Q_le_iff {ι : Type} [Fintype ι] (f : PartialBool ι) (t : ℕ) : Q f ≤ t ↔ QLe f t := by
  -- proof
  exact QuarticQuery.Q_le_iff

theorem D_le_iff {ι : Type} [Fintype ι] (f : PartialBool ι) (t : ℕ) : D f ≤ t ↔ DLe f t := by
  -- proof
  exact QuarticQuery.D_le_iff

theorem R_le_D {ι : Type} [Fintype ι] (f : PartialBool ι) : R f ≤ D f := by
  -- proof
  exact QuarticQuery.R_le_D f

theorem Q_le_D {ι : Type} [Fintype ι] (f : PartialBool ι) : Q f ≤ D f := by
  -- proof
  exact QuarticQuery.Q_le_D f

theorem D_le_card {ι : Type} [Fintype ι] (f : PartialBool ι) : D f ≤ Fintype.card ι := by
  -- proof
  exact QuarticQuery.D_le_card f

theorem R_reindex {ι κ : Type} [Fintype ι] [Fintype κ] (e : ι ≃ κ) (f : PartialBool ι) :
    R (reindex e f) = R f := by
  -- proof
  exact QuarticQuery.R_reindex e f

theorem Q_reindex {ι κ : Type} [Fintype ι] [Fintype κ] (e : ι ≃ κ) (f : PartialBool ι) :
    Q (reindex e f) = Q f := by
  -- proof
  exact QuarticQuery.Q_reindex e f
-- CHALLENGE-END

end QuarticQuery.Checked
