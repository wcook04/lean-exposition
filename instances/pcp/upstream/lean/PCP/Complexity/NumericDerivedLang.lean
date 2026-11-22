import PCP.Complexity.DerivedSeedLang
import PCP.Complexity.DerivedGridSemantics

/-!
# Complete numeric derived-grid branch

The single numeric seed is decoded, all words are materialized, both actual grid
points and the public edge weight are computed, and the three checked query
segments execute against the same physical history.
-/

namespace PCP.Lang.NumericDerived

open PCP.Algebraic ThreeColorFullFieldSampling BinaryFieldCode LocalCorrection DerivedGrid

variable {t n m : ℕ} [NeZero t] [NeZero m]

def program (k : Certificate) : Stmt 300 112 :=
  .seq (DerivedSeed.program k) (DerivedCall.program (weighted k) k)

attribute [local irreducible] DerivedSeed.program DerivedCall.program

set_option maxRecDepth 8192 in
/-- Complete physical trace and original optional-answer verdict, from actual stored source data. -/
theorem program_run (k : Certificate) (nodes : Fin 5 → OuterBranch.Field t)
    (ζ : OuterBranch.Field t) (h : ℕ) (hh : h ≤ 2 ^ t) (x : List Bool)
    (s : DerivedGrid.Sample k t n m) (qs : List ℕ) (bs : List Bool) (st : State 300 112)
    (hi : DerivedSeed.Input k (padDerived s) st)
    (hp : DerivedSeed.Public (n := n) (m := m) nodes ζ h x qs bs st) :
    let H := FiniteAlphabetIndex.alphabet (fieldEquiv t) hh
    let w := DerivedSeed.weight k h hh x s
    ((program k).run st).1.regs 275 = (decision k nodes ζ H w s qs bs).toNat ∧
    ((program k).run st).1.lists 110 = queries k nodes ζ H w s := by
  have hl := DerivedSeed.program_run k nodes ζ h hh x s qs bs st hi hp
  generalize hu : ((DerivedSeed.program k).run st).1 = u at *
  have hrun := DerivedCall.program_run (weighted k) k nodes ζ (firstPoint k s)
    (secondPoint k (FiniteAlphabetIndex.alphabet (fieldEquiv t) hh) s) s.2.1.1 s.2.2
    (DerivedSeed.weight k h hh x s) (primaryLocation k s.1) (firstSeed k s) (secondSeed k s)
    qs bs u hl
  simp only [program, run_seq_fst, hu]
  exact ⟨hrun.1, hrun.2.1.trans (queries_parts k nodes ζ _ _ s).symm⟩

end PCP.Lang.NumericDerived
