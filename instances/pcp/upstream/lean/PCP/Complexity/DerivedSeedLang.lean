import PCP.Complexity.DerivedSeedMaterialize
import PCP.Complexity.DerivedSeedFinish

/-! # Complete construction of the derived-grid callback's stored inputs from one numeric seed -/

namespace PCP.Lang.DerivedSeed

open PCP.Algebraic ThreeColorFullFieldSampling BinaryFieldCode LocalCorrection DerivedGrid

variable {t n m : ℕ} [NeZero t]

theorem Public.materialized {nodes : Fin 5 → OuterBranch.Field t} {ζ : OuterBranch.Field t}
    {h : ℕ} {x : List Bool} {qs : List ℕ} {bs : List Bool} {st : State 300 112}
    (hp : Public (n := n) (m := m) nodes ζ h x qs bs st) :
    Public (n := n) (m := m) nodes ζ h x qs bs (materialize.run st).1 := by
  apply hp.of_eq
  · intro i hi
    apply materialize_reg <;> simp [publicRegs] at hi <;> omega
  · intro L hL
    apply materialize_list <;> simp [publicLists] at hL <;> omega

def program (k : Certificate) : Stmt 300 112 := .seq materialize (finish k)

attribute [local irreducible] materialize finish

/-- Every coordinate, mask, point code and public edge value is computed internally. -/
theorem program_run (k : Certificate) (nodes : Fin 5 → OuterBranch.Field t)
    (ζ : OuterBranch.Field t) (h : ℕ) (hh : h ≤ 2 ^ t) (x : List Bool)
    (s : DerivedGrid.Sample k t n m) (qs : List ℕ) (bs : List Bool) (st : State 300 112)
    (hi : Input k (padDerived s) st) (hp : Public (n := n) (m := m) nodes ζ h x qs bs st) :
    DerivedCall.Context k nodes ζ (firstPoint k s)
      (secondPoint k (FiniteAlphabetIndex.alphabet (fieldEquiv t) hh) s)
      s.2.1.1 s.2.2 (weight k h hh x s) (primaryLocation k s.1)
      (firstSeed k s) (secondSeed k s) qs bs ((program k).run st).1 := by
  have hm := materialize_run k (padDerived s) st hi
  have hp' := hp.materialized
  generalize hu : (materialize.run st).1 = u at *
  have hf := finish_run k nodes ζ h hh x s qs bs u hm.2.2.2.1 hm.2.2.2.2 hp'
    hm.1 hm.2.1 hm.2.2.1
  simpa only [program, run_seq_fst, hu] using hf

end PCP.Lang.DerivedSeed
