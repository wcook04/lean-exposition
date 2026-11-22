/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Complexity.DerivedSeedCost
import PCP.Complexity.DerivedSeedOutputBound
import PCP.Complexity.DerivedCallCost
import PCP.Complexity.NumericDerivedLang

/-! # Complete numeric derived-grid branch runtime -/

namespace PCP.Lang.NumericDerived

open PCP.Algebraic ThreeColorFullFieldSampling BinaryFieldCode LocalCorrection DerivedGrid

attribute [local irreducible] DerivedSeed.program DerivedCall.program

def programCost (C : ℕ) (k : Certificate) (t n m h W : ℕ)
    (x : List Bool) (qs : List ℕ) (bs : List Bool) : ℕ :=
  DerivedSeed.programCost C k t n m h W x+
    DerivedCall.programCost k t n m (DerivedSeed.outputWidth t n m W) qs bs+1

set_option maxRecDepth 8192 in
/-- Actual numeric seed decoding, field computations, label transforms and physical reads. -/
theorem program_cost : ∃ C : ℕ, ∀ (t n m : ℕ) [NeZero t] [NeZero m] (k : Certificate)
    (nodes : Fin 5 → OuterBranch.Field t) (ζ : OuterBranch.Field t)
    (h : ℕ) (_hh : h ≤ 2 ^ t) (x : List Bool) (s : DerivedGrid.Sample k t n m)
    (qs : List ℕ) (bs : List Bool) (W : ℕ) (st : State 300 112),
    DerivedSeed.Input k (padDerived s) st →
    DerivedSeed.Public (n := n) (m := m) nodes ζ h x qs bs st →
    DerivedSeed.SourceBound W st →
    ((program k).run st).2 ≤ programCost C k t n m h W x qs bs := by
  obtain ⟨C, hC⟩ := DerivedSeed.program_cost
  refine ⟨C, ?_⟩
  intro t n m _ _ k nodes ζ h hh x s qs bs W st hi hp hb
  have hs := hC t n m k nodes ζ h hh x s qs bs W st hi hp hb
  have hc := DerivedSeed.program_run k nodes ζ h hh x s qs bs st hi hp
  have hout := DerivedSeed.program_output_bound k nodes ζ h hh x s qs bs st W hi hp hb
  generalize hu : ((DerivedSeed.program k).run st).1 = u at *
  have hd := DerivedCall.program_cost (weighted k) k nodes ζ (firstPoint k s)
    (secondPoint k (FiniteAlphabetIndex.alphabet (fieldEquiv t) hh) s) s.2.1.1 s.2.2
    (DerivedSeed.weight k h hh x s) (primaryLocation k s.1) (firstSeed k s) (secondSeed k s)
    qs bs (DerivedSeed.outputWidth t n m W) u hc hout
  simp only [program, run_seq_snd, hu]
  unfold programCost
  omega

end PCP.Lang.NumericDerived
