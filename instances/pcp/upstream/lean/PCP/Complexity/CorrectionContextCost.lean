/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Complexity.CorrectionContextInnerCost
import PCP.Complexity.CorrectionContextFinalizeCost

/-! # Complete charged cost of numeric correction-context materialization -/

namespace PCP.Lang.CorrectionContext

open PCP.Algebraic ThreeColorSeedIndex ThreeColorFullFieldSampling BinaryFieldCode
open LocalCorrection
variable {t n m : ℕ} [NeZero t]

attribute [local irreducible] CorrectionSeed.program materializeInner finalize

def materializeCost (k : Certificate) (t n m W : ℕ) (qs : List ℕ) (bs : List Bool) : ℕ :=
  innerCost k t m W +
    fixedConstant (finalize k) * (OuterBranch.storedWidth t n m qs bs [] + 1) + 1

theorem materialize_cost (k : Certificate) (nodes : Fin 5 → OuterBranch.Field t)
    (ζ : OuterBranch.Field t) (a : k.Point t n) (w : Fin t → ZMod 2)
    (s : k.Seed t n m) (qs : List ℕ) (bs : List Bool) (W : ℕ) (st : State 220 96)
    (hp : Public (m := m) k nodes ζ a w qs bs st) (hl : Loaded k s st)
    (hb : LoadedBound W st) :
    ((materialize k).run st).2 ≤ materializeCost k t n m W qs bs := by
  have hi := materializeInner_cost k nodes ζ a w s qs bs W st hp hl hb
  have hc := (materialize_run k nodes ζ a w s qs bs st hp hl).1
  simp only [materialize, run_seq_fst] at hc
  have hf := finalize_cost k nodes ζ a w s qs bs _ hc
  simp only [materialize, run_seq_snd]
  unfold materializeCost
  omega

/-- An explicit polynomial expression in the actual source and history sizes. -/
def programCost (k : Certificate) (t n m W : ℕ) (qs : List ℕ) (bs : List Bool) : ℕ :=
  CorrectionSeed.costConstant *
    (k.outer.dimension n + 4*m + t +
      CorrectionSeed.radixBound (k.outer.dimension n) m t + W + 10)^4 +
    materializeCost k t n m (loadedWidth (k.outer.dimension n) t m W) qs bs + 1

/-- Raw numeric seed, point, label and field data suffice; scratch is unrestricted. -/
theorem program_cost (k : Certificate) (nodes : Fin 5 → OuterBranch.Field t)
    (ζ : OuterBranch.Field t) (a : k.Point t n) (w : Fin t → ZMod 2)
    (s : k.Seed t n m) (qs : List ℕ) (bs : List Bool) (W : ℕ) (st : State 220 96)
    (hp : Public (m := m) k nodes ζ a w qs bs st)
    (hi : CorrectionSeed.Input (coordinateCodec k n) (padCall s) st)
    (hb : SourceBound W st) :
    ((program k).run st).2 ≤ programCost k t n m W qs bs := by
  have hs := CorrectionSeed.program_cost (coordinateCodec k n) (padCall s) W st hi hb.seed
  have hout := CorrectionSeed.program_run (coordinateCodec k n) (padCall s) st hi
  have hl : Loaded k s (CorrectionSeed.program.run st).1 :=
    ⟨hout.1, hout.2.1, hout.2.2.1, hout.2.2.2⟩
  have hm := materialize_cost k nodes ζ a w s qs bs _ _ hp.materialized hl
    (source_loaded k s W st hi hb)
  simp only [program, run_seq_snd]
  change (CorrectionSeed.program.run st).2 ≤ _ at hs
  unfold programCost
  dsimp only [coordinateCodec] at hs
  omega

end PCP.Lang.CorrectionContext
