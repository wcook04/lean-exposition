import PCP.Complexity.CorrectionContextFinalize

/-!
# Complete numeric correction-context construction

Only the raw structural seed code, public field data, requested point and label
are supplied. The program constructs every array needed by the weighted local
corrector, including both inner-test arms and both coordinate directions.
-/

namespace PCP.Lang.CorrectionContext

open PCP.Algebraic ThreeColorSeedIndex ThreeColorFullFieldSampling BinaryFieldCode
open LocalCorrection

variable {t n m : ℕ} [NeZero t]

def materialize (k : Certificate) : Stmt 220 96 := .seq (materializeInner k) (finalize k)

def program (k : Certificate) : Stmt 220 96 := .seq CorrectionSeed.program (materialize k)

attribute [local irreducible] materializeInner finalize CorrectionSeed.program

theorem materialize_frame (k : Certificate) (st : State 220 96) :
    Frame st ((materialize k).run st).1 :=
  (materializeInner_frame k st).trans (finalize_frame k _)

theorem materialize_run (k : Certificate) (nodes : Fin 5 → OuterBranch.Field t)
    (ζ : OuterBranch.Field t) (a : k.Point t n) (w : Fin t → ZMod 2)
    (s : k.Seed t n m) (qs : List ℕ) (bs : List Bool) (st : State 220 96)
    (hp : Public (m := m) k nodes ζ a w qs bs st) (hl : Loaded k s st) :
    OuterBranch.Context k.outer nodes ζ (k.sample a w s) qs bs
      (outerState ((materialize k).run st).1) ∧ Frame st ((materialize k).run st).1 := by
  have hi := materializeInner_run k nodes ζ a w s qs bs st hp hl
  have hp' := hp.of_frame hi.2.2.2.2
  have hl' := hl.of_frame hi.2.2.2.2
  generalize hu : ((materializeInner k).run st).1 = u at *
  refine ⟨?_, materialize_frame k st⟩
  simpa only [materialize, run_seq_fst, hu] using
    finalize_run k nodes ζ a w s qs bs u hp' hl' hi.1 hi.2.1 hi.2.2.1 hi.2.2.2.1

theorem Public.materialized {k : Certificate} {nodes : Fin 5 → OuterBranch.Field t}
    {ζ : OuterBranch.Field t} {a : k.Point t n} {w : Fin t → ZMod 2}
    {qs : List ℕ} {bs : List Bool} {st : State 220 96}
    (h : Public (m := m) k nodes ζ a w qs bs st) :
    Public (m := m) k nodes ζ a w qs bs (CorrectionSeed.program.run st).1 := by
  constructor
  all_goals first
    | exact (CorrectionSeed.program_reg st _ (by decide)).trans h.vertices
    | exact (CorrectionSeed.program_reg st _ (by decide)).trans h.pairs
    | exact (CorrectionSeed.program_reg st _ (by decide)).trans h.proper
    | exact (CorrectionSeed.program_reg st _ (by decide)).trans h.inner
    | exact (CorrectionSeed.program_reg st _ (by decide)).trans h.affineLabels
    | exact (CorrectionSeed.program_reg st _ (by decide)).trans h.cubicLabels
    | exact (CorrectionSeed.program_reg st _ (by decide)).trans h.root
    | exact (CorrectionSeed.program_reg st _ (by decide)).trans h.pointCode
    | exact (CorrectionSeed.program_list st _ (by decide)).trans h.point
    | exact (CorrectionSeed.program_list st _ (by decide)).trans h.label
    | exact (CorrectionSeed.program_list st _ (by decide)).trans h.modulus
    | exact (CorrectionSeed.program_list st _ (by decide)).trans h.nodes
    | exact (CorrectionSeed.program_list st _ (by decide)).trans h.history
    | exact (CorrectionSeed.program_list st _ (by decide)).trans h.answers

/-- The actual raw call code constructs the complete protected semantic context. -/
theorem program_run (k : Certificate) (nodes : Fin 5 → OuterBranch.Field t)
    (ζ : OuterBranch.Field t) (a : k.Point t n) (w : Fin t → ZMod 2)
    (s : k.Seed t n m) (qs : List ℕ) (bs : List Bool) (st : State 220 96)
    (hp : Public (m := m) k nodes ζ a w qs bs st)
    (hi : CorrectionSeed.Input (coordinateCodec k n) (padCall s) st) :
    OuterBranch.Context k.outer nodes ζ (k.sample a w s) qs bs
      (outerState ((program k).run st).1) ∧
    Public (m := m) k nodes ζ a w qs bs ((program k).run st).1 ∧
    Loaded k s ((program k).run st).1 := by
  have hs := CorrectionSeed.program_run (coordinateCodec k n) (padCall s) st hi
  have hl : Loaded k s (CorrectionSeed.program.run st).1 :=
    ⟨hs.1, hs.2.1, hs.2.2.1, hs.2.2.2⟩
  have hp' := hp.materialized
  generalize hu : (CorrectionSeed.program.run st).1 = u at *
  have hm := materialize_run k nodes ζ a w s qs bs u hp' hl
  simp only [program, run_seq_fst, hu]
  exact ⟨hm.1, hp'.of_frame hm.2, hl.of_frame hm.2⟩

end PCP.Lang.CorrectionContext
