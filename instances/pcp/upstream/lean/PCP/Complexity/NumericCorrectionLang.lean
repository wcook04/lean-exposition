import PCP.Complexity.CorrectionContextLang

/-!
# Certificate calls starting from their actual numeric seed

This wrapper materializes the seed and all inner-test inputs, clears the local
query accumulator, and executes the complete weighted corrector. Its result is
an optional bit and the exact ordered physical query trace.
-/

namespace PCP.Lang.NumericCorrection

open PCP.Algebraic ThreeColorSeedIndex ThreeColorFullFieldSampling BinaryFieldCode
open LocalCorrection CorrectionContext

variable {t n m : ℕ} [NeZero t] [NeZero m]

def correct : Stmt 220 96 := CorrectionSeed.call (by decide) (by decide)
  LocalCorrection.program

def program (k : Certificate) : Stmt 220 96 := .seq (CorrectionContext.program k)
  (.seq (.copy 80 49) (.seq (.copy 80 54) correct))

theorem correct_result (st : State 220 96) :
    (outerState (correct.run st).1, (correct.run st).2) =
      LocalCorrection.program.run (outerState st) :=
  CorrectionSeed.call_result (by decide) (by decide) LocalCorrection.program st

attribute [local irreducible] correct CorrectionContext.program

set_option maxRecDepth 8192 in
/-- No callback premise remains: both the optional answer and all physical reads are computed. -/
theorem program_run (k : Certificate) (nodes : Fin 5 → OuterBranch.Field t)
    (ζ : OuterBranch.Field t) (a : k.Point t n) (w : Fin t → ZMod 2)
    (s : k.Seed t n m) (qs : List ℕ) (bs : List Bool) (st : State 220 96)
    (hp : Public (m := m) k nodes ζ a w qs bs st)
    (hi : CorrectionSeed.Input (coordinateCodec k n) (padCall s) st) :
    let value := ComputableDerivedZeroOnGrid.call (BinaryMaterializedField.coordinates t)
      nodes ζ (k.oracle (m := m) qs bs) (k.rows a qs bs) a w s
    let trace := (ComputableBinaryLocalCorrection.queries (BinaryMaterializedField.coordinates t)
      nodes ζ a s.1 s.2.1 s.2.2.1 w s.2.2.2).map (fun q => queryCode (k.physical a q))
    ((program k).run st).1.regs 146 = present value ∧
    ((program k).run st).1.regs 147 = answer value ∧
    ((program k).run st).1.lists 49 = trace.reverse := by
  have hc := CorrectionContext.program_run k nodes ζ a w s qs bs st hp hi
  generalize hu : ((CorrectionContext.program k).run st).1 = u at *
  have hf : OuterBranch.Frame (outerState u) (outerState (setList u 49 [])) := by
    constructor
    · intro i _ _
      rfl
    · intro i _ _ hn
      change Function.update u.lists 49 [] (Fin.castLE (by decide) i) = u.lists _
      apply Function.update_of_ne
      intro h
      apply hn
      have hh := congrArg (fun x : Fin 96 => x.val) h
      exact Fin.ext hh
  have hctx := hc.1.of_frame hf
  have h54 : OuterBranch.Context k.outer nodes ζ (k.sample a w s) qs bs
      (outerState (setList (setList u 49 []) 54 [])) := by
    cases hctx
    constructor <;> assumption
  have hcall := LocalCorrection.program_call k nodes ζ a w s qs bs
    (outerState (setList (setList u 49 []) 54 [])) h54
  rw [← correct_result] at hcall
  simp only [program, run_seq_fst, hu, run_copy_fst, hc.2.2.input.empty,
    setList_lists, Function.update_of_ne (by decide : (80 : Fin 96) ≠ 49)]
  refine ⟨hcall.1, hcall.2.1, ?_⟩
  have hq := hcall.2.2.1
  change (correct.run (setList (setList u 49 []) 54 [])).1.lists 49 = _ ++ [] at hq
  simpa only [List.append_nil] using hq

set_option maxRecDepth 8192 in
/-- Global metadata and history sources beyond the materialization workspace are retained. -/
theorem correct_frame (st : State 220 96) : CorrectionContext.Frame st (correct.run st).1 := by
  unfold correct
  exact ⟨fun i hi => CorrectionSeed.call_reg (by decide) (by decide)
      LocalCorrection.program st i hi,
    fun L hL => CorrectionSeed.call_list (by decide) (by decide)
      LocalCorrection.program st L hL⟩

end PCP.Lang.NumericCorrection
