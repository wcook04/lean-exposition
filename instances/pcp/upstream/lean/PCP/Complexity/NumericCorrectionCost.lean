/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Complexity.NumericCorrectionLang
import PCP.Complexity.CorrectionContextCost

/-! # Polynomial charged cost of a complete numeric weighted-correction call -/

namespace PCP.Lang.NumericCorrection

open PCP.Algebraic ThreeColorSeedIndex ThreeColorFullFieldSampling BinaryFieldCode
open LocalCorrection CorrectionContext
-- Fixed state restrictions pass through both protected list resets.
set_option maxRecDepth 2048

variable {t n m : ℕ} [NeZero t] [NeZero m]

attribute [local irreducible] correct CorrectionContext.program LocalCorrection.program
  LocalCorrection.costConstant

def sourceWidth (t n m : ℕ) (qs : List ℕ) (bs : List Bool) : ℕ :=
  OuterBranch.storedWidth t n m qs bs [] + QueryAddress.width t n m 4

def outerCallCost (k : OuterBranch.Kind) (t n m : ℕ) (qs : List ℕ) (bs : List Bool) : ℕ :=
  LocalCorrection.costConstant *
    (32*(t+4*m+k.dimension n+2^t+sourceWidth t n m qs bs+20))^9

def callCost (k : Certificate) (t n m : ℕ) (qs : List ℕ) (bs : List Bool) : ℕ :=
  outerCallCost k.outer t n m qs bs

omit [NeZero m] in
theorem lifted_stored (k : OuterBranch.Kind) (nodes : Fin 5 → OuterBranch.Field t)
    (ζ : OuterBranch.Field t) (s : OuterBranch.Sample k t n m)
    (qs : List ℕ) (bs : List Bool) (st : State 180 80)
    (hc : OuterBranch.Context k nodes ζ s qs bs st) (hs : st.lists 54 = []) :
    OuterBranch.StoredBound (sourceWidth t n m qs bs) st := by
  have hb := hc.storedBound k nodes ζ s qs bs st
  rw [hs] at hb
  have hW : OuterBranch.storedWidth t n m qs bs [] ≤ sourceWidth t n m qs bs :=
    Nat.le_add_right _ _
  exact ⟨fun i hi hu => (hb.regs i hi hu).trans hW,
    fun L hL hu hn => (hb.lists L hL hu hn).trans hW⟩

theorem empty_budget (k : OuterBranch.Kind) (t n m W : ℕ) (st : State 180 80)
    (hq : st.lists 49 = []) : LocalCorrection.budget k t n m W st =
      32*(t+4*m+k.dimension n+2^t+W+20) := by
  simp only [LocalCorrection.budget, hq,
    show listSize ([] : List ℕ) = 0 from rfl, Nat.add_zero]

/-- Work with an arbitrary outer sample before specializing its dependent point type. -/
theorem outer_cost (k : OuterBranch.Kind) (nodes : Fin 5 → OuterBranch.Field t)
    (ζ : OuterBranch.Field t) (s : OuterBranch.Sample k t n m)
    (qs : List ℕ) (bs : List Bool) (st : State 180 80)
    (hc : OuterBranch.Context k nodes ζ s qs bs st)
    (hq : st.lists 49 = []) (hs : st.lists 54 = []) :
    (LocalCorrection.program.run st).2 ≤ outerCallCost k t n m qs bs := by
  have hb := lifted_stored k nodes ζ s qs bs st hc hs
  have hqW : QueryAddress.width t n m 4 ≤ sourceWidth t n m qs bs := Nat.le_add_left _ _
  have h := LocalCorrection.program_cost k nodes ζ s qs bs _ st hc hb
    (BranchQueryBounds.correction _ _ _ _ hqW)
  unfold outerCallCost
  exact h.trans_eq (congrArg (fun b => LocalCorrection.costConstant * b^9)
    (empty_budget k t n m _ st hq))

theorem correct_cost (k : Certificate) (nodes : Fin 5 → OuterBranch.Field t)
    (ζ : OuterBranch.Field t) (a : k.Point t n) (w : Fin t → ZMod 2)
    (s : k.Seed t n m) (qs : List ℕ) (bs : List Bool) (st : State 220 96)
    (hc : OuterBranch.Context k.outer nodes ζ (k.sample a w s) qs bs (outerState st))
    (hq : st.lists 49 = []) (hs : st.lists 54 = []) :
    (correct.run st).2 ≤ callCost k t n m qs bs := by
  have h := outer_cost k.outer nodes ζ (k.sample a w s) qs bs (outerState st) hc hq hs
  rw [← correct_result] at h
  exact h

/-- Explicit polynomial source/history budget, with arbitrary initial scratch. -/
def programCost (k : Certificate) (t n m W : ℕ) (qs : List ℕ) (bs : List Bool) : ℕ :=
  CorrectionContext.programCost k t n m W qs bs + callCost k t n m qs bs + 5

theorem program_cost (k : Certificate) (nodes : Fin 5 → OuterBranch.Field t)
    (ζ : OuterBranch.Field t) (a : k.Point t n) (w : Fin t → ZMod 2)
    (s : k.Seed t n m) (qs : List ℕ) (bs : List Bool) (W : ℕ) (st : State 220 96)
    (hp : Public (m := m) k nodes ζ a w qs bs st)
    (hi : CorrectionSeed.Input (coordinateCodec k n) (padCall s) st)
    (hb : SourceBound W st) :
    ((program k).run st).2 ≤ programCost k t n m W qs bs := by
  have hload := CorrectionContext.program_cost k nodes ζ a w s qs bs W st hp hi hb
  have hout := CorrectionContext.program_run k nodes ζ a w s qs bs st hp hi
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
      exact Fin.ext (congrArg (fun x : Fin 96 => x.val) h)
  have hc := hout.1.of_frame hf
  have hclear : OuterBranch.Context k.outer nodes ζ (k.sample a w s) qs bs
      (outerState (setList (setList u 49 []) 54 [])) := by
    cases hc
    constructor <;> assumption
  have hcall := correct_cost k nodes ζ a w s qs bs _ hclear
    (by simp [setList, Function.update]) (by simp [setList, Function.update])
  simp only [program, run_seq_snd, hu, run_copy_snd, run_copy_fst, hout.2.2.input.empty,
    setList_lists, Function.update_of_ne (by decide : (80 : Fin 96) ≠ 49),
    show listSize ([] : List ℕ) = 0 from rfl]
  unfold programCost
  omega

end PCP.Lang.NumericCorrection
