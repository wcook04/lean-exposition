/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Complexity.CorrectionContextLang
import PCP.Complexity.CorrectionSeedMaterializationCost
import PCP.Complexity.InnerSeedCost
import PCP.Complexity.OuterStoredBounds

/-! # Protected numeric resources for the complete correction-context loader -/

namespace PCP.Lang.CorrectionContext

open PCP.Algebraic ThreeColorSeedIndex ThreeColorFullFieldSampling BinaryFieldCode
open LocalCorrection

variable {t n m : ℕ} [NeZero t]

attribute [local irreducible] CorrectionSeed.program

structure PublicBound (W : ℕ) (st : State 220 96) : Prop where
  regs : ∀ i : Fin 220, 212 ≤ i.val → Nat.size (st.regs i) ≤ W
  lists : ∀ L : Fin 96, 83 ≤ L.val → L.val < 89 → listSize (st.lists L) ≤ W

structure SourceBound (W : ℕ) (st : State 220 96) : Prop where
  seed : CorrectionSeed.SourceBound W st
  payload : PublicBound W st

structure LoadedBound (W : ℕ) (st : State 220 96) : Prop where
  regs : ∀ i : Fin 220, 200 ≤ i.val → i ≠ 209 → i ≠ 210 → i ≠ 211 →
    Nat.size (st.regs i) ≤ W
  lists : ∀ L : Fin 96, 80 ≤ L.val → L.val < 89 → listSize (st.lists L) ≤ W

theorem PublicBound.of_frame {W : ℕ} {st out : State 220 96}
    (hb : PublicBound W st) (hf : Frame st out) : PublicBound W out :=
  ⟨fun i hi => by rw [hf.regs i (by omega)]; exact hb.regs i hi,
    fun L hL hu => by rw [hf.lists L (by omega)]; exact hb.lists L hL hu⟩

theorem LoadedBound.of_frame {W : ℕ} {st out : State 220 96}
    (hb : LoadedBound W st) (hf : Frame st out) : LoadedBound W out :=
  ⟨fun i hi h9 h10 h11 => by rw [hf.regs i (by omega)]; exact hb.regs i hi h9 h10 h11,
    fun L hL hu => by rw [hf.lists L hL]; exact hb.lists L hL hu⟩

def loadedWidth (d t m W : ℕ) : ℕ := W + (d + 4 * m) * (t + 1) + 1

/-- The seed loader initializes every newly charged component and both vector arrays. -/
theorem source_loaded (k : Certificate)
    (s : k.Seed t n m) (W : ℕ) (st : State 220 96)
    (hi : CorrectionSeed.Input (coordinateCodec k n) (padCall s) st)
    (hb : SourceBound W st) :
    LoadedBound (loadedWidth (k.outer.dimension n) t m W) (CorrectionSeed.program.run st).1 := by
  have hseed := hb.seed.program
  have hdata := CorrectionSeed.program_dataBound (coordinateCodec k n) (padCall s) W st hi hb.seed
  have hpub : PublicBound W (CorrectionSeed.program.run st).1 :=
    ⟨fun i hi => by rw [CorrectionSeed.program_reg st i hi]; exact hb.payload.regs i hi,
      fun L hL hu => by
        rw [CorrectionSeed.program_list st L hL]
        exact hb.payload.lists L hL hu⟩
  have harrays := CorrectionSeed.program_lists_size (coordinateCodec k n) (padCall s) st hi
  have hempty := (CorrectionSeed.program_run (coordinateCodec k n) (padCall s) st hi).1.empty
  have hW : W ≤ loadedWidth (k.outer.dimension n) t m W := by unfold loadedWidth; omega
  constructor
  · intro i h200 h209 h210 h211
    have he : i = 200 ∨ i = 201 ∨ i = 202 ∨ i = 203 ∨ i = 204 ∨ i = 205 ∨
        i = 206 ∨ i = 207 ∨ i = 208 ∨ 212 ≤ i.val := by omega
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | hpubi
    · exact (hseed 0).trans hW
    · exact (hseed 1).trans hW
    · exact (hseed 2).trans hW
    · exact (hseed 3).trans hW
    · exact (hdata 0).trans hW
    · exact (hdata 1).trans hW
    · exact (hdata 2).trans hW
    · exact (hdata 3).trans hW
    · exact (hseed 4).trans hW
    · exact (hpub.regs i hpubi).trans hW
  · intro L hL hu
    have he : L = 80 ∨ L = 81 ∨ L = 82 ∨ 83 ≤ L.val := by omega
    rcases he with rfl | rfl | rfl | hpubL
    · rw [hempty]
      exact Nat.zero_le _
    · exact harrays.1.trans (by
        change (k.outer.dimension n) * (t + 1) ≤ _
        unfold loadedWidth
        nlinarith only [Nat.zero_le (4 * m * (t + 1)), Nat.zero_le W])
    · exact harrays.2.trans (by
        unfold loadedWidth
        nlinarith only [Nat.zero_le (k.outer.dimension n * (t + 1)), Nat.zero_le W])
    · exact (hpub.lists L hpubL hu).trans hW

/-- Generic bound for fixed loaders that only read the initialized protected block. -/
def fixedConstant (p : Stmt 220 96) : ℕ := p.C * (p.width + p.csize + 1)

theorem loaded_cost (p : Stmt 220 96) (hp : p.loopFree = true)
    (hr : ∀ i ∈ p.uses, 200 ≤ i.val ∧ i ≠ 209 ∧ i ≠ 210 ∧ i ≠ 211)
    (hl : ∀ L ∈ p.lUses, 80 ≤ L.val ∧ L.val < 89)
    (W : ℕ) (st : State 220 96) (hb : LoadedBound W st) :
    (p.run st).2 ≤ fixedConstant p * (W + 1) := by
  apply loopFree_cost_le p hp st W
  · intro i hi
    exact hb.regs i (hr i hi).1 (hr i hi).2.1 (hr i hi).2.2.1 (hr i hi).2.2.2
  · intro L hL
    exact hb.lists L (hl L hL).1 (hl L hL).2

end PCP.Lang.CorrectionContext
