/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Complexity.DerivedSeedPointsCost
import PCP.Complexity.DerivedSeedEdgeCost
import PCP.Complexity.DerivedSeedMaterializeCost
import PCP.Complexity.DerivedSeedLang

/-! # Joining the actual derived-seed preparation costs -/

namespace PCP.Lang.DerivedSeed

open PCP.Algebraic ThreeColorSeedIndex ThreeColorFullFieldSampling BinaryFieldCode
open LocalCorrection DerivedGrid
variable {t n m : ℕ} [NeZero t]

attribute [local irreducible] points encode edge computed

theorem encodePoints_cost (k : Certificate) (h : ℕ) (hh : h ≤ 2 ^ t)
    (s : DerivedGrid.Sample k t n m) (st : State 300 112)
    (ht : st.regs 240 = t) (hq : st.regs 243 = 2 ^ t) (hcount : st.regs 279 = h)
    (hm : st.lists 101 = BinaryField.encode (BinaryWordMaterialization.modulus t))
    (he : st.lists 100 = [])
    (hx : st.lists 109 = List.ofFn (fun i => (fieldEquiv t (s.1 i)).val)) :
    (encodePoints.run st).2 ≤
      pointsCost (baseDimension k n) t h+2*encodeCost (k.outer.dimension n) t+2 := by
  have hp := points_cost k h hh s st ht hcount hm he hx
  have ho := points_run k h hh s st ht hcount hm he hx
  have hpq := (points_reg st 243 (by decide)).trans hq
  generalize hu : (points.run st).1 = u at *
  have ha := encode_cost k (firstPoint k s) 103 246 u hpq ho.1
  have haq := (encode_reg 103 246 243 (by decide) (by decide) u).trans hpq
  have hab := (encode_list 103 104 246 (by decide) u).trans ho.2
  generalize hv : ((encode 103 246).run u).1 = v at *
  have hb := encode_cost k (secondPoint k (FiniteAlphabetIndex.alphabet (fieldEquiv t) hh) s)
    104 247 v haq hab
  simp only [encodePoints, run_seq_snd, hu, hv]
  omega

theorem SourceBound.materialize {W : ℕ} {st : State 300 112} (hb : SourceBound W st) :
    SourceBound W (materialize.run st).1 := by
  constructor
  · intro i
    rw [materialize_reg st (inputPort i) (by fin_cases i <;> decide)
      (by fin_cases i <;> decide) (by fin_cases i <;> decide) (by fin_cases i <;> decide)
      (by fin_cases i <;> decide) (by fin_cases i <;> decide) (by fin_cases i <;> decide)]
    exact hb.input i
  · intro i hi
    rw [materialize_reg st i (by simp [publicRegs] at hi; omega)
      (by simp [publicRegs] at hi; omega) (by simp [publicRegs] at hi; omega)
      (by simp [publicRegs] at hi; omega) (by simp [publicRegs] at hi; omega)
      (by simp [publicRegs] at hi; omega) (by simp [publicRegs] at hi; omega)]
    exact hb.regs i hi
  · intro L hL
    rw [materialize_list st L (by simp [publicLists] at hL; omega)
      (by simp [publicLists] at hL; omega) (by simp [publicLists] at hL; omega)
      (by simp [publicLists] at hL; omega)]
    exact hb.lists L hL

theorem SourceBound.computed {k : Certificate} {W : ℕ} {st : State 300 112}
    (hb : SourceBound W st) : SourceBound W ((computed k).run st).1 := by
  constructor
  · intro i
    rw [computed_reg k st (inputPort i) (by fin_cases i <;> decide)
      (by fin_cases i <;> decide) (by fin_cases i <;> decide) (by fin_cases i <;> decide)]
    exact hb.input i
  · intro i hi
    rw [computed_reg k st i (by simp [publicRegs] at hi; omega)
      (by simp [publicRegs] at hi; omega) (by simp [publicRegs] at hi; omega)
      (by simp [publicRegs] at hi; omega)]
    exact hb.regs i hi
  · intro L hL
    rw [computed_list k st L (by simp [publicLists] at hL; omega)
      (by simp [publicLists] at hL; omega) (by simp [publicLists] at hL; omega)]
    exact hb.lists L hL

theorem payload_cost (k : Certificate) (W : ℕ) (st : State 300 112)
    (hb : SourceBound W st) (hd : DataBound W st) :
    ((payload k).run st).2 ≤ fixedConstant (payload k)*(W+1) := by
  apply loopFree_cost_le (payload k) (by cases k <;> decide) st W
  · intro i hi
    have he : i = 256 ∨ i = 250 ∨ i = 251 ∨ i = 252 ∨ i = 253 ∨
        i = 254 ∨ i = 255 ∨ i = 259 := by
      cases k <;> simp [payload, Stmt.uses, Stmt.mustW, Expr.uses] at hi <;> tauto
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hb.input 2
    · exact hb.regs 250 (by simp [publicRegs])
    · exact hb.regs 251 (by simp [publicRegs])
    · exact hb.regs 252 (by simp [publicRegs])
    · exact hb.regs 253 (by simp [publicRegs])
    · exact hb.regs 254 (by simp [publicRegs])
    · exact hb.regs 255 (by simp [publicRegs])
    · exact hd 4
  · intro L hL
    cases k <;> simp [payload, Stmt.lUses] at hL

end PCP.Lang.DerivedSeed
