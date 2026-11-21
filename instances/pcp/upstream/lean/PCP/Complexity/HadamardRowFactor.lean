/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Complexity.HadamardRowBase
import PCP.Complexity.HadamardFactorLoadCost

/-!
# The two queries contributed by one Hadamard factor

Both product and factor labels are computed from stored coefficient arrays, added
to the shared base label, and packed into the exact production numeric codes.
-/

namespace PCP.Lang.HadamardRow

open PCP.Algebraic BinaryPolynomialSpace Hadamard BooleanCoefficientList HadamardLabel

variable {t r a : ℕ}

def productPrepare : Stmt 80 32 :=
  .seq (.copy 22 13) (.seq (.assign 54 (.const 1)) (.assign 55 (.var 60)))

def productPart : Stmt 80 32 :=
  .seq productPrepare (.seq HadamardLabel.product (emitSum 5 20))

theorem productPart_stable : Stable productPart := by decide

theorem productPart_run (h : 1 + a ≤ r) (s : TestRandomness t r) (p : Coefficients t a)
    (st : State 80 32) (hc : Context s st) (ha : st.regs 60 = a)
    (hp : st.lists 18 = encode p) :
    (productPart.run st).1.lists 24 =
      code (BooleanCoefficientArithmetic.mixedProduct h s.linear p + s.base) :: st.lists 24 := by
  let u := setReg (setReg (setList st 13 (st.lists 22)) 54 1) 55 (st.regs 60)
  have hl := HadamardLabel.product_run h s.linear p u
    (by simpa [u, Function.update] using hc.1) (by simp [u, Function.update])
    (by simpa [u] using ha) (by simpa [u, Function.update] using hc.2.1)
    (by simpa [u, Function.update] using hc.2.2.1)
    (by simpa [u] using hc.2.2.2.2.2.1) (by simpa [u, Function.update] using hp)
  have hu7 := run_lists_frame HadamardLabel.product 7 (by decide) u
  have hu20 := run_lists_frame HadamardLabel.product 20 (by decide) u
  have hu24 := run_lists_frame HadamardLabel.product 24 (by decide) u
  dsimp only [u] at hl hu7 hu20 hu24
  simp only [productPart, productPrepare, run_seq_fst, run_copy_fst,
    run_assign_fst, Expr.eval, setReg_regs, setList_regs,
    Function.update_of_ne (by decide : (60 : Fin 80) ≠ 54)]
  generalize hv : (HadamardLabel.product.run
    (setReg (setReg (setList st 13 (st.lists 22)) 54 1) 55 (st.regs 60))).1 = v at *
  have hh := emitSum_run 5 20 (by decide)
    (BooleanCoefficientArithmetic.mixedProduct h s.linear p) s.base v hl
    (by simpa [Function.update] using hu20.trans hc.2.2.2.1)
    (by simpa [Function.update] using hu7.trans hc.2.2.1)
  rw [hu24] at hh
  simpa [Function.update] using hh

def factorPrepare : Stmt 80 32 := .seq (.copy 18 13) (.assign 54 (.var 60))

def factorPart : Stmt 80 32 :=
  .seq factorPrepare (.seq HadamardLabel.embed (emitSum 5 20))

theorem factorPart_stable : Stable factorPart := by decide

theorem factorPart_run (h : a ≤ r) (s : TestRandomness t r) (p : Coefficients t a)
    (st : State 80 32) (hc : Context s st) (ha : st.regs 60 = a)
    (hp : st.lists 18 = encode p) :
    (factorPart.run st).1.lists 24 =
      code (BooleanCoefficientArithmetic.embed h p + s.base) :: st.lists 24 := by
  let u := setReg (setList st 13 (st.lists 18)) 54 (st.regs 60)
  have hl := HadamardLabel.embed_run h p u
    (by simpa [u, Function.update] using hc.1) (by simpa [u] using ha)
    (by simpa [u, Function.update] using hc.2.1)
    (by simpa [u, Function.update] using hc.2.2.1) (by simpa [u] using hp)
  have hu7 := run_lists_frame HadamardLabel.embed 7 (by decide) u
  have hu20 := run_lists_frame HadamardLabel.embed 20 (by decide) u
  have hu24 := run_lists_frame HadamardLabel.embed 24 (by decide) u
  dsimp only [u] at hl hu7 hu20 hu24
  simp only [factorPart, factorPrepare, run_seq_fst, run_copy_fst,
    run_assign_fst, Expr.eval, setList_regs]
  generalize hv : (HadamardLabel.embed.run
    (setReg (setList st 13 (st.lists 18)) 54 (st.regs 60))).1 = v at *
  have hh := emitSum_run 5 20 (by decide)
    (BooleanCoefficientArithmetic.embed h p) s.base v hl
    (by simpa [Function.update] using hu20.trans hc.2.2.2.1)
    (by simpa [Function.update] using hu7.trans hc.2.2.1)
  rw [hu24] at hh
  simpa [Function.update] using hh

/-- Source factor bits and their degree remain available between the two queries. -/
theorem productPart_source (st : State 80 32) :
    (productPart.run st).1.lists 18 = st.lists 18 ∧
    (productPart.run st).1.regs 60 = st.regs 60 := by
  exact ⟨run_lists_frame productPart 18 (by decide) st,
    run_regs_frame productPart 60 (by decide) st⟩

def pair : Stmt 80 32 := .seq productPart factorPart

theorem pair_run (h : 1 + a ≤ r) (s : TestRandomness t r) (p : Coefficients t a)
    (st : State 80 32) (hc : Context s st) (ha : st.regs 60 = a)
    (hp : st.lists 18 = encode p) :
    (pair.run st).1.lists 24 =
      code (BooleanCoefficientArithmetic.embed (by omega : a ≤ r) p + s.base) ::
        code (BooleanCoefficientArithmetic.mixedProduct h s.linear p + s.base) :: st.lists 24 := by
  have hprod := productPart_run h s p st hc ha hp
  have hctx := context_frame productPart productPart_stable s st hc
  have hsource := productPart_source st
  simp only [pair, run_seq_fst]
  generalize hs : (productPart.run st).1 = u at *
  rw [factorPart_run (by omega : a ≤ r) s p u hctx
    (hsource.2.trans ha) (hsource.1.trans hp), hprod]

theorem pair_stable : Stable pair := by decide

end PCP.Lang.HadamardRow
