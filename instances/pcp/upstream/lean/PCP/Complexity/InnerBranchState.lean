/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Complexity.HadamardRowBranchCost
import PCP.Complexity.InterpolationBranchCost

/-!
# Stored inputs for the complete inner binary low-degree selector

The Hadamard payload is relocated to registers 110--119, so both branches'
source data coexist. Register 100 chooses the branch, histories are lists 36/37,
and the common outputs are forward query list 38 and verdict register 101.
-/

namespace PCP.Lang.InnerBranch

open PCP.Algebraic BinaryPolynomialSpace InterpolationBranch

variable {t n m : ℕ} [NeZero t]

abbrev Seed (t m : ℕ) :=
  BinaryLowDegreeTest.TestRandomness (Field t) (Fin 4 × Fin m) t 1

def hadRegs (i : Fin 100) : Fin 120 :=
  if h : 80 ≤ i.val ∧ i.val < 90 then ⟨i.val + 30, by omega⟩ else i.castLE (by decide)

def hadLists : Fin 32 → Fin 40 := Fin.castLE (by decide)
def interpRegs : Fin 100 → Fin 120 := Fin.castLE (by decide)

theorem hadRegs_injective : Function.Injective hadRegs := by
  intro i j h
  apply Fin.ext
  have h := congrArg Fin.val h
  simp only [hadRegs] at h
  split_ifs at h <;> simp only [Fin.val_castLE] at h <;> omega

def location (site : StandardCorrection.Site (Field t) n) (x : Point t m) :
    HadamardRow.Location (Field t) n m 4 1 :=
  match site with
  | .color uv => .colorLine uv x
  | .valid uv => .validLine uv x
  | .difference uv => .differenceLine uv x
  | .proper uv => .properLine uv x

omit [NeZero t] in
theorem location_query (site : StandardCorrection.Site (Field t) n) (x : Point t m)
    (p : Coefficients t 1) : (location site x).query p = site.query x p := by
  cases site <;> rfl

structure Context (a : Fin 5 → Field t) (site : StandardCorrection.Site (Field t) n)
    (s : Seed t m) (st : State 120 40) : Prop where
  coin : st.regs 100 = s.1.toNat
  hadamard : HadamardRow.Sources s.2.1.2 (st.restrict hadRegs hadLists)
  payload : HadamardRow.Payload
    ((location site s.2.1.1).payload (t := t) (BinaryFieldCode.fieldEquiv t))
    (st.restrict hadRegs hadLists)
  interpolation : InterpolationBranch.Context a 0 s.2.2.1.1.1 s.2.2.1.1.2
    s.2.2.2 site (st.restrict interpRegs id)

def hadCall : Stmt 120 40 := HadamardRow.branch.rename hadRegs hadLists

def interpCall : Stmt 120 40 := InterpolationBranch.program.rename interpRegs id

def prepareHad : Stmt 120 40 := .seq (.copy 36 30)
  (.seq (.copy 37 31) (.copy 7 27))

def hadamard : Stmt 120 40 := .seq prepareHad
  (.seq hadCall (.seq (.copy 26 38) (.assign 101 (.var 63))))

def interpolate : Stmt 120 40 := .seq interpCall
  (.seq (.copy 20 38) (.assign 101 (.var 11)))

/-- The sole branch choice is the actual Boolean sampler coin. -/
def program : Stmt 120 40 := .ite 100 interpolate hadamard

theorem hadCall_result (st : State 120 40) :
    ((hadCall.run st).1.restrict hadRegs hadLists, (hadCall.run st).2) =
      HadamardRow.branch.run (st.restrict hadRegs hadLists) :=
  HadamardRow.branch.run_rename hadRegs hadLists hadRegs_injective (Fin.castLE_injective _) st

theorem interpCall_result (st : State 120 40) :
    ((interpCall.run st).1.restrict interpRegs id, (interpCall.run st).2) =
      InterpolationBranch.program.run (st.restrict interpRegs id) :=
  InterpolationBranch.program.run_rename interpRegs id (Fin.castLE_injective _)
    Function.injective_id st

end PCP.Lang.InnerBranch
