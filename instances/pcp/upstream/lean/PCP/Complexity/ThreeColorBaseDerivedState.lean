import PCP.Complexity.ThreeColorBaseCardinal
import PCP.Complexity.ThreeColorBaseSeed
import PCP.Complexity.NumericDerivedLang

/-! # Preserving source words around the larger numeric derived-grid workspace -/

set_option maxRecDepth 1024

namespace PCP.Lang.ThreeColorBaseDerived

open PCP.Algebraic ThreeColorParameterChoice ThreeColorParameters ThreeColorFullFieldSampling
  LocalCorrection DerivedGrid ThreeColorBaseSetup

def index : Certificate → Fin 7
  | .valid => 4
  | .proper => 5

def factor : Certificate → ℕ
  | .valid => 1
  | .proper => 2

def resultPort : Certificate → Fin 400
  | .valid => 305
  | .proper => 306

/-- The three public source words lie in the gap between the callee's work and protected tapes. -/
def lists (L : Fin 112) : Fin 128 :=
  ⟨if L.val < 100 then L.val else L.val+3, by split_ifs <;> omega⟩

theorem lists_injective : Function.Injective lists := by
  intro i j h
  apply Fin.ext
  have he := congrArg Fin.val h
  simp only [lists] at he
  split_ifs at he <;> omega

def branch (k : Certificate) : Stmt 400 128 :=
  (NumericDerived.program k).rename (Fin.castLE (by decide)) lists

def view (st : State 400 128) : State 300 112 :=
  st.restrict (Fin.castLE (by decide)) lists

theorem branch_result (k : Certificate) (st : State 400 128) :
    (view ((branch k).run st).1, ((branch k).run st).2) =
      (NumericDerived.program k).run (view st) :=
  (NumericDerived.program k).run_rename _ _ (Fin.castLE_injective _) lists_injective st

theorem branch_reg (k : Certificate) (st : State 400 128) (i : Fin 400) (hi : 300 ≤ i.val) :
    ((branch k).run st).1.regs i = st.regs i := by
  apply Stmt.run_rename_reg_outside
  intro j hj
  have := congrArg Fin.val hj
  simp only [Fin.val_castLE] at this
  omega

theorem branch_list (k : Certificate) (st : State 400 128) (L : Fin 128)
    (hL : 115 ≤ L.val ∨ (100 ≤ L.val ∧ L.val < 103)) :
    ((branch k).run st).1.lists L = st.lists L := by
  apply Stmt.run_rename_list_outside
  intro j hj
  have := congrArg Fin.val hj
  simp only [lists] at this
  split_ifs at this <;> omega

def rawSample (k : Certificate) (N : ℕ) (bits : List Bool) :
    DerivedGrid.RawSample k (binaryDimension (exponent N))
      (size (exponent N)) (size (exponent N)) :=
  match k with
  | .valid => ThreeColorBaseSeed.sample N bits 4
  | .proper => ThreeColorBaseSeed.sample N bits 5

theorem validSample (k : Certificate) (N : ℕ) (bits : List Bool)
    (h : Valid (ThreeColorBaseSeed.sample N bits)) : ValidDerived (rawSample k N bits) := by
  cases k
  · exact h 4
  · exact h 5

def sample (k : Certificate) (N : ℕ) (bits : List Bool)
    (h : Valid (ThreeColorBaseSeed.sample N bits)) :
    DerivedGrid.Sample k (binaryDimension (exponent N))
      (size (exponent N)) (size (exponent N)) :=
  unpadDerived (rawSample k N bits) (validSample k N bits h)

end PCP.Lang.ThreeColorBaseDerived
