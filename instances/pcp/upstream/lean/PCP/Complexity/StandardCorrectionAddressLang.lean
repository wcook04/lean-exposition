import PCP.Complexity.StandardCorrectionSite
import PCP.Complexity.HadamardLabelLang

/-!
# Shared homogeneous labels and physical line-table address emission

The weighted generator corrector and the Lagrange constraint share these
programs and the production label and proof-address codecs.
-/

namespace PCP.Lang.StandardCorrection

open PCP.Algebraic BinaryPolynomialSpace BooleanCoefficientArithmetic

variable {F : Type*} {q n m t C1 C3 : ℕ}

def homogeneousRegs (_ : Fin 1) : Fin 80 := 71
def homogeneousLists : Fin 2 → Fin 26 := ![17, 18]
def labelRegs : Fin 5 → Fin 80 := ![72, 60, 73, 74, 75]
def labelLists (_ : Fin 1) : Fin 26 := 18

theorem homogeneousLists_injective : Function.Injective homogeneousLists := by decide
theorem labelRegs_injective : Function.Injective labelRegs := by decide

def homogeneous : Stmt 80 26 :=
  BooleanAffineList.homogeneous.rename homogeneousRegs homogeneousLists

def decodeLabel : Stmt 80 26 := WordCodec.decode.rename labelRegs labelLists

def label : Stmt 80 26 := .seq homogeneous decodeLabel

theorem homogeneous_result (w : Fin t → ZMod 2) (st : State 80 26)
    (hw : st.lists 17 = List.ofFn (fun i => (w i).val)) :
    (homogeneous.run st).1.lists 18 =
      BooleanCoefficientList.encode (homogeneousIndex (le_refl 1) w) := by
  have hr := BooleanAffineList.homogeneous.run_rename homogeneousRegs homogeneousLists
    (Function.injective_of_subsingleton _) homogeneousLists_injective st
  exact (congrArg (fun p : State 1 2 × ℕ => p.1.lists 1) hr).trans
    (BooleanAffineList.homogeneous_run w (st.restrict homogeneousRegs homogeneousLists) hw)

/-- The actual homogeneous coefficient code is computed once from its stored coordinate bits. -/
theorem label_run (w : Fin t → ZMod 2) (st : State 80 26)
    (hw : st.lists 17 = List.ofFn (fun i => (w i).val)) :
    (label.run st).1.regs 60 =
      (BooleanCoefficientIndex.coefficientEquiv t 1 (homogeneousIndex (le_refl 1) w)).val := by
  have hh := homogeneous_result w st hw
  have hr := WordCodec.decode.run_rename labelRegs labelLists labelRegs_injective
    (Function.injective_of_subsingleton _) (homogeneous.run st).1
  have hp := (WordCodec.decode_run
    ((homogeneous.run st).1.restrict labelRegs labelLists)).1
  have ho := (congrArg (fun p : State 5 1 × ℕ => p.1.regs 1) hr).trans hp
  change (decodeLabel.run (homogeneous.run st).1).1.regs 60 =
    WordCodec.value ((homogeneous.run st).1.lists 18) at ho
  rw [hh, HadamardLabel.value_encode] at ho
  exact ho

theorem label_source (st : State 80 26) : (label.run st).1.lists 17 = st.lists 17 :=
  run_lists_frame label 17 (by decide) st

theorem label_cost (w : Fin t → ZMod 2) (st : State 80 26)
    (hw : st.lists 17 = List.ofFn (fun i => (w i).val)) :
    (label.run st).2 ≤ (WordCodec.passConstant*3+30)*(t+2)^2 := by
  have hh := homogeneous_result w st hw
  have hc := BooleanAffineList.homogeneous_cost w
    (st.restrict homogeneousRegs homogeneousLists) hw
  rw [← Stmt.run_rename_cost _ _ _ (Function.injective_of_subsingleton _)
    homogeneousLists_injective st] at hc
  change (homogeneous.run st).2 ≤ _ at hc
  have hb : BinaryField.Bits ((homogeneous.run st).1.lists 18) := by
    rw [hh]
    exact BooleanCoefficientList.encode_bits _
  have hd := WordCodec.decode_cost ((homogeneous.run st).1.restrict labelRegs labelLists) hb
  rw [← Stmt.run_rename_cost _ _ _ labelRegs_injective
    (Function.injective_of_subsingleton _) (homogeneous.run st).1] at hd
  change (decodeLabel.run (homogeneous.run st).1).2 ≤
    (WordCodec.passConstant*3+20)*(((homogeneous.run st).1.lists 18).length+1)^2 at hd
  rw [hh, BooleanAffineList.encode_homogeneous, List.length_cons, List.length_ofFn] at hd
  rw [label, run_seq_snd]
  nlinarith only [hc, hd]

def addressRegs : Fin 14 → Fin 80 :=
  ![50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63]
def addressLists : Fin 2 → Fin 26 := ![20, 21]

theorem addressRegs_injective : Function.Injective addressRegs := by decide
theorem addressLists_injective : Function.Injective addressLists := by decide

def emit : Stmt 80 26 := QueryAddress.emit.rename addressRegs addressLists

/-- Nine fixed prefix entries plus the computed inner point and label form an exact query. -/
def AddressContext (eF : F ≃ Fin q)
    (e1 : Coefficients t 1 ≃ Fin C1) (_e3 : Coefficients t 3 ≃ Fin C3)
    (s : Site F n) (u : BinaryLocalCorrection.InnerPoint F m 4)
    (w : Coefficients t 1) (st : State 80 26) : Prop :=
  (∀ i : Fin 9, st.regs (addressRegs (i.castAdd 5)) = s.prefix eF C1 C3 m i) ∧
    st.regs 59 = (ThreeColorQueryIndex.innerIndex eF m 4 u).val ∧
    st.regs 60 = (e1 w).val

theorem address_view (eF : F ≃ Fin q)
    (e1 : Coefficients t 1 ≃ Fin C1) (e3 : Coefficients t 3 ≃ Fin C3)
    (s : Site F n) (u : BinaryLocalCorrection.InnerPoint F m 4) (w : Coefficients t 1)
    (st : State 80 26) (hc : AddressContext eF e1 e3 s u w st) :
    QueryAddress.View eF e1 e3 (s.query u w) (st.restrict addressRegs addressLists) := by
  intro i
  by_cases hi : i.val < 9
  · have he : (⟨i.val, hi⟩ : Fin 9).castAdd 2 = i := Fin.ext rfl
    rw [← he, Site.inputs_prefix]
    exact hc.1 ⟨i.val, hi⟩
  · have he : i = 9 ∨ i = 10 := by omega
    rcases he with rfl | rfl
    · simpa [Site.inputs_inner, addressRegs] using hc.2.1
    · simpa [Site.inputs_label, addressRegs] using hc.2.2

/-- Emit the exact physical address, with no constructor or enumeration supplied by a callback. -/
theorem emit_run (eF : F ≃ Fin q)
    (e1 : Coefficients t 1 ≃ Fin C1) (e3 : Coefficients t 3 ≃ Fin C3)
    (s : Site F n) (u : BinaryLocalCorrection.InnerPoint F m 4) (w : Coefficients t 1)
    (st : State 80 26) (hc : AddressContext eF e1 e3 s u w st) :
    (emit.run st).1.lists 20 = (ThreeColorQueryIndex.equiv eF e1 e3 (s.query u w)).val ::
      st.lists 20 ∧ (emit.run st).1.regs 61 =
      (ThreeColorQueryIndex.equiv eF e1 e3 (s.query u w)).val := by
  have hv := address_view eF e1 e3 s u w st hc
  have hr := QueryAddress.emit.run_rename addressRegs addressLists
    addressRegs_injective addressLists_injective st
  have hp := (QueryAddress.emit_run eF e1 e3 (s.query u w)
    (st.restrict addressRegs addressLists) hv).1
  have ha := QueryAddress.program_run_state eF e1 e3 (s.query u w)
    (st.restrict addressRegs addressLists) hv
  constructor
  · exact (congrArg (fun p : State 14 2 × ℕ => p.1.lists 0) hr).trans hp
  · exact (congrArg (fun p : State 14 2 × ℕ => p.1.regs 11) hr).trans ha

/-- The emitter retains all eleven numeric payload entries and its caller scratch list. -/
theorem emit_frame (st : State 80 26) :
    (∀ i : Fin 11, (emit.run st).1.regs (addressRegs (i.castAdd 3)) =
      st.regs (addressRegs (i.castAdd 3))) ∧
      (emit.run st).1.lists 21 = st.lists 21 := by
  have hr := QueryAddress.emit.run_rename addressRegs addressLists
    addressRegs_injective addressLists_injective st
  have hp := QueryAddress.program_frame (st.restrict addressRegs addressLists)
  constructor
  · intro i
    exact (congrArg (fun p : State 14 2 × ℕ => p.1.regs (i.castAdd 3)) hr).trans (hp.1 i)
  · exact (congrArg (fun p : State 14 2 × ℕ => p.1.lists 1) hr).trans hp.2.2

/-- Address construction is charged in the bit sizes of its actual stored payload and result. -/
theorem emit_cost (eF : F ≃ Fin q)
    (e1 : Coefficients t 1 ≃ Fin C1) (e3 : Coefficients t 3 ≃ Fin C3)
    (s : Site F n) (u : BinaryLocalCorrection.InnerPoint F m 4) (w : Coefficients t 1)
    (st : State 80 26) (hc : AddressContext eF e1 e3 s u w st) (W : ℕ)
    (hb : ∀ i : Fin 11, Nat.size (st.regs (addressRegs (i.castAdd 3))) ≤ W)
    (hs : listSize (st.lists 21) ≤ W)
    (ha : Nat.size (ThreeColorQueryIndex.equiv eF e1 e3 (s.query u w)).val ≤ W) :
    (emit.run st).2 ≤
      (QueryAddress.program.C *
        (QueryAddress.program.width + QueryAddress.program.csize + 1) + 2) * (W+1) := by
  rw [emit, Stmt.run_rename_cost _ _ _ addressRegs_injective addressLists_injective]
  exact QueryAddress.emit_cost eF e1 e3 (s.query u w) (st.restrict addressRegs addressLists)
    (address_view eF e1 e3 s u w st hc) W hb hs ha

end PCP.Lang.StandardCorrection
