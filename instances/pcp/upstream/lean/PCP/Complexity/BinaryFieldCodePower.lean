import PCP.Complexity.BinaryFieldCodeCost
import PCP.Complexity.BinaryFieldCodeSemantics
import PCP.Complexity.LangBinaryEncode

/-!
# Binary powering from stored natural-number field and exponent codes

The exponent is serialized by the proved bit-budget loop and passed to the
existing materialized binary-power program. No loop uses the exponent itself
as its iteration count. Base, exponent, bit budget, width, and modulus survive.
-/

namespace PCP.Lang.BinaryFieldCodePower

open PCP.Algebraic BinaryField BinaryFieldCode BinaryRootPredicate

/-- Reserve six registers beyond the complete numeric field-operation workspace. -/
def regs : Fin 36 → Fin 42 := Fin.castAdd 6

def embed (p : Stmt 36 11) : Stmt 42 11 := p.rename regs id

theorem embed_state (p : Stmt 36 11) (st : State 42 11) :
    ((embed p).run st).1.restrict regs id = (p.run (st.restrict regs id)).1 :=
  congrArg Prod.fst (p.run_rename regs id (Fin.castAdd_injective 36 6) Function.injective_id st)

/-- Encoder workspace is disjoint from the caller's exponent and bit budget. -/
def digitRegs : Fin 4 → Fin 42 := Fin.natAdd 38

def digitLists (_ : Fin 1) : Fin 11 := 9

def encodeExponent : Stmt 42 11 := .seq (.copy 7 9) (.seq (.assign 38 (.var 36))
  (.seq (.assign 39 (.var 37)) (BinaryEncode.program.rename digitRegs digitLists)))

theorem encodeExponent_run (st : State 42 11)
    (h : Nat.size (st.regs 36) ≤ st.regs 37) (he : st.lists 7 = []) :
    (encodeExponent.run st).1.lists 9 = (st.regs 36).bits.map Bool.toNat := by
  let s := setReg (setReg (setList st 9 []) 38 (st.regs 36)) 39 (st.regs 37)
  have hh := congrArg (fun z : State 4 1 × ℕ => z.1.lists 0)
    (BinaryEncode.program.run_rename digitRegs digitLists (Fin.natAdd_injective 4 38)
      (Function.injective_of_subsingleton _) s)
  have hb := (BinaryEncode.program_run (s.restrict digitRegs digitLists)
    (by simpa [s, digitRegs, Function.update] using h)).2
  simp only [encodeExponent, run_seq_fst, run_copy_fst, run_assign_fst, Expr.eval, he]
  exact hh.trans (by
    simpa [s, digitRegs, digitLists, Function.update, BinaryEncode.digits] using hb)

/-- Exponent preparation, field-word serialization, binary powering, and numeric result decoding. -/
def program : Stmt 42 11 := .seq encodeExponent (.seq (embed (loadCode 24 8))
  (.seq (embed power36) (embed finish)))

variable {t : ℕ} [NeZero t]

/-- Materialized word power agrees with the production field's natural power. -/
theorem power_coefficients (a : BinaryMaterializedField.Element t) (n : ℕ) :
    BinaryWordMaterialization.fieldPower a.coefficients n = (a ^ n).coefficients := by
  apply BinaryWordMaterialization.toField_injective
  rw [BinaryWordMaterialization.toField_fieldPower]
  exact ((BinaryMaterializedField.referenceHom (t := t)).map_pow a n).symm

/-- The runtime accepts a binary base, exponent, and explicit exponent-bit budget. -/
theorem program_run (st : State 42 11) (a : BinaryMaterializedField.Element t) (n W : ℕ)
    (h20 : st.regs 20 = t) (h24 : st.regs 24 = (fieldEquiv t a).val)
    (h36 : st.regs 36 = n) (h37 : st.regs 37 = W) (hn : Nat.size n ≤ W)
    (hm : st.lists 3 = encode (BinaryWordMaterialization.modulus t)) (he : st.lists 7 = []) :
    (program.run st).1.regs 26 = (fieldEquiv t (a ^ n)).val := by
  have hd := encodeExponent_run st (by simpa [h36, h37] using hn) he
  rw [h36] at hd
  have h20' := run_regs_frame encodeExponent 20 (by decide) st
  have h24' := run_regs_frame encodeExponent 24 (by decide) st
  have h3' := run_lists_frame encodeExponent 3 (by decide) st
  have h7' := run_lists_frame encodeExponent 7 (by decide) st
  generalize hs : (encodeExponent.run st).1 = s at *
  have hload := loadCode_run 24 8 (s.restrict regs id) (h7'.trans he)
  change _ = BinaryPolynomialSelector.digits (s.regs 20) (s.regs 24) at hload
  rw [h20', h20, h24', h24, ← BinaryFieldWordCode.encode_word] at hload
  change _ = encode (BinaryFieldWordCode.word t ⟨code a.coefficients, code_lt _⟩) at hload
  rw [word_code] at hload
  have hload' := congrArg (fun v : State 36 11 => v.lists 8) (embed_state (loadCode 24 8) s)
  have hw := hload'.trans hload
  have hu3 := run_lists_frame (embed (loadCode 24 8)) 3 (by decide) s
  have hu7 := run_lists_frame (embed (loadCode 24 8)) 7 (by decide) s
  have hu9 := run_lists_frame (embed (loadCode 24 8)) 9 (by decide) s
  generalize hu : ((embed (loadCode 24 8)).run s).1 = u at *
  have hp := power36_run (u.restrict regs id) a.coefficients n
    (hu3.trans (h3'.trans hm)) hw (hu9.trans hd) (hu7.trans (h7'.trans he))
  have hp' := congrArg (fun v : State 36 11 => v.lists 1) (embed_state power36 u)
  have ho := hp'.trans hp
  rw [power_coefficients] at ho
  generalize hv : ((embed power36).run u).1 = v at *
  have hf := finish_run (v.restrict regs id)
  have hf' := congrArg (fun s : State 36 11 => s.regs 26) (embed_state finish v)
  simp only [program, run_seq_fst, hs, hu, hv]
  apply hf'.trans (hf.trans ?_)
  change v.lists 1 = encode (a ^ n).coefficients at ho
  change WordCodec.value (v.lists 1) = _
  rw [ho]
  rfl

/-- Public scalar inputs and fixed field data survive the complete operation. -/
theorem program_frame (st : State 42 11) :
    (program.run st).1.regs 20 = st.regs 20 ∧
    (program.run st).1.regs 24 = st.regs 24 ∧
    (program.run st).1.regs 36 = st.regs 36 ∧
    (program.run st).1.regs 37 = st.regs 37 ∧
    (program.run st).1.lists 3 = st.lists 3 ∧ (program.run st).1.lists 7 = st.lists 7 := by
  exact ⟨run_regs_frame program 20 (by decide) st, run_regs_frame program 24 (by decide) st,
    run_regs_frame program 36 (by decide) st, run_regs_frame program 37 (by decide) st,
    run_lists_frame program 3 (by decide) st, run_lists_frame program 7 (by decide) st⟩

end PCP.Lang.BinaryFieldCodePower
