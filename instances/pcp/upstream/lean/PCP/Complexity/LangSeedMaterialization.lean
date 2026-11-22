import PCP.Complexity.LangUniformDecodeCost
import PCP.Complexity.BinaryFieldCodeSemantics

/-!
# Materializing seed labels and field points in production order

The same actual uniform-radix program handles binary labels, field vectors,
and sum/product coordinate domains. These equalities identify the structural
seed codecs with the concrete numeric field representation used by arithmetic.
-/

namespace PCP.Lang.UniformDecode

open PCP.Algebraic ThreeColorSeedIndex

theorem fieldCodec_materialized (t : ℕ) [NeZero t] :
    (fieldCodec (BinaryMaterializedField.coordinates t)).equiv =
      BinaryFieldCode.fieldEquiv t := by
  have h : (fieldCodec (BinaryMaterializedField.coordinates t)).equiv.symm =
      (BinaryFieldCode.fieldEquiv t).symm := by
    ext i
    rfl
  exact congrArg Equiv.symm h

theorem program_bits {t : ℕ} (w : Fin t → ZMod 2) (st : State 7 3)
    (hc : st.regs 0 = ((bitsCodec t).equiv w).val)
    (hn : st.regs 5 = t) (hb : st.regs 6 = 2) (he : st.lists 2 = []) :
    (program.run st).1.lists 1 = List.ofFn (fun i => (w i).val) := by
  have hr := program_finFunction 2 t ((bitsCodec t).equiv w) st hc hn hb he
  rw [hr]
  congr 1
  funext i
  change ((finFunctionFinEquiv.symm (finFunctionFinEquiv
    (fun j => (ZMod.finEquiv 2).symm (w j)))) i).val = (w i).val
  rw [Equiv.symm_apply_apply]
  rfl

theorem program_fieldPoint {t : ℕ} [NeZero t] {σ : Type*} (σc : Codec σ)
    (p : σ → BinaryMaterializedField.Element t) (st : State 7 3)
    (hc : st.regs 0 = ((σc.function
      (fieldCodec (BinaryMaterializedField.coordinates t))).equiv p).val)
    (hn : st.regs 5 = σc.size) (hb : st.regs 6 = 2 ^ t) (he : st.lists 2 = []) :
    (program.run st).1.lists 1 = List.ofFn
      (fun i => (BinaryFieldCode.fieldEquiv t (p (σc.equiv.symm i))).val) := by
  have hr := program_codecFunction σc (fieldCodec (BinaryMaterializedField.coordinates t))
    p st hc hn hb he
  rw [hr]
  apply congrArg List.ofFn
  funext i
  exact congrArg Fin.val (congrArg (fun e => e (p (σc.equiv.symm i)))
    (fieldCodec_materialized t))

end PCP.Lang.UniformDecode
