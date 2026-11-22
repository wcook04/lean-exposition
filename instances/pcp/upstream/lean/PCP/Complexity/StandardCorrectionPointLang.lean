import PCP.Complexity.LangAffineVectorCost
import PCP.Complexity.BinaryFieldCodePowerCost
import PCP.Complexity.LangQueryAddressState

/-!
# Concrete root-power affine points for standard local correction

One pass computes a stored root's selected power, forms the full affine point,
and encodes that point in the production little-endian coordinate order.
-/

namespace PCP.Lang.StandardCorrection

open PCP.Algebraic BinaryFieldCode

variable {t d : ℕ} [NeZero t]

@[irreducible] def power : Stmt 80 26 :=
  BinaryFieldCodePower.program.rename (Fin.castLE (by decide)) (Fin.castLE (by decide))

def affine : Stmt 80 26 :=
  AffineVector.program.rename (Fin.castLE (by decide)) (Fin.castLE (by decide))

def radixRegs : Fin 6 → Fin 80 := ![45, 64, 59, 65, 66, 67]
def radixLists (_ : Fin 1) : Fin 26 := 16

theorem radixRegs_injective : Function.Injective radixRegs := by decide

def radix : Stmt 80 26 := RadixCodec.encode.rename radixRegs radixLists

def powerCall : Stmt 80 26 :=
  .seq (.assign 20 (.var 43)) (.seq (.assign 24 (.var 44))
    (.seq (.assign 36 (.var 46)) (.seq (.assign 37 (.const 3)) power)))

def affineCall : Stmt 80 26 :=
  .seq (.assign 2 (.var 26)) (.seq (.assign 23 (.var 43)) affine)

def point : Stmt 80 26 := .seq powerCall (.seq affineCall radix)

/-- Stored source values; all arithmetic work registers may initially contain arbitrary values. -/
def PointContext (ζ : BinaryMaterializedField.Element t)
    (u v : Fin d → BinaryMaterializedField.Element t) (st : State 80 26) : Prop :=
  st.regs 43 = t ∧ st.regs 44 = (fieldEquiv t ζ).val ∧ st.regs 45 = 2 ^ t ∧
  st.lists 3 = BinaryField.encode (BinaryWordMaterialization.modulus t) ∧
  st.lists 7 = [] ∧ st.lists 12 = List.ofFn (fun i => (fieldEquiv t (u i)).val) ∧
  st.lists 13 = List.ofFn (fun i => (fieldEquiv t (v i)).val)

theorem power_result (st : State 80 26) :
    (((power.run st).1.restrict (Fin.castLE (by decide)) (Fin.castLE (by decide))),
      (power.run st).2) = BinaryFieldCodePower.program.run
        (st.restrict (Fin.castLE (by decide)) (Fin.castLE (by decide))) :=
  by
    unfold power
    exact BinaryFieldCodePower.program.run_rename _ _
      (Fin.castLE_injective _) (Fin.castLE_injective _) st

theorem affine_result (st : State 80 26) :
    (((affine.run st).1.restrict (Fin.castLE (by decide)) (Fin.castLE (by decide))),
      (affine.run st).2) = AffineVector.program.run
        (st.restrict (Fin.castLE (by decide)) (Fin.castLE (by decide))) :=
  AffineVector.program.run_rename _ _
    (Fin.castLE_injective _) (Fin.castLE_injective _) st

theorem powerCall_run (ζ : BinaryMaterializedField.Element t)
    (u v : Fin d → BinaryMaterializedField.Element t) (k : ℕ) (hk : k ≤ 5)
    (st : State 80 26) (hc : PointContext ζ u v st) (he : st.regs 46 = k) :
    (powerCall.run st).1.regs 26 = (fieldEquiv t (ζ^k)).val := by
  let s := setReg (setReg (setReg (setReg st 20 (st.regs 43)) 24 (st.regs 44))
    36 (st.regs 46)) 37 3
  have hr := power_result s
  have hp := BinaryFieldCodePower.program_run
    (s.restrict (Fin.castLE (by decide)) (Fin.castLE (by decide))) ζ k 3
    (by simpa [s, Function.update] using hc.1)
    (by simpa [s, Function.update] using hc.2.1)
    (by simpa [s, Function.update] using he) (by simp [s])
    (Nat.size_le.mpr (by norm_num; omega)) hc.2.2.2.1 hc.2.2.2.2.1
  have ho := (congrArg (fun p : State 42 11 × ℕ => p.1.regs 26) hr).trans hp
  simp only [State.restrict_regs,
    show Fin.castLE (by decide : 42 ≤ 80) (26 : Fin 42) = (26 : Fin 80) from rfl] at ho
  simp only [powerCall, run_seq_fst, run_assign_fst, Expr.eval, setReg_regs,
    Function.update, Fin.reduceEq, dite_false]
  exact ho

theorem affineCall_run (ζ a : BinaryMaterializedField.Element t)
    (u v : Fin d → BinaryMaterializedField.Element t)
    (st : State 80 26) (hc : PointContext ζ u v st)
    (ha : st.regs 26 = (fieldEquiv t a).val) :
    (affineCall.run st).1.lists 16 = List.ofFn
      (fun i => (fieldEquiv t (PolynomialLine.point u v a i)).val) := by
  let s := setReg (setReg st 2 (st.regs 26)) 23 (st.regs 43)
  have hr := affine_result s
  have hp := AffineVector.program_point a u v
    (s.restrict (Fin.castLE (by decide)) (Fin.castLE (by decide)))
    ⟨by simpa [s, Function.update] using ha,
      by simpa [s] using hc.1, hc.2.2.2.1, hc.2.2.2.2.1⟩
    hc.2.2.2.2.2.1 hc.2.2.2.2.2.2
  simp only [affineCall, run_seq_fst, run_assign_fst, Expr.eval]
  exact (congrArg (fun p : State 41 17 × ℕ => p.1.lists 16) hr).trans hp

omit [NeZero t] in
theorem radix_run (z : Fin d → BinaryMaterializedField.Element t)
    (st : State 80 26) (hq : st.regs 45 = 2 ^ t)
    (hz : st.lists 16 = List.ofFn (fun i => (fieldEquiv t (z i)).val)) :
    (radix.run st).1.regs 59 = (finFunctionFinEquiv (fun i => fieldEquiv t (z i))).val := by
  have hr := RadixCodec.encode.run_rename radixRegs radixLists radixRegs_injective
    (Function.injective_of_subsingleton _) st
  have hp := (RadixCodec.encode_run (st.restrict radixRegs radixLists)).2.1
  have ho := (congrArg (fun p : State 6 1 × ℕ => p.1.regs 2) hr).trans hp
  change (radix.run st).1.regs 59 = RadixCodec.value (st.regs 45) (st.lists 16) at ho
  rw [hq, hz, RadixCodec.value_finFunction] at ho
  exact ho

theorem power_reg_outside (st : State 80 26) (i : Fin 80) (hi : 42 ≤ i.val) :
    (power.run st).1.regs i = st.regs i := by
  unfold power
  apply Stmt.run_rename_reg_outside
  intro j hj
  have he := congrArg Fin.val hj
  simp only [Fin.val_castLE] at he
  omega

theorem power_list_outside (st : State 80 26) (i : Fin 26) (hi : 11 ≤ i.val) :
    (power.run st).1.lists i = st.lists i := by
  unfold power
  apply Stmt.run_rename_list_outside
  intro j hj
  have he := congrArg Fin.val hj
  simp only [Fin.val_castLE] at he
  omega

theorem powerCall_context (ζ : BinaryMaterializedField.Element t)
    (u v : Fin d → BinaryMaterializedField.Element t)
    (st : State 80 26) (hc : PointContext ζ u v st) :
    PointContext ζ u v (powerCall.run st).1 := by
  let s := setReg (setReg (setReg (setReg st 20 (st.regs 43)) 24 (st.regs 44))
    36 (st.regs 46)) 37 3
  have hr := power_result s
  have hf := BinaryFieldCodePower.program_frame
    (s.restrict (Fin.castLE (by decide)) (Fin.castLE (by decide)))
  have hm := (congrArg (fun p : State 42 11 × ℕ => p.1.lists 3) hr).trans hf.2.2.2.2.1
  have he := (congrArg (fun p : State 42 11 × ℕ => p.1.lists 7) hr).trans hf.2.2.2.2.2
  have h43 := power_reg_outside s 43 (by decide)
  have h44 := power_reg_outside s 44 (by decide)
  have h45 := power_reg_outside s 45 (by decide)
  have h12 := power_list_outside s 12 (by decide)
  have h13 := power_list_outside s 13 (by decide)
  have hsc : PointContext ζ u v s := by
    simpa [s, PointContext, Function.update] using hc
  simp only [powerCall, run_seq_fst, run_assign_fst, Expr.eval, setReg_regs,
    Function.update, Fin.reduceEq, dite_false]
  exact ⟨h43.trans hsc.1, h44.trans hsc.2.1, h45.trans hsc.2.2.1,
    hm.trans hsc.2.2.2.1, he.trans hsc.2.2.2.2.1,
    h12.trans hsc.2.2.2.2.2.1, h13.trans hsc.2.2.2.2.2.2⟩

theorem point_run (ζ : BinaryMaterializedField.Element t)
    (u v : Fin d → BinaryMaterializedField.Element t) (k : ℕ) (hk : k ≤ 5)
    (st : State 80 26) (hc : PointContext ζ u v st) (he : st.regs 46 = k) :
    (point.run st).1.regs 59 = (finFunctionFinEquiv
      (fun i => fieldEquiv t (PolynomialLine.point u v (ζ^k) i))).val := by
  have hpow := powerCall_run ζ u v k hk st hc he
  have hsc := powerCall_context ζ u v st hc
  simp only [point, run_seq_fst]
  generalize hs : (powerCall.run st).1 = s at *
  have hvec := affineCall_run ζ (ζ^k) u v s hsc hpow
  have hq := (run_regs_frame affineCall 45 (by decide) s).trans hsc.2.2.1
  exact radix_run _ (affineCall.run s).1 hq hvec

theorem powerCall_cost (ζ : BinaryMaterializedField.Element t)
    (u v : Fin d → BinaryMaterializedField.Element t) (k : ℕ) (hk : k ≤ 5)
    (st : State 80 26) (hc : PointContext ζ u v st) (he : st.regs 46 = k) :
    (powerCall.run st).2 ≤ 40000000 * (t+4)^4 := by
  let s := setReg (setReg (setReg (setReg st 20 (st.regs 43)) 24 (st.regs 44))
    36 (st.regs 46)) 37 3
  have hr := power_result s
  have hp := BinaryFieldCodePower.program_cost
    (s.restrict (Fin.castLE (by decide)) (Fin.castLE (by decide))) ζ k 3
    (by simpa [s, Function.update] using hc.1)
    (by simpa [s, Function.update] using hc.2.1)
    (by simpa [s, Function.update] using he) (by simp [s])
    (Nat.size_le.mpr (by norm_num; omega)) hc.2.2.2.1 hc.2.2.2.2.1
  rw [← congrArg Prod.snd hr] at hp
  have hζ : Nat.size (fieldEquiv t ζ).val ≤ t := Nat.size_le.mpr (fieldEquiv t ζ).isLt
  have hst := size_le_self t
  have hsk : Nat.size k ≤ 3 := Nat.size_le.mpr (by norm_num; omega)
  have hlin : t+4 ≤ (t+4)^4 := Nat.le_self_pow (by decide) _
  simp only [powerCall, run_seq_snd, run_assign_fst, Expr.eval, setReg_regs,
    Function.update, Fin.reduceEq, dite_false]
  change (Expr.var 43).cost st.regs + ((Expr.var 44).cost _ +
    ((Expr.var 46).cost _ + ((Expr.const 3).cost _ + (power.run s).2 + 1)+1)+1)+1 ≤ _
  simp only [Expr.cost, Expr.readSize, Expr.eval, setReg_regs, Function.update,
    Fin.reduceEq, dite_false, hc.1, hc.2.1, he]
  have h3 : Nat.size 3 = 2 := rfl
  rw [h3]
  nlinarith only [hp, hζ, hst, hsk, hlin]

theorem affineCall_cost (ζ a : BinaryMaterializedField.Element t)
    (u v : Fin d → BinaryMaterializedField.Element t)
    (st : State 80 26) (hc : PointContext ζ u v st)
    (ha : st.regs 26 = (fieldEquiv t a).val) :
    (affineCall.run st).2 ≤ 101000000 * (t+d+1)^5 := by
  let s := setReg (setReg st 2 (st.regs 26)) 23 (st.regs 43)
  have hr := affine_result s
  have hp := AffineVector.program_cost a (List.ofFn (fun i => (u i, v i)))
    (s.restrict (Fin.castLE (by decide)) (Fin.castLE (by decide)))
    ⟨by simpa [s, Function.update] using ha,
      by simpa [s] using hc.1, hc.2.2.2.1, hc.2.2.2.2.1⟩
    (by simpa [s, AffineVector.leftCodes, Function.comp_def] using hc.2.2.2.2.2.1)
    (by simpa [s, AffineVector.rightCodes, Function.comp_def] using hc.2.2.2.2.2.2)
  rw [← congrArg Prod.snd hr, List.length_ofFn] at hp
  have hsa : Nat.size (fieldEquiv t a).val ≤ t := Nat.size_le.mpr (fieldEquiv t a).isLt
  have hst := size_le_self t
  have hlin : t+d+1 ≤ (t+d+1)^5 := Nat.le_self_pow (by decide) _
  simp only [affineCall, run_seq_snd, run_assign_fst, Expr.eval]
  change (Expr.var 26).cost st.regs + ((Expr.var 43).cost _ + (affine.run s).2 + 1)+1 ≤ _
  simp only [Expr.cost, Expr.readSize, Expr.eval, setReg_regs, Function.update,
    Fin.reduceEq, dite_false, hc.1, ha]
  nlinarith only [hp, hsa, hst, hlin]

omit [NeZero t] in
theorem fieldCodes_size (z : Fin d → BinaryMaterializedField.Element t) :
    listSize (List.ofFn (fun i => (fieldEquiv t (z i)).val)) ≤ d*(t+1) := by
  simp only [listSize, List.map_ofFn, Fin.sum_ofFn]
  calc
    _ ≤ ∑ _i : Fin d, (t+1) := Finset.sum_le_sum fun i _ =>
      Nat.add_le_add_right (Nat.size_le.mpr (fieldEquiv t (z i)).isLt) 1
    _ = _ := by simp

omit [NeZero t] in
theorem radix_cost (z : Fin d → BinaryMaterializedField.Element t)
    (st : State 80 26) (hq : st.regs 45 = 2 ^ t)
    (hz : st.lists 16 = List.ofFn (fun i => (fieldEquiv t (z i)).val)) :
    (radix.run st).2 ≤ (RadixCodec.passConstant+20)*(t+d+2)^4 := by
  have hp := RadixCodec.encode_cost (st.restrict radixRegs radixLists) (by
    change ∀ w ∈ st.lists 16, w < st.regs 45
    rw [hq, hz]
    intro w hw
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hw
    exact (fieldEquiv t (z i)).isLt)
  rw [← Stmt.run_rename_cost _ _ _ radixRegs_injective
    (Function.injective_of_subsingleton _) st] at hp
  change (radix.run st).2 ≤ (RadixCodec.passConstant+20)*
    (RadixCodec.workBound (st.regs 45) (st.lists 16)+1)^2 at hp
  rw [hq, hz] at hp
  have hs := fieldCodes_size z
  have hw : RadixCodec.workBound (2^t)
      (List.ofFn (fun i => (fieldEquiv t (z i)).val))+1 ≤ (t+d+2)^2 := by
    simp only [RadixCodec.workBound, List.length_ofFn, Nat.size_pow]
    nlinarith only [hs, Nat.zero_le (t^2), Nat.zero_le (d^2)]
  have hh := hp.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hw 2))
  simpa only [← pow_mul] using hh

/-- Each root-power point is evaluated with a polynomial cost in dimension and field bit width. -/
theorem point_cost (ζ : BinaryMaterializedField.Element t)
    (u v : Fin d → BinaryMaterializedField.Element t) (k : ℕ) (hk : k ≤ 5)
    (st : State 80 26) (hc : PointContext ζ u v st) (he : st.regs 46 = k) :
    (point.run st).2 ≤ (RadixCodec.passConstant+141000025)*(t+d+4)^5 := by
  have hp := powerCall_cost ζ u v k hk st hc he
  have hpow := powerCall_run ζ u v k hk st hc he
  have hsc := powerCall_context ζ u v st hc
  simp only [point, run_seq_snd]
  generalize hs : (powerCall.run st).1 = s at *
  have ha := affineCall_cost ζ (ζ^k) u v s hsc hpow
  have hvec := affineCall_run ζ (ζ^k) u v s hsc hpow
  have hq := (run_regs_frame affineCall 45 (by decide) s).trans hsc.2.2.1
  have hr := radix_cost _ (affineCall.run s).1 hq hvec
  have h45 : (t+d+4)^4 ≤ (t+d+4)^5 := Nat.pow_le_pow_right (by omega) (by decide)
  have hpc := hp.trans (Nat.mul_le_mul_left 40000000
    ((Nat.pow_le_pow_left (by omega : t+4 ≤ t+d+4) 4).trans h45))
  have hac := ha.trans (Nat.mul_le_mul_left 101000000
    (Nat.pow_le_pow_left (by omega : t+d+1 ≤ t+d+4) 5))
  have hrc := hr.trans (Nat.mul_le_mul_left (RadixCodec.passConstant+20)
    ((Nat.pow_le_pow_left (by omega : t+d+2 ≤ t+d+4) 4).trans h45))
  have hpos : 1 ≤ (t+d+4)^5 := Nat.one_le_pow _ _ (by omega)
  nlinarith only [hpc, hac, hrc, hpos]

/-- The shared affine-point stage accepts any scalar, independently of how it was computed. -/
def scalarPoint : Stmt 80 26 := .seq affineCall radix

/-- Source context for arbitrary-scalar line interpolation. -/
def AffineContext (u v : Fin d → BinaryMaterializedField.Element t)
    (st : State 80 26) : Prop :=
  st.regs 43 = t ∧ st.regs 45 = 2 ^ t ∧
  st.lists 3 = BinaryField.encode (BinaryWordMaterialization.modulus t) ∧
  st.lists 7 = [] ∧ st.lists 12 = List.ofFn (fun i => (fieldEquiv t (u i)).val) ∧
  st.lists 13 = List.ofFn (fun i => (fieldEquiv t (v i)).val)

theorem affineCall_run_core (a : BinaryMaterializedField.Element t)
    (u v : Fin d → BinaryMaterializedField.Element t)
    (st : State 80 26) (hc : AffineContext u v st)
    (ha : st.regs 26 = (fieldEquiv t a).val) :
    (affineCall.run st).1.lists 16 = List.ofFn
      (fun i => (fieldEquiv t (PolynomialLine.point u v a i)).val) := by
  let s := setReg (setReg st 2 (st.regs 26)) 23 (st.regs 43)
  have hr := affine_result s
  have hp := AffineVector.program_point a u v
    (s.restrict (Fin.castLE (by decide)) (Fin.castLE (by decide)))
    ⟨by simpa [s, Function.update] using ha,
      by simpa [s] using hc.1, hc.2.2.1, hc.2.2.2.1⟩ hc.2.2.2.2.1 hc.2.2.2.2.2
  simp only [affineCall, run_seq_fst, run_assign_fst, Expr.eval]
  exact (congrArg (fun p : State 41 17 × ℕ => p.1.lists 16) hr).trans hp

/-- Exact arbitrary-scalar vector computation and production coordinate encoding. -/
theorem scalarPoint_run (a : BinaryMaterializedField.Element t)
    (u v : Fin d → BinaryMaterializedField.Element t)
    (st : State 80 26) (hc : AffineContext u v st)
    (ha : st.regs 26 = (fieldEquiv t a).val) :
    (scalarPoint.run st).1.regs 59 = (finFunctionFinEquiv
      (fun i => fieldEquiv t (PolynomialLine.point u v a i))).val := by
  have hv := affineCall_run_core a u v st hc ha
  have hq := (run_regs_frame affineCall 45 (by decide) st).trans hc.2.1
  exact radix_run _ (affineCall.run st).1 hq hv

theorem affineCall_cost_core (a : BinaryMaterializedField.Element t)
    (u v : Fin d → BinaryMaterializedField.Element t)
    (st : State 80 26) (hc : AffineContext u v st)
    (ha : st.regs 26 = (fieldEquiv t a).val) :
    (affineCall.run st).2 ≤ 101000000 * (t+d+1)^5 := by
  let s := setReg (setReg st 2 (st.regs 26)) 23 (st.regs 43)
  have hr := affine_result s
  have hp := AffineVector.program_cost a (List.ofFn (fun i => (u i, v i)))
    (s.restrict (Fin.castLE (by decide)) (Fin.castLE (by decide)))
    ⟨by simpa [s, Function.update] using ha,
      by simpa [s] using hc.1, hc.2.2.1, hc.2.2.2.1⟩
    (by simpa [s, AffineVector.leftCodes, Function.comp_def] using hc.2.2.2.2.1)
    (by simpa [s, AffineVector.rightCodes, Function.comp_def] using hc.2.2.2.2.2)
  rw [← congrArg Prod.snd hr, List.length_ofFn] at hp
  have hsa : Nat.size (fieldEquiv t a).val ≤ t := Nat.size_le.mpr (fieldEquiv t a).isLt
  have hst := size_le_self t
  have hlin : t+d+1 ≤ (t+d+1)^5 := Nat.le_self_pow (by decide) _
  simp only [affineCall, run_seq_snd, run_assign_fst, Expr.eval]
  change (Expr.var 26).cost st.regs + ((Expr.var 43).cost _ + (affine.run s).2 + 1)+1 ≤ _
  simp only [Expr.cost, Expr.readSize, Expr.eval, setReg_regs, Function.update,
    Fin.reduceEq, dite_false, hc.1, ha]
  nlinarith only [hp, hsa, hst, hlin]

/-- Uniform charged cost of the shared arbitrary-scalar stage. -/
theorem scalarPoint_cost (a : BinaryMaterializedField.Element t)
    (u v : Fin d → BinaryMaterializedField.Element t)
    (st : State 80 26) (hc : AffineContext u v st)
    (ha : st.regs 26 = (fieldEquiv t a).val) :
    (scalarPoint.run st).2 ≤ (RadixCodec.passConstant+101000025)*(t+d+2)^5 := by
  have hav := affineCall_run_core a u v st hc ha
  have hac := affineCall_cost_core a u v st hc ha
  have hq := (run_regs_frame affineCall 45 (by decide) st).trans hc.2.1
  have hrc := radix_cost _ (affineCall.run st).1 hq hav
  have h45 : (t+d+2)^4 ≤ (t+d+2)^5 := Nat.pow_le_pow_right (by omega) (by decide)
  have hac' := hac.trans (Nat.mul_le_mul_left 101000000
    (Nat.pow_le_pow_left (by omega : t+d+1 ≤ t+d+2) 5))
  have hrc' := hrc.trans (Nat.mul_le_mul_left (RadixCodec.passConstant+20) h45)
  have hpos : 1 ≤ (t+d+2)^5 := Nat.one_le_pow _ _ (by omega)
  rw [scalarPoint, run_seq_snd]
  nlinarith only [hac', hrc', hpos]

end PCP.Lang.StandardCorrection
