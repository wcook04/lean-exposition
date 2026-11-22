import PCP.Complexity.ThreeColorNodeSetup

/-!
# Charged cost of the five materialized interpolation nodes
-/

namespace PCP.Lang.ThreeColorContext

open PCP.Algebraic ThreeColorParameters BinaryFieldCode

theorem nodePrepare_cost (a : ℕ) (i : Fin 5) (st : State 50 15) (h : Roots a st) :
    ((nodePrepare i).run st).2 ≤ 2 * binaryDimension a + 30 := by
  have hr : Nat.size (st.regs 49) ≤ binaryDimension a := by
    rw [h.2.2.2]
    exact Nat.size_le.mpr (Fin.isLt _)
  have hi : Nat.size (i.val+1) ≤ 3 := Nat.size_le.mpr (by have := i.isLt; omega)
  simp only [nodePrepare, Stmt.run, Expr.cost, Expr.readSize, Expr.eval]
  change Nat.size (st.regs 49) + Nat.size (st.regs 49) + 1 +
    (Nat.size (i.val+1) + Nat.size (i.val+1) + 1 + 5 + 1) + 1 ≤ _
  omega

theorem nodeStep_cost (a : ℕ) (i : Fin 5) (st : State 50 15) (h : Roots a st) :
    ((nodeStep i).run st).2 ≤ 40000000 * (2 ^ binaryDimension a + 4) ^ 4 := by
  have hpc := nodePrepare_cost a i st h
  have hcode := nodeStep_code a i st h
  have h20 : ((nodePrepare i).run st).1.regs 20 = binaryDimension a := by
    simpa [nodePrepare, Stmt.run, Function.update] using h.1.1
  have h24 : ((nodePrepare i).run st).1.regs 24 =
      (fieldEquiv (binaryDimension a) (generator a)).val := by
    have hp : ((nodePrepare i).run st).1.regs 24 = st.regs 49 := by
      simp [nodePrepare, Stmt.run, Expr.eval, Function.update]
    rw [hp, ProductionGrid.fieldEquiv_eq_fieldCode]
    exact h.2.2.2
  have h36 : ((nodePrepare i).run st).1.regs 36 = i.val+1 := by
    simp [nodePrepare, Stmt.run, Expr.eval, Function.update]
  have h37 : ((nodePrepare i).run st).1.regs 37 = 3 := by
    simp [nodePrepare, Stmt.run, Expr.eval, Function.update]
  have hm : ((nodePrepare i).run st).1.lists 3 =
      BinaryField.encode (BinaryWordMaterialization.modulus (binaryDimension a)) := h.1.2.2.1
  have he : ((nodePrepare i).run st).1.lists 7 = [] := h.1.2.2.2
  have h47 : ((nodePrepare i).run st).1.regs 47 = 2 ^ binaryDimension a := by
    simpa [nodePrepare, Stmt.run, Function.update] using h.2.1
  have hn : Nat.size (i.val+1) ≤ 3 := Nat.size_le.mpr (by have := i.isLt; omega)
  generalize hu : ((nodePrepare i).run st).1 = u at *
  have hc := BinaryFieldCodePower.program_cost (t := binaryDimension a)
    (u.restrict powerRegs fieldLists) (generator a) (i.val+1) 3 h20 h24 h36 h37 hn hm he
  have ht := congrArg Prod.snd (powerCall_result u)
  dsimp only [Prod.snd] at ht
  rw [← ht] at hc
  have hp47 := run_regs_frame powerCall 47 (by decide) u
  generalize hv : (powerCall.run u).1 = v at *
  have hsz47 : Nat.size (v.regs 47) ≤ 2 ^ binaryDimension a := by
    rw [hp47, h47]
    exact size_le_self _
  simp only [nodeStep, run_seq_fst, hu, hv, run_assign_fst, Expr.eval, run_push_fst,
    setList_regs, setReg_regs, Function.update_of_ne (by decide : (26 : Fin 50) ≠ 28)] at hcode
  have hsz26 : Nat.size (v.regs 26) ≤ binaryDimension a := by
    rw [hcode]
    exact Nat.size_le.mpr (Fin.isLt _)
  let q := 2 ^ binaryDimension a
  have htq : binaryDimension a ≤ q := (Nat.lt_two_pow_self).le
  have hc' : (powerCall.run u).2 ≤ 30000000 * (q + 4) ^ 4 :=
    hc.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 4))
  have hpow : q + 4 ≤ (q + 4) ^ 4 := le_self_pow₀ (by omega) (by decide)
  simp only [nodeStep, run_seq_snd, hu, hv, run_assign_fst, Expr.eval, run_push_snd,
    setReg_regs,
    Function.update_of_ne (by decide : (26 : Fin 50) ≠ 28)]
  change ((nodePrepare i).run st).2 + ((powerCall.run u).2 +
    (Nat.size (v.regs 47) + Nat.size (v.regs 47) + 1 +
      (Nat.size (v.regs 26) + 1) + 1) + 1) + 1 ≤ 40000000 * (q + 4) ^ 4
  change Nat.size (v.regs 47) ≤ q at hsz47
  nlinarith

theorem nodeSequence_cost (a : ℕ) (is : List (Fin 5)) (st : State 50 15)
    (h : Roots a st) :
    ((nodeSequence is).run st).2 ≤
      is.length * (40000000 * (2 ^ binaryDimension a + 4) ^ 4 + 1) + 1 := by
  induction is generalizing st with
  | nil => simp [nodeSequence, Stmt.run]
  | cons i is ih =>
    have hc := nodeStep_cost a i st h
    have ht := ih ((nodeStep i).run st).1 (nodeStep_roots a i st h)
    simp only [nodeSequence, run_seq_snd, List.length_cons]
    nlinarith

theorem nodeCodes_size (a : ℕ) :
    listSize (List.ofFn (fun i : Fin 5 => (fieldCode a (nodes a i)).val)) ≤
      5 * (binaryDimension a + 1) := by
  have hb (is : List (Fin 5)) :
      listSize (is.map (fun i => (fieldCode a (nodes a i)).val)) ≤
        is.length * (binaryDimension a + 1) := by
    induction is with
    | nil => simp [listSize]
    | cons i is ih =>
      have hi : Nat.size ((fieldCode a (nodes a i)).val) ≤ binaryDimension a :=
        Nat.size_le.mpr (Fin.isLt _)
      simp only [List.map_cons, listSize, List.sum_cons, List.length_cons] at ih ⊢
      nlinarith
  simpa only [List.ofFn_eq_map, List.length_finRange] using hb (List.finRange 5)

theorem storeNodes_cost (a : ℕ) (st : State 50 15) (h : Roots a st) :
    (storeNodes.run st).2 ≤ 300000000 * (2 ^ binaryDimension a + 4) ^ 4 := by
  let s := setList st 14 []
  have hs : Roots a s := by simpa [Roots, FieldContext, s, Function.update] using h
  have hc := nodeSequence_cost a (List.finRange 5) s hs
  have hp := nodeSequence_run a (List.finRange 5) s hs
  have hout : ((nodeSequence (List.finRange 5)).run s).1.lists 14 =
      (List.ofFn (fun i : Fin 5 => (fieldCode a (nodes a i)).val)).reverse := by
    simpa only [List.ofFn_eq_map, s, setList_lists, Function.update_self,
      List.append_nil] using hp.2
  have hsz := nodeCodes_size a
  simp only [List.length_finRange] at hc
  let q := 2 ^ binaryDimension a
  have htq : binaryDimension a ≤ q := (Nat.lt_two_pow_self).le
  have hpow : q + 4 ≤ (q + 4) ^ 4 := le_self_pow₀ (by omega) (by decide)
  dsimp only [s] at hc hout
  simp only [storeNodes, run_seq_snd, run_copy_snd, run_copy_fst, run_rev_snd, h.1.2.2.2]
  rw [hout, listSize_reverse]
  simp only [show listSize ([] : List ℕ) = 0 from rfl, zero_add]
  change _ ≤ 300000000 * (q + 4) ^ 4
  change _ ≤ 5 * (40000000 * (q + 4) ^ 4 + 1) + 1 at hc
  nlinarith

end PCP.Lang.ThreeColorContext
