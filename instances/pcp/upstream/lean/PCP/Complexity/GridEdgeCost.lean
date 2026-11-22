import PCP.Complexity.GridEdgeKernelCost

/-!
# Polynomial charged cost of the complete public edge interpolation program
-/

namespace PCP.Lang.GridEdge

open PCP.Algebraic BinaryFieldCode

variable {t h n : ℕ} [NeZero t]

def ReaderBound (C : ℕ) : Prop := ∀ (st : State 70 20) (W : ℕ),
  (∀ i ∈ [51, 53, 55], Nat.size (st.regs i) ≤ W) → listSize (st.lists 16) ≤ W →
    (reader.run st).2 ≤ C * (W + 1) ^ 2

def passConstant (C : ℕ) : ℕ :=
  C + 81 * (MixedRadixDecode.passConstant + 20) + 145822000040

theorem body_cost (C : ℕ) (hC : ReaderBound C)
    (hh : h ≤ 2 ^ t) (x : List Bool)
    (z : Fin (n + n) → BinaryMaterializedField.Element t) (j : Fin (h ^ (n + n)))
    (a : BinaryMaterializedField.Element t) (st : State 70 20)
    (hc : Context t h n x z st) (hj : st.regs 51 = j.val)
    (ha : st.regs 50 = (fieldEquiv t a).val) (W : ℕ) (hw : Budget t h n x W) :
    (body.run st).2 ≤ passConstant C * (W + 1) ^ 6 := by
  have hk := kernel_cost_of_reader_bound C hC hh x z j a st hc hj ha W hw
  have hkc := context_readOnly kernel_readOnly x z st hc
  have hki := (kernel_counter st).trans hj
  have hsj : Nat.size j.val ≤ W := (size_le_self _).trans (j.isLt.le.trans hw.2.2.2.1)
  have hsj' : Nat.size (j.val + 1) ≤ W + 1 := (size_le_self _).trans (by
    have := j.isLt; have := hw.2.2.2.1; omega)
  have hlin : W + 1 ≤ (W + 1) ^ 6 := by
    simpa using Nat.pow_le_pow_right (by omega : 1 ≤ W + 1) (by decide : 1 ≤ 6)
  rw [body, run_seq_snd]
  simp only [bump, Stmt.run, Expr.cost, Expr.readSize, Expr.eval, hki,
    hkc.2.2.2.2.2.2.1, Nat.size_one, passConstant]
  nlinarith only [hk, hsj, hsj', hlin]

theorem iterate_cost (C : ℕ) (hC : ReaderBound C)
    (hh : h ≤ 2 ^ t) (x : List Bool)
    (z : Fin (n + n) → BinaryMaterializedField.Element t) (k j : ℕ)
    (hjk : j + k ≤ h ^ (n + n)) (a : BinaryMaterializedField.Element t)
    (c : ℕ) (st : State 70 20) (hc : Context t h n x z st)
    (hj : st.regs 51 = j) (ha : st.regs 50 = (fieldEquiv t a).val)
    (W : ℕ) (hw : Budget t h n x W) :
    (iterate body.run c k st).2 ≤ k * (c + passConstant C * (W + 1) ^ 6) := by
  induction k generalizing j a st with
  | zero => simp [iterate]
  | succ k ih =>
    have hjlt : j < h ^ (n + n) := by omega
    have hb := body_run hh x z ⟨j, hjlt⟩ a st hc hj ha
    have hbc := body_cost C hC hh x z ⟨j, hjlt⟩ a st hc hj ha W hw
    have ht := ih (j+1) (by omega) (a + term hh x z j) (body.run st).1
      hb.1 hb.2.1 hb.2.2
    simp only [iterate, Nat.succ_mul]
    omega

theorem loop_cost (C : ℕ) (hC : ReaderBound C)
    (hh : h ≤ 2 ^ t) (x : List Bool)
    (z : Fin (n + n) → BinaryMaterializedField.Element t)
    (st : State 70 20) (hc : Context t h n x z st) (hj : st.regs 51 = 0)
    (ha : st.regs 50 = (fieldEquiv t (0 : BinaryMaterializedField.Element t)).val)
    (W : ℕ) (hw : Budget t h n x W) :
    (loop.run st).2 ≤ (passConstant C + 3) * (W + 1) ^ 7 := by
  have hi := iterate_cost C hC hh x z (h ^ (n + n)) 0 (by omega) 0
    (Nat.size (h ^ (n + n)) + 1) st hc hj ha W hw
  have hs := (size_le_self (h ^ (n + n))).trans hw.2.2.2.1
  have hlin : W + 1 ≤ (W + 1) ^ 6 := by
    simpa using Nat.pow_le_pow_right (by omega : 1 ≤ W + 1) (by decide : 1 ≤ 6)
  have hpass : Nat.size (h ^ (n + n)) + 1 + passConstant C * (W+1)^6 ≤
      (passConstant C + 1) * (W+1)^6 := by nlinarith only [hs, hlin]
  have hprod := Nat.mul_le_mul (hw.2.2.2.1.trans (by omega : W ≤ W+1)) hpass
  have hlin' : W + 1 ≤ (W + 1)^7 := hlin.trans (Nat.pow_le_pow_right (by omega) (by decide))
  rw [loop, run_loop_snd, hc.2.2.1]
  nlinarith only [hi, hprod, hs, hlin']

/-- A concrete bound on every semantic input magnitude. -/
def budget (t h n : ℕ) (x : List Bool) : ℕ :=
  listSize (x.map Bool.toNat) + h ^ (n + n) + h ^ n + (n + n) + h + t + 2

omit [NeZero t] in
theorem budget_spec (t h n : ℕ) (x : List Bool) : Budget t h n x (budget t h n x) := by
  have hv : ThreeColorEncoding.vertexCount x ≤ listSize (x.map Bool.toNat) :=
    (ThreeColorEncoding.size_le_length x).trans
      (by simpa only [List.length_map] using length_le_listSize (x.map Bool.toNat))
  dsimp [Budget, budget]
  omega

omit [NeZero t] in
theorem header_cost (st : State 70 20) (x : List Bool)
    (hx : st.lists 16 = x.map Bool.toNat) :
    (header.run st).2 ≤ 100 * (listSize (x.map Bool.toNat) + 1)^2 := by
  rw [header, Stmt.run_rename_cost _ _ _ headerRegs_injective headerLists_injective]
  have hp := GraphHeader.program_cost (st.restrict headerRegs headerLists) (by
    change ∀ v ∈ st.lists 16, v ≤ 1
    rw [hx]
    intro v hv
    obtain ⟨b, _, rfl⟩ := List.mem_map.mp hv
    cases b <;> decide)
  simpa only [State.restrict_lists, show headerLists 0 = (16 : Fin 20) from rfl, hx] using hp

omit [NeZero t] in
theorem partial_power_le (h j n : ℕ) (hj : j ≤ n) : h ^ j ≤ h ^ n + 1 := by
  by_cases hz : h = 0
  · subst h
    cases j <;> simp
  · exact (Nat.pow_le_pow_right (by omega : 1 ≤ h) hj).trans (by omega)

omit [NeZero t] in
theorem power_iterate_cost (h n W j k c : ℕ) (hjk : j + k ≤ n)
    (hh : h ≤ W) (hp : h ^ n ≤ W) (st : State 70 20)
    (h45 : st.regs 45 = h) (h55 : st.regs 55 = h ^ j) :
    (iterate powerBody.run c k st).2 ≤ k * (c + 3*W+4) := by
  induction k generalizing j st with
  | zero => simp [iterate]
  | succ k ih =>
    have hsj : Nat.size (h ^ j) ≤ W+1 := (size_le_self _).trans
      ((partial_power_le h j n (by omega)).trans (by omega))
    have hsj' : Nat.size (h ^ (j+1)) ≤ W+1 := (size_le_self _).trans
      ((partial_power_le h (j+1) n (by omega)).trans (by omega))
    have hsh := (size_le_self h).trans hh
    have hbody : (powerBody.run st).2 ≤ 3*W+4 := by
      simp only [powerBody, Stmt.run, Expr.cost, Expr.readSize, Expr.eval, h45, h55,
        ← pow_succ]
      omega
    have hs45 : (powerBody.run st).1.regs 45 = h := by
      simpa [powerBody, Stmt.run, Function.update] using h45
    have hs55 : (powerBody.run st).1.regs 55 = h ^ (j+1) := by
      simp [powerBody, Stmt.run, Expr.eval, h45, h55, pow_succ]
    have ht := ih (j+1) (by omega) _ hs45 hs55
    change c + (powerBody.run st).2 + (iterate powerBody.run c k (powerBody.run st).1).2 ≤ _
    nlinarith only [hbody, ht]

omit [NeZero t] in
theorem capacity_cost (h n W : ℕ) (st : State 70 20)
    (hh : h ≤ W) (hn : n ≤ W) (hp : h ^ n ≤ W)
    (h45 : st.regs 45 = h) (h54 : st.regs 54 = n) :
    (capacity.run st).2 ≤ 10*(W+1)^2 := by
  let s := setReg st 55 1
  have hit := power_iterate_cost h n W 0 n (Nat.size n+1) (by omega) hh hp s
    (by simpa [s, Function.update] using h45) (by simp [s])
  have hs54 : s.regs 54 = n := by simpa [s, Function.update] using h54
  have hsn := (size_le_self n).trans hn
  have hprod := Nat.mul_le_mul hn (show Nat.size n+1+3*W+4 ≤ 4*W+5 by omega)
  simp only [capacity, run_seq_snd, run_assign_fst, Expr.eval, run_loop_snd]
  have hass : ((Stmt.assign 55 (.const 1)).run st).2 = 3 := by
    simp [Stmt.run, Expr.cost, Expr.readSize, Expr.eval]
  rw [hass]
  change 3 + ((iterate powerBody.run (Nat.size (s.regs 54)+1) (s.regs 54) s).2 +
    Nat.size (s.regs 54)+1)+1 ≤ _
  rw [hs54]
  nlinarith only [hit, hprod, hsn]

omit [NeZero t] in
theorem finishSetup_cost (h n W : ℕ) (st : State 70 20)
    (hn : n + n ≤ W) (hp : h ^ n ≤ W) (hpp : h ^ (n + n) ≤ W)
    (h54 : st.regs 54 = n) (h55 : st.regs 55 = h ^ n) :
    (finishSetup.run st).2 ≤ 20*(W+1) := by
  have hs := (size_le_self (h ^ n)).trans hp
  have hss := (size_le_self (h ^ (n + n))).trans hpp
  have hsn := (size_le_self n).trans (show n ≤ W by omega)
  have hsd := (size_le_self (n + n)).trans hn
  simp only [finishSetup, run_seq_snd, run_assign_fst, Expr.eval, setReg_regs,
    Function.update, Fin.reduceEq, dite_false]
  simp only [Stmt.run, Expr.cost, Expr.readSize, Expr.eval, setReg_regs,
    Function.update, Fin.reduceEq, dite_false, h54, h55, ← pow_add,
    Nat.size_one, Nat.size_zero]
  omega

/-- Both preprocessing loops are charged, including the copied public graph. -/
theorem setup_cost (x : List Bool) (z : Fin (n + n) → BinaryMaterializedField.Element t)
    (st : State 70 20) (hi : Input t h n x z st) (W : ℕ) (hw : Budget t h n x W) :
    (setup.run st).2 ≤ 150*(W+1)^2 := by
  have hh := header_cost st x hi.2.2.2.2.2.2
  have hh' := hh.trans (Nat.mul_le_mul_left 100 (Nat.pow_le_pow_left
    (Nat.add_le_add_right hw.2.2.2.2.2.2 1) 2))
  have hsi := header_input x z st hi
  simp only [setup, run_seq_snd]
  generalize hs : (header.run st).1 = s at *
  have hcap := capacity_cost h n W s hw.2.1 (by have := hw.2.2.1; omega)
    hw.2.2.2.2.1 hsi.2.1 hsi.2.2.1
  have hui := capacity_input x z s hsi
  have hup := capacity_run s
  rw [hsi.2.1, hsi.2.2.1] at hup
  generalize hu : (capacity.run s).1 = u at *
  have hfin := finishSetup_cost h n W u hw.2.2.1 hw.2.2.2.2.1 hw.2.2.2.1 hui.2.2.1 hup
  nlinarith only [hh', hcap, hfin]

/-- A single constant bounds the executable program for every field, grid and public input. -/
theorem program_cost : ∃ C : ℕ, ∀ (t h n : ℕ) [NeZero t] (_hh : h ≤ 2^t)
    (x : List Bool) (z : Fin (n + n) → BinaryMaterializedField.Element t)
    (st : State 70 20), Input t h n x z st →
      (program.run st).2 ≤ C * (budget t h n x + 1)^7 := by
  obtain ⟨C, hC⟩ := reader_cost
  refine ⟨passConstant C + 154, ?_⟩
  intro t h n _ hh x z st hi
  have hw := budget_spec t h n x
  have hs := setup_cost x z st hi _ hw
  have hr := setup_run x z st hi
  have hl := loop_cost C hC hh x z (setup.run st).1 hr.1 hr.2.1 hr.2.2 _ hw
  have hp : (budget t h n x + 1)^2 ≤ (budget t h n x + 1)^7 :=
    Nat.pow_le_pow_right (by omega) (by decide)
  have hp1 : 1 ≤ (budget t h n x + 1)^7 := Nat.one_le_pow _ _ (by omega)
  have hs' := hs.trans (Nat.mul_le_mul_left 150 hp)
  rw [program, run_seq_snd]
  nlinarith only [hl, hs', hp1]

end PCP.Lang.GridEdge
