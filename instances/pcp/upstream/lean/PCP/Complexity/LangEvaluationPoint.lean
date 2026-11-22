import PCP.Complexity.BinaryFieldCodePowerCost
import PCP.Algebraic.SetMultilinear
import PCP.Complexity.LangFramedTabulation

/-!
# Stored coordinates of the four-block power sampler

Each coordinate is computed by materialized binary field powering. The numeric
index follows the production finite-product codec: the digit varies first.
-/

set_option maxRecDepth 4096

namespace PCP.Lang.EvaluationPoint

open PCP.Algebraic

/-- Field-power workspace, disjoint from the enumeration registers. -/
def powerRegs (i : Fin 42) : Fin 47 := ⟨i.val + 4, by omega⟩
def powerLists (i : Fin 11) : Fin 13 := ⟨i.val + 2, by omega⟩

theorem powerRegs_injective : Function.Injective powerRegs := by
  intro i j h
  apply Fin.ext
  have := congrArg Fin.val h
  simp only [powerRegs] at this
  omega

theorem powerLists_injective : Function.Injective powerLists := by
  intro i j h
  apply Fin.ext
  have := congrArg Fin.val h
  simp only [powerLists] at this
  omega

def power : Stmt 47 13 := BinaryFieldCodePower.program.rename powerRegs powerLists

theorem power_result (st : State 47 13) :
    ((power.run st).1.restrict powerRegs powerLists, (power.run st).2) =
      BinaryFieldCodePower.program.run (st.restrict powerRegs powerLists) := by
  unfold power
  exact BinaryFieldCodePower.program.run_rename powerRegs powerLists
    powerRegs_injective powerLists_injective st

theorem power_reg_result (st : State 47 13) (i : Fin 42) :
    (power.run st).1.regs (powerRegs i) =
      (BinaryFieldCodePower.program.run (st.restrict powerRegs powerLists)).1.regs i := by
  have h := congrArg (fun z : State 42 11 × ℕ => z.1.regs i) (power_result st)
  simpa only [State.restrict_regs] using h

theorem power_list_result (st : State 47 13) (i : Fin 11) :
    (power.run st).1.lists (powerLists i) =
      (BinaryFieldCodePower.program.run (st.restrict powerRegs powerLists)).1.lists i := by
  have h := congrArg (fun z : State 42 11 × ℕ => z.1.lists i) (power_result st)
  simpa only [State.restrict_lists] using h

theorem power_reg_outside (x : Fin 47) (hx : x.val < 4 ∨ x = 46) (st : State 47 13) :
    (power.run st).1.regs x = st.regs x := by
  unfold power
  apply Stmt.run_rename_reg_outside
  intro i h
  have := congrArg Fin.val h
  simp only [powerRegs] at this
  rcases hx with hx | rfl <;> omega

theorem power_list_outside (L : Fin 13) (hL : L.val < 2) (st : State 47 13) :
    (power.run st).1.lists L = st.lists L := by
  unfold power
  apply Stmt.run_rename_list_outside
  intro i h
  have := congrArg Fin.val h
  simp only [powerLists] at this
  omega

/-- Coordinates numbered `k` use block `k / m` and digit `k % m`. -/
def exponent (m k : ℕ) : ℕ := k % m * m ^ (k / m)

def multiply : Stmt 47 13 := .assign 40 (.mul 40 46)

/-- Fixed linear budget for the exponent bit serialization. -/
def budget : Stmt 47 13 := .seq (.assign 41 (.const 4))
  (.seq (.assign 41 (.mul 41 46))
    (.seq (.assign 42 (.const 1)) (.assign 41 (.add 41 42))))

theorem budget_run (st : State 47 13) :
    (budget.run st).1.regs 40 = st.regs 40 ∧
    (budget.run st).1.regs 41 = 4 * st.regs 46 + 1 := by
  simp [budget, run_seq_fst, run_assign_fst, Expr.eval, Function.update]

/-- Prepare the coordinate exponent and a proved linear exponent-bit budget. -/
def prepare : Stmt 47 13 := .seq (.assign 40 (.mod 0 46))
  (.seq (.assign 36 (.div 0 46)) (.seq (.loop 36 multiply) budget))

theorem multiply_iterate (c n : ℕ) (st : State 47 13) :
    (iterate multiply.run c n st).1.regs 40 = st.regs 40 * st.regs 46 ^ n ∧
    (iterate multiply.run c n st).1.regs 46 = st.regs 46 := by
  induction n generalizing st with
  | zero => simp [iterate]
  | succ n ih =>
      rw [iterate_succ_fst]
      have h := ih (multiply.run st).1
      simp only [multiply, run_assign_fst, Expr.eval, setReg_regs,
        Function.update_self, Function.update_of_ne (by decide : (46 : Fin 47) ≠ 40)] at h
      simpa [multiply, run_assign_fst, Expr.eval, pow_succ,
        Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using h

theorem prepare_run (st : State 47 13) :
    (prepare.run st).1.regs 40 = exponent (st.regs 46) (st.regs 0) ∧
    (prepare.run st).1.regs 41 = 4 * st.regs 46 + 1 := by
  let s := setReg (setReg st 40 (st.regs 0 % st.regs 46)) 36 (st.regs 0 / st.regs 46)
  have h := multiply_iterate (Nat.size (s.regs 36) + 1) (s.regs 36) s
  have hb := budget_run (iterate multiply.run (Nat.size (s.regs 36) + 1) (s.regs 36) s).1
  simp only [prepare, run_seq_fst, run_assign_fst, Expr.eval, setReg_regs,
    Function.update_of_ne (by decide : (0 : Fin 47) ≠ 40),
    Function.update_of_ne (by decide : (46 : Fin 47) ≠ 40), run_loop_fst]
  exact ⟨hb.1.trans (by simpa [s, Function.update, exponent] using h.1),
    hb.2.trans (by rw [h.2]; simp [s, Function.update])⟩

private theorem size_power (m i : ℕ) : Nat.size (m ^ i) ≤ i * Nat.size m + 1 := by
  induction i with
  | zero => simp
  | succ i ih =>
      have h := size_mul_le (m ^ i) m
      rw [← pow_succ] at h
      nlinarith

theorem exponent_size (m k : ℕ) (hm : 0 < m) (hk : k < 4 * m) :
    Nat.size (exponent m k) ≤ 4 * m + 1 := by
  have hi : k / m < 4 := (Nat.div_lt_iff_lt_mul hm).2 (by omega)
  have hj := Nat.size_le_size (Nat.mod_lt k hm).le
  have hp := size_power m (k / m)
  have hx := size_mul_le (k % m) (m ^ (k / m))
  have hs := size_le_self m
  dsimp [exponent]
  nlinarith

/-- Scalar kernel for one consecutive stored coordinate. -/
def kernel : Stmt 47 13 := .seq prepare (.seq power (.assign 1 (.var 30)))

variable {t : ℕ} [NeZero t]

/-- Retained field data and the sampler's numeric base. -/
def View (m : ℕ) (a : BinaryMaterializedField.Element t) (st : State 47 13) : Prop :=
  st.regs 24 = t ∧ st.regs 28 = (BinaryFieldCode.fieldEquiv t a).val ∧
  st.regs 46 = m ∧
  st.lists 5 = BinaryField.encode (BinaryWordMaterialization.modulus t) ∧ st.lists 9 = []

theorem view_stable (m : ℕ) (a : BinaryMaterializedField.Element t) :
    FramedTabulation.Stable (View m a) := by
  refine ⟨?_, ?_, ?_⟩ <;> intro st hs v <;> simpa [View, Function.update] using hs

theorem prepare_view (m : ℕ) (a : BinaryMaterializedField.Element t) (st : State 47 13)
    (hs : View m a st) : View m a (prepare.run st).1 := by
  exact ⟨(run_regs_frame prepare 24 (by decide) st).trans hs.1,
    (run_regs_frame prepare 28 (by decide) st).trans hs.2.1,
    (run_regs_frame prepare 46 (by decide) st).trans hs.2.2.1,
    (run_lists_frame prepare 5 (by decide) st).trans hs.2.2.2.1,
    (run_lists_frame prepare 9 (by decide) st).trans hs.2.2.2.2⟩

theorem kernel_run (m : ℕ) (a : BinaryMaterializedField.Element t) (st : State 47 13)
    (hm : 0 < m) (hk : st.regs 0 < 4 * m) (hs : View m a st) :
    (kernel.run st).1.regs 1 =
      (BinaryFieldCode.fieldEquiv t (a ^ exponent m (st.regs 0))).val := by
  have hp := prepare_run st
  have hv := prepare_view m a st hs
  rw [hs.2.2.1] at hp
  generalize hu : (prepare.run st).1 = u at *
  have hr := BinaryFieldCodePower.program_run (u.restrict powerRegs powerLists) a
    (exponent m (st.regs 0)) (4 * m + 1) hv.1 hv.2.1 hp.1 hp.2
    (exponent_size m _ hm hk) hv.2.2.2.1 hv.2.2.2.2
  rw [← power_result u] at hr
  simp only [State.restrict_regs, show powerRegs 26 = (30 : Fin 47) from rfl] at hr
  simp only [kernel, run_seq_fst, hu, run_assign_fst, Expr.eval, setReg_regs,
    Function.update_self]
  exact hr

theorem power_view (m : ℕ) (a : BinaryMaterializedField.Element t) (st : State 47 13)
    (hs : View m a st) : View m a (power.run st).1 := by
  have hp := BinaryFieldCodePower.program_frame (st.restrict powerRegs powerLists)
  rw [← power_result st] at hp
  simp only [State.restrict_regs, State.restrict_lists,
    show powerRegs 20 = (24 : Fin 47) from rfl,
    show powerRegs 24 = (28 : Fin 47) from rfl,
    show powerLists 3 = (5 : Fin 13) from rfl,
    show powerLists 7 = (9 : Fin 13) from rfl] at hp
  dsimp only [View] at hs ⊢
  rw [hp.1, hp.2.1, power_reg_outside 46 (Or.inr rfl) st, hp.2.2.2.2.1, hp.2.2.2.2.2]
  exact hs


theorem kernel_view (m : ℕ) (a : BinaryMaterializedField.Element t) (st : State 47 13)
    (hs : View m a st) : View m a (kernel.run st).1 := by
  have hv := power_view m a (prepare.run st).1 (prepare_view m a st hs)
  simpa [kernel, run_seq_fst, run_assign_fst, View, Function.update] using hv

theorem kernel_reg (st : State 47 13) (x : Fin 47) (hx : x.val < 4) (hx1 : x ≠ 1) :
    (kernel.run st).1.regs x = st.regs x := by
  have hp := power_reg_outside x (Or.inl hx) (prepare.run st).1
  have hs : (prepare.run st).1.regs x = st.regs x := by
    apply run_regs_frame
    simp only [prepare, budget, multiply, Stmt.regWrites, List.mem_append,
      List.mem_cons, List.not_mem_nil, or_false]
    intro h
    rcases h with h | h | h | h | h | h | h <;> subst x <;> norm_num at hx
  simp only [kernel, run_seq_fst, run_assign_fst, setReg_regs,
    Function.update_of_ne hx1]
  exact hp.trans hs

theorem kernel_list (st : State 47 13) (L : Fin 13) (hL : L.val < 2) :
    (kernel.run st).1.lists L = st.lists L := by
  have hp := power_list_outside L hL (prepare.run st).1
  have hs : (prepare.run st).1.lists L = st.lists L := by
    apply run_lists_frame
    simp [prepare, budget, multiply, Stmt.listWrites]
  simp only [kernel, run_seq_fst, run_assign_fst, setReg_lists]
  exact hp.trans hs

theorem kernel_spec (m : ℕ) (a : BinaryMaterializedField.Element t) (input : List ℕ)
    (hm : 0 < m) : FramedTabulation.KernelSpec kernel input (4 * m)
      (fun k => (BinaryFieldCode.fieldEquiv t (a ^ exponent m k)).val) (View m a) := by
  intro st hi h2 h3 hk hs
  have h0 := kernel_reg st 0 (by decide) (by decide)
  have h2' := kernel_reg st 2 (by decide) (by decide)
  have h3' := kernel_reg st 3 (by decide) (by decide)
  have hl0 := kernel_list st 0 (by decide)
  have hl1 := kernel_list st 1 (by decide)
  have hout := kernel_run m a st hm hk hs
  have hv := kernel_view m a st hs
  simp only [h0, h2', h3', hl0, hl1, hout, h2, h3, hi, hv, and_self]

/-- Enumerate all four blocks in the production variable order. -/
def program : Stmt 47 13 := .seq (.assign 3 (.const 4))
  (.seq (.assign 3 (.mul 3 46)) (Tabulation.tabulate kernel))

theorem program_run (m : ℕ) (a : BinaryMaterializedField.Element t) (st : State 47 13)
    (hm : 0 < m) (hs : View m a st) (he : st.lists 1 = []) :
    (program.run st).1.lists 1 = (List.range (4 * m)).map
      (fun k => (BinaryFieldCode.fieldEquiv t (a ^ exponent m k)).val) ∧
    (program.run st).1.lists 0 = st.lists 0 ∧ View m a (program.run st).1 := by
  let s := setReg (setReg st 3 4) 3 (4 * m)
  have hv : View m a s := by simpa [View, s, Function.update] using hs
  have hr := FramedTabulation.tabulate_spec (kernel_spec m a (st.lists 0) hm)
    (view_stable m a) s rfl (by simp [s, Function.update]) he hv
  simpa [program, run_seq_fst, run_assign_fst, Expr.eval, Function.update, hs.2.2.1, s]
    using hr

/-- The computed list is precisely the semantic sampler in the address codec's order. -/
theorem program_evaluationPoint (m : ℕ) [NeZero m] (a : BinaryMaterializedField.Element t)
    (st : State 47 13) (hs : View m a st) (he : st.lists 1 = []) :
    (program.run st).1.lists 1 = List.ofFn (fun k : Fin (4 * m) =>
      (BinaryFieldCode.fieldEquiv t
        (SetMultilinear.evaluationPoint m 4 a (finProdFinEquiv.symm k))).val) := by
  rw [(program_run m a st (NeZero.pos m) hs he).1]
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp only [List.getElem_map, List.getElem_range, List.getElem_ofFn]
    rfl

end PCP.Lang.EvaluationPoint
