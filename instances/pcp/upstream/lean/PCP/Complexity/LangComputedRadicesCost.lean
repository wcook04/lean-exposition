import PCP.Complexity.LangComputedRadices

/-!
# Charged cost of computing the exact sampler radices
-/

namespace PCP.Lang.ComputedRadices

open ArithmeticExpression

variable (terms : Fin 7 → Term 4)

def computeConstant (i : Fin 7) : ℕ :=
  (scalar (terms i)).C * ((scalar (terms i)).width + (scalar (terms i)).csize + 1)

def emitConstant : ℕ := (∑ i, computeConstant terms i) + 40

theorem compute_cost (i : Fin 7) (n m c t W : ℕ) (st : State 15 2)
    (hc : Context n m c t st) (hs : ∀ j : Fin 4, Nat.size (![n, m, c, t] j) ≤ W) :
    ((compute terms i).run st).2 ≤ computeConstant terms i * (W + 1) := by
  rw [compute, Stmt.run_rename_cost _ _ _ (Fin.castLE_injective _) Function.injective_id]
  apply scalar_cost_inputs (terms i) _ W
  intro j
  change Nat.size (st.regs (j.castAdd 11)) ≤ W
  rw [hc j]
  exact hs j

theorem power_cost (st : State 15 2) :
    (power.run st).2 ≤ 20 * (st.regs 9 + 1) ^ 2 := by
  rw [power, Stmt.run_rename_cost _ _ _ (Fin.natAdd_injective _ _) Function.injective_id]
  exact PowerTwo.program_cost _

theorem emit_cost (i : Fin 7) (n m c t B W : ℕ) (st : State 15 2)
    (hc : Context n m c t st) (hs : ∀ j : Fin 4, Nat.size (![n, m, c, t] j) ≤ W)
    (hb : (terms i).eval ![n, m, c, t] ≤ B) :
    ((emit terms i).run st).2 ≤ emitConstant terms * (B + W + 1) ^ 2 := by
  have hcr := (compute_run terms i n m c t st hc).1
  have hcc := compute_cost terms i n m c t W st hc hs
  generalize hu : ((compute terms i).run st).1 = u at *
  let s := setReg u 9 (u.regs 4)
  have hsr : s.regs 9 = (terms i).eval ![n, m, c, t] := by simpa [s] using hcr
  have hp := power_run s
  have hpc := power_cost s
  rw [hsr] at hp hpc
  have hi : computeConstant terms i ≤ ∑ j, computeConstant terms j :=
    Finset.single_le_sum (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
  have hsz := (size_le_self ((terms i).eval ![n, m, c, t])).trans hb
  have h1 : 1 ≤ B + W + 1 := by omega
  have hsq : B + W + 1 ≤ (B + W + 1) ^ 2 := Nat.le_pow (by decide)
  have hpow : ((terms i).eval ![n, m, c, t] + 1) ^ 2 ≤ (B + W + 1) ^ 2 :=
    Nat.pow_le_pow_left (by omega) _
  have hpc' := hpc.trans (Nat.mul_le_mul_left _ hpow)
  have hcc' := hcc.trans (Nat.mul_le_mul hi
    (show W + 1 ≤ (B + W + 1) ^ 2 by omega))
  simp only [emit, run_seq_snd, hu, run_assign_fst, Expr.eval, run_push_snd]
  change ((compute terms i).run st).2 + ((Expr.var 4).cost u.regs +
    ((power.run s).2 + (Nat.size ((power.run s).1.regs 12) + 1) + 1) + 1) + 1 ≤ _
  simp only [Expr.cost, Expr.readSize, Expr.eval, hcr, hp, Nat.size_pow]
  unfold emitConstant
  nlinarith only [hcc', hpc', hb, hsz, hsq, h1]

theorem emitAll_cost (is : List (Fin 7)) (n m c t B W : ℕ) (st : State 15 2)
    (hc : Context n m c t st) (hs : ∀ j : Fin 4, Nat.size (![n, m, c, t] j) ≤ W)
    (hb : ∀ i, (terms i).eval ![n, m, c, t] ≤ B) :
    ((emitAll terms is).run st).2 ≤ is.length * (emitConstant terms * (B + W + 1) ^ 2 + 1) + 1 := by
  induction is generalizing st with
  | nil => simp [emitAll, Stmt.run]
  | cons i is ih =>
      have hr := (emit_run terms i n m c t st hc).2.1
      have hcost := emit_cost terms i n m c t B W st hc hs (hb i)
      have hit := ih ((emit terms i).run st).1 hr
      simp only [emitAll, run_seq_snd, List.length_cons]
      nlinarith

theorem radices_size (is : List (Fin 7)) (n m c t B : ℕ)
    (hb : ∀ i, (terms i).eval ![n, m, c, t] ≤ B) :
    listSize (is.map (fun i => 2 ^ (terms i).eval ![n, m, c, t])) ≤ is.length * (B + 2) := by
  induction is with
  | nil => simp [listSize]
  | cons i is ih =>
      simp only [List.map_cons, listSize, List.sum_cons, Nat.size_pow, List.length_cons] at ih ⊢
      have := hb i
      nlinarith

/-- Only seven fixed computations occur; numeric output magnitudes are never loop bounds. -/
theorem program_cost (n m c t B W : ℕ) (st : State 15 2)
    (hc : Context n m c t st) (he : st.lists 0 = [])
    (hs : ∀ j : Fin 4, Nat.size (![n, m, c, t] j) ≤ W)
    (hb : ∀ i, (terms i).eval ![n, m, c, t] ≤ B) :
    ((program terms).run st).2 ≤ (7 * emitConstant terms + 40) * (B + W + 1) ^ 2 := by
  have hrun := (emitAll_run terms (List.finRange 7) n m c t st hc).1
  have hcost := emitAll_cost terms (List.finRange 7) n m c t B W st hc hs hb
  have hsize := radices_size terms (List.finRange 7) n m c t B hb
  simp only [List.length_finRange] at hcost hsize
  have hsq : B + W + 1 ≤ (B + W + 1) ^ 2 := Nat.le_pow (by decide)
  have hpos : 1 ≤ (B + W + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  simp only [program, run_seq_snd, run_rev_snd, hrun, he, List.append_nil, listSize_reverse]
  nlinarith only [hcost, hsize, hsq, hpos]

end PCP.Lang.ComputedRadices
