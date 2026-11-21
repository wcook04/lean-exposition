import PCP.Complexity.LangCost
import PCP.Complexity.CanonicalWidth

/-!
# Ceiling logarithms by a counted language program

The program repeatedly halves `N-1`, counting only nonzero passes. A loop of
`N` iterations suffices, including at zero. Its exact output is `clog 2 N`, and
its charged cost is quadratic in `N`. In the verifier, `N` is bounded by the
public input length. The program does not use a logarithm oracle.
-/

namespace PCP.Lang.Clog

/-- Input is register zero, result register two; one, three and four are scratch. -/
def body : Stmt 5 0 :=
  .ite 1 (.seq (.assign 1 (.div 1 3)) (.assign 2 (.add 2 4))) .skip

def setup : Stmt 5 0 :=
  .seq (.assign 4 (.const 1)) (.seq (.assign 3 (.const 2))
    (.seq (.assign 1 (.sub 0 4)) (.assign 2 (.const 0))))

def program : Stmt 5 0 := .seq setup (.loop 0 body)

theorem body_step (st : State 5 0) (h3 : st.regs 3 = 2) (h4 : st.regs 4 = 1) :
    (body.run st).1.regs 1 = st.regs 1 / 2 ∧
    (body.run st).1.regs 2 = st.regs 2 + (if st.regs 1 = 0 then 0 else 1) ∧
    (body.run st).1.regs 3 = 2 ∧ (body.run st).1.regs 4 = 1 := by
  by_cases h : st.regs 1 = 0 <;>
    simp [body, Stmt.run, h, Expr.eval, Function.update, h3, h4]

/-- Sufficiently many bounded iterations exhaust every nonzero halving pass. -/
theorem iterate_result (c k : ℕ) (st : State 5 0)
    (h3 : st.regs 3 = 2) (h4 : st.regs 4 = 1) (hk : st.regs 1 ≤ k) :
    (iterate body.run c k st).1.regs 1 = 0 ∧
    (iterate body.run c k st).1.regs 2 = st.regs 2 + PCP.Machine.halvings (st.regs 1) := by
  induction k generalizing st with
  | zero =>
    have h : st.regs 1 = 0 := by omega
    simp [iterate, h]
  | succ k ih =>
    obtain ⟨h1, h2, h3', h4'⟩ := body_step st h3 h4
    have hle : (body.run st).1.regs 1 ≤ k := by rw [h1]; omega
    obtain ⟨hz, hr⟩ := ih (body.run st).1 h3' h4' hle
    rw [iterate_succ_fst]
    refine ⟨hz, ?_⟩
    rw [hr, h1, h2]
    rcases hw : st.regs 1 with _ | w
    · simp
    · rw [PCP.Machine.halvings_succ]
      simp only [Nat.succ_ne_zero, ite_false]
      omega

/-- Exact logarithm, including the conventions at zero and one. -/
theorem program_run (st : State 5 0) :
    (program.run st).1.regs 2 = Nat.clog 2 (st.regs 0) := by
  let s := (setup.run st).1
  have hs0 : s.regs 0 = st.regs 0 := by simp [s, setup, Stmt.run, Expr.eval, Function.update]
  have hs1 : s.regs 1 = st.regs 0 - 1 := by simp [s, setup, Stmt.run, Expr.eval, Function.update]
  have hs2 : s.regs 2 = 0 := by simp [s, setup, Stmt.run, Expr.eval, Function.update]
  have hs3 : s.regs 3 = 2 := by simp [s, setup, Stmt.run, Expr.eval, Function.update]
  have hs4 : s.regs 4 = 1 := by simp [s, setup, Stmt.run, Expr.eval, Function.update]
  have h := (iterate_result (Nat.size (s.regs 0) + 1) (s.regs 0) s hs3 hs4
    (by rw [hs0, hs1]; omega)).2
  change (iterate body.run (Nat.size (s.regs 0) + 1) (s.regs 0) s).1.regs 2 = _
  rw [h, hs1, hs2, zero_add]
  rcases hn : st.regs 0 with _ | n
  · simp
  · simpa using PCP.Machine.halvings_eq_clog n

theorem body_invariant (B : ℕ) (st : State 5 0)
    (h : st.regs 1 + st.regs 2 ≤ B ∧ st.regs 3 = 2 ∧ st.regs 4 = 1) :
    (body.run st).1.regs 1 + (body.run st).1.regs 2 ≤ B ∧
      (body.run st).1.regs 3 = 2 ∧ (body.run st).1.regs 4 = 1 := by
  obtain ⟨h1, h2, h3, h4⟩ := body_step st h.2.1 h.2.2
  refine ⟨?_, h3, h4⟩
  rw [h1, h2]
  split_ifs <;> omega

theorem body_cost (B : ℕ) (st : State 5 0)
    (h : st.regs 1 + st.regs 2 ≤ B ∧ st.regs 3 = 2 ∧ st.regs 4 = 1) :
    (body.run st).2 ≤ body.C * (10 * (B + 1)) := by
  apply (loopFree_bound body (by decide) st).1.trans
  apply Nat.mul_le_mul_left
  have h1 := size_le_self (st.regs 1)
  have h2 := size_le_self (st.regs 2)
  simp [body, Stmt.meas, Stmt.uses, Stmt.mustW, Expr.uses, Stmt.lUses,
    Stmt.csize, Expr.csize, h.2.1, h.2.2, show Nat.size 2 = 2 from rfl]
  omega

/-- A coarse polynomial bound is enough because the input is a public length. -/
theorem program_cost (st : State 5 0) :
    (program.run st).2 ≤ (setup.C * 4 + body.C * 10 + 5) * (st.regs 0 + 1) ^ 2 := by
  let N := st.regs 0
  let s := (setup.run st).1
  have hs0 : s.regs 0 = N := by simp [s, N, setup, Stmt.run, Expr.eval, Function.update]
  have hs : s.regs 1 + s.regs 2 ≤ N ∧ s.regs 3 = 2 ∧ s.regs 4 = 1 := by
    simp [s, N, setup, Stmt.run, Expr.eval, Function.update]
  have hsetup : (setup.run st).2 ≤ setup.C * (4 * (N + 1)) := by
    apply (loopFree_bound setup (by decide) st).1.trans
    apply Nat.mul_le_mul_left
    have hN := size_le_self N
    simp [setup, Stmt.meas, Stmt.uses, Stmt.mustW, Expr.uses, Stmt.lUses,
      Stmt.csize, Expr.csize]
    have h2 : Nat.size 2 = 2 := rfl
    dsimp [N] at hN
    omega
  have hi := iterate_cost_le body.run (Nat.size N + 1) (body.C * (10 * (N + 1)))
    (fun s : State 5 0 => s.regs 1 + s.regs 2 ≤ N ∧ s.regs 3 = 2 ∧ s.regs 4 = 1)
    (body_invariant N) (body_cost N) N s hs
  have hn := size_le_self N
  have hsum : (program.run st).2 ≤
      setup.C * (4 * (N + 1)) +
      N * (Nat.size N + 1 + body.C * (10 * (N + 1))) + Nat.size N + 2 := by
    change (setup.run st).2 + ((iterate body.run
      (Nat.size (s.regs 0) + 1) (s.regs 0) s).2 + Nat.size (s.regs 0) + 1) + 1 ≤ _
    rw [hs0]
    omega
  apply hsum.trans
  dsimp [N]
  dsimp [N] at hn
  nlinarith [Nat.zero_le (setup.C * (st.regs 0 * (st.regs 0 + 1)))]

end PCP.Lang.Clog
