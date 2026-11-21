import PCP.Complexity.LangClog
import PCP.Complexity.LangRenaming
import PCP.Algebraic.ThreeColorParameterChoice

/-!
# Computing the verifier's least admissible dimension

A counted search maintains `a`, `2^a`, and `a*2^a`. It stops updating at the
first admissible exponent and agrees exactly with `ThreeColorParameterChoice`.
The preliminary logarithm is the actual halving program. Every search value
is bounded by the proved parameter volume, even after the fixed loop continues.
-/

namespace PCP.Lang.ThreeColorParameter

open PCP.Algebraic.ThreeColorParameterChoice

def body : Stmt 8 0 :=
  .seq (.assign 1 (.lt 7 2))
    (.ite 1 (.seq (.assign 5 (.add 5 4))
      (.seq (.assign 6 (.add 6 6)) (.assign 7 (.mul 5 6)))) .skip)

def setup : Stmt 8 0 :=
  .seq (.assign 4 (.const 1)) (.seq (.assign 5 (.const 2))
    (.seq (.assign 6 (.const 4)) (.assign 7 (.const 8))))

def select : Stmt 8 0 := .seq setup (.loop 0 body)

def regMap (i : Fin 5) : Fin 8 := i.castAdd 3

def logarithm : Stmt 8 0 := Clog.program.rename regMap id

def program : Stmt 8 0 := .seq logarithm select

/-- The test used by the code is exactly the least-exponent stopping condition. -/
theorem below_iff (N a : ℕ) (ha : 2 ≤ a) :
    a * 2 ^ a < Nat.clog 2 N ↔ a < exponent N := by
  constructor
  · intro h
    by_contra hn
    have hle : exponent N ≤ a := by omega
    have hv : volume N ≤ a * 2 ^ a :=
      Nat.mul_le_mul hle (Nat.pow_le_pow_right (by decide) hle)
    have := le_volume N
    omega
  · intro h
    by_contra hn
    have he := exponent_le ha (by omega : Nat.clog 2 N ≤ a * 2 ^ a)
    omega

/-- The live state represents one candidate; register one is expendable scratch. -/
def Represents (N a : ℕ) (st : State 8 0) : Prop :=
  st.regs 0 = N ∧ st.regs 2 = Nat.clog 2 N ∧ st.regs 4 = 1 ∧
    st.regs 5 = a ∧ st.regs 6 = 2 ^ a ∧ st.regs 7 = a * 2 ^ a

theorem body_step (N a : ℕ) (st : State 8 0) (hs : Represents N a st)
    (ha : 2 ≤ a) (he : a ≤ exponent N) :
    Represents N (min (exponent N) (a + 1)) (body.run st).1 := by
  have ht := below_iff N a ha
  by_cases hlt : a < exponent N
  · have hv : a * 2 ^ a < Nat.clog 2 N := ht.mpr hlt
    have hm : min (exponent N) (a + 1) = a + 1 := min_eq_right (by omega)
    rcases hs with ⟨h0, h2, h4, h5, h6, h7⟩
    simp [Represents, body, Stmt.run, Expr.eval, Function.update, h0, h2, h4, h5, h6, h7,
      hv, hm, pow_succ, Nat.mul_two]
  · have hae : a = exponent N := by omega
    have hv : ¬ a * 2 ^ a < Nat.clog 2 N := fun h => hlt (ht.mp h)
    have hm : min (exponent N) (a + 1) = a := by omega
    rcases hs with ⟨h0, h2, h4, h5, h6, h7⟩
    simp [Represents, body, Stmt.run, Expr.eval, Function.update, h0, h2, h4, h5, h6, h7,
      hv, hm]

theorem iterate_represents (N c k a : ℕ) (st : State 8 0) (hs : Represents N a st)
    (ha : 2 ≤ a) (he : a ≤ exponent N) :
    Represents N (min (exponent N) (a + k)) (iterate body.run c k st).1 := by
  induction k generalizing st a with
  | zero => simpa [iterate, Nat.min_eq_right he] using hs
  | succ k ih =>
    rw [iterate_succ_fst]
    have hs' := body_step N a st hs ha he
    have ha' : 2 ≤ min (exponent N) (a + 1) := by have := exponent_ge_two N; omega
    have he' : min (exponent N) (a + 1) ≤ exponent N := Nat.min_le_left _ _
    have h := ih _ _ hs' ha' he'
    have hm : min (exponent N) (min (exponent N) (a + 1) + k) =
        min (exponent N) (a + (k + 1)) := by omega
    simpa only [hm] using h

theorem exponent_le_input_add_two (N : ℕ) : exponent N ≤ N + 2 := by
  apply exponent_le (by omega)
  have hc := PCP.Machine.clog_le_self N
  have hp : 1 ≤ 2 ^ (N + 2) := Nat.one_le_two_pow
  nlinarith

/-- The selector returns the exact exponent, dimension, and parameter volume. -/
theorem select_run (st : State 8 0) (hc : st.regs 2 = Nat.clog 2 (st.regs 0)) :
    Represents (st.regs 0) (exponent (st.regs 0)) (select.run st).1 := by
  let s := (setup.run st).1
  have hs : Represents (st.regs 0) 2 s := by
    simp [Represents, s, setup, Stmt.run, Expr.eval, Function.update, hc]
  have h0 : s.regs 0 = st.regs 0 := hs.1
  have h := iterate_represents (st.regs 0) (Nat.size (st.regs 0) + 1)
    (st.regs 0) 2 s hs (by decide) (exponent_ge_two _)
  have hm : min (exponent (st.regs 0)) (2 + st.regs 0) = exponent (st.regs 0) :=
    min_eq_left (by have := exponent_le_input_add_two (st.regs 0); omega)
  change Represents _ _ (iterate body.run (Nat.size (s.regs 0) + 1) (s.regs 0) s).1
  rw [h0]
  simpa only [hm] using h

theorem logarithm_run (st : State 8 0) :
    (logarithm.run st).1.regs 2 = Nat.clog 2 (st.regs 0) := by
  have h := congrArg (fun p => p.1.regs 2)
    (Clog.program.run_rename regMap id
      (by intro i j h; exact Fin.ext (congrArg (fun x : Fin 8 => x.val) h))
      Function.injective_id st)
  exact h.trans (Clog.program_run (st.restrict regMap id))

theorem logarithm_preserves_input (st : State 8 0) :
    (logarithm.run st).1.regs 0 = st.regs 0 :=
  run_regs_frame logarithm 0 (by decide) st

/-- The full algorithm includes actual computation of its logarithm. -/
theorem program_run (st : State 8 0) :
    Represents (st.regs 0) (exponent (st.regs 0)) (program.run st).1 := by
  rw [program, run_seq_fst]
  have h := select_run (logarithm.run st).1
    (by rw [logarithm_preserves_input]; exact logarithm_run st)
  simpa only [logarithm_preserves_input] using h

/-- All three growing search values stay within one linear public-size bound. -/
theorem candidate_bound (N a : ℕ) (ha : 2 ≤ a) (he : a ≤ exponent N) :
    a ≤ 32 * (N + 1) ∧ 2 ^ a ≤ 32 * (N + 1) ∧ a * 2 ^ a ≤ 32 * (N + 1) := by
  have hc := PCP.Machine.clog_le_self N
  have hv := volume_le_log_add_one N
  have ham : a * 2 ^ a ≤ volume N :=
    Nat.mul_le_mul he (Nat.pow_le_pow_right (by decide) he)
  have hp : 1 ≤ 2 ^ a := Nat.one_le_two_pow
  have h1 : a ≤ a * 2 ^ a := Nat.le_mul_of_pos_right _ hp
  have h2 : 2 ^ a ≤ a * 2 ^ a := Nat.le_mul_of_pos_left _ (by omega)
  omega

/-- A fixed multiplier for each bounded search pass. -/
def passConstant : ℕ := body.C * (body.width + body.csize + 1)

theorem body_cost (N a : ℕ) (st : State 8 0) (hs : Represents N a st)
    (ha : 2 ≤ a) (he : a ≤ exponent N) :
    (body.run st).2 ≤ passConstant * (32 * (N + 1) + 1) := by
  apply loopFree_cost_le body (by decide) st
  · intro r hr
    have hb := candidate_bound N a ha he
    have hc := PCP.Machine.clog_le_self N
    apply (size_le_self _).trans
    rcases hs with ⟨h0, h2, h4, h5, h6, h7⟩
    fin_cases r <;>
      simp [body, Stmt.uses, Stmt.mustW, Expr.uses] at hr <;>
      simp_all <;> omega
  · intro L
    exact Fin.elim0 L

/-- Exact operational cost of the least-exponent search is uniformly quadratic. -/
theorem select_cost (st : State 8 0) (hc : st.regs 2 = Nat.clog 2 (st.regs 0)) :
    (select.run st).2 ≤ (setup.C * 12 + passConstant * 33 + 3) * (st.regs 0 + 1) ^ 2 := by
  let N := st.regs 0
  let s := (setup.run st).1
  have hs : Represents N 2 s := by
    simp [Represents, s, N, setup, Stmt.run, Expr.eval, Function.update, hc]
  have hi := iterate_cost_le body.run (Nat.size N + 1)
    (passConstant * (32 * (N + 1) + 1))
    (fun s => ∃ a, 2 ≤ a ∧ a ≤ exponent N ∧ Represents N a s)
    (by
      rintro s ⟨a, ha, he, hs⟩
      refine ⟨min (exponent N) (a + 1), ?_, Nat.min_le_left _ _, body_step N a s hs ha he⟩
      have := exponent_ge_two N
      omega)
    (by rintro s ⟨a, ha, he, hs⟩; exact body_cost N a s hs ha he)
    N s ⟨2, by decide, exponent_ge_two N, hs⟩
  have hsetup : (setup.run st).2 ≤ setup.C * 12 := by
    apply (loopFree_bound setup (by decide) st).1.trans
    apply Nat.mul_le_mul_left
    norm_num [setup, Stmt.meas, Stmt.uses, Stmt.mustW, Expr.uses, Stmt.lUses,
      Stmt.csize, Expr.csize, Nat.size]
    decide
  have hn := size_le_self N
  have hsum : (select.run st).2 ≤ setup.C * 12 +
      N * (Nat.size N + 1 + passConstant * (32 * (N + 1) + 1)) + Nat.size N + 2 := by
    change (setup.run st).2 + ((iterate body.run
      (Nat.size (s.regs 0) + 1) (s.regs 0) s).2 + Nat.size (s.regs 0) + 1) + 1 ≤ _
    rw [hs.1]
    omega
  apply hsum.trans
  change _ ≤ _ * (N + 1) ^ 2
  nlinarith [Nat.zero_le (setup.C * N * (N + 2)),
    Nat.zero_le (passConstant * N)]

/-- The complete parameter program has an explicit polynomial charged-time bound. -/
theorem program_cost (st : State 8 0) :
    (program.run st).2 ≤
      (Clog.setup.C * 4 + Clog.body.C * 10 + setup.C * 12 + passConstant * 33 + 9) *
        (st.regs 0 + 1) ^ 2 := by
  have hcost := Clog.program_cost (st.restrict regMap id)
  have hr := Clog.program.run_rename_cost regMap id
    (by intro i j h; exact Fin.ext (congrArg (fun x : Fin 8 => x.val) h))
    Function.injective_id st
  change (logarithm.run st).2 = _ at hr
  rw [← hr] at hcost
  change (logarithm.run st).2 ≤
    (Clog.setup.C * 4 + Clog.body.C * 10 + 5) * (st.regs 0 + 1) ^ 2 at hcost
  have hs := select_cost (logarithm.run st).1
    (by rw [logarithm_preserves_input]; exact logarithm_run st)
  rw [logarithm_preserves_input] at hs
  rw [program, run_seq_snd]
  nlinarith [show 1 ≤ (st.regs 0 + 1) ^ 2 by simp only [pow_two]; nlinarith]

end PCP.Lang.ThreeColorParameter
