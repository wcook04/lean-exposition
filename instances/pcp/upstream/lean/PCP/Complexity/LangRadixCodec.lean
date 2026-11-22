import PCP.Complexity.LangWordCodec
import Mathlib.Algebra.BigOperators.Fin

/-!
# Stored tuple codes in a variable radix

The program consumes a stored list of digits in increasing coordinate order.
It computes their little-endian radix code and the next place value, preserving
the supplied radix. This is the finite-function convention used in the verifier's
seed and query codecs. High zero digits remain part of the input width.
-/

namespace PCP.Lang.RadixCodec

open scoped BigOperators

def value (base : ℕ) : List ℕ → ℕ
  | [] => 0
  | d :: ds => d + base * value base ds

@[simp] theorem value_append (base : ℕ) (xs ys : List ℕ) :
    value base (xs ++ ys) = value base xs + base ^ xs.length * value base ys := by
  induction xs with
  | nil => simp [value]
  | cons x xs ih => simp [value, ih, pow_succ]; ring

theorem value_lt (base : ℕ) {xs : List ℕ} (h : ∀ x ∈ xs, x < base) :
    value base xs < base ^ xs.length := by
  induction xs with
  | nil => simp [value]
  | cons x xs ih =>
      have hx := h x (by simp)
      have ht := ih (fun y hy => h y (by simp [hy]))
      simp only [value, List.length_cons, pow_succ]
      nlinarith

/-- Stored digits are in increasing coordinate order. -/
theorem value_ofFn (base n : ℕ) (f : Fin n → ℕ) :
    value base (List.ofFn f) = ∑ i, base ^ i.val * f i := by
  induction n with
  | zero => simp [value]
  | succ n ih =>
      rw [List.ofFn_succ, value, ih, Fin.sum_univ_succ]
      simp only [Fin.val_zero, pow_zero, one_mul, Fin.val_succ, pow_succ]
      rw [Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      ring

/-- Exact agreement with the production finite-function codec. -/
theorem value_finFunction (base n : ℕ) (f : Fin n → Fin base) :
    value base (List.ofFn fun i => (f i).val) = (finFunctionFinEquiv f).val := by
  simp [value_ofFn, Nat.mul_comm]

def body : Stmt 6 1 :=
  .seq (.pop 0 4 5) (.seq (.assign 4 (.mul 4 3))
    (.seq (.assign 2 (.add 2 4)) (.assign 3 (.mul 3 0))))

def setup : Stmt 6 1 :=
  .seq (.len 0 1) (.seq (.assign 2 (.const 0)) (.assign 3 (.const 1)))

def encode : Stmt 6 1 := .seq setup (.loop 1 body)

theorem body_step (st : State 6 1) (x : ℕ) (xs : List ℕ) (hl : st.lists 0 = x :: xs) :
    (body.run st).1.regs 0 = st.regs 0 ∧
    (body.run st).1.regs 2 = st.regs 2 + st.regs 3 * x ∧
    (body.run st).1.regs 3 = st.regs 3 * st.regs 0 ∧ (body.run st).1.lists 0 = xs := by
  simp [body, Stmt.run, Expr.eval, Function.update, hl, Nat.mul_comm]

/-- General accumulation law for an arbitrary current place value. -/
theorem iterate_result (c : ℕ) (xs : List ℕ) (st : State 6 1) (hl : st.lists 0 = xs) :
    (iterate body.run c xs.length st).1.regs 0 = st.regs 0 ∧
    (iterate body.run c xs.length st).1.regs 2 =
      st.regs 2 + st.regs 3 * value (st.regs 0) xs ∧
    (iterate body.run c xs.length st).1.regs 3 = st.regs 3 * st.regs 0 ^ xs.length ∧
    (iterate body.run c xs.length st).1.lists 0 = [] := by
  induction xs generalizing st with
  | nil => simp [iterate, value, hl]
  | cons x xs ih =>
      obtain ⟨h0, h2, h3, hL⟩ := body_step st x xs hl
      obtain ⟨h0', h2', h3', hL'⟩ := ih (body.run st).1 hL
      rw [List.length_cons, iterate_succ_fst]
      refine ⟨h0'.trans h0, ?_, ?_, hL'⟩
      · rw [h2', h0, h2, h3, value]; ring
      · rw [h3', h0, h3, pow_succ]; ring

/-- The actual computed tuple code, place value, and exhausted work list. -/
theorem encode_run (st : State 6 1) :
    (encode.run st).1.regs 0 = st.regs 0 ∧
    (encode.run st).1.regs 2 = value (st.regs 0) (st.lists 0) ∧
    (encode.run st).1.regs 3 = st.regs 0 ^ (st.lists 0).length ∧
    (encode.run st).1.lists 0 = [] := by
  let s := (setup.run st).1
  have hn : s.regs 1 = (st.lists 0).length := by
    simp [s, setup, Stmt.run, Expr.eval, Function.update]
  have h := iterate_result (Nat.size (st.lists 0).length + 1) (st.lists 0) s (by rfl)
  change (iterate body.run (Nat.size (s.regs 1) + 1) (s.regs 1) s).1.regs 0 = _ ∧
    (iterate body.run (Nat.size (s.regs 1) + 1) (s.regs 1) s).1.regs 2 = _ ∧
    (iterate body.run (Nat.size (s.regs 1) + 1) (s.regs 1) s).1.regs 3 = _ ∧
    (iterate body.run (Nat.size (s.regs 1) + 1) (s.regs 1) s).1.lists 0 = _
  rw [hn]
  simpa [s, setup, Stmt.run, Expr.eval, Function.update] using h

/-- Prefix accumulation for the actual counted loop. -/
def Inv (base : ℕ) (xs : List ℕ) (j : ℕ) (st : State 6 1) : Prop :=
  st.regs 0 = base ∧ st.regs 2 = value base (xs.take j) ∧
    st.regs 3 = base ^ j ∧ st.lists 0 = xs.drop j

theorem body_inv (base : ℕ) (xs : List ℕ) (j : ℕ) (st : State 6 1)
    (hj : j < xs.length) (hs : Inv base xs j st) : Inv base xs (j + 1) (body.run st).1 := by
  have hl : st.lists 0 = xs[j] :: xs.drop (j + 1) :=
    hs.2.2.2.trans (List.drop_eq_getElem_cons hj)
  obtain ⟨h0, h2, h3, hL⟩ := body_step st xs[j] _ hl
  refine ⟨h0.trans hs.1, ?_, ?_, hL⟩
  · rw [h2, hs.2.1, hs.2.2.1, List.take_succ_eq_append_getElem hj, value_append]
    simp [value, List.length_take, Nat.min_eq_left hj.le]
  · rw [h3, hs.1, hs.2.2.1, pow_succ]

private theorem power_bound (base j : ℕ) : base ^ j ≤ 2 ^ (Nat.size base * j) := by
  calc base ^ j ≤ (2 ^ Nat.size base) ^ j := Nat.pow_le_pow_left (Nat.lt_size_self base).le j
    _ = _ := by rw [← pow_mul]

private theorem size_power (base j : ℕ) : Nat.size (base ^ j) ≤ Nat.size base * j + 1 := by
  apply Nat.size_le.mpr
  exact (power_bound base j).trans_lt (Nat.pow_lt_pow_right (by decide) (by omega))

private theorem size_value (base : ℕ) (xs : List ℕ) (h : ∀ x ∈ xs, x < base) :
    Nat.size (value base xs) ≤ Nat.size base * xs.length :=
  Nat.size_le.mpr ((value_lt base h).trans_le (power_bound base xs.length))

private theorem listSize_drop_le (xs : List ℕ) (j : ℕ) : listSize (xs.drop j) ≤ listSize xs := by
  have h := listSize_append (xs.take j) (xs.drop j)
  rw [List.take_append_drop] at h
  omega

/-- This polynomial resource bound includes the stored digit list and growing place values. -/
def workBound (base : ℕ) (xs : List ℕ) : ℕ :=
  listSize xs + (xs.length + 1) * (Nat.size base + 1) + 1

def passConstant : ℕ := body.C * (body.width + body.csize + 1)

theorem body_reads (base : ℕ) (xs : List ℕ) (j : ℕ) (st : State 6 1)
    (h : ∀ x ∈ xs, x < base) (hj : j ≤ xs.length) (hs : Inv base xs j st) :
    (∀ r ∈ body.uses, Nat.size (st.regs r) ≤ workBound base xs) ∧
      (∀ L ∈ body.lUses, listSize (st.lists L) ≤ workBound base xs) := by
  have hbase : Nat.size base ≤ workBound base xs := by dsimp [workBound]; nlinarith
  have hvalue : Nat.size (st.regs 2) ≤ workBound base xs := by
    rw [hs.2.1]
    have hv := size_value base (xs.take j) (fun x hx => h x (List.mem_of_mem_take hx))
    have hl : (xs.take j).length ≤ xs.length := by simp
    have hm := Nat.mul_le_mul_left (Nat.size base) hl
    dsimp [workBound]
    nlinarith
  have hweight : Nat.size (st.regs 3) ≤ workBound base xs := by
    rw [hs.2.2.1]
    have hp := size_power base j
    have hm := Nat.mul_le_mul_left (Nat.size base) hj
    dsimp [workBound]
    nlinarith
  have hlist : listSize (st.lists 0) ≤ workBound base xs := by
    rw [hs.2.2.2]
    have hl := listSize_drop_le xs j
    dsimp [workBound]; omega
  constructor
  · intro r hr
    have h0 : Nat.size (st.regs 0) ≤ workBound base xs := hs.1 ▸ hbase
    fin_cases r <;> simp [body, Stmt.uses, Stmt.mustW, Expr.uses] at hr <;> dsimp <;> omega
  · intro L hL
    have he : L = 0 := Subsingleton.elim _ _
    subst L
    exact hlist

/-- Charged runtime, polynomial in digit-list size and radix bit length. -/
theorem encode_cost (st : State 6 1) (h : ∀ x ∈ st.lists 0, x < st.regs 0) :
    (encode.run st).2 ≤ (passConstant + 20) * (workBound (st.regs 0) (st.lists 0) + 1) ^ 2 := by
  let base := st.regs 0
  let xs := st.lists 0
  let W := workBound base xs
  let s := (setup.run st).1
  have hs : Inv base xs 0 s := by
    simp [Inv, base, xs, s, setup, Stmt.run, Expr.eval, Function.update, value]
  have hn : s.regs 1 = xs.length := by simp [s, xs, setup, Stmt.run, Expr.eval, Function.update]
  have hsize : listSize xs ≤ W := by dsimp [W, workBound]; omega
  have hl : xs.length ≤ W := (length_le_listSize xs).trans hsize
  have hsN : Nat.size xs.length ≤ W := (size_le_self _).trans hl
  have hi := loop_cost_le 1 body (by decide) s W (Inv base xs)
    (by rw [hn]; exact hl)
    (fun j s hj hs => body_inv base xs j s (by simpa only [hn] using hj) hs)
    (fun j s hj hs => (body_reads base xs j s h (by rw [hn] at hj; omega) hs).1)
    (fun j s hj hs => (body_reads base xs j s h (by rw [hn] at hj; omega) hs).2) hs
  have hsetup : (setup.run st).2 ≤ 2 * W + 10 := by
    simp [setup, Stmt.run, Expr.cost, Expr.readSize, Expr.eval]
    dsimp [xs] at hsize hsN
    omega
  change (setup.run st).2 + ((Stmt.loop 1 body).run s).2 + 1 ≤ _
  change _ ≤ (passConstant + 20) * (W + 1) ^ 2
  change ((Stmt.loop 1 body).run s).2 ≤ (passConstant + 3) * (W + 1) ^ 2 at hi
  nlinarith

end PCP.Lang.RadixCodec
