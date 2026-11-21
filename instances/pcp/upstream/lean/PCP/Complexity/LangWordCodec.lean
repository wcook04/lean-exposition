import PCP.Complexity.BinaryFieldLang
import PCP.Complexity.SeedBits

/-!
# Reading stored little-endian bit words

The language program consumes a natural list of zero/one digits and accumulates
its integer value. Leading high zeroes are retained by the representation proof.
The charged running time is quadratic in the word length; the proof bounds the
bit sizes of growing powers, rather than charging their numeric values.
-/

namespace PCP.Lang.WordCodec

open BinaryField

def value : List ℕ → ℕ
  | [] => 0
  | d :: ds => d + 2 * value ds

@[simp] theorem value_append (xs ys : List ℕ) :
    value (xs ++ ys) = value xs + 2 ^ xs.length * value ys := by
  induction xs with
  | nil => simp [value]
  | cons x xs ih => simp [value, ih, pow_succ]; ring

theorem value_lt {xs : List ℕ} (h : Bits xs) : value xs < 2 ^ xs.length := by
  induction xs with
  | nil => simp [value]
  | cons x xs ih =>
    have hx := h x (by simp)
    have ht := ih (fun y hy => h y (by simp [hy]))
    simp only [value, List.length_cons, pow_succ]
    omega

/-- The public random-bit convention is least significant bit first. -/
@[simp] theorem value_map_bool (bs : List Bool) :
    value (bs.map Bool.toNat) = PCP.Machine.bitsValue bs := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    simp only [List.map_cons, value, PCP.Machine.bitsValue_cons, ih]
    cases b <;> simp [Nat.bit, Nat.add_comm]

def body : Stmt 5 1 :=
  .seq (.pop 0 3 4) (.seq (.assign 3 (.mul 3 2))
    (.seq (.assign 1 (.add 1 3)) (.assign 2 (.add 2 2))))

def setup : Stmt 5 1 :=
  .seq (.len 0 0) (.seq (.assign 1 (.const 0)) (.assign 2 (.const 1)))

def decode : Stmt 5 1 := .seq setup (.loop 0 body)

theorem body_step (st : State 5 1) (x : ℕ) (xs : List ℕ) (hl : st.lists 0 = x :: xs) :
    (body.run st).1.regs 1 = st.regs 1 + st.regs 2 * x ∧
    (body.run st).1.regs 2 = st.regs 2 * 2 ∧ (body.run st).1.lists 0 = xs := by
  simp [body, Stmt.run, Expr.eval, Function.update, hl, Nat.mul_comm, two_mul]

/-- General accumulator equation, permitting a caller-supplied initial place value. -/
theorem iterate_result (c : ℕ) (xs : List ℕ) (st : State 5 1) (hl : st.lists 0 = xs) :
    (iterate body.run c xs.length st).1.regs 1 = st.regs 1 + st.regs 2 * value xs ∧
    (iterate body.run c xs.length st).1.regs 2 = st.regs 2 * 2 ^ xs.length ∧
    (iterate body.run c xs.length st).1.lists 0 = [] := by
  induction xs generalizing st with
  | nil => simp [iterate, value, hl]
  | cons x xs ih =>
    obtain ⟨h1, h2, h0⟩ := body_step st x xs hl
    obtain ⟨h1', h2', h0'⟩ := ih (body.run st).1 h0
    rw [List.length_cons, iterate_succ_fst]
    refine ⟨?_, ?_, h0'⟩
    · rw [h1', h1, h2, value]
      ring
    · rw [h2', h2, pow_succ]
      ring

/-- Exact decoded integer, the exhausted input, and the next bit's place value. -/
theorem decode_run (st : State 5 1) :
    (decode.run st).1.regs 1 = value (st.lists 0) ∧
    (decode.run st).1.regs 2 = 2 ^ (st.lists 0).length ∧
    (decode.run st).1.lists 0 = [] := by
  let s := (setup.run st).1
  have hs0 : s.regs 0 = (st.lists 0).length := by
    simp [s, setup, Stmt.run, Expr.eval, Function.update]
  have hsl : s.lists 0 = st.lists 0 := rfl
  have h := iterate_result (Nat.size (st.lists 0).length + 1) (st.lists 0) s hsl
  change (iterate body.run (Nat.size (s.regs 0) + 1) (s.regs 0) s).1.regs 1 = _ ∧
    (iterate body.run (Nat.size (s.regs 0) + 1) (s.regs 0) s).1.regs 2 = _ ∧
    (iterate body.run (Nat.size (s.regs 0) + 1) (s.regs 0) s).1.lists 0 = _
  rw [hs0]
  simpa [s, setup, Stmt.run, Expr.eval, Function.update] using h

/-- The counted prefix invariant records both value and bit-size progress. -/
def Inv (xs : List ℕ) (j : ℕ) (st : State 5 1) : Prop :=
  st.regs 1 = value (xs.take j) ∧ st.regs 2 = 2 ^ j ∧ st.lists 0 = xs.drop j

theorem body_inv (xs : List ℕ) (j : ℕ) (st : State 5 1)
    (hj : j < xs.length) (hs : Inv xs j st) : Inv xs (j + 1) (body.run st).1 := by
  have hl : st.lists 0 = xs[j] :: xs.drop (j + 1) := by
    rw [hs.2.2]
    exact List.drop_eq_getElem_cons hj
  obtain ⟨h1, h2, h0⟩ := body_step st xs[j] _ hl
  refine ⟨?_, ?_, h0⟩
  · rw [h1, hs.1, hs.2.1, List.take_succ_eq_append_getElem hj, value_append]
    simp [value, List.length_take, Nat.min_eq_left hj.le]
  · rw [h2, hs.2.1, pow_succ]

def passConstant : ℕ := body.C * (body.width + body.csize + 1)

theorem body_cost (xs : List ℕ) (hx : Bits xs) (j : ℕ) (st : State 5 1)
    (hj : j ≤ xs.length) (hs : Inv xs j st) :
    (body.run st).2 ≤ passConstant * (2 * xs.length + 3) := by
  apply loopFree_cost_le body (by decide) st
  · intro r hr
    have hv : Nat.size (st.regs 1) ≤ xs.length := by
      rw [hs.1]
      apply Nat.size_le.mpr
      have h := value_lt (xs := xs.take j) (fun x h => hx x (List.mem_of_mem_take h))
      exact h.trans_le (Nat.pow_le_pow_right (by decide) (by simp))
    have hw : Nat.size (st.regs 2) ≤ xs.length + 1 := by rw [hs.2.1, Nat.size_pow]; omega
    fin_cases r <;> simp [body, Stmt.uses, Stmt.mustW, Expr.uses] at hr <;> dsimp <;> omega
  · intro L _
    have hL : L = 0 := Subsingleton.elim _ _
    subst L
    rw [hs.2.2]
    have hb := listSize_bits (a := xs.drop j) (fun x h => hx x (List.mem_of_mem_drop h))
    have hl : (xs.drop j).length ≤ xs.length := by simp
    omega

/-- Decoding costs polynomially many bit operations even for a numerically huge word. -/
theorem decode_cost (st : State 5 1) (hx : Bits (st.lists 0)) :
    (decode.run st).2 ≤ (passConstant * 3 + 20) * ((st.lists 0).length + 1) ^ 2 := by
  let xs := st.lists 0
  let s := (setup.run st).1
  have hs : Inv xs 0 s := by simp [Inv, value, xs, s, setup, Stmt.run, Expr.eval, Function.update]
  have hs0 : s.regs 0 = xs.length := by simp [xs, s, setup, Stmt.run, Expr.eval, Function.update]
  have hi := iterate_cost_idx body.run (Nat.size xs.length + 1)
    (passConstant * (2 * xs.length + 3)) xs.length (Inv xs)
    (fun j s hj hs => ⟨body_inv xs j s hj hs, body_cost xs hx j s hj.le hs⟩) s hs
  have hl := listSize_bits hx
  have hn := size_le_self xs.length
  have hsetup : (setup.run st).2 ≤ 3 * xs.length + 10 := by
    simp only [setup, Stmt.run, Expr.cost, Expr.readSize, Expr.eval]
    change listSize xs + Nat.size xs.length + 7 ≤ _
    dsimp [xs] at hn ⊢
    omega
  have hsum : (decode.run st).2 ≤ 3 * xs.length + 10 +
      xs.length * (Nat.size xs.length + 1 + passConstant * (2 * xs.length + 3)) +
      Nat.size xs.length + 2 := by
    change (setup.run st).2 + ((iterate body.run
      (Nat.size (s.regs 0) + 1) (s.regs 0) s).2 + Nat.size (s.regs 0) + 1) + 1 ≤ _
    rw [hs0]
    omega
  apply hsum.trans
  change _ ≤ _ * (xs.length + 1) ^ 2
  nlinarith [Nat.zero_le (passConstant * xs.length ^ 2)]

end PCP.Lang.WordCodec
