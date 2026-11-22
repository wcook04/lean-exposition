/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Complexity.LangCost
import PCP.Algebraic.BinaryWordMaterialization

/-!
# Stored binary words in the counted-loop language

The programs in this file operate on lists of stored natural-number coefficients.
The coefficient encoding uses the values `0` and `1`, in increasing degree order.
Correctness relates the actual `Lang.Stmt.run` result to the materialized arithmetic;
cost statements concern the charged operational semantics of `Lang`, not machine time.
-/

namespace PCP.Lang.BinaryField

open PCP.Algebraic

/-- A stored list of binary coefficients. -/
def Bits (a : List ℕ) : Prop := ∀ x ∈ a, x < 2

/-- The concrete natural-list encoding of a stored coefficient array. -/
def encode {t : ℕ} (v : BinaryWordMaterialization.Word t) : List ℕ :=
  List.ofFn fun i => (BinaryWordMaterialization.toWord v i).val

@[simp] theorem encode_length {t : ℕ} (v : BinaryWordMaterialization.Word t) :
    (encode v).length = t := by simp [encode]

theorem encode_bits {t : ℕ} (v : BinaryWordMaterialization.Word t) : Bits (encode v) := by
  intro x hx
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
  exact ZMod.val_lt _

/-- List coefficient addition, including its explicit reduction modulo two. -/
def addWords (a b : List ℕ) : List ℕ := List.zipWith (fun x y => (x + y) % 2) a b

theorem addWords_bits (a b : List ℕ) : Bits (addWords a b) := by
  induction a generalizing b with
  | nil => simp [Bits, addWords]
  | cons a as ih =>
    cases b with
    | nil => simp [Bits, addWords]
    | cons b bs =>
      intro x hx
      simp only [addWords, List.zipWith_cons_cons, List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact Nat.mod_lt _ (by decide)
      · exact ih bs x hx

@[simp] theorem encode_add {t : ℕ} (v w : BinaryWordMaterialization.Word t) :
    encode (BinaryWordMaterialization.add v w) = addWords (encode v) (encode w) := by
  apply List.ext_getElem
  · simp [addWords]
  · intro i hi hi'
    simp [encode, addWords, BinaryWordMaterialization.toWord_add, ZMod.val_add]

/-- Registers `1,2,3` are scratch; register `4` holds two. Lists `0,2` are consumed,
and the sum is pushed onto list `1`. All other registers and lists are available to callers. -/
def addBody : Stmt 8 8 :=
  .seq (.pop 0 1 3) (.seq (.pop 2 2 3)
    (.seq (.assign 1 (.add 1 2)) (.seq (.assign 1 (.mod 1 4)) (.push 1 1))))

/-- Add two equal-length stored words. The caller supplies an empty output list `1`.
The loop bound is the stored length of list `0`; the final reverse restores degree order. -/
def add : Stmt 8 8 :=
  .seq (.assign 4 (.const 2)) (.seq (.len 0 0) (.seq (.loop 0 addBody) (.rev 1)))

theorem addBody_step (st : State 8 8) (x y : ℕ) (a b : List ℕ)
    (ha : st.lists 0 = x :: a) (hb : st.lists 2 = y :: b) (h2 : st.regs 4 = 2) :
    (addBody.run st).1.lists 0 = a ∧
    (addBody.run st).1.lists 2 = b ∧
    (addBody.run st).1.lists 1 = (x + y) % 2 :: st.lists 1 ∧
    (addBody.run st).1.regs 4 = 2 := by
  simp [addBody, Stmt.run, ha, hb, Expr.eval, Function.update, h2]

/-- The loop consumes equal prefixes and materializes their coefficient sums. -/
theorem add_iterate (c j : ℕ) (st : State 8 8) (a b out : List ℕ)
    (ha : st.lists 0 = a) (hb : st.lists 2 = b) (ho : st.lists 1 = out)
    (h2 : st.regs 4 = 2) (hj : j ≤ a.length) (hlen : a.length = b.length) :
    (iterate addBody.run c j st).1.lists 1 = (addWords (a.take j) (b.take j)).reverse ++ out ∧
    (iterate addBody.run c j st).1.lists 0 = a.drop j ∧
    (iterate addBody.run c j st).1.lists 2 = b.drop j := by
  induction j generalizing st a b out with
  | zero => simp [iterate_zero_fst, addWords, ha, hb, ho]
  | succ j ih =>
    cases a with
    | nil => simp at hj
    | cons x a =>
      cases b with
      | nil => simp at hlen
      | cons y b =>
        obtain ⟨h0, h2', h1, hr⟩ := addBody_step st x y a b ha hb h2
        obtain ⟨k1, k0, k2⟩ := ih (addBody.run st).1 a b ((x + y) % 2 :: out)
          h0 h2' (by rw [h1, ho]) hr (by simp at hj; omega) (by simpa using hlen)
        rw [iterate_succ_fst]
        refine ⟨?_, ?_, ?_⟩
        · simpa [addWords, List.reverse_cons, List.append_assoc] using k1
        · simpa using k0
        · simpa using k2

/-- Exact semantics of the addition subroutine. -/
theorem add_run (st : State 8 8) (a b : List ℕ) (ha : st.lists 0 = a)
    (hb : st.lists 2 = b) (ho : st.lists 1 = []) (hlen : a.length = b.length) :
    (add.run st).1.lists 1 = addWords a b := by
  simp only [add, run_seq_fst, run_assign_fst, Expr.eval, run_len_fst, run_rev_fst,
    run_loop_fst, setReg_lists, setReg_regs, Function.update_self]
  have h := (add_iterate (Nat.size a.length + 1) a.length
    (setReg (setReg st 4 2) 0 a.length) a b []
    (by simp [ha]) (by simp [hb]) (by simp [ho]) (by simp [Function.update])
    le_rfl hlen).1
  simpa [ha, List.take_of_length_le (show b.length ≤ a.length by omega)] using
    congrArg List.reverse h

/-- The actual language result encodes precisely the materialized array sum. -/
theorem add_run_encode {t : ℕ} (st : State 8 8)
    (v w : BinaryWordMaterialization.Word t)
    (ha : st.lists 0 = encode v) (hb : st.lists 2 = encode w) (ho : st.lists 1 = []) :
    (add.run st).1.lists 1 = encode (BinaryWordMaterialization.add v w) := by
  rw [encode_add]
  exact add_run st _ _ ha hb ho (by simp)

theorem listSize_bits {a : List ℕ} (ha : Bits a) : listSize a ≤ 2 * a.length := by
  induction a with
  | nil => simp [listSize]
  | cons x a ih =>
    have hx : Nat.size x ≤ 1 := size_le_one_of_le_one (by have := ha x (by simp); omega)
    have ht := ih (fun y hy => ha y (by simp [hy]))
    simp only [listSize, List.map_cons, List.sum_cons, List.length_cons] at *
    omega

/-- A binary addition stage has uniformly bounded charged cost and retains binary inputs. -/
theorem addBody_cost (st : State 8 8) (ha : Bits (st.lists 0))
    (hb : Bits (st.lists 2)) (h2 : st.regs 4 = 2) :
    (addBody.run st).2 ≤ 32 ∧ Bits ((addBody.run st).1.lists 0) ∧
    Bits ((addBody.run st).1.lists 2) ∧ (addBody.run st).1.regs 4 = 2 := by
  rcases h0 : st.lists 0 with _ | ⟨x, a⟩ <;>
    rcases h1 : st.lists 2 with _ | ⟨y, b⟩
  all_goals simp only [h0, h1] at ha hb
  · simp [addBody, Stmt.run, h0, h1, Expr.eval, Expr.cost, Expr.readSize,
      Function.update, h2, show Nat.size 2 = 2 by decide, Bits]
  · simp only [addBody, Fin.isValue, Stmt.run, h0, setReg_lists, h1, Expr.eval,
      setReg_regs, Function.update, Fin.reduceEq, dite_true, dite_false, setList_regs,
      zero_add, Expr.cost, Expr.readSize, Nat.size_zero, h2,
      show Nat.size 2 = 2 by decide, setList_lists, Order.add_one_le_iff, Bits,
      zero_ne_one, List.not_mem_nil, Order.lt_two_iff, IsEmpty.forall_iff,
      implies_true, and_true, true_and]
    have hy := hb y (by simp)
    have hys : Nat.size y ≤ 1 := size_le_one_of_le_one (by omega)
    have hyr : Nat.size (y % 2) ≤ 1 := size_le_one_of_le_one (by omega)
    have hbt : Bits b := fun z hz => hb z (by simp [hz])
    exact ⟨by omega, fun z hz => Nat.le_of_lt_succ (hbt z hz)⟩
  · simp only [addBody, Fin.isValue, Stmt.run, h0, setReg_lists, setList_lists,
      Function.update, Fin.reduceEq, dite_true, dite_false, h1, Expr.eval, setReg_regs,
      add_zero, Expr.cost, Expr.readSize, Nat.size_zero, setList_regs, h2,
      show Nat.size 2 = 2 by decide, one_ne_zero, Order.add_one_le_iff, Bits,
      zero_ne_one, Order.lt_two_iff, List.not_mem_nil, IsEmpty.forall_iff,
      implies_true, and_self, and_true]
    have hx := ha x (by simp)
    have hxs : Nat.size x ≤ 1 := size_le_one_of_le_one (by omega)
    have hxr : Nat.size (x % 2) ≤ 1 := size_le_one_of_le_one (by omega)
    have hat : Bits a := fun z hz => ha z (by simp [hz])
    exact ⟨by omega, fun z hz => Nat.le_of_lt_succ (hat z hz)⟩
  · simp only [addBody, Fin.isValue, Stmt.run, h0, setReg_lists, setList_lists,
      Function.update, Fin.reduceEq, dite_true, dite_false, h1, Expr.eval, setReg_regs,
      setList_regs, Expr.cost, Expr.readSize, h2, show Nat.size 2 = 2 by decide,
      one_ne_zero, Order.add_one_le_iff, Bits, zero_ne_one, Order.lt_two_iff, and_true]
    have hx := ha x (by simp)
    have hy := hb y (by simp)
    have hxs : Nat.size x ≤ 1 := size_le_one_of_le_one (by omega)
    have hys : Nat.size y ≤ 1 := size_le_one_of_le_one (by omega)
    have hxy : Nat.size (x + y) ≤ 3 := (size_add_le x y).trans (by omega)
    have hxr : Nat.size ((x + y) % 2) ≤ 1 :=
      size_le_one_of_le_one (by omega)
    have hat : Bits a := fun z hz => ha z (by simp [hz])
    have hbt : Bits b := fun z hz => hb z (by simp [hz])
    exact ⟨by omega, (fun z hz => Nat.le_of_lt_succ (hat z hz)),
      fun z hz => Nat.le_of_lt_succ (hbt z hz)⟩

/-- Addition has a concrete quadratic bound in the stored word length.
The logarithmic loop bookkeeping is charged by the actual operational semantics. -/
theorem add_cost (st : State 8 8) (a b : List ℕ) (ha : st.lists 0 = a)
    (hb : st.lists 2 = b) (ho : st.lists 1 = []) (hlen : a.length = b.length)
    (haBit : Bits a) (hbBit : Bits b) :
    (add.run st).2 ≤ 50 * (a.length + 1) ^ 2 := by
  let s := setReg (setReg st 4 2) 0 a.length
  have hbits : Bits (s.lists 0) ∧ Bits (s.lists 2) ∧ s.regs 4 = 2 := by
    simp [s, ha, hb, Function.update, haBit, hbBit]
  have hit := iterate_cost_le addBody.run (Nat.size a.length + 1) 32
    (fun s => Bits (s.lists 0) ∧ Bits (s.lists 2) ∧ s.regs 4 = 2)
    (fun s hs => (addBody_cost s hs.1 hs.2.1 hs.2.2).2)
    (fun s hs => (addBody_cost s hs.1 hs.2.1 hs.2.2).1) a.length s hbits
  have hout := (add_iterate (Nat.size a.length + 1) a.length s a b []
    (by simp [s, ha]) (by simp [s, hb]) (by simp [s, ho]) hbits.2.2 le_rfl hlen).1
  have houtSize : listSize ((iterate addBody.run (Nat.size a.length + 1) a.length s).1.lists 1)
      ≤ 2 * a.length := by
    rw [hout, List.append_nil, listSize_reverse]
    have h := listSize_bits (addWords_bits (a.take a.length) (b.take a.length))
    simpa [addWords, hlen] using h
  have hsize := listSize_bits haBit
  have hlenSize := size_le_self a.length
  simp only [add, run_seq_snd, run_assign_fst, run_len_snd, run_len_fst,
    run_loop_snd, run_rev_snd, run_loop_fst, setReg_lists, setReg_regs, Expr.eval,
    Function.update_self, ha]
  change (Expr.const 2).cost st.regs + (listSize a + Nat.size a.length + 1 +
    ((iterate addBody.run (Nat.size a.length + 1) a.length s).2 + Nat.size a.length + 1 +
      (listSize ((iterate addBody.run (Nat.size a.length + 1) a.length s).1.lists 1) + 1) + 1) + 1)
    + 1 ≤ _
  norm_num [Expr.cost, Expr.readSize, Expr.eval, show Nat.size 2 = 2 by decide]
  have hm := Nat.mul_le_mul_left a.length hlenSize
  nlinarith

/-- Stored multiplication by `X`, before reduction; defined for nonempty words. -/
def shiftUpWords (a : List ℕ) : List ℕ := 0 :: a.dropLast

/-- Read the highest stored coefficient. -/
def topWord (a : List ℕ) : ℕ := a.reverse.headD 0

/-- A reduced shift uses a single stored addition when its top coefficient is one. -/
def shiftWords (m a : List ℕ) : List ℕ :=
  if topWord a = 0 then shiftUpWords a else addWords (shiftUpWords a) m

theorem encode_shiftUp {t : ℕ} (ht : 0 < t) (v : BinaryWordMaterialization.Word t) :
    encode (BinaryWordMaterialization.ofWord
      (BinaryWordArithmetic.shiftUp (BinaryWordMaterialization.toWord v))) =
      shiftUpWords (encode v) := by
  apply List.ext_getElem
  · simp [shiftUpWords]; omega
  · intro i hi hi'
    simp only [encode, BinaryWordMaterialization.toWord_ofWord, List.getElem_ofFn,
      BinaryWordArithmetic.shiftUp, shiftUpWords, List.getElem_cons]
    split_ifs with h
    · simp
    · simp only [List.getElem_dropLast, List.getElem_ofFn]

theorem encode_top {t : ℕ} (ht : 0 < t) (v : BinaryWordMaterialization.Word t) :
    topWord (encode v) = (BinaryWordArithmetic.top ht
      (BinaryWordMaterialization.toWord v)).val := by
  have hn : (encode v).reverse ≠ [] := by
    intro h
    have := congrArg List.length h
    simp at this
    omega
  rw [topWord, List.headD_eq_head?, List.head?_eq_some_head hn, Option.getD_some,
    List.head_eq_getElem, List.getElem_reverse]
  simp [encode, BinaryWordArithmetic.top]

/-- The list reduced shift is the same operation as the materialized array shift. -/
theorem encode_shift {t : ℕ} (ht : 0 < t) (m v : BinaryWordMaterialization.Word t) :
    encode (BinaryWordMaterialization.shift ht m v) = shiftWords (encode m) (encode v) := by
  rw [shiftWords, encode_top ht v]
  let x := BinaryWordArithmetic.top ht (BinaryWordMaterialization.toWord v)
  have hx : x = 0 ∨ x = 1 := by
    have hv := ZMod.val_lt x
    have hv' : x.val = 0 ∨ x.val = 1 := by omega
    rcases hv' with h | h
    · left; exact ZMod.val_injective 2 (by simpa using h)
    · right; exact ZMod.val_injective 2 (by simpa only [show (1 : ZMod 2).val = 1 from rfl] using h)
  rcases hx with hx | hx
  · have hword : BinaryWordMaterialization.shift ht m v =
        BinaryWordMaterialization.ofWord
          (BinaryWordArithmetic.shiftUp (BinaryWordMaterialization.toWord v)) := by
      unfold BinaryWordMaterialization.shift BinaryWordArithmetic.shift
      change BinaryWordMaterialization.ofWord (_ - x • _) = _
      simp [hx]
    simpa only [show BinaryWordArithmetic.top ht (BinaryWordMaterialization.toWord v) = 0
      from hx, ZMod.val_zero, ite_true, hword] using encode_shiftUp ht v
  · have hword : BinaryWordMaterialization.shift ht m v =
        BinaryWordMaterialization.add
          (BinaryWordMaterialization.ofWord
            (BinaryWordArithmetic.shiftUp (BinaryWordMaterialization.toWord v))) m := by
      unfold BinaryWordMaterialization.shift BinaryWordArithmetic.shift
        BinaryWordMaterialization.add
      rw [BinaryWordMaterialization.toWord_ofWord]
      change BinaryWordMaterialization.ofWord (_ - x • _) = _
      have hn : -BinaryWordMaterialization.toWord m = BinaryWordMaterialization.toWord m := by
        funext i
        exact CharTwo.neg_eq _
      simp [hx, sub_eq_add_neg, hn]
    rw [hword, encode_add, encode_shiftUp ht v]
    simp only [show BinaryWordArithmetic.top ht (BinaryWordMaterialization.toWord v) = 1
      from hx, show (1 : ZMod 2).val = 1 from rfl, Nat.one_ne_zero, ite_false]

/-- Extract the highest bit to register `5` and shift list `0` in place. -/
def shiftPrep : Stmt 8 8 :=
  .seq (.rev 0) (.seq (.pop 0 5 3)
    (.seq (.rev 0) (.seq (.assign 1 (.const 0)) (.push 0 1))))

theorem shiftPrep_run (st : State 8 8) (a : List ℕ) (ha : st.lists 0 = a) :
    (shiftPrep.run st).1.lists 0 = shiftUpWords a ∧
    (shiftPrep.run st).1.regs 5 = topWord a := by
  rcases h : a.reverse with _ | ⟨x, b⟩
  · have hz : a = [] := by simpa using congrArg List.reverse h
    simp [shiftPrep, Stmt.run, ha, hz, shiftUpWords, topWord, Expr.eval, Function.update]
  · have hd : a.dropLast = b.reverse := by
      have := congrArg (fun l : List ℕ => l.tail.reverse) h
      simpa using this
    simp [shiftPrep, Stmt.run, ha, h, shiftUpWords, topWord, hd, Expr.eval, Function.update]

/-- Multiply list `0` by `X` modulo the monic polynomial with lower coefficients in list `3`.
List `7` supplies an empty output buffer; list `1` receives the resulting word. -/
def shift : Stmt 8 8 :=
  .seq shiftPrep (.ite 5
    (.seq (.copy 3 2) (.seq (.copy 7 1) add)) (.copy 0 1))

theorem shift_run (st : State 8 8) (m a : List ℕ) (ha : st.lists 0 = a)
    (hm : st.lists 3 = m) (he : st.lists 7 = []) (hpos : 0 < a.length)
    (hlen : a.length = m.length) :
    (shift.run st).1.lists 1 = shiftWords m a := by
  obtain ⟨h0, h5⟩ := shiftPrep_run st a ha
  have h3 := run_lists_frame shiftPrep 3 (by decide) st
  have h7 := run_lists_frame shiftPrep 7 (by decide) st
  simp only [shift, run_seq_fst, run_ite_fst, h5, shiftWords]
  by_cases hz : topWord a = 0
  · simp [hz, run_copy_fst, h0]
  · rw [ite_eq_left hz, ite_eq_right hz]
    simp only [run_copy_fst]
    exact add_run _ (shiftUpWords a) m (by simp [Function.update, h0])
      (by simp [Function.update, h3, hm]) (by simp [Function.update, h7, he])
      (by simp [shiftUpWords]; omega)

theorem shift_run_encode {t : ℕ} (ht : 0 < t) (st : State 8 8)
    (m v : BinaryWordMaterialization.Word t)
    (ha : st.lists 0 = encode v) (hm : st.lists 3 = encode m) (he : st.lists 7 = []) :
    (shift.run st).1.lists 1 = encode (BinaryWordMaterialization.shift ht m v) := by
  rw [encode_shift]
  exact shift_run st _ _ ha hm he (by simpa using ht) (by simp)

theorem shiftUpWords_bits {a : List ℕ} (ha : Bits a) : Bits (shiftUpWords a) := by
  intro x hx
  rcases List.mem_cons.mp hx with rfl | hx
  · decide
  · exact ha x (List.mem_of_mem_dropLast hx)

theorem topWord_lt_two {a : List ℕ} (ha : Bits a) : topWord a < 2 := by
  rcases h : a.reverse with _ | ⟨x, b⟩
  · simp [topWord, h]
  · have hx : x ∈ a := List.mem_reverse.mp (by simp [h])
    simpa only [topWord, h, List.headD_cons] using ha x hx

theorem shiftWords_bits (m a : List ℕ) (ha : Bits a) : Bits (shiftWords m a) := by
  unfold shiftWords
  split_ifs
  · exact shiftUpWords_bits ha
  · exact addWords_bits _ _

theorem shiftWords_length (m a : List ℕ) (hpos : 0 < a.length)
    (hlen : a.length = m.length) : (shiftWords m a).length = a.length := by
  unfold shiftWords
  split_ifs <;> simp [shiftUpWords, addWords] <;> omega

theorem shiftPrep_cost (st : State 8 8) (a : List ℕ) (ha : st.lists 0 = a)
    (hbit : Bits a) : (shiftPrep.run st).2 ≤ 5000 * (a.length + 1) := by
  have hcost := loopFree_cost_le shiftPrep (by decide) st (2 * a.length)
    (by simp [shiftPrep, Stmt.uses, Stmt.mustW, Expr.uses])
    (by
      intro L hL
      have hL0 : L = 0 := by simpa [shiftPrep, Stmt.lUses] using hL
      subst L
      rw [ha]
      exact listSize_bits hbit)
  have hc : shiftPrep.C * (shiftPrep.width + shiftPrep.csize + 1) = 2368 := by decide
  rw [hc] at hcost
  omega

/-- Reduced shifting has a concrete quadratic bound, including all stored copies and reversals. -/
theorem shift_cost (st : State 8 8) (m a : List ℕ) (ha : st.lists 0 = a)
    (hm : st.lists 3 = m) (he : st.lists 7 = []) (hpos : 0 < a.length)
    (hlen : a.length = m.length) (haBit : Bits a) (hmBit : Bits m) :
    (shift.run st).2 ≤ 6000 * (a.length + 1) ^ 2 := by
  let s := (shiftPrep.run st).1
  obtain ⟨h0, h5⟩ := shiftPrep_run st a ha
  have h3 := (run_lists_frame shiftPrep 3 (by decide) st).trans hm
  have h7 := (run_lists_frame shiftPrep 7 (by decide) st).trans he
  have hp := shiftPrep_cost st a ha haBit
  have htSize : Nat.size (topWord a) ≤ 1 := size_le_one_of_le_one (by
    have := topWord_lt_two haBit
    omega)
  have hmSize := listSize_bits hmBit
  have huSize := listSize_bits (shiftUpWords_bits haBit)
  have huLen : (shiftUpWords a).length = a.length := by simp [shiftUpWords]; omega
  rw [huLen] at huSize
  simp only [shift, run_seq_snd, run_ite_snd, h5]
  by_cases hz : topWord a = 0
  · simp only [hz, ne_eq, not_true_eq_false, ite_false, run_copy_snd, h0, Nat.size_zero]
    nlinarith
  · rw [ite_eq_left hz]
    have hadd := add_cost (setList (setList s 2 (s.lists 3)) 1 (s.lists 7))
      (shiftUpWords a) m (by simp [Function.update, s, h0])
      (by simp [Function.update, s, h3]) (by simp [s, h7]) (by omega)
      (shiftUpWords_bits haBit) hmBit
    rw [huLen] at hadd
    simp only [s, h3, h7] at hadd
    simp only [run_copy_snd, run_copy_fst, setList_lists,
      Function.update_of_ne (by decide : (7 : Fin 8) ≠ 2), h3, h7]
    simp only [show listSize ([] : List ℕ) = 0 from rfl]
    nlinarith

/-- Add the saved shift register `5` into the saved accumulator `6`. -/
def accumulate : Stmt 8 8 :=
  .seq (.copy 6 0) (.seq (.copy 5 2) (.seq (.copy 7 1)
    (.seq add (.copy 1 6))))

theorem accumulate_run (st : State 8 8) (a w : List ℕ)
    (ha : st.lists 6 = a) (hw : st.lists 5 = w) (he : st.lists 7 = [])
    (hlen : a.length = w.length) :
    (accumulate.run st).1.lists 6 = addWords a w := by
  simp only [accumulate, run_seq_fst, run_copy_fst, setList_lists, Function.update_self]
  apply add_run
  · simp [Function.update, ha]
  · simp [Function.update, hw]
  · simp [Function.update, he]
  · exact hlen

theorem accumulate_cost (st : State 8 8) (a w : List ℕ)
    (ha : st.lists 6 = a) (hw : st.lists 5 = w) (he : st.lists 7 = [])
    (hlen : a.length = w.length) (haBit : Bits a) (hwBit : Bits w) :
    (accumulate.run st).2 ≤ 100 * (a.length + 1) ^ 2 := by
  let s := setList (setList (setList st 0 a) 2 w) 1 []
  have hadd := add_cost s a w (by simp [s, Function.update]) (by simp [s, Function.update])
    (by simp [s]) hlen haBit hwBit
  have hout := add_run s a w (by simp [s, Function.update]) (by simp [s, Function.update])
    (by simp [s]) hlen
  have haSize := listSize_bits haBit
  have hwSize := listSize_bits hwBit
  have hoSize := listSize_bits (addWords_bits a w)
  have hoLen : (addWords a w).length = a.length := by simp [addWords, hlen]
  rw [hoLen] at hoSize
  simp only [accumulate, run_seq_snd, run_copy_snd, run_copy_fst, setList_lists]
  simp only [Function.update, Fin.reduceEq, dite_false, ha, hw, he]
  change listSize a + 1 + (listSize w + 1 + (listSize [] + 1 +
    ((add.run s).2 + (listSize ((add.run s).1.lists 1) + 1) + 1) + 1) + 1) + 1 ≤ _
  rw [hout]
  simp only [show listSize ([] : List ℕ) = 0 from rfl]
  nlinarith

/-- Advance the saved reduction register `5`, keeping the modulus in list `3`. -/
def advance : Stmt 8 8 := .seq (.copy 5 0) (.seq shift (.copy 1 5))

theorem advance_run (st : State 8 8) (m w : List ℕ) (hm : st.lists 3 = m)
    (hw : st.lists 5 = w) (he : st.lists 7 = []) (hpos : 0 < w.length)
    (hlen : w.length = m.length) :
    (advance.run st).1.lists 5 = shiftWords m w := by
  simp only [advance, run_seq_fst, run_copy_fst, setList_lists, Function.update_self]
  exact shift_run _ m w (by simp [hw]) (by simp [Function.update, hm])
    (by simp [Function.update, he]) hpos hlen

theorem advance_cost (st : State 8 8) (m w : List ℕ) (hm : st.lists 3 = m)
    (hw : st.lists 5 = w) (he : st.lists 7 = []) (hpos : 0 < w.length)
    (hlen : w.length = m.length) (hmBit : Bits m) (hwBit : Bits w) :
    (advance.run st).2 ≤ 6100 * (w.length + 1) ^ 2 := by
  let s := setList st 0 w
  have hs := shift_cost s m w (by simp [s]) (by simp [s, Function.update, hm])
    (by simp [s, Function.update, he]) hpos hlen hwBit hmBit
  have ho := shift_run s m w (by simp [s]) (by simp [s, Function.update, hm])
    (by simp [s, Function.update, he]) hpos hlen
  have hwSize := listSize_bits hwBit
  have hoSize := listSize_bits (shiftWords_bits m w hwBit)
  rw [shiftWords_length m w hpos hlen] at hoSize
  simp only [advance, run_seq_snd, run_copy_snd, run_copy_fst, hw]
  change listSize w + 1 + ((shift.run s).2 +
    (listSize ((shift.run s).1.lists 1) + 1) + 1) + 1 ≤ _
  rw [ho]
  nlinarith

/-- One schoolbook multiplication stage consumes one coefficient from list `4`. -/
def mulBody : Stmt 8 8 :=
  .seq (.pop 4 6 3) (.seq (.ite 6 accumulate .skip) advance)

theorem mulBody_step (st : State 8 8) (m w a : List ℕ) (x : ℕ) (v : List ℕ)
    (hm : st.lists 3 = m) (hw : st.lists 5 = w) (ha : st.lists 6 = a)
    (hv : st.lists 4 = x :: v) (he : st.lists 7 = [])
    (hpos : 0 < w.length) (hmLen : w.length = m.length) (haLen : a.length = w.length) :
    (mulBody.run st).1.lists 3 = m ∧
    (mulBody.run st).1.lists 4 = v ∧
    (mulBody.run st).1.lists 5 = shiftWords m w ∧
    (mulBody.run st).1.lists 6 = (if x = 0 then a else addWords a w) ∧
    (mulBody.run st).1.lists 7 = [] := by
  let s := (Stmt.pop 4 6 3).run st |>.1
  have hs3 : s.lists 3 = m := by simp [s, Stmt.run, hv, Function.update, hm]
  have hs4 : s.lists 4 = v := by simp [s, Stmt.run, hv]
  have hs5 : s.lists 5 = w := by simp [s, Stmt.run, hv, Function.update, hw]
  have hs6 : s.lists 6 = a := by simp [s, Stmt.run, hv, Function.update, ha]
  have hs7 : s.lists 7 = [] := by simp [s, Stmt.run, hv, Function.update, he]
  have hsx : s.regs 6 = x := by simp [s, Stmt.run, hv, Function.update]
  let u := ((Stmt.ite 6 accumulate .skip).run s).1
  have hu3 : u.lists 3 = m := (run_lists_frame (.ite 6 accumulate .skip) 3 (by decide) s).trans hs3
  have hu4 : u.lists 4 = v := (run_lists_frame (.ite 6 accumulate .skip) 4 (by decide) s).trans hs4
  have hu5 : u.lists 5 = w := (run_lists_frame (.ite 6 accumulate .skip) 5 (by decide) s).trans hs5
  have hu7 : u.lists 7 = [] := (run_lists_frame (.ite 6 accumulate .skip) 7 (by decide) s).trans hs7
  have hu6 : u.lists 6 = (if x = 0 then a else addWords a w) := by
    simp only [u, run_ite_fst, hsx]
    by_cases hx : x = 0
    · simp [hx, Stmt.run, hs6]
    · rw [ite_eq_left hx, ite_eq_right hx]
      exact accumulate_run s a w hs6 hs5 hs7 haLen
  change (advance.run u).1.lists 3 = m ∧ _
  exact ⟨(run_lists_frame advance 3 (by decide) u).trans hu3,
    (run_lists_frame advance 4 (by decide) u).trans hu4,
    advance_run u m w hu3 hu5 hu7 hpos hmLen,
    (run_lists_frame advance 6 (by decide) u).trans hu6,
    (run_lists_frame advance 7 (by decide) u).trans hu7⟩

/-- The stored-list schoolbook recurrence, with an explicit accumulator. -/
def mulWords (m : List ℕ) : List ℕ → List ℕ → List ℕ → List ℕ
  | [], _, a => a
  | x :: v, w, a => mulWords m v (shiftWords m w) (if x = 0 then a else addWords a w)

/-- The multiplication loop computes the stored-list recurrence exactly. -/
theorem mul_iterate (c : ℕ) (st : State 8 8) (m v w a : List ℕ)
    (hm : st.lists 3 = m) (hv : st.lists 4 = v) (hw : st.lists 5 = w)
    (ha : st.lists 6 = a) (he : st.lists 7 = [])
    (hpos : 0 < w.length) (hmLen : w.length = m.length) (haLen : a.length = w.length) :
    (iterate mulBody.run c v.length st).1.lists 6 = mulWords m v w a := by
  induction v generalizing st w a with
  | nil => simpa [iterate, mulWords] using ha
  | cons x v ih =>
    obtain ⟨h3, h4, h5, h6, h7⟩ := mulBody_step st m w a x v
      hm hw ha hv he hpos hmLen haLen
    rw [List.length_cons, iterate_succ_fst]
    apply ih _ _ _ h3 h4 h5 h6 h7
    · simpa [shiftWords_length m w hpos hmLen] using hpos
    · simpa [shiftWords_length m w hpos hmLen] using hmLen
    · rw [shiftWords_length m w hpos hmLen]
      split_ifs <;> simp [addWords, haLen]

theorem encode_add_scale {t : ℕ} (a w : BinaryWordMaterialization.Word t) (x : ZMod 2) :
    encode (BinaryWordMaterialization.add a (BinaryWordMaterialization.scale x w)) =
      if x.val = 0 then encode a else addWords (encode a) (encode w) := by
  have hx : x = 0 ∨ x = 1 := by
    have hv := ZMod.val_lt x
    rcases (show x.val = 0 ∨ x.val = 1 by omega) with h | h
    · left; exact ZMod.val_injective 2 (by simpa using h)
    · right; exact ZMod.val_injective 2 (by simpa only [show (1 : ZMod 2).val = 1 from rfl] using h)
  rcases hx with rfl | rfl
  · simp [BinaryWordMaterialization.add, BinaryWordMaterialization.scale]
  · simp [BinaryWordMaterialization.scale, show (1 : ZMod 2).val = 1 from rfl]

/-- Stored multiplication invariant, including the saved modulus and the remaining input. -/
def MulInv {t : ℕ} (ht : 0 < t) (m v w : BinaryWordMaterialization.Word t)
    (j : ℕ) (st : State 8 8) : Prop :=
  ∃ hj : j ≤ t,
    st.lists 3 = encode m ∧ st.lists 4 = (encode v).drop j ∧
    st.lists 5 = encode (BinaryWordMaterialization.mulState ht m v w j hj).2 ∧
    st.lists 6 = encode (BinaryWordMaterialization.mulState ht m v w j hj).1 ∧
    st.lists 7 = []

theorem mulBody_inv {t : ℕ} (ht : 0 < t) (m v w : BinaryWordMaterialization.Word t)
    (j : ℕ) (st : State 8 8) (hj : j < t) (h : MulInv ht m v w j st) :
    MulInv ht m v w (j + 1) (mulBody.run st).1 := by
  obtain ⟨hle, hm, hv, hw, ha, he⟩ := h
  have hv' : st.lists 4 = (BinaryWordMaterialization.toWord v ⟨j, hj⟩).val ::
      (encode v).drop (j + 1) := by
    rw [hv, List.drop_eq_getElem_cons (by simpa using hj)]
    simp [encode]
  obtain ⟨h3, h4, h5, h6, h7⟩ := mulBody_step st (encode m)
    (encode (BinaryWordMaterialization.mulState ht m v w j hle).2)
    (encode (BinaryWordMaterialization.mulState ht m v w j hle).1)
    (BinaryWordMaterialization.toWord v ⟨j, hj⟩).val ((encode v).drop (j + 1))
    hm hw ha hv' he (by simpa using ht) (by simp) (by simp)
  refine ⟨by omega, h3, h4, ?_, ?_, h7⟩
  · simpa only [BinaryWordMaterialization.mulState, encode_shift ht] using h5
  · simpa only [BinaryWordMaterialization.mulState, encode_add_scale] using h6

/-- Actual loop correctness against the existing materialized multiplication, without
replacing the stored-list implementation by its semantic recurrence. -/
theorem mul_iterate_encode {t : ℕ} (ht : 0 < t) (c : ℕ) (st : State 8 8)
    (m v w : BinaryWordMaterialization.Word t)
    (hm : st.lists 3 = encode m) (hv : st.lists 4 = encode v)
    (hw : st.lists 5 = encode w)
    (ha : st.lists 6 = encode (BinaryWordMaterialization.zero t)) (he : st.lists 7 = []) :
    (iterate mulBody.run c t st).1.lists 6 =
      encode (BinaryWordMaterialization.mul ht m v w) := by
  have h := iterate_inv mulBody.run c t (MulInv ht m v w)
    (fun j s hj hs => mulBody_inv ht m v w j s hj hs) st
    ⟨Nat.zero_le t, hm, by simpa using hv, hw, ha, he⟩
  exact h.choose_spec.2.2.2.1

/-- Materialize the zero accumulator using one push per coefficient of list `5`. -/
def zeroAccumulator : Stmt 8 8 :=
  .seq (.copy 7 6) (.seq (.len 5 7) (.seq (.assign 1 (.const 0)) (.loop 7 (.push 6 1))))

theorem pushZero_iterate (c n : ℕ) (st : State 8 8) (h0 : st.regs 1 = 0) :
    (iterate (Stmt.push (6 : Fin 8) (1 : Fin 8)).run c n st).1.lists 6 =
      List.replicate n 0 ++ st.lists 6 := by
  induction n generalizing st with
  | zero => simp [iterate]
  | succ n ih =>
    rw [iterate_succ_fst, ih _ (by simp [run_push_fst, h0]), run_push_fst]
    simp only [setList_lists, Function.update_self, h0, List.replicate_succ',
      List.append_assoc, List.singleton_append]

@[simp] theorem encode_zero (t : ℕ) :
    encode (BinaryWordMaterialization.zero t) = List.replicate t 0 := by
  simp [encode]

theorem zeroAccumulator_run (st : State 8 8) (he : st.lists 7 = []) :
    (zeroAccumulator.run st).1.lists 6 = List.replicate (st.lists 5).length 0 := by
  simp only [zeroAccumulator, run_seq_fst, run_copy_fst, run_len_fst, run_assign_fst,
    Expr.eval, run_loop_fst, setReg_regs, Function.update_of_ne (by decide : (7 : Fin 8) ≠ 1),
    Function.update_self, setList_lists,
    Function.update_of_ne (by decide : (5 : Fin 8) ≠ 6)]
  rw [pushZero_iterate _ _ _ (by simp)]
  simp [he]

/-- Complete schoolbook multiplication on stored words: lists `3,4,5` hold modulus,
left operand and right operand; list `7` is empty; list `1` receives the product. -/
def mul : Stmt 8 8 :=
  .seq zeroAccumulator (.seq (.len 4 7) (.seq (.loop 7 mulBody) (.copy 6 1)))

theorem mul_run_encode {t : ℕ} (ht : 0 < t) (st : State 8 8)
    (m v w : BinaryWordMaterialization.Word t)
    (hm : st.lists 3 = encode m) (hv : st.lists 4 = encode v)
    (hw : st.lists 5 = encode w) (he : st.lists 7 = []) :
    (mul.run st).1.lists 1 = encode (BinaryWordMaterialization.mul ht m v w) := by
  let s := (zeroAccumulator.run st).1
  have h3 : s.lists 3 = encode m :=
    (run_lists_frame zeroAccumulator 3 (by decide) st).trans hm
  have h4 : s.lists 4 = encode v :=
    (run_lists_frame zeroAccumulator 4 (by decide) st).trans hv
  have h5 : s.lists 5 = encode w :=
    (run_lists_frame zeroAccumulator 5 (by decide) st).trans hw
  have h7 : s.lists 7 = [] := (run_lists_frame zeroAccumulator 7 (by decide) st).trans he
  have h6 : s.lists 6 = encode (BinaryWordMaterialization.zero t) := by
    simpa only [s, hw, encode_length, encode_zero] using zeroAccumulator_run st he
  simp only [mul, run_seq_fst, run_len_fst, run_copy_fst, run_loop_fst,
    setReg_regs, Function.update_self, setList_lists]
  change (iterate mulBody.run (Nat.size (s.lists 4).length + 1) (s.lists 4).length
    (setReg s 7 (s.lists 4).length)).1.lists 6 = _
  rw [h4, encode_length]
  exact mul_iterate_encode ht _ _ m v w (by simpa using h3) (by simpa using h4)
    (by simpa using h5) (by simpa using h6) (by simpa using h7)

theorem mulBody_cost (st : State 8 8) (m w a : List ℕ) (x : ℕ) (v : List ℕ)
    (hm : st.lists 3 = m) (hw : st.lists 5 = w) (ha : st.lists 6 = a)
    (hv : st.lists 4 = x :: v) (he : st.lists 7 = [])
    (hpos : 0 < w.length) (hmLen : w.length = m.length) (haLen : a.length = w.length)
    (hmBit : Bits m) (hwBit : Bits w) (haBit : Bits a) (hx : x < 2) :
    (mulBody.run st).2 ≤ 6300 * (w.length + 1) ^ 2 := by
  let s := (Stmt.pop 4 6 3).run st |>.1
  have hs3 : s.lists 3 = m := by simp [s, Stmt.run, hv, Function.update, hm]
  have hs5 : s.lists 5 = w := by simp [s, Stmt.run, hv, Function.update, hw]
  have hs6 : s.lists 6 = a := by simp [s, Stmt.run, hv, Function.update, ha]
  have hs7 : s.lists 7 = [] := by simp [s, Stmt.run, hv, Function.update, he]
  have hsx : s.regs 6 = x := by simp [s, Stmt.run, hv, Function.update]
  let u := ((Stmt.ite 6 accumulate .skip).run s).1
  have hu3 : u.lists 3 = m := (run_lists_frame (.ite 6 accumulate .skip) 3 (by decide) s).trans hs3
  have hu5 : u.lists 5 = w := (run_lists_frame (.ite 6 accumulate .skip) 5 (by decide) s).trans hs5
  have hu7 : u.lists 7 = [] := (run_lists_frame (.ite 6 accumulate .skip) 7 (by decide) s).trans hs7
  have hadv := advance_cost u m w hu3 hu5 hu7 hpos hmLen hmBit hwBit
  have hacc := accumulate_cost s a w hs6 hs5 hs7 haLen haBit hwBit
  rw [haLen] at hacc
  have hxs : Nat.size x ≤ 1 := size_le_one_of_le_one (by omega)
  have hpop : ((Stmt.pop (4 : Fin 8) (6 : Fin 8) 3).run st).2 ≤ 2 := by
    simpa only [Stmt.run, hv] using Nat.add_le_add_right hxs 1
  have hite : ((Stmt.ite 6 accumulate .skip).run s).2 ≤
      100 * (w.length + 1) ^ 2 + 2 := by
    rw [run_ite_snd, hsx]
    split_ifs
    · omega
    · change 1 + Nat.size x + 1 ≤ _
      nlinarith
  change ((Stmt.pop (4 : Fin 8) (6 : Fin 8) 3).run st).2 +
    (((Stmt.ite 6 accumulate .skip).run s).2 + (advance.run u).2 + 1) + 1 ≤ _
  nlinarith

theorem mulBody_inv_cost {t : ℕ} (ht : 0 < t) (m v w : BinaryWordMaterialization.Word t)
    (j : ℕ) (st : State 8 8) (hj : j < t) (h : MulInv ht m v w j st) :
    (mulBody.run st).2 ≤ 6300 * (t + 1) ^ 2 := by
  obtain ⟨hle, hm, hv, hw, ha, he⟩ := h
  have hv' : st.lists 4 = (BinaryWordMaterialization.toWord v ⟨j, hj⟩).val ::
      (encode v).drop (j + 1) := by
    rw [hv, List.drop_eq_getElem_cons (by simpa using hj)]
    simp [encode]
  simpa only [encode_length] using mulBody_cost st (encode m)
    (encode (BinaryWordMaterialization.mulState ht m v w j hle).2)
    (encode (BinaryWordMaterialization.mulState ht m v w j hle).1)
    (BinaryWordMaterialization.toWord v ⟨j, hj⟩).val ((encode v).drop (j + 1))
    hm hw ha hv' he (by simpa using ht) (by simp) (by simp)
    (encode_bits _) (encode_bits _) (encode_bits _) (ZMod.val_lt _)

theorem zeroAccumulator_cost (st : State 8 8) (he : st.lists 7 = [])
    (hw : Bits (st.lists 5)) :
    (zeroAccumulator.run st).2 ≤ 10 * ((st.lists 5).length + 1) ^ 2 := by
  let n := (st.lists 5).length
  let s := setReg (setReg (setList st 6 []) 7 n) 1 0
  have hit := iterate_cost_le (Stmt.push (6 : Fin 8) (1 : Fin 8)).run
    (Nat.size n + 1) 1 (fun s => s.regs 1 = 0)
    (fun s hs => by simpa [run_push_fst] using hs)
    (fun s hs => by simp [run_push_snd, hs]) n s (by simp [s])
  have hs := listSize_bits hw
  have hn := size_le_self n
  simp only [zeroAccumulator, run_seq_snd, run_copy_snd, he, run_copy_fst, run_len_snd,
    run_len_fst, run_assign_fst, Expr.eval, run_loop_snd, setReg_regs, setList_lists,
    Function.update_of_ne (by decide : (5 : Fin 8) ≠ 6),
    Function.update_of_ne (by decide : (7 : Fin 8) ≠ 1), Function.update_self]
  change listSize [] + 1 + (listSize (st.lists 5) + Nat.size n + 1 +
    ((Expr.const 0).cost _ + ((iterate (Stmt.push 6 1).run (Nat.size n + 1) n s).2 +
      Nat.size n + 1) + 1) + 1) + 1 ≤ _
  simp only [Expr.cost, Expr.readSize, Expr.eval, Nat.size_zero,
    show listSize ([] : List ℕ) = 0 from rfl]
  change _ ≤ 10 * (n + 1) ^ 2
  have hmul := Nat.mul_le_mul_left n hn
  nlinarith

/-- Complete stored-word multiplication has cubic charged `Lang` cost.
All intermediate coefficient lists, copies, and loop counters are included. -/
theorem mul_cost_encode {t : ℕ} (ht : 0 < t) (st : State 8 8)
    (m v w : BinaryWordMaterialization.Word t)
    (hm : st.lists 3 = encode m) (hv : st.lists 4 = encode v)
    (hw : st.lists 5 = encode w) (he : st.lists 7 = []) :
    (mul.run st).2 ≤ 6500 * (t + 1) ^ 3 := by
  let s := (zeroAccumulator.run st).1
  have h3 : s.lists 3 = encode m :=
    (run_lists_frame zeroAccumulator 3 (by decide) st).trans hm
  have h4 : s.lists 4 = encode v :=
    (run_lists_frame zeroAccumulator 4 (by decide) st).trans hv
  have h5 : s.lists 5 = encode w :=
    (run_lists_frame zeroAccumulator 5 (by decide) st).trans hw
  have h7 : s.lists 7 = [] := (run_lists_frame zeroAccumulator 7 (by decide) st).trans he
  have h6 : s.lists 6 = encode (BinaryWordMaterialization.zero t) := by
    simpa only [s, hw, encode_length, encode_zero] using zeroAccumulator_run st he
  let u := setReg s 7 t
  have hinit : MulInv ht m v w 0 u :=
    ⟨Nat.zero_le t, by simpa [u] using h3, by simpa [u] using h4,
      by simpa [u, BinaryWordMaterialization.mulState] using h5,
      by simpa [u, BinaryWordMaterialization.mulState] using h6, by simpa [u] using h7⟩
  have hit := iterate_cost_idx mulBody.run (Nat.size t + 1) (6300 * (t + 1) ^ 2) t
    (MulInv ht m v w)
    (fun j s hj hs => ⟨mulBody_inv ht m v w j s hj hs,
      mulBody_inv_cost ht m v w j s hj hs⟩) u hinit
  have hout := mul_iterate_encode ht (Nat.size t + 1) u m v w
    (by simpa [u] using h3) (by simpa [u] using h4) (by simpa [u] using h5)
    (by simpa [u] using h6) (by simpa [u] using h7)
  have hz := zeroAccumulator_cost st he (by rw [hw]; exact encode_bits w)
  simp only [hw, encode_length] at hz
  have hvSize := listSize_bits (encode_bits v)
  have hoSize := listSize_bits (encode_bits (BinaryWordMaterialization.mul ht m v w))
  simp only [encode_length] at hvSize hoSize
  have hsz := size_le_self t
  simp only [mul, run_seq_snd, run_len_snd, run_len_fst, run_loop_snd,
    run_copy_snd, run_loop_fst, setReg_regs, Function.update_self]
  change (zeroAccumulator.run st).2 + (listSize (s.lists 4) + Nat.size (s.lists 4).length + 1 +
    ((iterate mulBody.run (Nat.size (s.lists 4).length + 1) (s.lists 4).length
      (setReg s 7 (s.lists 4).length)).2 + Nat.size (s.lists 4).length + 1 +
      (listSize ((iterate mulBody.run (Nat.size (s.lists 4).length + 1) (s.lists 4).length
        (setReg s 7 (s.lists 4).length)).1.lists 6) + 1) + 1) + 1) + 1 ≤ _
  rw [h4, encode_length]
  change (zeroAccumulator.run st).2 + (listSize (encode v) + Nat.size t + 1 +
    ((iterate mulBody.run (Nat.size t + 1) t u).2 + Nat.size t + 1 +
      (listSize ((iterate mulBody.run (Nat.size t + 1) t u).1.lists 6) + 1) + 1) + 1) + 1 ≤ _
  rw [hout]
  have hmul := Nat.mul_le_mul_left t hsz
  nlinarith

end PCP.Lang.BinaryField
