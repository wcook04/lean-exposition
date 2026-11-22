import PCP.Complexity.BinaryFieldCodeSemantics
import PCP.Complexity.BinaryFieldCodeCost
import PCP.Algebraic.FiniteGeneratorSearch

/-! # Testing full multiplicative order by an explicitly bounded power loop -/

namespace PCP.Lang.BinaryGeneratorPredicate

open PCP.Algebraic BinaryField BinaryFieldCode BooleanLoops

-- The explicit register-write sets unfold stored field arithmetic.

variable {t : ℕ} [NeZero t]

abbrev Field (t : ℕ) := BinaryMaterializedField.Element t

def GoodPrefix (a : Field t) (n : ℕ) : Prop :=
  ∀ k : Fin (n + 1), k.val ≠ 0 → a ^ k.val ≠ 1

instance (a : Field t) (n : ℕ) : Decidable (GoodPrefix a n) := by
  unfold GoodPrefix
  infer_instance

@[simp] theorem goodPrefix_zero (a : Field t) : GoodPrefix a 0 := by
  intro k hk
  have := k.isLt
  omega

theorem goodPrefix_succ (a : Field t) (n : ℕ) :
    GoodPrefix a (n + 1) ↔ GoodPrefix a n ∧ a ^ (n + 1) ≠ 1 := by
  constructor
  · intro h
    exact ⟨fun k hk => h k.castSucc hk, h (Fin.last (n+1)) (by simp)⟩
  · rintro ⟨h, hn⟩ k hk
    have hklt := k.isLt
    by_cases he : k.val = n + 1
    · simpa [he] using hn
    · exact h ⟨k.val, by omega⟩ hk

@[simp] theorem fieldCode_one : (fieldEquiv t (1 : Field t)).val = 1 :=
  BinaryFieldWordCode.value_encode_one t (NeZero.pos t)

@[simp] theorem fieldCode_zero : (fieldEquiv t (0 : Field t)).val = 0 := by
  change WordCodec.value (encode (BinaryWordMaterialization.zero t)) = 0
  rw [encode_zero]
  have h (n : ℕ) : WordCodec.value (List.replicate n 0) = 0 := by
    induction n with
    | zero => rfl
    | succ n ih => simp [List.replicate_succ, WordCodec.value, ih]
  exact h t

theorem fieldCode_eq_one (a : Field t) : (fieldEquiv t a).val = 1 ↔ a = 1 := by
  rw [← fieldCode_one (t := t)]
  exact ⟨fun h => (fieldEquiv t).injective (Fin.ext h), fun h => congrArg (fun x : Field t => (fieldEquiv t x).val) h⟩

theorem fieldCode_eq_zero (a : Field t) : (fieldEquiv t a).val = 0 ↔ a = 0 := by
  rw [← fieldCode_zero (t := t)]
  exact ⟨fun h => (fieldEquiv t).injective (Fin.ext h), fun h => congrArg (fun x : Field t => (fieldEquiv t x).val) h⟩

def tail : Stmt 36 11 := .seq (.assign 25 (.var 26))
  (.seq (.assign 0 (.const 1)) (.seq (.assign 1 (.eq 25 0))
    (.seq (.assign 1 (.sub 0 1)) (.assign 29 (.mul 29 1)))))

def body : Stmt 36 11 := .seq (binary .mul) tail

def Context (a : Field t) (st : State 36 11) : Prop :=
  st.regs 20 = t ∧ st.regs 24 = (fieldEquiv t a).val ∧
    st.lists 3 = encode (BinaryWordMaterialization.modulus t) ∧ st.lists 7 = []

set_option maxHeartbeats 1000000 in
-- Checking the field-multiplication frame unfolds a fixed register program.
theorem body_context (a : Field t) (st : State 36 11) (hc : Context a st) :
    Context a (body.run st).1 := by
  exact ⟨(run_regs_frame body 20 (by decide) st).trans hc.1,
    (run_regs_frame body 24 (by decide) st).trans hc.2.1,
    (run_lists_frame body 3 (by decide) st).trans hc.2.2.1,
    (run_lists_frame body 7 (by decide) st).trans hc.2.2.2⟩

theorem body_step (a : Field t) (n : ℕ) (st : State 36 11) (hc : Context a st)
    (hp : st.regs 25 = (fieldEquiv t (a ^ n)).val)
    (hg : st.regs 29 = truth (GoodPrefix a n)) :
    (body.run st).1.regs 25 = (fieldEquiv t (a ^ (n+1))).val ∧
    (body.run st).1.regs 29 = truth (GoodPrefix a (n+1)) := by
  have hm := binary_run_field .mul st a (a^n) hc.1 hc.2.1 hp hc.2.2.1 hc.2.2.2
  have hf := run_regs_frame (binary .mul) 29 (by decide) st
  simp only [Op.fieldEval, ← pow_succ'] at hm
  simp only [body, run_seq_fst, tail, run_assign_fst, Expr.eval, setReg_regs,
    Function.update, Fin.reduceEq, dite_true, dite_false, hm, hf, hg]
  refine ⟨trivial, ?_⟩
  simp only [truth, goodPrefix_succ, fieldCode_eq_one]
  split_ifs <;> simp_all

def prepare : Stmt 36 11 := .seq (.assign 24 (.var 33))
  (.seq (.assign 25 (.const 1)) (.seq (.assign 29 (.const 1))
    (.seq (.assign 0 (.const 2)) (.assign 30 (.sub 28 0)))))

def finish : Stmt 36 11 := .seq (.assign 0 (.const 0))
  (.seq (.assign 1 (.const 1)) (.seq (.assign 2 (.eq 24 0))
    (.seq (.assign 2 (.sub 1 2)) (.assign 27 (.mul 29 2)))))

def program : Stmt 36 11 := .seq prepare (.seq (.loop 30 body) finish)

theorem program_run (a : Field t) (st : State 36 11)
    (ht : st.regs 20 = t) (ha : st.regs 33 = (fieldEquiv t a).val)
    (hq : st.regs 28 = 2 ^ t)
    (hm : st.lists 3 = encode (BinaryWordMaterialization.modulus t)) (he : st.lists 7 = []) :
    (program.run st).1.regs 27 = truth
      (FiniteGeneratorSearch.Candidate (2 ^ t - 1) a) := by
  let q := 2 ^ t
  have hq2 : 2 ≤ q := by
    exact (by norm_num : 2 ≤ 2^1).trans (Nat.pow_le_pow_right (by decide) (NeZero.pos t))
  let s := (prepare.run st).1
  have hs : Context a s ∧ s.regs 25 = (fieldEquiv t (a^0)).val ∧
      s.regs 29 = truth (GoodPrefix a 0) := by
    rw [pow_zero, fieldCode_one]
    simp [s, prepare, Stmt.run, Expr.eval, Function.update, Context, ht, ha, hm, he, truth]
  have hs30 : s.regs 30 = q - 2 := by
    simp [s, prepare, Stmt.run, Expr.eval, Function.update, hq, q]
  have hit := iterate_inv body.run (Nat.size (q-2) + 1) (q-2)
    (fun n u => Context a u ∧ u.regs 25 = (fieldEquiv t (a^n)).val ∧
      u.regs 29 = truth (GoodPrefix a n))
    (fun n u _ hu => ⟨body_context a u hu.1, body_step a n u hu.1 hu.2.1 hu.2.2⟩) s hs
  have hc : FiniteGeneratorSearch.Candidate (q-1) a ↔ GoodPrefix a (q-2) ∧ a ≠ 0 := by
    have hn : q - 2 + 1 = q - 1 := by omega
    constructor
    · intro h
      refine ⟨?_, ?_⟩
      · intro k hk
        exact h.2 ⟨k.val, by have := k.isLt; omega⟩ hk
      · intro hz
        have hpow := h.1
        rw [hz, zero_pow (by omega : q-1 ≠ 0)] at hpow
        exact zero_ne_one hpow
    · rintro ⟨h, ha⟩
      refine ⟨?_, ?_⟩
      · simpa only [BinaryMaterializedField.card_element] using
          FiniteField.pow_card_sub_one_eq_one a ha
      · intro k hk
        exact h ⟨k.val, by have := k.isLt; omega⟩ hk
  simp only [program, run_seq_fst, run_loop_fst]
  change (finish.run (iterate body.run (Nat.size (s.regs 30)+1) (s.regs 30) s).1).1.regs 27 = _
  rw [hs30]
  simp only [finish, run_seq_fst, run_assign_fst, Expr.eval, setReg_regs,
    Function.update, Fin.reduceEq, dite_true, dite_false, hit.1.2.1, hit.2.2]
  change truth (GoodPrefix a (q-2)) * (1 - if (fieldEquiv t a).val = 0 then 1 else 0) =
    truth (FiniteGeneratorSearch.Candidate (q-1) a)
  simp only [truth, hc, fieldCode_eq_zero]
  split_ifs <;> simp_all

end PCP.Lang.BinaryGeneratorPredicate
