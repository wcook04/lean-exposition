import PCP.Complexity.LangCost
import PCP.Complexity.LangSpace

/-!
# Splitting the first separator-delimited stored word

The first list is scanned until numeric separator two. The remaining suffix is
kept verbatim, including any further separators. The fixed loop is bounded by
the original list length and becomes inactive after the first separator.
-/

namespace PCP.Lang.SplitFirst

def body : Stmt 5 2 :=
  .ite 3 (.seq (.pop 0 1 2) (.seq (.assign 2 (.eq 1 4))
    (.ite 2 (.assign 3 (.const 0)) (.push 1 1)))) .skip

def setup : Stmt 5 2 :=
  .seq (.len 0 0) (.seq (.assign 1 (.const 0)) (.seq (.assign 2 (.const 0))
    (.seq (.assign 3 (.const 1)) (.assign 4 (.const 2)))))

def program : Stmt 5 2 := .seq setup (.seq (.loop 0 body) (.rev 1))

theorem body_inactive (st : State 5 2) (h : st.regs 3 = 0) :
    (body.run st).1 = st := by simp [body, Stmt.run, h]

theorem iterate_inactive (c n : ℕ) (st : State 5 2) (h : st.regs 3 = 0) :
    (iterate body.run c n st).1 = st := by
  induction n with
  | zero => rfl
  | succ n ih => rw [iterate_succ_fst, body_inactive st h, ih]

theorem body_value (v : ℕ) (vs acc : List ℕ) (st : State 5 2)
    (h0 : st.lists 0 = v :: vs) (h1 : st.lists 1 = acc)
    (ha : st.regs 3 = 1) (hs : st.regs 4 = 2) (hv : v ≠ 2) :
    (body.run st).1.lists 0 = vs ∧ (body.run st).1.lists 1 = v :: acc ∧
    (body.run st).1.regs 3 = 1 ∧ (body.run st).1.regs 4 = 2 := by
  simp [body, Stmt.run, Expr.eval, Function.update, h0, h1, ha, hs, hv]

theorem body_separator (vs acc : List ℕ) (st : State 5 2)
    (h0 : st.lists 0 = 2 :: vs) (h1 : st.lists 1 = acc)
    (ha : st.regs 3 = 1) (hs : st.regs 4 = 2) :
    (body.run st).1.lists 0 = vs ∧ (body.run st).1.lists 1 = acc ∧
    (body.run st).1.regs 3 = 0 ∧ (body.run st).1.regs 4 = 2 := by
  simp [body, Stmt.run, Expr.eval, Function.update, h0, h1, ha, hs]

/-- The suffix is unchanged throughout the surplus inactive iterations. -/
theorem iterate_split (xs ys acc : List ℕ) (hxs : ∀ v ∈ xs, v ≠ 2)
    (c extra : ℕ) (st : State 5 2) (h0 : st.lists 0 = xs ++ 2 :: ys)
    (h1 : st.lists 1 = acc) (ha : st.regs 3 = 1) (hs : st.regs 4 = 2) :
    let u := (iterate body.run c (xs.length + 1 + extra) st).1
    u.lists 0 = ys ∧ u.lists 1 = xs.reverse ++ acc ∧ u.regs 3 = 0 ∧ u.regs 4 = 2 := by
  induction xs generalizing acc st with
  | nil =>
    obtain ⟨hh0, hh1, hha, hhs⟩ := body_separator ys acc st h0 h1 ha hs
    simp only [List.length_nil, zero_add, show 1 + extra = extra + 1 by omega,
      iterate_succ_fst, iterate_inactive _ _ _ hha, List.reverse_nil, List.nil_append]
    exact ⟨hh0, hh1, hha, hhs⟩
  | cons v xs ih =>
    have hv := hxs v (by simp)
    have htail : ∀ v ∈ xs, v ≠ 2 := fun v hv => hxs v (by simp [hv])
    have hb := body_value v (xs ++ 2 :: ys) acc st h0 h1 ha hs hv
    have hout := ih (v :: acc) htail (body.run st).1 hb.1 hb.2.1 hb.2.2.1 hb.2.2.2
    simp only [List.length_cons, show xs.length + 1 + 1 + extra =
      (xs.length + 1 + extra) + 1 by omega, iterate_succ_fst]
    simpa [List.reverse_cons, List.append_assoc] using hout

theorem program_run (xs ys : List ℕ) (hxs : ∀ v ∈ xs, v ≠ 2)
    (st : State 5 2) (h0 : st.lists 0 = xs ++ 2 :: ys) (h1 : st.lists 1 = []) :
    (program.run st).1.lists 0 = ys ∧ (program.run st).1.lists 1 = xs := by
  let s := (setup.run st).1
  have hs0 : s.lists 0 = xs ++ 2 :: ys := by simpa [s, setup, Stmt.run] using h0
  have hs1 : s.lists 1 = [] := by simpa [s, setup, Stmt.run] using h1
  have hsa : s.regs 3 = 1 := by simp [s, setup, Stmt.run, Expr.eval, Function.update]
  have hss : s.regs 4 = 2 := by simp [s, setup, Stmt.run, Expr.eval, Function.update]
  have hlen : s.regs 0 = xs.length + 1 + ys.length := by
    simp [s, setup, Stmt.run, Expr.eval, Function.update, h0]
    omega
  have hout := iterate_split xs ys [] hxs (Nat.size (s.regs 0) + 1) ys.length s
    hs0 hs1 hsa hss
  simp only [program, run_seq_fst, run_loop_fst, run_rev_fst]
  change (setList (iterate body.run (Nat.size (s.regs 0) + 1) (s.regs 0) s).1 1
    ((iterate body.run (Nat.size (s.regs 0) + 1) (s.regs 0) s).1.lists 1).reverse).lists 0 = _ ∧ _
  rw [hlen] at hout ⊢
  simp only [setList_lists, Function.update_of_ne (by decide : (0 : Fin 2) ≠ 1),
    Function.update_self]
  exact ⟨hout.1, by simpa only [List.append_nil, List.reverse_reverse] using
    (congrArg List.reverse hout.2.1)⟩

end PCP.Lang.SplitFirst
