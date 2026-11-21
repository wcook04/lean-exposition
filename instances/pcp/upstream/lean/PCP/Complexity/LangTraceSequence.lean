import PCP.Complexity.LangCost

/-! # Finite statement sequences preserving a context and accumulating exact ordered traces -/

namespace PCP.Lang.TraceSequence

variable {R Q : ℕ} {A : Type*}

def program (p : A → Stmt R Q) : List A → Stmt R Q
  | [] => .skip
  | a :: as => .seq (p a) (program p as)

theorem program_run (p : A → Stmt R Q) (Inv : State R Q → Prop)
    (acc : Fin R) (trace : Fin Q) (value : A → ℕ) (queries : A → List ℕ)
    (hstep : ∀ a st, Inv st →
      ((p a).run st).1.regs acc = st.regs acc * value a ∧
      ((p a).run st).1.lists trace = (queries a).reverse ++ st.lists trace ∧
      Inv ((p a).run st).1) (as : List A) (st : State R Q) (hi : Inv st) :
    ((program p as).run st).1.regs acc = st.regs acc * (as.map value).prod ∧
    ((program p as).run st).1.lists trace = (as.flatMap queries).reverse ++ st.lists trace ∧
    Inv ((program p as).run st).1 := by
  induction as generalizing st with
  | nil => simpa [program, Stmt.run] using hi
  | cons a as ih =>
      have hp := hstep a st hi
      have ht := ih (p a |>.run st).1 hp.2.2
      simp only [program, run_seq_fst]
      refine ⟨?_, ?_, ht.2.2⟩
      · rw [ht.1, hp.1]
        simp [Nat.mul_assoc]
      · rw [ht.2.1, hp.2.1]
        simp [List.flatMap_cons, List.reverse_append, List.append_assoc]

theorem program_cost (p : A → Stmt R Q) (Inv : State R Q → Prop) (B : ℕ)
    (hinv : ∀ a st, Inv st → Inv ((p a).run st).1)
    (hcost : ∀ a st, Inv st → ((p a).run st).2 ≤ B)
    (as : List A) (st : State R Q) (hi : Inv st) :
    ((program p as).run st).2 ≤ as.length*(B+1)+1 := by
  induction as generalizing st with
  | nil => simp [program, Stmt.run]
  | cons a as ih =>
      have hp := hcost a st hi
      have ht := ih (p a |>.run st).1 (hinv a st hi)
      simp only [program, run_seq_snd, List.length_cons]
      nlinarith

end PCP.Lang.TraceSequence
