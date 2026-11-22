import PCP.Complexity.LocalCorrectionVerdict
import PCP.Complexity.LangCost
import PCP.Algebraic.ComputableDerivedZeroOnGrid

/-!
# Executable acceptance decision for both optional grid corrections

The primary answer is a bit, while each certificate call can abort. Acceptance
requires both calls to return, the first answer to vanish, and the second answer
to agree with the primary bit. Every source register is preserved.
-/

namespace PCP.Lang.DerivedGrid

open PCP.Algebraic LocalCorrection

def verdict : Stmt 7 0 := .seq (.assign 6 (.const 0))
  (.ite 1 (.ite 3
    (.seq (.assign 5 (.eq 2 6))
      (.ite 5 (.assign 5 (.eq 0 4)) (.assign 5 (.const 0))))
    (.assign 5 (.const 0))) (.assign 5 (.const 0)))

def accepts (p : ZMod 2) (a b : Option (ZMod 2)) : Bool :=
  decide (BinaryZeroOnGrid.optionCheck (some p) a b = some (0, 0))

theorem accepts_some (p a b : ZMod 2) :
    accepts p (some a) (some b) = decide (a = 0 ∧ b = p) := by
  simp [accepts, BinaryZeroOnGrid.optionCheck, BinaryZeroOnGrid.checkBits, sub_eq_zero]

theorem verdict_run (p : ZMod 2) (a b : Option (ZMod 2)) (st : State 7 0)
    (h0 : st.regs 0 = p.val) (h1 : st.regs 1 = present a)
    (h2 : st.regs 2 = answer a) (h3 : st.regs 3 = present b)
    (h4 : st.regs 4 = answer b) :
    (verdict.run st).1.regs 5 = (accepts p a b).toNat := by
  cases a with
  | none => simp [verdict, Stmt.run, Expr.eval, Function.update, h1, present,
      accepts, BinaryZeroOnGrid.optionCheck]
  | some a =>
    cases b with
    | none => simp [verdict, Stmt.run, Expr.eval, Function.update, h1, h3, present,
        accepts, BinaryZeroOnGrid.optionCheck]
    | some b =>
      have ha : a.val = 0 ↔ a = 0 := by
        exact ZMod.val_eq_zero a
      have hp : p.val = b.val ↔ b = p := by
        rw [(ZMod.val_injective 2).eq_iff, eq_comm]
      rw [accepts_some]
      by_cases haz : a = 0 <;> by_cases hbp : b = p <;>
        simp [verdict, Stmt.run, Expr.eval, Function.update, h0, h1, h2, h3, h4,
          present, answer, ha, hp, haz, hbp]

theorem verdict_frame (st : State 7 0) (i : Fin 7) (hi : i.val < 5) :
    (verdict.run st).1.regs i = st.regs i := by
  apply run_regs_frame
  have h5 : i ≠ 5 := by intro h; subst i; norm_num at hi
  have h6 : i ≠ 6 := by intro h; subst i; norm_num at hi
  simp [verdict, Stmt.regWrites, h5, h6]

theorem verdict_cost (p : ZMod 2) (a b : Option (ZMod 2)) (st : State 7 0)
    (h0 : st.regs 0 = p.val) (h1 : st.regs 1 = present a)
    (h2 : st.regs 2 = answer a) (h3 : st.regs 3 = present b)
    (h4 : st.regs 4 = answer b) : (verdict.run st).2 ≤ 1000000 := by
  have ha : present a ≤ 1 ∧ answer a ≤ 1 := by
    cases a with
    | none => simp [present, answer]
    | some a => have := ZMod.val_lt a; simp only [present, answer]; omega
  have hb : present b ≤ 1 ∧ answer b ≤ 1 := by
    cases b with
    | none => simp [present, answer]
    | some b => have := ZMod.val_lt b; simp only [present, answer]; omega
  have hp := ZMod.val_lt p
  have hsize : ∀ i ∈ verdict.uses, Nat.size (st.regs i) ≤ 1 := by
    intro i hi
    have hh : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by
      simp [verdict, Stmt.uses, Expr.uses, Stmt.mustW, List.mem_cons] at hi
      tauto
    rcases hh with rfl | rfl | rfl | rfl | rfl <;>
      apply (Nat.size_le).2 <;> simp only [h0, h1, h2, h3, h4] <;> omega
  have h := loopFree_cost_le verdict (by decide) st 1 hsize
    (by intro L; exact Fin.elim0 L)
  exact h.trans (by decide)

/-- The exact acceptance predicate of the named executable derived check. -/
theorem accepts_check {F : Type*} [Field F] [DecidableEq F] [Algebra (ZMod 2) F]
    {n m c t r : ℕ} (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2))
    (Q : (Fin n → F) → BinaryPolynomialSpace.Coefficients t 1 →
      BinaryPolynomialSpace.Coefficients t r)
    (nodes : Fin (c + 1) → F) (ζ : F) (H : Finset F)
    (p : (Fin n → F) → BinaryPolynomialSpace.Coefficients t r → ZMod 2)
    (M : BinaryZeroOnGridCorrection.CertificatePoint F n →
      BinaryPolynomialSpace.Coefficients t 1 → ZMod 2)
    (A : BinaryZeroOnGridCorrection.Auxiliary F n m c t)
    (s : DerivedZeroOnGrid.TestSample F n m c t r) :
    accepts (Hadamard.selfCorrect (p s.1)
        (Q s.1 (BooleanCoefficientArithmetic.homogeneousIndex (le_refl 1) s.2.1.1)) s.2.2)
      (ComputableDerivedZeroOnGrid.call ρ nodes ζ M
        (A (BinaryZeroOnGrid.zeroPoint s.1)) (BinaryZeroOnGrid.zeroPoint s.1)
        s.2.1.1 s.2.1.2.1)
      (ComputableDerivedZeroOnGrid.call ρ nodes ζ M
        (A (FieldQueryArithmetic.recoveryPoint H s.1))
        (FieldQueryArithmetic.recoveryPoint H s.1) s.2.1.1 s.2.1.2.2) =
      decide (ComputableDerivedZeroOnGrid.check ρ Q nodes ζ H p M A s = some (0, 0)) := rfl

end PCP.Lang.DerivedGrid
