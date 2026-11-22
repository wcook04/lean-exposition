import PCP.Complexity.LangStep
import PCP.Algebraic.ComputableBinaryLocalCorrection

/-!
# Actual optional-answer decision of weighted local correction

The three field reads are binary. Rejection of the inner test or disagreement
at the sampled point produces `none`; otherwise the recovered zero-point bit
is returned. Source registers survive the decision.
-/

namespace PCP.Lang.LocalCorrection

open PCP.Algebraic

def verdict : Stmt 6 0 := .seq (.assign 4 (.eq 1 2))
  (.ite 0 (.ite 4 (.seq (.assign 4 (.const 1)) (.assign 5 (.var 3)))
    (.seq (.assign 4 (.const 0)) (.assign 5 (.const 0))))
    (.seq (.assign 4 (.const 0)) (.assign 5 (.const 0))))

def present {A : Type*} : Option A → ℕ
  | none => 0
  | some _ => 1

def answer : Option (ZMod 2) → ℕ
  | none => 0
  | some x => x.val

def decision (ok : Bool) (observed checked recovered : ZMod 2) : Option (ZMod 2) :=
  if ok then if checked = observed then some recovered else none else none

theorem verdict_run (ok : Bool) (observed checked recovered : ZMod 2)
    (st : State 6 0) (h0 : st.regs 0 = ok.toNat) (h1 : st.regs 1 = observed.val)
    (h2 : st.regs 2 = checked.val) (h3 : st.regs 3 = recovered.val) :
    (verdict.run st).1.regs 4 = present (decision ok observed checked recovered) ∧
    (verdict.run st).1.regs 5 = answer (decision ok observed checked recovered) := by
  have heq : observed.val = checked.val ↔ checked = observed := by
    constructor
    · intro h
      exact (ZMod.val_injective 2 h).symm
    · intro h
      rw [h]
  cases ok <;> by_cases h : checked = observed <;>
    simp [verdict, Stmt.run, Expr.eval, Function.update, h0, h1, h2, h3,
      decision, present, answer, heq, h]

theorem verdict_frame (st : State 6 0) (i : Fin 6) (hi : i.val < 4) :
    (verdict.run st).1.regs i = st.regs i := by
  apply run_regs_frame
  simp only [verdict, Stmt.regWrites, List.mem_cons, List.mem_append,
    List.not_mem_nil, or_false, not_or]
  have h4 : i ≠ 4 := by intro h; subst i; norm_num at hi
  have h5 : i ≠ 5 := by intro h; subst i; norm_num at hi
  tauto

theorem verdict_cost (ok : Bool) (observed checked recovered : ZMod 2)
    (st : State 6 0) (h0 : st.regs 0 = ok.toNat) (h1 : st.regs 1 = observed.val)
    (h2 : st.regs 2 = checked.val) (h3 : st.regs 3 = recovered.val) :
    (verdict.run st).2 ≤ 30 := by
  have ho := ZMod.val_lt observed
  have hc := ZMod.val_lt checked
  have hr := ZMod.val_lt recovered
  have hobs : observed.val = 0 ∨ observed.val = 1 := by omega
  have hchk : checked.val = 0 ∨ checked.val = 1 := by omega
  have hrec : recovered.val = 0 ∨ recovered.val = 1 := by omega
  cases ok <;> rcases hobs with hobs | hobs <;>
    rcases hchk with hchk | hchk <;> rcases hrec with hrec | hrec <;>
    norm_num [verdict, Stmt.run, Expr.eval, Expr.cost, Expr.readSize,
      Function.update, Fin.reduceEq, h0, h1, h2, h3, hobs, hchk, hrec]
  all_goals norm_num [Fin.ext_iff]

/-- The decision is precisely the existing weighted corrector's optional answer. -/
theorem decision_run {F σ : Type*} [Field F] [DecidableEq F] [Algebra (ZMod 2) F]
    {m c t : ℕ} (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2)) (nodes : Fin (c + 1) → F)
    (ζ : F) (f : (σ → F) → BinaryPolynomialSpace.Coefficients t 1 → ZMod 2)
    (H : (σ → F) → BinaryLocalCorrection.RowOracle F m c t) (a b : σ → F) (z : Fˣ)
    (v : BinaryLocalCorrection.InnerPoint F m c) (w : Fin t → ZMod 2)
    (s : BinaryLocalCorrection.InnerSeed F m c t) :
    decision (ComputableBinaryLowDegreeTest.test (le_refl 1) ρ nodes (H b) s)
      (f (PolynomialLine.point a b (z : F))
        (BooleanCoefficientArithmetic.homogeneousIndex (le_refl 1) w))
      (ComputableBinaryStandardLocalCorrection.correct c ζ ρ (H b)
        (SetMultilinear.evaluationPoint m c (z : F)) v w)
      (ComputableBinaryStandardLocalCorrection.correct c ζ ρ (H b)
        (SetMultilinear.evaluationPoint m c 0) v w) =
      ComputableBinaryLocalCorrection.run ρ nodes ζ f H a b z v w s := rfl

end PCP.Lang.LocalCorrection
