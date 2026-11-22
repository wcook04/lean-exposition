import PCP.Algebraic.GeneratorLowDegreeTest

/-!
# Weighted local correction (PCP-SOSA27, Fact 2.8 and Lemma 3.4)

The Lagrange weights recover the center from the `c+1` noncentral samples.
Completeness and correction only need distinct, nonzero nodes. The paper
supplies these using a full multiplicative generator and `q > 2c`.
-/

namespace PCP.Algebraic.StandardLocalCorrection

open Finset PolynomialLine GeneratorLowDegreeTest

variable {F σ : Type*} [Field F] {c : ℕ} {ζ : F}

def GoodNodes (c : ℕ) (ζ : F) : Prop :=
  Function.Injective (nodes c ζ) ∧ ζ ≠ 0

theorem goodNodes_of_generator [Fintype F] (hq : 2 * c < Fintype.card F)
    (hζ : IsPrimitiveRoot ζ (Fintype.card F - 1)) : GoodNodes c ζ :=
  ⟨nodes_injective hq hζ, generator_ne_zero hζ⟩

theorem GoodNodes.ne_zero (hζ : GoodNodes c ζ) (_ : c + 1 ≠ 0) : ζ ≠ 0 := hζ.2

theorem GoodNodes.weight_ne_zero (hζ : GoodNodes c ζ) (i : Fin (c + 1)) :
    weights c ζ i ≠ 0 := by
  classical
  rw [weights, LagrangeConstraint.weight_eq_prod]
  apply prod_ne_zero_iff.mpr
  intro j hj
  exact div_ne_zero (sub_ne_zero.mpr (pow_ne_zero _ hζ.2).symm)
    (sub_ne_zero.mpr (hζ.1.ne (mem_erase.mp hj).1.symm))

noncomputable def correct (c : ℕ) (ζ : F) (f : (σ → F) → F) (u v : σ → F) : F :=
  ∑ i : Fin (c + 1), weights c ζ i * f (point u v (nodes c ζ i))

def queries (c : ℕ) (ζ : F) (u v : σ → F) : List (σ → F) :=
  List.ofFn (fun i : Fin (c + 1) => point u v (nodes c ζ i))

@[simp] theorem queries_length (c : ℕ) (ζ : F) (u v : σ → F) :
    (queries c ζ u v).length = c + 1 := by simp [queries]

theorem correct_congr (c : ℕ) (ζ : F) (u v : σ → F) (f g : (σ → F) → F)
    (h : ∀ x ∈ queries c ζ u v, f x = g x) :
    correct c ζ f u v = correct c ζ g u v := by
  apply sum_congr rfl
  intro i _
  rw [h _ (List.mem_ofFn.mpr ⟨i, rfl⟩)]

/-- Fact 2.8, including the constant-polynomial identity. -/
theorem correct_eval (hζ : GoodNodes c ζ)
    (P : MvPolynomial σ F) (hP : P.totalDegree ≤ c) (u v : σ → F) :
    correct c ζ (fun x => MvPolynomial.eval x P) u v = MvPolynomial.eval u P := by
  have h := LagrangeConstraint.interpolant_eval hζ.1 P hP u v 0
  rw [LagrangeConstraint.eval_interpolant_eq_sum, point_zero] at h
  exact h

variable [Fintype F] [DecidableEq F] [Fintype σ] [DecidableEq σ]

/-- Lemma 3.4: the corrector errs with probability at most `(c+1)·δ(f,P)`, because every
individual noncentral sample is uniform. No hypothesis on `δ` or the field size is needed. -/
theorem failure_le (hζ : GoodNodes c ζ)
    (P : MvPolynomial σ F) (hP : P.totalDegree ≤ c) (f : (σ → F) → F) (u : σ → F) :
    relativeDistance (correct c ζ f u) (fun _ => MvPolynomial.eval u P) ≤
      (c + 1 : ℕ) * relativeDistance f (fun x => MvPolynomial.eval x P) := by
  have he : (fun _ : σ → F => MvPolynomial.eval u P) =
      correct c ζ (fun x => MvPolynomial.eval x P) u :=
    (funext (correct_eval hζ P hP u)).symm
  rw [he]
  apply (relativeDistance_sum_le
    (fun (i : Fin (c + 1)) v => weights c ζ i * f (point u v (nodes c ζ i)))
    (fun (i : Fin (c + 1)) v => weights c ζ i * MvPolynomial.eval
      (point u v (nodes c ζ i)) P)).trans
  calc
    _ ≤ ∑ _i : Fin (c + 1), relativeDistance f (fun x => MvPolynomial.eval x P) := by
      apply sum_le_sum
      intro i _
      have h := relativeDistance_le_of_disagreement
        (fun v : σ → F => weights c ζ i * f (point u v (nodes c ζ i)))
        (fun v => weights c ζ i * MvPolynomial.eval (point u v (nodes c ζ i)) P)
        (fun v => f (point u v (nodes c ζ i)))
        (fun v => MvPolynomial.eval (point u v (nodes c ζ i)) P)
        (fun v hne heq => hne (congrArg (weights c ζ i * ·) heq))
      exact h.trans_eq (relativeDistance_affineSampling u (nodes c ζ i)
        (pow_ne_zero _ hζ.2) f (fun x => MvPolynomial.eval x P))
    _ = _ := by simp

end PCP.Algebraic.StandardLocalCorrection
