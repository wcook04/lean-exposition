/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Algebraic.BinaryConstraintRobust
import PCP.Algebraic.PolynomialDistance

/-!
# Binary consistency of a difference table

The three-query check in A §7, Claim 7.3, samples two independent field points
and one shared homogeneous Hadamard label. Its honest encoding rejection is
exactly half the field discrepancy. Each primary-oracle error has the original
uniform point-and-label marginal, and the difference-table error has the
uniform paired-point marginal. Polynomial distance then forces formal equality
under an explicit strict threshold. No low-degree tester soundness is assumed.
-/

namespace PCP.Algebraic.BinaryDifferenceConsistency

open Finset MvPolynomial BinaryPolynomialSpace Hadamard HadamardWeights

section Polynomial

variable {R σ : Type*} [CommRing R]

/-- The formal polynomial `P(a)-P(b)` on two copies of the variables. -/
noncomputable def differencePolynomial (P : MvPolynomial σ R) : MvPolynomial (σ ⊕ σ) R :=
  rename Sum.inl P - rename Sum.inr P

@[simp] theorem eval_differencePolynomial (P : MvPolynomial σ R) (a b : σ → R) :
    eval (Sum.elim a b) (differencePolynomial P) = eval a P - eval b P := by
  simp [differencePolynomial, eval_rename, Function.comp_def]

/-- Taking a difference on disjoint variable blocks does not increase ordinary total degree. -/
theorem totalDegree_differencePolynomial_le (P : MvPolynomial σ R) :
    (differencePolynomial P).totalDegree ≤ P.totalDegree :=
  (totalDegree_sub _ _).trans
    (max_le (totalDegree_rename_le Sum.inl P) (totalDegree_rename_le Sum.inr P))

end Polynomial

section Procedure

variable {F σ : Type*} {t r : ℕ}

/-- The binary difference check reads a common homogeneous label at three locations. -/
noncomputable def check (hr : 1 ≤ r)
    (f : (σ → F) → Coefficients t r → ZMod 2)
    (g : ((σ ⊕ σ) → F) → Coefficients t r → ZMod 2)
    (a b : σ → F) (w : Fin t → ZMod 2) : ZMod 2 :=
  g (Sum.elim a b) (homogeneousIndex hr w) -
    (f a (homogeneousIndex hr w) - f b (homogeneousIndex hr w))

/-- A primary-table location or a difference-table location. -/
abbrev Query (F σ : Type*) (t r : ℕ) :=
  ((σ → F) × Coefficients t r) ⊕ (((σ ⊕ σ) → F) × Coefficients t r)

/-- The three actual queries, with no independence requirement on the answers. -/
noncomputable def queries (hr : 1 ≤ r) (a b : σ → F) (w : Fin t → ZMod 2) :
    List (Query F σ t r) :=
  [Sum.inr (Sum.elim a b, homogeneousIndex hr w),
    Sum.inl (a, homogeneousIndex hr w), Sum.inl (b, homogeneousIndex hr w)]

@[simp] theorem queries_length (hr : 1 ≤ r) (a b : σ → F) (w : Fin t → ZMod 2) :
    (queries hr a b w).length = 3 := rfl

/-- Read one tagged query from the two tables. -/
def read (f : (σ → F) → Coefficients t r → ZMod 2)
    (g : ((σ ⊕ σ) → F) → Coefficients t r → ZMod 2) : Query F σ t r → ZMod 2
  | Sum.inl p => f p.1 p.2
  | Sum.inr p => g p.1 p.2

/-- Agreement on the query list determines the verdict. -/
theorem check_congr (hr : 1 ≤ r) (a b : σ → F) (w : Fin t → ZMod 2)
    (f f' : (σ → F) → Coefficients t r → ZMod 2)
    (g g' : ((σ ⊕ σ) → F) → Coefficients t r → ZMod 2)
    (h : ∀ q ∈ queries hr a b w, read f g q = read f' g' q) :
    check hr f g a b w = check hr f' g' a b w := by
  have hg := h (Sum.inr (Sum.elim a b, homogeneousIndex hr w)) (by simp [queries])
  have ha := h (Sum.inl (a, homogeneousIndex hr w)) (by simp [queries])
  have hb := h (Sum.inl (b, homogeneousIndex hr w)) (by simp [queries])
  simp only [read] at hg ha hb
  simp only [check, hg, ha, hb]

end Procedure

section Encoding

variable {F σ : Type*} [Field F] [Algebra (ZMod 2) F] {t r : ℕ}

/-- Honest binary answers observe the actual field difference discrepancy. -/
theorem check_encode (hr : 1 ≤ r) (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2))
    (f : (σ → F) → F) (g : ((σ ⊕ σ) → F) → F)
    (a b : σ → F) (w : Fin t → ZMod 2) :
    check hr (fun x => encode r (ρ (f x))) (fun x => encode r (ρ (g x))) a b w =
      linearEncode (ρ (g (Sum.elim a b) - (f a - f b))) w := by
  simp only [check, encode_homogeneousIndex, linearEncode_comm, map_sub]

/-- A correct difference function passes for every random seed. -/
theorem check_encode_eq_zero (hr : 1 ≤ r) (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2))
    (f : (σ → F) → F) (a b : σ → F) (w : Fin t → ZMod 2) :
    check hr (fun x => encode r (ρ (f x)))
      (fun x => encode r (ρ (f (x ∘ Sum.inl) - f (x ∘ Sum.inr)))) a b w = 0 := by
  rw [check_encode]
  simp [Function.comp_def, linearEncode_apply]

/-- In particular the formal difference polynomial has perfect completeness. -/
theorem check_differencePolynomial (hr : 1 ≤ r)
    (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2)) (P : MvPolynomial σ F)
    (a b : σ → F) (w : Fin t → ZMod 2) :
    check hr (fun x => encode r (ρ (eval x P)))
      (fun x => encode r (ρ (eval x (differencePolynomial P)))) a b w = 0 := by
  rw [check_encode, eval_differencePolynomial, sub_self]
  simp [linearEncode_apply]

end Encoding

section Finite

variable {F σ : Type*} [Field F] [Fintype F]
variable [Fintype σ] [DecidableEq σ] {t r D : ℕ}

/-- Actual normalized rejection on independent uniform points and a shared uniform label. -/
noncomputable def rejectionRate (hr : 1 ≤ r)
    (f : (σ → F) → Coefficients t r → ZMod 2)
    (g : ((σ ⊕ σ) → F) → Coefficients t r → ZMod 2) : ℚ :=
  relativeDistance
    (fun s : ((σ → F) × (σ → F)) × (Fin t → ZMod 2) =>
      g (Sum.elim s.1.1 s.1.2) (homogeneousIndex hr s.2))
    (fun s => f s.1.1 (homogeneousIndex hr s.2) - f s.1.2 (homogeneousIndex hr s.2))

omit [Field F] in
/-- The distance definition is exactly the probability of a nonzero check residual. -/
theorem rejectionRate_eq_check_distance (hr : 1 ≤ r)
    (f : (σ → F) → Coefficients t r → ZMod 2)
    (g : ((σ ⊕ σ) → F) → Coefficients t r → ZMod 2) :
    rejectionRate hr f g = relativeDistance
      (fun s : ((σ → F) × (σ → F)) × (Fin t → ZMod 2) =>
        check hr f g s.1.1 s.1.2 s.2) (fun _ => 0) := by
  simp only [rejectionRate, check, relativeDistance, hammingDist, sub_ne_zero]

private def firstLabelEquiv {V W : Type*} : ((V × V) × W) ≃ ((V × W) × V) where
  toFun s := ((s.1.1, s.2), s.1.2)
  invFun s := ((s.1.1, s.2), s.1.2)
  left_inv _ := rfl
  right_inv _ := rfl

private def secondLabelEquiv {V W : Type*} : ((V × V) × W) ≃ ((V × W) × V) where
  toFun s := ((s.1.2, s.2), s.1.1)
  invFun s := ((s.2, s.1.1), s.1.2)
  left_inv _ := rfl
  right_inv _ := rfl

/-- Each primary query has exactly the uniform point-and-label error marginal. -/
theorem primary_marginal (hr : 1 ≤ r)
    (f f' : (σ → F) → Coefficients t r → ZMod 2) :
    relativeDistance
      (fun s : ((σ → F) × (σ → F)) × (Fin t → ZMod 2) =>
        f s.1.1 (homogeneousIndex hr s.2))
      (fun s => f' s.1.1 (homogeneousIndex hr s.2)) =
      BinaryLagrangeConstraint.homogeneousDistance hr f f' ∧
    relativeDistance
      (fun s : ((σ → F) × (σ → F)) × (Fin t → ZMod 2) =>
        f s.1.2 (homogeneousIndex hr s.2))
      (fun s => f' s.1.2 (homogeneousIndex hr s.2)) =
      BinaryLagrangeConstraint.homogeneousDistance hr f f' := by
  constructor
  · calc
      _ = relativeDistance
          (fun s : ((σ → F) × (Fin t → ZMod 2)) × (σ → F) =>
            f s.1.1 (homogeneousIndex hr s.1.2))
          (fun s => f' s.1.1 (homogeneousIndex hr s.1.2)) :=
        relativeDistance_comp_equiv firstLabelEquiv _ _
      _ = _ := relativeDistance_comp_fst (κ := σ → F)
        (fun s : (σ → F) × (Fin t → ZMod 2) => f s.1 (homogeneousIndex hr s.2))
        (fun s => f' s.1 (homogeneousIndex hr s.2))
  · calc
      _ = relativeDistance
          (fun s : ((σ → F) × (Fin t → ZMod 2)) × (σ → F) =>
            f s.1.1 (homogeneousIndex hr s.1.2))
          (fun s => f' s.1.1 (homogeneousIndex hr s.1.2)) :=
        relativeDistance_comp_equiv secondLabelEquiv _ _
      _ = _ := relativeDistance_comp_fst (κ := σ → F)
        (fun s : (σ → F) × (Fin t → ZMod 2) => f s.1 (homogeneousIndex hr s.2))
        (fun s => f' s.1 (homogeneousIndex hr s.2))

omit [Field F] in
/-- The table query is uniform on both variable blocks and the shared label. -/
theorem table_marginal (hr : 1 ≤ r)
    (g g' : ((σ ⊕ σ) → F) → Coefficients t r → ZMod 2) :
    relativeDistance
      (fun s : ((σ → F) × (σ → F)) × (Fin t → ZMod 2) =>
        g (Sum.elim s.1.1 s.1.2) (homogeneousIndex hr s.2))
      (fun s => g' (Sum.elim s.1.1 s.1.2) (homogeneousIndex hr s.2)) =
      BinaryLagrangeConstraint.homogeneousDistance hr g g' :=
  relativeDistance_comp_equiv
    ((Equiv.sumArrowEquivProdArrow σ σ F).symm.prodCongr (Equiv.refl _))
    (fun s : ((σ ⊕ σ) → F) × (Fin t → ZMod 2) => g s.1 (homogeneousIndex hr s.2))
    (fun s => g' s.1 (homogeneousIndex hr s.2))

/-- Replacing the two received tables changes rejection by at most their actual query errors. -/
theorem rejectionRate_le_add_errors (hr : 1 ≤ r)
    (f f' : (σ → F) → Coefficients t r → ZMod 2)
    (g g' : ((σ ⊕ σ) → F) → Coefficients t r → ZMod 2) :
    rejectionRate hr f' g' ≤ rejectionRate hr f g +
      2 * BinaryLagrangeConstraint.homogeneousDistance hr f f' +
        BinaryLagrangeConstraint.homogeneousDistance hr g g' := by
  have ht := relativeDistance_triangle
    (fun s : ((σ → F) × (σ → F)) × (Fin t → ZMod 2) =>
      g' (Sum.elim s.1.1 s.1.2) (homogeneousIndex hr s.2))
    (fun s => g (Sum.elim s.1.1 s.1.2) (homogeneousIndex hr s.2))
    (fun s => f' s.1.1 (homogeneousIndex hr s.2) - f' s.1.2 (homogeneousIndex hr s.2))
  have hu := relativeDistance_triangle
    (fun s : ((σ → F) × (σ → F)) × (Fin t → ZMod 2) =>
      g (Sum.elim s.1.1 s.1.2) (homogeneousIndex hr s.2))
    (fun s => f s.1.1 (homogeneousIndex hr s.2) - f s.1.2 (homogeneousIndex hr s.2))
    (fun s => f' s.1.1 (homogeneousIndex hr s.2) - f' s.1.2 (homogeneousIndex hr s.2))
  have hs := relativeDistance_sub_le
    (fun s : ((σ → F) × (σ → F)) × (Fin t → ZMod 2) => f s.1.1 (homogeneousIndex hr s.2))
    (fun s => f s.1.2 (homogeneousIndex hr s.2))
    (fun s => f' s.1.1 (homogeneousIndex hr s.2))
    (fun s => f' s.1.2 (homogeneousIndex hr s.2))
  rw [table_marginal] at ht
  have hgcomm : BinaryLagrangeConstraint.homogeneousDistance hr g' g =
      BinaryLagrangeConstraint.homogeneousDistance hr g g' := relativeDistance_comm _ _
  rw [hgcomm] at ht
  rw [(primary_marginal hr f f').1, (primary_marginal hr f f').2] at hs
  dsimp only [rejectionRate]
  linarith

variable [DecidableEq F] [Algebra (ZMod 2) F]

/-- A shared homogeneous label detects exactly half of the field discrepancies. -/
theorem rejectionRate_encode (hr : 1 ≤ r) (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2))
    (f : (σ → F) → F) (g : ((σ ⊕ σ) → F) → F) :
    rejectionRate hr (fun x => encode r (ρ (f x))) (fun x => encode r (ρ (g x))) =
      (1 : ℚ) / 2 * relativeDistance
        (fun ab : (σ → F) × (σ → F) => g (Sum.elim ab.1 ab.2))
        (fun ab => f ab.1 - f ab.2) := by
  have h := relativeDistance_homogeneous_queries hr
    (fun ab : (σ → F) × (σ → F) => ρ (g (Sum.elim ab.1 ab.2)))
    (fun ab => ρ (f ab.1 - f ab.2))
  rw [relativeDistance_map ρ ρ.injective] at h
  simpa only [rejectionRate, encode_homogeneousIndex, linearEncode_comm, map_sub] using h

omit [Algebra (ZMod 2) F] in
/-- Polynomial distance for an arbitrary finite variable type, by bijective renaming. -/
theorem eval_distance_ge_finite (P Q : MvPolynomial σ F)
    (hP : P.totalDegree ≤ D) (hQ : Q.totalDegree ≤ D) (hne : P ≠ Q) :
    1 - (D : ℚ) / Fintype.card F ≤
      relativeDistance (fun x => eval x P) (fun x => eval x Q) := by
  let e := Fintype.equivFin σ
  have h := eval_distance_ge (rename e P) (rename e Q)
    ((totalDegree_rename_le e P).trans hP) ((totalDegree_rename_le e Q).trans hQ)
    (fun he => hne (rename_injective e e.injective he))
  have he := relativeDistance_comp_equiv (Equiv.arrowCongr e.symm (Equiv.refl F))
    (fun x => eval x P) (fun x => eval x Q)
  change relativeDistance (fun x : Fin (Fintype.card σ) → F => eval (x ∘ e) P)
    (fun x => eval (x ∘ e) Q) = _ at he
  simpa only [eval_rename, he] using h

/-- Honest binary rejection is half the distance between the evaluated formal polynomials. -/
theorem rejectionRate_encode_polynomial (hr : 1 ≤ r)
    (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2))
    (P : MvPolynomial σ F) (Q : MvPolynomial (σ ⊕ σ) F) :
    rejectionRate hr (fun x => encode r (ρ (eval x P)))
      (fun x => encode r (ρ (eval x Q))) =
      (1 : ℚ) / 2 * relativeDistance (fun x => eval x Q)
        (fun x => eval x (differencePolynomial P)) := by
  rw [rejectionRate_encode]
  have he := relativeDistance_comp_equiv (Equiv.sumArrowEquivProdArrow σ σ F).symm
    (fun x => eval x Q) (fun x => eval x (differencePolynomial P))
  simpa only [Equiv.sumArrowEquivProdArrow, Equiv.coe_fn_symm_mk,
    eval_differencePolynomial] using congrArg (fun z : ℚ => (1 : ℚ) / 2 * z) he

omit [DecidableEq F] in
/-- Different formal polynomials force the predicted half-distance rejection. -/
theorem rejectionRate_encode_ge_of_ne (hr : 1 ≤ r)
    (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2))
    (P : MvPolynomial σ F) (Q : MvPolynomial (σ ⊕ σ) F)
    (hP : P.totalDegree ≤ D) (hQ : Q.totalDegree ≤ D)
    (hne : Q ≠ differencePolynomial P) :
    (1 - (D : ℚ) / Fintype.card F) / 2 ≤
      rejectionRate hr (fun x => encode r (ρ (eval x P)))
        (fun x => encode r (ρ (eval x Q))) := by
  classical
  rw [rejectionRate_encode_polynomial]
  have h := eval_distance_ge_finite Q (differencePolynomial P) hQ
    ((totalDegree_differencePolynomial_le P).trans hP) hne
  linarith

omit [DecidableEq F] in
/-- Claim 7.3 with explicit errors and a strict polynomial-distance threshold.
The two proximity premises concern exactly the homogeneous queries used by the check. -/
theorem eq_differencePolynomial_of_close (hr : 1 ≤ r)
    (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2))
    (P : MvPolynomial σ F) (Q : MvPolynomial (σ ⊕ σ) F)
    (hP : P.totalDegree ≤ D) (hQ : Q.totalDegree ≤ D)
    (f : (σ → F) → Coefficients t r → ZMod 2)
    (g : ((σ ⊕ σ) → F) → Coefficients t r → ZMod 2) {η εf εg : ℚ}
    (hreject : rejectionRate hr f g ≤ η)
    (hf : BinaryLagrangeConstraint.homogeneousDistance hr f
      (fun x => encode r (ρ (eval x P))) ≤ εf)
    (hg : BinaryLagrangeConstraint.homogeneousDistance hr g
      (fun x => encode r (ρ (eval x Q))) ≤ εg)
    (hsmall : η + 2 * εf + εg < (1 - (D : ℚ) / Fintype.card F) / 2) :
    Q = differencePolynomial P := by
  classical
  by_contra hne
  have hlow := rejectionRate_encode_ge_of_ne hr ρ P Q hP hQ hne
  have hup := rejectionRate_le_add_errors hr f (fun x => encode r (ρ (eval x P)))
    g (fun x => encode r (ρ (eval x Q)))
  linarith

end Finite

end PCP.Algebraic.BinaryDifferenceConsistency
