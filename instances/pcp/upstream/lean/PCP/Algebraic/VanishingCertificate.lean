/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Algebraic.GridVanishing
import PCP.Algebraic.PolynomialSubstitution

/-!
# A single polynomial certifying vanishing on a grid

Corollary 2.10. The two blocks of variables are indexed by `σ ⊕ σ`.
The certificate `M(X,Y) = ∑ i, Qᵢ(X) Yᵢ` satisfies the formal identities
`M(X,0) = 0` and `M(X,Z_H(X)) = P(X)`. Conversely, these identities force
`P` to vanish on the grid, even for certificates nonlinear in the second block.

The grid alphabet is nonempty for the certificate's degree bound `deg M ≤ deg P`.
This is essential: on an empty positive-dimensional grid the constant one vanishes
vacuously, but cannot have a degree-zero certificate with `M(X,0) = 0`.
-/

namespace PCP.Algebraic.GridVanishing

open Finset MvPolynomial

variable {R σ : Type*} [CommRing R]

/-- Substitute polynomials for the second block, keeping the first block formal. -/
noncomputable def substitute (Y : σ → MvPolynomial σ R) :
    MvPolynomial (σ ⊕ σ) R →+* MvPolynomial σ R :=
  eval₂Hom C (Sum.elim X Y)

@[simp] theorem substitute_rename (Y : σ → MvPolynomial σ R) (p : MvPolynomial σ R) :
    substitute Y (rename Sum.inl p) = p := by
  rw [substitute, eval₂Hom_rename]
  exact eval₂_eta p

@[simp] theorem substitute_X_inl (Y : σ → MvPolynomial σ R) (i : σ) :
    substitute Y (X (Sum.inl i)) = X i := by
  simp [substitute]

@[simp] theorem substitute_X_inr (Y : σ → MvPolynomial σ R) (i : σ) :
    substitute Y (X (Sum.inr i)) = Y i := by
  simp [substitute]

theorem eval_substitute (Y : σ → MvPolynomial σ R)
    (M : MvPolynomial (σ ⊕ σ) R) (x : σ → R) :
    eval x (substitute Y M) = eval (Sum.elim x (fun i => eval x (Y i))) M := by
  simp only [substitute, coe_eval₂Hom, eval_eval₂]
  congr 1
  · ext a
    simp
  · funext i
    cases i <;> simp

/-- The algebraic conditions in Corollary 2.10, separate from degree bounds. -/
def IsCertificate (H : Finset R) (p : MvPolynomial σ R)
    (M : MvPolynomial (σ ⊕ σ) R) : Prop :=
  substitute (fun _ => 0) M = 0 ∧ substitute (coordinate H) M = p

/-- Soundness uses the two formal identities and imposes no shape restriction on `M`. -/
theorem IsCertificate.vanishesOn {H : Finset R} {p : MvPolynomial σ R}
    {M : MvPolynomial (σ ⊕ σ) R} (hM : IsCertificate H p M) : VanishesOn H p := by
  intro x hx
  rw [← hM.2, eval_substitute]
  have hpoint : (fun i => eval x (coordinate H i)) = fun _ => 0 := by
    funext i
    exact eval_coordinate_eq_zero H i x (hx i)
  rw [hpoint]
  have h := congrArg (eval x) hM.1
  simpa [eval_substitute] using h

variable [Fintype σ]

/-- Package a family of coefficient polynomials into one polynomial in two blocks. -/
noncomputable def certificate (Q : σ → MvPolynomial σ R) : MvPolynomial (σ ⊕ σ) R :=
  ∑ i, rename Sum.inl (Q i) * X (Sum.inr i)

theorem substitute_certificate (Y Q : σ → MvPolynomial σ R) :
    substitute Y (certificate Q) = ∑ i, Q i * Y i := by
  simp [certificate]

@[simp] theorem substitute_zero_certificate (Q : σ → MvPolynomial σ R) :
    substitute (fun _ => 0) (certificate Q) = 0 := by
  simp [substitute_certificate]

theorem eval_certificate (Q : σ → MvPolynomial σ R) (x y : σ → R) :
    eval (Sum.elim x y) (certificate Q) = ∑ i, eval x (Q i) * y i := by
  simp [certificate, eval_rename, Function.comp_def]

theorem certificate_isCertificate (H : Finset R) (p : MvPolynomial σ R)
    (Q : σ → MvPolynomial σ R) (hp : p = ∑ i, Q i * coordinate H i) :
    IsCertificate H p (certificate Q) := by
  exact ⟨substitute_zero_certificate Q, (substitute_certificate _ _).trans hp.symm⟩

variable [IsDomain R]

/-- Packaging the coefficient polynomials preserves the original degree bound. -/
theorem totalDegree_certificate_le (H : Finset R) (hH : H.Nonempty)
    (Q : σ → MvPolynomial σ R) (d : ℕ)
    (hQ : ∀ i, Q i ≠ 0 → (Q i).totalDegree + H.card ≤ d) :
    (certificate Q).totalDegree ≤ d := by
  classical
  apply totalDegree_finsetSum_le
  intro i _
  by_cases hi : Q i = 0
  · simp [hi]
  · calc
      _ ≤ (rename Sum.inl (Q i)).totalDegree +
          (X (Sum.inr i) : MvPolynomial (σ ⊕ σ) R).totalDegree :=
        totalDegree_mul _ _
      _ ≤ (Q i).totalDegree + 1 :=
        add_le_add (totalDegree_rename_le _ _) (by simp)
      _ ≤ (Q i).totalDegree + H.card := Nat.add_le_add_left (card_pos.mpr hH) _
      _ ≤ d := hQ i hi

omit [Fintype σ] in
/-- Corollary 2.10, with the necessary nonempty-alphabet hypothesis. -/
theorem vanishesOn_iff_exists_certificate [Finite σ] (H : Finset R) (hH : H.Nonempty)
    (p : MvPolynomial σ R) :
    VanishesOn H p ↔ ∃ M : MvPolynomial (σ ⊕ σ) R,
      M.totalDegree ≤ p.totalDegree ∧ IsCertificate H p M := by
  let := Fintype.ofFinite σ
  constructor
  · intro hp
    obtain ⟨Q, hQ, hsum⟩ := exists_decomposition H p hp
    exact ⟨certificate Q, totalDegree_certificate_le H hH Q p.totalDegree hQ,
      certificate_isCertificate H p Q hsum⟩
  · rintro ⟨M, _, hM⟩
    exact hM.vanishesOn

omit [Fintype σ] in
/-- Setting the certificate variables to zero does not increase total degree. -/
theorem totalDegree_substitute_zero_le (M : MvPolynomial (σ ⊕ σ) R) :
    (substitute (fun _ => 0) M).totalDegree ≤ M.totalDegree := by
  apply totalDegree_substitution_le_of_affine
  intro i
  cases i <;> simp

omit [Fintype σ] in
/-- Substitution by the vanishing polynomials multiplies degree by at most `|H|`. -/
theorem totalDegree_substitute_coordinate_le [Finite σ] (H : Finset R) (hH : H.Nonempty)
    (M : MvPolynomial (σ ⊕ σ) R) :
    (substitute (coordinate H) M).totalDegree ≤ M.totalDegree * H.card := by
  apply totalDegree_substitution_le
  intro i
  cases i with
  | inl i => simpa using card_pos.mpr hH
  | inr i => exact (totalDegree_coordinate H i).le

end PCP.Algebraic.GridVanishing
