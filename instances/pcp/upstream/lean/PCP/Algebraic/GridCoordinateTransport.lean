/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Algebraic.VanishingCertificate
import PCP.Algebraic.BinaryConstraintRobust

/-!
# Changing finite coordinate types in grid verifiers

A coordinate equivalence preserves polynomial evaluations, ordinary total degree,
grid vanishing, and received-oracle distances. In particular a sum of coordinate
blocks can be flattened before invoking a verifier indexed by `Fin n`.

Certificates need not be transported through their formal substitutions: construct
a new bounded certificate after flattening the constraint polynomial. The final
lemma gives this construction directly from vanishing of the original polynomial.
-/

namespace PCP.Algebraic.GridCoordinateTransport

open MvPolynomial GridVanishing BinaryPolynomialSpace Hadamard

variable {R σ τ : Type*}

/-- Pull a point on the renamed coordinates back to the original coordinates. -/
def pointEquiv (e : σ ≃ τ) (R : Type*) : (τ → R) ≃ (σ → R) :=
  Equiv.arrowCongr e.symm (Equiv.refl R)

@[simp] theorem pointEquiv_apply (e : σ ≃ τ) (x : τ → R) :
    pointEquiv e R x = x ∘ e := rfl

/-- Reindex the points of a received row oracle without changing any inner query label. -/
def rows {L B : Type*} (e : σ ≃ τ) (H : (σ → R) → L → B) : (τ → R) → L → B :=
  fun x => H (x ∘ e)

section Polynomial

variable [CommRing R]

/-- Evaluation of the renamed polynomial uses exactly the pulled-back point. -/
theorem eval_rename (e : σ ≃ τ) (P : MvPolynomial σ R) (x : τ → R) :
    eval x (rename e P) = eval (x ∘ e) P := MvPolynomial.eval_rename e x P

/-- Bijective renaming preserves ordinary total degree exactly. -/
theorem totalDegree_rename (e : σ ≃ τ) (P : MvPolynomial σ R) :
    (rename e P).totalDegree = P.totalDegree :=
  totalDegree_renameEquiv e P

/-- Grid vanishing is unchanged, including empty grids and empty coordinate types. -/
theorem vanishesOn_rename_iff (e : σ ≃ τ) (H : Finset R) (P : MvPolynomial σ R) :
    VanishesOn H (rename e P) ↔ VanishesOn H P := by
  constructor
  · intro h x hx
    have he := h (x ∘ e.symm) (fun i => hx (e.symm i))
    simpa only [eval_rename, Function.comp_def, Equiv.symm_apply_apply] using he
  · intro h x hx
    rw [eval_rename]
    exact h (x ∘ e) (fun i => hx (e i))

/-- Honest encoded polynomial rows are carried to the encoding of the renamed polynomial. -/
theorem rows_encode {t r : ℕ} (e : σ ≃ τ) (ρ : R → Fin t → ZMod 2)
    (P : MvPolynomial σ R) :
    rows e (fun x q => encode r (ρ (eval x P)) q) =
      fun x q => encode r (ρ (eval x (rename e P))) q := by
  funext x
  rw [eval_rename]
  rfl

end Polynomial

section Distances

variable [Fintype R] [Fintype σ] [DecidableEq σ] [Fintype τ] [DecidableEq τ]

/-- The complete point-and-label distribution is preserved, for any finite label type. -/
theorem distance_rows {L B : Type*} [Fintype L] [DecidableEq B]
    (e : σ ≃ τ) (H G : (σ → R) → L → B) :
    relativeDistance (fun p : (τ → R) × L => rows e H p.1 p.2)
      (fun p => rows e G p.1 p.2) =
      relativeDistance (fun p : (σ → R) × L => H p.1 p.2) (fun p => G p.1 p.2) := by
  exact relativeDistance_comp_equiv ((pointEquiv e R).prodCongr (Equiv.refl L))
    (fun p : (σ → R) × L => H p.1 p.2) (fun p => G p.1 p.2)

/-- In particular the full coefficient-query distance is invariant. -/
theorem full_distance_rows {t r : ℕ} (e : σ ≃ τ)
    (H G : (σ → R) → Coefficients t r → ZMod 2) :
    relativeDistance (fun p : (τ → R) × Coefficients t r => rows e H p.1 p.2)
      (fun p => rows e G p.1 p.2) =
      relativeDistance (fun p : (σ → R) × Coefficients t r => H p.1 p.2)
        (fun p => G p.1 p.2) := distance_rows e H G

/-- Homogeneous-label error is also unchanged; no factor or loss is introduced. -/
theorem homogeneous_distance_rows {t r : ℕ} (hr : 1 ≤ r) (e : σ ≃ τ)
    (H G : (σ → R) → Coefficients t r → ZMod 2) :
    BinaryLagrangeConstraint.homogeneousDistance hr (rows e H) (rows e G) =
      BinaryLagrangeConstraint.homogeneousDistance hr H G :=
  distance_rows e (fun x w => H x (homogeneousIndex hr w))
    (fun x w => G x (homogeneousIndex hr w))

end Distances

section Certificate

variable [CommRing R] [IsDomain R] [Finite τ]

/-- Construct the certificate after coordinate flattening, preserving the original degree bound. -/
theorem exists_certificate_after_rename (e : σ ≃ τ) (H : Finset R) (hH : H.Nonempty)
    (P : MvPolynomial σ R) (hP : VanishesOn H P) :
    ∃ M : MvPolynomial (τ ⊕ τ) R,
      M.totalDegree ≤ P.totalDegree ∧ IsCertificate H (rename e P) M := by
  classical
  let := Fintype.ofFinite τ
  obtain ⟨M, hdeg, hcert⟩ := (vanishesOn_iff_exists_certificate H hH (rename e P)).mp
    ((vanishesOn_rename_iff e H P).mpr hP)
  exact ⟨M, hdeg.trans_eq (totalDegree_rename e P), hcert⟩

end Certificate

end PCP.Algebraic.GridCoordinateTransport
