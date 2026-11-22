/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Algebraic.ThreeColorAlgebra
import PCP.Algebraic.GraphGridEmbedding
import PCP.Algebraic.GridInterpolation
import PCP.Algebraic.VanishingCertificate
import PCP.Algebraic.BinaryDifferenceConsistency

/-!
# Polynomial constraints for a graph on a Cartesian grid

The vertex and edge constraints of §7 are actual formal polynomials. The edge
indicator is interpolated from the input graph; it is not an additional proof
table. Their simultaneous vanishing characterizes ordinary three-colorability.
A coloring supplies bounded-degree polynomials and vanishing certificates.
These are mathematical existence statements, with no running-time assertion.
-/

namespace PCP.Algebraic.ThreeColorGrid

open MvPolynomial GridVanishing BinaryDifferenceConsistency ThreeColorAlgebra

variable {F σ : Type*} [Field F]

/-- The vertex constraint applied to the coloring polynomial. -/
noncomputable def validPolynomial (P : MvPolynomial σ F) : MvPolynomial σ F := P ^ 3 - 1

/-- The edge constraint, using the difference table's polynomial. -/
noncomputable def properPolynomial (E Q : MvPolynomial σ F) : MvPolynomial σ F :=
  E * validPolynomial Q

@[simp] theorem eval_validPolynomial (P : MvPolynomial σ F) (x : σ → F) :
    eval x (validPolynomial P) = eval x P ^ 3 - 1 := by simp [validPolynomial]

@[simp] theorem eval_properPolynomial (E Q : MvPolynomial σ F) (x : σ → F) :
    eval x (properPolynomial E Q) = eval x E * (eval x Q ^ 3 - 1) := by
  simp [properPolynomial]

theorem totalDegree_validPolynomial_le (P : MvPolynomial σ F) :
    (validPolynomial P).totalDegree ≤ 3 * P.totalDegree := by
  exact (totalDegree_sub_C_le (P ^ 3) 1).trans (totalDegree_pow P 3)

theorem totalDegree_properPolynomial_le (E Q : MvPolynomial σ F) :
    (properPolynomial E Q).totalDegree ≤ E.totalDegree + 3 * Q.totalDegree :=
  (totalDegree_mul _ _).trans (Nat.add_le_add_left (totalDegree_validPolynomial_le Q) _)

variable [Fintype σ] [DecidableEq σ] [DecidableEq F]

omit [Field F] [Fintype σ] [DecidableEq σ] [DecidableEq F] in
theorem coe_sum (H : Finset F) (a b : σ → H) :
    (fun i => (Sum.elim a b i).val) =
      Sum.elim (fun i => (a i : F)) (fun i => (b i : F)) := by
  funext i
  cases i <;> rfl

/-- The low-degree extension of the input graph's zero-one adjacency table. -/
noncomputable def edgeExtension (H : Finset F) (G : SimpleGraph (σ → H)) :
    MvPolynomial (σ ⊕ σ) F := by
  classical
  exact GridInterpolation.interpolate H (fun x =>
    if G.Adj (fun i => x (Sum.inl i)) (fun i => x (Sum.inr i)) then 1 else 0)

open scoped Classical in
@[simp] theorem eval_edgeExtension (H : Finset F) (G : SimpleGraph (σ → H))
    (a b : σ → H) :
    eval (Sum.elim (fun i => (a i : F)) (fun i => (b i : F))) (edgeExtension H G) =
      if G.Adj a b then 1 else 0 := by
  classical
  unfold edgeExtension
  rw [← coe_sum, GridInterpolation.eval_interpolate]
  rfl

theorem totalDegree_edgeExtension_le (H : Finset F) (G : SimpleGraph (σ → H)) :
    (edgeExtension H G).totalDegree ≤ 2 * ((H.card - 1) * Fintype.card σ) := by
  classical
  exact (GridInterpolation.totalDegree_interpolate_le H _).trans (by
    simp [Fintype.card_sum, mul_add, two_mul])

omit [Fintype σ] [DecidableEq σ] [DecidableEq F] in
/-- Grid vanishing may be tested using coordinatewise subtypes. -/
theorem vanishesOn_iff_grid (H : Finset F) (P : MvPolynomial σ F) :
    VanishesOn H P ↔ ∀ a : σ → H, eval (fun i => (a i : F)) P = 0 := by
  constructor
  · exact fun h a => h _ (fun i => (a i).property)
  · exact fun h x hx => h (fun i => ⟨x i, hx i⟩)

/-- The two grid equations are precisely the vertex and edge constraints. -/
theorem constraints_iff_satisfies (H : Finset F)
    (G : SimpleGraph (σ → H)) (P : MvPolynomial σ F) :
    (VanishesOn H (validPolynomial P) ∧
      VanishesOn H (properPolynomial (edgeExtension H G) (differencePolynomial P))) ↔
      Satisfies G (fun a => eval (fun i => (a i : F)) P) := by
  classical
  rw [vanishesOn_iff_grid, vanishesOn_iff_grid]
  simp only [eval_validPolynomial, Satisfies]
  constructor
  · rintro ⟨hv, he⟩
    refine ⟨hv, ?_⟩
    intro a b hab
    have h := he (Sum.elim a b)
    simpa [coe_sum, hab] using h
  · rintro ⟨hv, he⟩
    refine ⟨hv, ?_⟩
    intro x
    let a : σ → H := fun i => x (Sum.inl i)
    let b : σ → H := fun i => x (Sum.inr i)
    have hx : x = Sum.elim a b := by ext i; cases i <;> rfl
    rw [hx]
    by_cases hab : G.Adj a b
    · simpa [coe_sum, hab] using he a b hab
    · simp [coe_sum, hab]

/-- Every coloring has a low-degree extension satisfying both grid constraints. -/
theorem colorable_iff_exists_constraints [CharP F 2] {ω : F}
    (hω : IsPrimitiveRoot ω 3) (H : Finset F) (G : SimpleGraph (σ → H)) :
    G.Colorable 3 ↔ ∃ P : MvPolynomial σ F,
      P.totalDegree ≤ (H.card - 1) * Fintype.card σ ∧
      VanishesOn H (validPolynomial P) ∧
      VanishesOn H (properPolynomial (edgeExtension H G) (differencePolynomial P)) := by
  constructor
  · intro hG
    obtain ⟨f, hf⟩ := (colorable_iff_exists_satisfies hω G).mp hG
    refine ⟨GridInterpolation.interpolate H f,
      GridInterpolation.totalDegree_interpolate_le H f, ?_⟩
    apply (constraints_iff_satisfies H G _).mpr
    simpa only [GridInterpolation.eval_interpolate] using hf
  · rintro ⟨P, _, hP⟩
    exact (colorable_iff_exists_satisfies hω G).mpr
      ⟨_, (constraints_iff_satisfies H G P).mp hP⟩

/-- The §7 witness consists of a coloring extension and two bounded certificates. -/
theorem colorable_iff_exists_certificates [CharP F 2] {ω : F}
    (hω : IsPrimitiveRoot ω 3) (H : Finset F) (hH : H.Nonempty)
    (G : SimpleGraph (σ → H)) :
    G.Colorable 3 ↔ ∃ (P : MvPolynomial σ F)
      (MVal : MvPolynomial (σ ⊕ σ) F)
      (MProp : MvPolynomial ((σ ⊕ σ) ⊕ (σ ⊕ σ)) F),
      P.totalDegree ≤ (H.card - 1) * Fintype.card σ ∧
      MVal.totalDegree ≤ 3 * ((H.card - 1) * Fintype.card σ) ∧
      MProp.totalDegree ≤ 5 * ((H.card - 1) * Fintype.card σ) ∧
      IsCertificate H (validPolynomial P) MVal ∧
      IsCertificate H
        (properPolynomial (edgeExtension H G) (differencePolynomial P)) MProp := by
  constructor
  · intro hG
    obtain ⟨P, hd, hv, he⟩ := (colorable_iff_exists_constraints hω H G).mp hG
    obtain ⟨MVal, hdv, hcv⟩ := (vanishesOn_iff_exists_certificate H hH _).mp hv
    obtain ⟨MProp, hde, hce⟩ := (vanishesOn_iff_exists_certificate H hH _).mp he
    refine ⟨P, MVal, MProp, hd, ?_, ?_, hcv, hce⟩
    · exact hdv.trans ((totalDegree_validPolynomial_le P).trans (Nat.mul_le_mul_left 3 hd))
    · have h := totalDegree_properPolynomial_le (edgeExtension H G) (differencePolynomial P)
      have hE := totalDegree_edgeExtension_le H G
      have hQ := totalDegree_differencePolynomial_le P
      omega
  · rintro ⟨P, MVal, MProp, hd, _, _, hcv, hce⟩
    exact (colorable_iff_exists_constraints hω H G).mpr
      ⟨P, hd, hcv.vanishesOn, hce.vanishesOn⟩

/-- Soundness only needs the decoded difference identity and the two grid equations;
it imposes no interpolation-degree restriction on the decoded coloring. -/
theorem colorable_of_vanishing [CharP F 2] {ω : F} (hω : IsPrimitiveRoot ω 3)
    (H : Finset F) (G : SimpleGraph (σ → H)) (P : MvPolynomial σ F)
    (Q : MvPolynomial (σ ⊕ σ) F) (hQ : Q = differencePolynomial P)
    (hv : VanishesOn H (validPolynomial P))
    (he : VanishesOn H (properPolynomial (edgeExtension H G) Q)) : G.Colorable 3 := by
  subst Q
  exact (colorable_iff_exists_satisfies hω G).mpr
    ⟨_, (constraints_iff_satisfies H G P).mp ⟨hv, he⟩⟩

/-- The bounded algebraic witness characterizes any finite graph that fits in the grid.
The embedding and padded graph are supplied by the stated cardinality bound. -/
theorem colorable_iff_exists_certificates_on_grid [CharP F 2] {ω : F}
    (hω : IsPrimitiveRoot ω 3) {V : Type*} [Fintype V] (G : SimpleGraph V)
    (H : Finset F) (hH : H.Nonempty)
    (hsize : Fintype.card V ≤ H.card ^ Fintype.card σ) :
    let G' := GraphGridEmbedding.pad G (GraphGridEmbedding.gridEmbedding H hsize)
    G.Colorable 3 ↔ ∃ (P : MvPolynomial σ F)
      (MVal : MvPolynomial (σ ⊕ σ) F)
      (MProp : MvPolynomial ((σ ⊕ σ) ⊕ (σ ⊕ σ)) F),
      P.totalDegree ≤ (H.card - 1) * Fintype.card σ ∧
      MVal.totalDegree ≤ 3 * ((H.card - 1) * Fintype.card σ) ∧
      MProp.totalDegree ≤ 5 * ((H.card - 1) * Fintype.card σ) ∧
      IsCertificate H (validPolynomial P) MVal ∧
      IsCertificate H
        (properPolynomial (edgeExtension H G') (differencePolynomial P)) MProp := by
  exact (GraphGridEmbedding.threeColorable_pad_iff G
    (GraphGridEmbedding.gridEmbedding H hsize)).symm.trans
    (colorable_iff_exists_certificates hω H hH _)

end PCP.Algebraic.ThreeColorGrid
