/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Algebraic.ThreeColorGrid
import PCP.Algebraic.GridCoordinateTransport
import PCP.Algebraic.DerivedZeroOnGridSoundness

/-!
# Three-colorability from the three concrete constraint tests

The difference check and both freshly randomized derived-grid checks constrain
four received polynomial tables. Explicit proximity to four actual polynomials
suffices for soundness; an outer low-degree test can supply these bounds. The
public edge polynomial is the input graph's actual grid interpolation. The edge
branch flattens its coordinate blocks before making its certificate queries.
-/

namespace PCP.Algebraic.ThreeColorDecodedSoundness

open MvPolynomial BinaryPolynomialSpace Hadamard GridVanishing ThreeColorGrid
open BinaryZeroOnGridCorrection

variable {F : Type*} [Field F] [Algebra (ZMod 2) F] [Fintype F] [DecidableEq F]
variable {n m c t D : ℕ}

/-- The actual vertex branch: a fresh two-query read of the membership cubic. -/
noncomputable def vertexRejectionRate (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2))
    (nodes : Fin (c + 1) → F) (ζ : F) (H : Finset F)
    (p : (Fin n → F) → Coefficients t 3 → ZMod 2)
    (mVal : CertificatePoint F n → Coefficients t 1 → ZMod 2)
    (aVal : Auxiliary F n m c t) : ℚ :=
  DerivedZeroOnGrid.rejectionRate ρ (fun _ => HadamardDerivedOracle.cubic)
    (fun _ => HadamardDerivedOracle.natDegree_cubic_le) nodes ζ H p mVal aVal

/-- The actual edge branch: flatten the difference table and use the public edge weight. -/
noncomputable def properRejectionRate (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2))
    (nodes : Fin (c + 1) → F) (ζ : F) (H : Finset F)
    (G : SimpleGraph (Fin n → H))
    (q : ((Fin n ⊕ Fin n) → F) → Coefficients t 3 → ZMod 2)
    (mProp : CertificatePoint F (n + n) → Coefficients t 1 → ZMod 2)
    (aProp : Auxiliary F (n + n) m c t) : ℚ :=
  DerivedZeroOnGrid.rejectionRate ρ
    (fun x => HadamardDerivedOracle.weightedCubic
      (eval (x ∘ finSumFinEquiv) (edgeExtension H G)))
    (fun x => HadamardDerivedOracle.natDegree_weightedCubic_le
      (eval (x ∘ finSumFinEquiv) (edgeExtension H G))) nodes ζ H
    (GridCoordinateTransport.rows finSumFinEquiv q) mProp aProp

variable [NeZero m] [CharP F 2]

/-- A low actual derived-grid rejection forces vanishing of its decoded constraint. -/
private theorem vanishesOn_of_rejection_bound
    (hq : 2 * c < Fintype.card F)
    (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2))
    (T : (Fin n → F) → Polynomial F) (hT : ∀ x, (T x).natDegree ≤ 3)
    {nodes : Fin (c + 1) → F} (hnodes : GeneratorLowDegreeTest.IsGeneratorNodes nodes)
    {ζ : F} (hζ : StandardLocalCorrection.GoodNodes c ζ) (H : Finset F) (hH : H.Nonempty)
    (f : (Fin n → F) → F) (P : MvPolynomial (Fin n) F)
    (hvalue : ∀ x, (T x).eval (f x) = eval x P)
    (M : MvPolynomial (Fin n ⊕ Fin n) F)
    (hP : P.totalDegree ≤ D) (hM : M.totalDegree ≤ D) (hdecode : c * m ^ c ≤ D)
    (p : (Fin n → F) → Coefficients t 3 → ZMod 2)
    (M' : CertificatePoint F n → Coefficients t 1 → ZMod 2) (A : Auxiliary F n m c t)
    {ε κ : ℚ} (hp : HadamardDerivedOracle.fullDistance ρ p f ≤ ε)
    (hm : BinaryLagrangeConstraint.homogeneousDistance (le_refl 1) M'
      (fun x => encode 1 (ρ (eval x M))) ≤ ε)
    (hreject : DerivedZeroOnGrid.rejectionRate ρ T hT nodes ζ H p M' A ≤ κ)
    (hsmall : (1 + 2 * BinaryLocalCorrection.soundnessConstant c) * (κ + 2 * ε) +
      2 * ε + (D : ℚ) / (Fintype.card F - 1 : ℕ) <
        (1 - ((D * H.card : ℕ) : ℚ) / Fintype.card F) / 2) :
    VanishesOn H P := by
  by_contra hnot
  have hlow := DerivedZeroOnGrid.rejectionRate_lower_bound hq ρ T hT hnodes hζ H hH
    f P hvalue M hP hM hdecode hnot p M' A hp hm
  have hcoef : 0 ≤ 1 + 2 * BinaryLocalCorrection.soundnessConstant c := by
    have h := BinaryLocalCorrection.soundnessConstant_nonneg c
    linarith
  have hup := mul_le_mul_of_nonneg_left (add_le_add hreject (le_refl (2 * ε))) hcoef
  linarith

/-- The three actual normalized branch rejection bounds imply ordinary graph
three-colorability. The full and homogeneous proximity premises are explicit;
no auxiliary-table proximity or unproved tester soundness premise is assumed. -/
theorem colorable_of_rejection_bounds
    (hq : 2 * c < Fintype.card F)
    (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2))
    {nodes : Fin (c + 1) → F} (hnodes : GeneratorLowDegreeTest.IsGeneratorNodes nodes)
    {ζ : F} (hζ : StandardLocalCorrection.GoodNodes c ζ) {ω : F} (hω : IsPrimitiveRoot ω 3)
    (H : Finset F) (hH : H.Nonempty) (G : SimpleGraph (Fin n → H))
    (P : MvPolynomial (Fin n) F) (Q : MvPolynomial (Fin n ⊕ Fin n) F)
    (MVal : MvPolynomial (Fin n ⊕ Fin n) F)
    (MProp : MvPolynomial (Fin (n + n) ⊕ Fin (n + n)) F)
    (hP : P.totalDegree ≤ D) (hQ : Q.totalDegree ≤ D)
    (hMVal : MVal.totalDegree ≤ D) (hMProp : MProp.totalDegree ≤ D)
    (hE : (edgeExtension H G).totalDegree ≤ 2 * D) (hdecode : c * m ^ c ≤ D)
    (p : (Fin n → F) → Coefficients t 3 → ZMod 2)
    (q : ((Fin n ⊕ Fin n) → F) → Coefficients t 3 → ZMod 2)
    (mVal : CertificatePoint F n → Coefficients t 1 → ZMod 2)
    (mProp : CertificatePoint F (n + n) → Coefficients t 1 → ZMod 2)
    (aVal : Auxiliary F n m c t) (aProp : Auxiliary F (n + n) m c t)
    {ε κ : ℚ}
    (hpFull : HadamardDerivedOracle.fullDistance ρ p (fun x => eval x P) ≤ ε)
    (hqFull : HadamardDerivedOracle.fullDistance ρ q (fun x => eval x Q) ≤ ε)
    (hpHom : BinaryLagrangeConstraint.homogeneousDistance (by decide : 1 ≤ 3) p
      (fun x => encode 3 (ρ (eval x P))) ≤ ε)
    (hqHom : BinaryLagrangeConstraint.homogeneousDistance (by decide : 1 ≤ 3) q
      (fun x => encode 3 (ρ (eval x Q))) ≤ ε)
    (hmVal : BinaryLagrangeConstraint.homogeneousDistance (le_refl 1) mVal
      (fun x => encode 1 (ρ (eval x MVal))) ≤ ε)
    (hmProp : BinaryLagrangeConstraint.homogeneousDistance (le_refl 1) mProp
      (fun x => encode 1 (ρ (eval x MProp))) ≤ ε)
    (hDiff : BinaryDifferenceConsistency.rejectionRate (by decide : 1 ≤ 3) p q ≤ κ)
    (hVal : vertexRejectionRate ρ nodes ζ H p mVal aVal ≤ κ)
    (hProp : properRejectionRate ρ nodes ζ H G q mProp aProp ≤ κ)
    (hsmallDiff : κ + 3 * ε < (1 - (D : ℚ) / Fintype.card F) / 2)
    (hsmallGrid : (1 + 2 * BinaryLocalCorrection.soundnessConstant c) * (κ + 2 * ε) +
      2 * ε + (5 * D : ℕ) / (Fintype.card F - 1 : ℕ) <
        (1 - ((5 * D * H.card : ℕ) : ℚ) / Fintype.card F) / 2) :
    G.Colorable 3 := by
  have hdiff := BinaryDifferenceConsistency.eq_differencePolynomial_of_close
    (by decide : 1 ≤ 3) ρ P Q hP hQ p q hDiff hpHom hqHom (by linarith)
  have hv : VanishesOn H (validPolynomial P) := by
    apply vanishesOn_of_rejection_bound (D := 5 * D) hq ρ
      (fun _ => HadamardDerivedOracle.cubic)
      (fun _ => HadamardDerivedOracle.natDegree_cubic_le) hnodes hζ H hH
      (fun x => eval x P) (validPolynomial P)
      (fun x => by simp only [HadamardDerivedOracle.eval_cubic, eval_validPolynomial])
      MVal _ (by omega) (by omega) p mVal aVal hpFull hmVal hVal hsmallGrid
    have hd := totalDegree_validPolynomial_le P
    omega
  have hpQ : HadamardDerivedOracle.fullDistance ρ
      (GridCoordinateTransport.rows finSumFinEquiv q)
      (fun x => eval (x ∘ finSumFinEquiv) Q) ≤ ε := by
    change relativeDistance
      (fun s : (Fin (n + n) → F) × Coefficients t 3 =>
        GridCoordinateTransport.rows finSumFinEquiv q s.1 s.2)
      (fun s => GridCoordinateTransport.rows finSumFinEquiv
        (fun x => encode 3 (ρ (eval x Q))) s.1 s.2) ≤ ε
    rw [GridCoordinateTransport.full_distance_rows]
    exact hqFull
  have heFlat : VanishesOn H
      (rename finSumFinEquiv (properPolynomial (edgeExtension H G) Q)) := by
    apply vanishesOn_of_rejection_bound (D := 5 * D) hq ρ
      (fun x => HadamardDerivedOracle.weightedCubic
        (eval (x ∘ finSumFinEquiv) (edgeExtension H G)))
      (fun x => HadamardDerivedOracle.natDegree_weightedCubic_le
        (eval (x ∘ finSumFinEquiv) (edgeExtension H G))) hnodes hζ H hH
      (fun x => eval (x ∘ finSumFinEquiv) Q)
      (rename finSumFinEquiv (properPolynomial (edgeExtension H G) Q))
      (fun x => by simp only [HadamardDerivedOracle.eval_weightedCubic,
        GridCoordinateTransport.eval_rename, eval_properPolynomial])
      MProp _ (by omega) (by omega)
      (GridCoordinateTransport.rows finSumFinEquiv q) mProp aProp
      hpQ hmProp hProp hsmallGrid
    rw [GridCoordinateTransport.totalDegree_rename]
    have hd := totalDegree_properPolynomial_le (edgeExtension H G) Q
    omega
  exact colorable_of_vanishing hω H G P Q hdiff hv
    ((GridCoordinateTransport.vanishesOn_rename_iff finSumFinEquiv H _).mp heFlat)

end PCP.Algebraic.ThreeColorDecodedSoundness
