/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Algebraic.ThreeColorVerifier

/-!
# Perfect completeness of the eight-table three-color proof

A proper coloring is extended to a polynomial on the ambient field. Its formal
difference and two grid-vanishing certificates supply all four primary proof
tables, and their honest encoded line restrictions supply the four shared
auxiliary tables. The proper certificate is constructed after flattening its
coordinate blocks. Every branch accepts on every finite seed.
-/

namespace PCP.Algebraic.ThreeColorVerifier

open MvPolynomial GridVanishing Hadamard BinaryDifferenceConsistency ThreeColorGrid

variable {F : Type*} [Field F] [Algebra (ZMod 2) F] {n m c t : ℕ}
variable [NeZero m]

/-- The complete honest proof, including the four auxiliary tables shared between tests. -/
noncomputable def honestProof (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2))
    (P : MvPolynomial (Fin n) F) (MVal : MvPolynomial (Fin n ⊕ Fin n) F)
    (MProp : MvPolynomial (Fin (n + n) ⊕ Fin (n + n)) F) : Proof F n m c t where
  color := fun x => encode 3 (ρ (eval x P))
  validCert := fun x => encode 1 (ρ (eval x MVal))
  difference := fun x => encode 3 (ρ (eval x (differencePolynomial P)))
  properCert := fun x => encode 1 (ρ (eval x MProp))
  colorLines := EncodedLineLowDegreeTest.honestTable ρ P
  validLines := EncodedLineLowDegreeTest.honestTable ρ MVal
  differenceLines := EncodedLineLowDegreeTest.honestTable ρ (differencePolynomial P)
  properLines := EncodedLineLowDegreeTest.honestTable ρ MProp

variable [CharP F 2]

open scoped Classical in
/-- Each branch accepts the same honest eight-table proof for every seed. -/
theorem branchTest_honestProof (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2))
    {nodes : Fin (c + 1) → F} (hnodes : Function.Injective nodes)
    {ζ : F} (hζ : StandardLocalCorrection.GoodNodes c ζ) (H : Finset F)
    (G : SimpleGraph (Fin n → H))
    (P : MvPolynomial (Fin n) F) (MVal : MvPolynomial (Fin n ⊕ Fin n) F)
    (MProp : MvPolynomial (Fin (n + n) ⊕ Fin (n + n)) F)
    (hP : P.totalDegree < m ^ c) (hMVal : MVal.totalDegree < m ^ c)
    (hMProp : MProp.totalDegree < m ^ c)
    (hvalid : IsCertificate H (validPolynomial P) MVal)
    (hproper : IsCertificate H
      (rename (flatten n) (properPolynomial (edgeExtension H G) (differencePolynomial P))) MProp)
    (i : Fin 7) (s : BranchSeed F n m c t i) :
    branchTest ρ nodes ζ H G (honestProof ρ P MVal MProp) i s = true := by
  classical
  fin_cases i
  · exact EncodedLineLowDegreeTest.test_eval (by omega) ρ hnodes hζ P hP s
  · exact EncodedLineLowDegreeTest.test_eval (le_refl 1) ρ hnodes hζ MVal hMVal s
  · exact EncodedLineLowDegreeTest.test_eval (by omega) ρ hnodes hζ
      (differencePolynomial P) ((totalDegree_differencePolynomial_le P).trans_lt hP) s
  · exact EncodedLineLowDegreeTest.test_eval (le_refl 1) ρ hnodes hζ MProp hMProp s
  · change decide (DerivedZeroOnGrid.check ρ _ _ nodes ζ H _ _ _ s = some (0, 0)) = true
    apply decide_eq_true
    exact DerivedZeroOnGrid.check_eval ρ (fun _ => HadamardDerivedOracle.cubic)
      (fun _ => HadamardDerivedOracle.natDegree_cubic_le) hnodes hζ
      (fun x => eval x P) (validPolynomial P)
      (fun x => by simp only [HadamardDerivedOracle.eval_cubic, eval_validPolynomial])
      MVal hMVal hvalid s
  · change decide (DerivedZeroOnGrid.check ρ _ _ nodes ζ H _ _ _ s = some (0, 0)) = true
    apply decide_eq_true
    exact DerivedZeroOnGrid.check_eval ρ
      (fun x => HadamardDerivedOracle.weightedCubic (edgeValue H G x))
      (fun x => HadamardDerivedOracle.natDegree_weightedCubic_le (edgeValue H G x))
      hnodes hζ (fun x => eval (x ∘ flatten n) (differencePolynomial P))
      (rename (flatten n) (properPolynomial (edgeExtension H G) (differencePolynomial P)))
      (fun x => by simp only [HadamardDerivedOracle.eval_weightedCubic, edgeValue,
        MvPolynomial.eval_rename, eval_properPolynomial]) MProp hMProp hproper s
  · change decide (BinaryDifferenceConsistency.check _ _ _ s.1.1 s.1.2 s.2 = 0) = true
    exact decide_eq_true (check_differencePolynomial (by omega) ρ P s.1.1 s.1.2 s.2)

open scoped Classical in
/-- Perfect completeness for every seed of the actual seven-branch conjunction. -/
theorem test_honestProof (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2))
    {nodes : Fin (c + 1) → F} (hnodes : Function.Injective nodes)
    {ζ : F} (hζ : StandardLocalCorrection.GoodNodes c ζ) (H : Finset F)
    (G : SimpleGraph (Fin n → H))
    (P : MvPolynomial (Fin n) F) (MVal : MvPolynomial (Fin n ⊕ Fin n) F)
    (MProp : MvPolynomial (Fin (n + n) ⊕ Fin (n + n)) F)
    (hP : P.totalDegree < m ^ c) (hMVal : MVal.totalDegree < m ^ c)
    (hMProp : MProp.totalDegree < m ^ c)
    (hvalid : IsCertificate H (validPolynomial P) MVal)
    (hproper : IsCertificate H
      (rename (flatten n) (properPolynomial (edgeExtension H G) (differencePolynomial P))) MProp)
    (s : Sample F n m c t) :
    test ρ nodes ζ H G (honestProof ρ P MVal MProp) s = true := by
  apply (FiniteConjunction.test_eq_true _ _).mpr
  intro i
  exact branchTest_honestProof ρ hnodes hζ H G P MVal MProp hP hMVal hMProp hvalid hproper i (s i)

/-- A colorable grid graph supplies an actual eight-table proof accepted on every seed. -/
theorem exists_proof_test_eq_true (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2))
    {nodes : Fin (c + 1) → F} (hnodes : Function.Injective nodes)
    {ζ : F} (hζ : StandardLocalCorrection.GoodNodes c ζ) {ω : F} (hω : IsPrimitiveRoot ω 3)
    (H : Finset F) (hH : H.Nonempty) (G : SimpleGraph (Fin n → H)) (hG : G.Colorable 3)
    (hdegree : 5 * ((H.card - 1) * n) < m ^ c) :
    ∃ π : Proof F n m c t, ∀ s, test ρ nodes ζ H G π s = true := by
  classical
  obtain ⟨P, hd, hv, he⟩ := (colorable_iff_exists_constraints hω H G).mp hG
  have hP : P.totalDegree ≤ (H.card - 1) * n := by simpa only [Fintype.card_fin] using hd
  obtain ⟨MVal, hdv, hcv⟩ := (vanishesOn_iff_exists_certificate H hH _).mp hv
  obtain ⟨MProp, hdp, hcp⟩ := GridCoordinateTransport.exists_certificate_after_rename
    (flatten n) H hH (properPolynomial (edgeExtension H G) (differencePolynomial P)) he
  have hMVal : MVal.totalDegree ≤ 3 * ((H.card - 1) * n) :=
    hdv.trans ((totalDegree_validPolynomial_le P).trans (Nat.mul_le_mul_left 3 hP))
  have hMProp : MProp.totalDegree ≤ 5 * ((H.card - 1) * n) := by
    have h := totalDegree_properPolynomial_le (edgeExtension H G) (differencePolynomial P)
    have hE : (edgeExtension H G).totalDegree ≤ 2 * ((H.card - 1) * n) := by
      simpa only [Fintype.card_fin] using totalDegree_edgeExtension_le H G
    have hQ := (totalDegree_differencePolynomial_le P).trans hP
    omega
  refine ⟨honestProof ρ P MVal MProp, ?_⟩
  intro s
  exact test_honestProof ρ hnodes hζ H G P MVal MProp (by omega) (by omega)
    (hMProp.trans_lt hdegree) hcv hcp s

variable [Fintype F]

open scoped Classical in
/-- A colorable graph has zero rejection under the actual complete finite seed. -/
theorem exists_proof_rejectionRate_eq_zero (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2))
    {nodes : Fin (c + 1) → F} (hnodes : Function.Injective nodes)
    {ζ : F} (hζ : StandardLocalCorrection.GoodNodes c ζ) {ω : F} (hω : IsPrimitiveRoot ω 3)
    (H : Finset F) (hH : H.Nonempty) (G : SimpleGraph (Fin n → H)) (hG : G.Colorable 3)
    (hdegree : 5 * ((H.card - 1) * n) < m ^ c) :
    ∃ π : Proof F n m c t, rejectionRate ρ nodes ζ H G π = 0 := by
  classical
  obtain ⟨π, hπ⟩ := exists_proof_test_eq_true ρ hnodes hζ hω H hH G hG hdegree
  refine ⟨π, ?_⟩
  apply relativeDistance_eq_zero_iff.mpr
  funext s
  exact hπ s

end PCP.Algebraic.ThreeColorVerifier
