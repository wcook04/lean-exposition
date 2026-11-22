/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Algebraic.ThreeColorVerifier
import PCP.Algebraic.ThreeColorDecodedSoundness
import PCP.Algebraic.ThreeColorSoundnessBudget

/-!
# Soundness of the actual seven-check three-color verifier

Small rejection of the conjunction bounds all seven actual branch rates. The
four low-degree branches construct the four nearby formal polynomials. Their
proximity bounds discharge every decoding premise of the constraint argument.
The resulting positive rejection gap depends only on the fixed inner degree.

The field, its binary coordinates, roots and interpolation nodes are explicit
parameters satisfying the stated bounds. Efficient parameter construction,
uniform-bit sampling and running time are separate obligations.
-/

namespace PCP.Algebraic.ThreeColorVerifier

open MvPolynomial BinaryPolynomialSpace Hadamard

variable {F : Type*} [Field F] [Algebra (ZMod 2) F] [Fintype F]
variable {n m c t : ℕ} [NeZero m] [CharP F 2]

/-- An actual outer test bounded by a larger rejection budget supplies the same
larger full and homogeneous proximity budgets. -/
private theorem exists_close_of_rejection_le {σ : Type*} [Fintype σ] [DecidableEq σ]
    {r : ℕ} (hq : PointLineConstants.fieldFactor * (c * m ^ c) ^ 3 ≤ Fintype.card F)
    (hr : 1 ≤ r) (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2))
    {nodes : Fin (c + 1) → F} (hnodes : GeneratorLowDegreeTest.IsGeneratorNodes nodes)
    {ζ : F} (hζ : StandardLocalCorrection.GoodNodes c ζ)
    (f : (σ → F) → Coefficients t r → ZMod 2)
    (L : EncodedLineLowDegreeTest.Auxiliary F σ m c t) {κ : ℚ}
    (hrej : EncodedLineLowDegreeTest.rejectionRate hr ρ nodes ζ f L ≤ κ)
    (hsmall : EncodedLineLowDegreeTest.lineErrorConstant c * κ ≤
      PointLineConstants.smallError) :
    ∃ P : MvPolynomial σ F, P.totalDegree ≤ c * m ^ c ∧
      HadamardDerivedOracle.fullDistance ρ f (fun x => eval x P) ≤
        EncodedLineLowDegreeTest.soundnessConstant c * κ ∧
      BinaryLagrangeConstraint.homogeneousDistance hr f
        (fun x => encode r (ρ (eval x P))) ≤
          EncodedLineLowDegreeTest.soundnessConstant c * κ := by
  have hsmall' := (mul_le_mul_of_nonneg_left hrej
    (EncodedLineLowDegreeTest.lineErrorConstant_nonneg c)).trans hsmall
  obtain ⟨P, hP, hf, hh⟩ := EncodedLineLowDegreeTest.exists_close hq hr ρ hnodes hζ f L hsmall'
  have hbudget := mul_le_mul_of_nonneg_left hrej
    (EncodedLineLowDegreeTest.soundnessConstant_nonneg c)
  exact ⟨P, hP, hf.trans hbudget, hh.trans hbudget⟩

open scoped Classical in
/-- Small actual rejection implies ordinary three-colorability, with every
polynomial and proximity bound constructed from the four low-degree checks. -/
theorem colorable_of_rejection_lt
    (hc : 1 ≤ c)
    (hq : PointLineConstants.fieldFactor * (c * m ^ c) ^ 3 ≤ Fintype.card F)
    (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2))
    {nodes : Fin (c + 1) → F} (hnodes : GeneratorLowDegreeTest.IsGeneratorNodes nodes)
    {ζ : F} (hζ : StandardLocalCorrection.GoodNodes c ζ) {ω : F} (hω : IsPrimitiveRoot ω 3)
    (H : Finset F) (hH : H.Nonempty)
    (hgrid : 100 * (c * m ^ c) * H.card ≤ Fintype.card F)
    (hdegree : (H.card - 1) * n ≤ c * m ^ c)
    (G : SimpleGraph (Fin n → H)) (π : Proof F n m c t)
    (hsmall : rejectionRate ρ nodes ζ H G π < ThreeColorSoundnessBudget.gap c) :
    G.Colorable 3 := by
  classical
  let κ := rejectionRate ρ nodes ζ H G π
  have hκ : 0 ≤ κ := rejectionRate_nonneg ρ nodes ζ H G π
  have hD : 0 < c * m ^ c := Nat.mul_pos hc (pow_pos (NeZero.pos m) c)
  have hbudget := ThreeColorSoundnessBudget.sufficient_budget c hκ hsmall hD
    (Finset.card_pos.mpr hH) hgrid
  have h0 := branchRejectionRate_le ρ nodes ζ H G π 0
  have h1 := branchRejectionRate_le ρ nodes ζ H G π 1
  have h2 := branchRejectionRate_le ρ nodes ζ H G π 2
  have h3 := branchRejectionRate_le ρ nodes ζ H G π 3
  have h4 := branchRejectionRate_le ρ nodes ζ H G π 4
  have h5 := branchRejectionRate_le ρ nodes ζ H G π 5
  have h6 := branchRejectionRate_le ρ nodes ζ H G π 6
  rw [branchRejectionRate_zero] at h0
  rw [branchRejectionRate_one] at h1
  rw [branchRejectionRate_two] at h2
  rw [branchRejectionRate_three] at h3
  rw [branchRejectionRate_four] at h4
  rw [branchRejectionRate_five] at h5
  rw [branchRejectionRate_six] at h6
  obtain ⟨P, hP, hpFull, hpHom⟩ := exists_close_of_rejection_le hq (by decide : 1 ≤ 3)
    ρ hnodes hζ π.color π.colorLines h0 hbudget.1
  obtain ⟨MVal, hMVal, _, hmVal⟩ := exists_close_of_rejection_le hq (le_refl 1)
    ρ hnodes hζ π.validCert π.validLines h1 hbudget.1
  obtain ⟨Q, hQ, hqFull, hqHom⟩ := exists_close_of_rejection_le hq (by decide : 1 ≤ 3)
    ρ hnodes hζ π.difference π.differenceLines h2 hbudget.1
  obtain ⟨MProp, hMProp, _, hmProp⟩ := exists_close_of_rejection_le hq (le_refl 1)
    ρ hnodes hζ π.properCert π.properLines h3 hbudget.1
  have hcD : c ≤ c * m ^ c := Nat.le_mul_of_pos_right c (pow_pos (NeZero.pos m) c)
  have hinner := (Nat.mul_le_mul_left 2 hcD).trans_lt
    (PointLineConstants.field_bound_linear (Fintype.one_lt_card (α := F)) hq)
  have hE : (ThreeColorGrid.edgeExtension H G).totalDegree ≤ 2 * (c * m ^ c) := by
    have he := ThreeColorGrid.totalDegree_edgeExtension_le H G
    simp only [Fintype.card_fin] at he
    exact he.trans (Nat.mul_le_mul_left 2 hdegree)
  apply ThreeColorDecodedSoundness.colorable_of_rejection_bounds hinner ρ hnodes hζ hω
    H hH G P Q MVal MProp hP hQ hMVal hMProp hE (le_refl _)
    π.color π.difference π.validCert π.properCert (validAuxiliary π) (properAuxiliary π)
    hpFull hqFull hpHom hqHom hmVal hmProp h6
  · exact h4
  · exact h5
  · exact hbudget.2.1
  · exact hbudget.2.2

open scoped Classical in
/-- Every received eight-table proof of a non-three-colorable grid graph is
rejected with a fixed positive probability, independent of graph size. -/
theorem rejectionRate_ge_of_not_colorable
    (hc : 1 ≤ c)
    (hq : PointLineConstants.fieldFactor * (c * m ^ c) ^ 3 ≤ Fintype.card F)
    (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2))
    {nodes : Fin (c + 1) → F} (hnodes : GeneratorLowDegreeTest.IsGeneratorNodes nodes)
    {ζ : F} (hζ : StandardLocalCorrection.GoodNodes c ζ) {ω : F} (hω : IsPrimitiveRoot ω 3)
    (H : Finset F) (hH : H.Nonempty)
    (hgrid : 100 * (c * m ^ c) * H.card ≤ Fintype.card F)
    (hdegree : (H.card - 1) * n ≤ c * m ^ c)
    (G : SimpleGraph (Fin n → H)) (hG : ¬ G.Colorable 3) (π : Proof F n m c t) :
    ThreeColorSoundnessBudget.gap c ≤ rejectionRate ρ nodes ζ H G π := by
  apply le_of_not_gt
  intro hsmall
  exact hG (colorable_of_rejection_lt hc hq ρ hnodes hζ hω H hH hgrid hdegree G π hsmall)

end PCP.Algebraic.ThreeColorVerifier
