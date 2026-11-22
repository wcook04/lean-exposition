import PCP.Complexity.DerivedGridSemantics

/-! # Physical query identities for the two actual cubic derived-grid branches -/

namespace PCP.Lang.DerivedGrid

open PCP.Algebraic BinaryFieldCode LocalCorrection

variable {t n m : ℕ} [NeZero t]

private theorem queries_congr {F : Type*} [Field F] [DecidableEq F] [Algebra (ZMod 2) F]
    {n m c t r : ℕ} (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2))
    (Q P : (Fin n → F) → BinaryPolynomialSpace.Coefficients t 1 →
      BinaryPolynomialSpace.Coefficients t r)
    (nodes : Fin (c + 1) → F) (ζ : F) (H : Finset F)
    (s : DerivedZeroOnGrid.TestSample F n m c t r) (h : Q s.1 = P s.1) :
    ComputableDerivedZeroOnGrid.queries ρ Q nodes ζ H s =
      ComputableDerivedZeroOnGrid.queries ρ P nodes ζ H s := by
  simp only [ComputableDerivedZeroOnGrid.queries, h]


theorem queries_valid (nodes : Fin 5 → OuterBranch.Field t) (ζ : OuterBranch.Field t)
    (H : Finset (OuterBranch.Field t)) (weight : OuterBranch.Field t)
    (s : Sample .valid t n m) :
    queries .valid nodes ζ H weight s =
      (ComputableDerivedZeroOnGrid.queries (BinaryMaterializedField.coordinates t)
        (fun _ => BooleanCoefficientRecovery.cubicQuery (BinaryMaterializedField.coordinates t))
        nodes ζ H s).map (fun q => queryCode (ThreeColorVerifier.validGridQuery q)) := by
  have hQ : transform .valid weight =
      (fun _ : Fin n → OuterBranch.Field t => BooleanCoefficientRecovery.cubicQuery
        (BinaryMaterializedField.coordinates t)) := rfl
  have h := queries_congr (BinaryMaterializedField.coordinates t)
    (transform .valid weight)
    (fun _ => BooleanCoefficientRecovery.cubicQuery (BinaryMaterializedField.coordinates t))
    nodes ζ H s (congrFun hQ s.1)
  exact congrArg (List.map (fun q => queryCode (ThreeColorVerifier.validGridQuery q))) h

theorem queries_proper (nodes : Fin 5 → OuterBranch.Field t) (ζ : OuterBranch.Field t)
    (H : Finset (OuterBranch.Field t))
    (weights : (Fin (n + n) → OuterBranch.Field t) → OuterBranch.Field t)
    (s : Sample .proper t n m) :
    queries .proper nodes ζ H (weights s.1) s =
      (ComputableDerivedZeroOnGrid.queries (BinaryMaterializedField.coordinates t)
        (fun x => BooleanCoefficientRecovery.weightedCubicQuery
          (BinaryMaterializedField.coordinates t) (weights x)) nodes ζ H s).map
            (fun q => queryCode (ThreeColorVerifier.properGridQuery q)) := by
  have h := queries_congr (BinaryMaterializedField.coordinates t)
    (transform .proper (weights s.1))
    (fun x => BooleanCoefficientRecovery.weightedCubicQuery
      (BinaryMaterializedField.coordinates t) (weights x)) nodes ζ H s rfl
  exact congrArg (List.map (fun q => queryCode (ThreeColorVerifier.properGridQuery q))) h

end PCP.Lang.DerivedGrid
