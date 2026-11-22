import PCP.Complexity.DerivedGridSite
import PCP.Algebraic.ThreeColorOracle

/-! # The complete derived-grid verdict on the actual shared physical answer history -/

namespace PCP.Lang.DerivedGrid

open PCP.Algebraic BinaryFieldCode LocalCorrection BinaryPolynomialSpace

variable {t n m : ℕ} [NeZero t]

def historyProof (qs : List ℕ) (bs : List Bool) :
    ThreeColorVerifier.Proof (OuterBranch.Field t) n m 4 t :=
  ThreeColorVerifier.ofOracle (fun q => (QueryTree.answersOracle qs bs (queryCode q)).toNat)

def decision (k : Certificate) (nodes : Fin 5 → OuterBranch.Field t)
    (ζ : OuterBranch.Field t) (H : Finset (OuterBranch.Field t)) (weight : OuterBranch.Field t)
    (s : Sample k t n m) (qs : List ℕ) (bs : List Bool) : Bool :=
  accepts (DerivedCall.primaryBit (weighted k) weight s.2.1.1 s.2.2
    (primaryLocation (m := m) k s.1) qs bs)
    (DerivedCall.callValue k nodes ζ (firstPoint k s) s.2.1.1 (firstSeed k s) qs bs)
    (DerivedCall.callValue k nodes ζ (secondPoint k H s) s.2.1.1 (secondSeed k s) qs bs)

theorem boolEquiv_natCast (b : Bool) : BinarySeedPadding.boolEquiv b = (b.toNat : ZMod 2) := by
  cases b <;> rfl

/-- The color constraint uses precisely the actual cubic transform and physical proof tables. -/
theorem decision_valid (nodes : Fin 5 → OuterBranch.Field t) (ζ : OuterBranch.Field t)
    (H : Finset (OuterBranch.Field t)) (weight : OuterBranch.Field t)
    (s : Sample .valid t n m) (qs : List ℕ) (bs : List Bool) :
    decision .valid nodes ζ H weight s qs bs =
      decide (ComputableDerivedZeroOnGrid.check (BinaryMaterializedField.coordinates t)
        (fun _ => BooleanCoefficientRecovery.cubicQuery (BinaryMaterializedField.coordinates t))
        nodes ζ H (historyProof (n := n) (m := m) qs bs).color
        (historyProof (n := n) (m := m) qs bs).validCert
        (ThreeColorVerifier.validAuxiliary (historyProof (n := n) (m := m) qs bs))
        s = some (0,0)) := by
  unfold decision DerivedCall.primaryBit
  simp only [boolEquiv_natCast]
  rfl

/-- Only the weight at the sampled point is evaluated by the weighted derived branch. -/
theorem decision_proper (nodes : Fin 5 → OuterBranch.Field t) (ζ : OuterBranch.Field t)
    (H : Finset (OuterBranch.Field t)) (weights : (Fin (n + n) → OuterBranch.Field t) →
      OuterBranch.Field t) (s : Sample .proper t n m) (qs : List ℕ) (bs : List Bool) :
    decision .proper nodes ζ H (weights s.1) s qs bs =
      decide (ComputableDerivedZeroOnGrid.check (BinaryMaterializedField.coordinates t)
        (fun x => BooleanCoefficientRecovery.weightedCubicQuery
          (BinaryMaterializedField.coordinates t) (weights x)) nodes ζ H
        (ThreeColorVerifier.flatDifference (historyProof (n := n) (m := m) qs bs))
        (historyProof (n := n) (m := m) qs bs).properCert
        (ThreeColorVerifier.properAuxiliary (historyProof (n := n) (m := m) qs bs))
        s = some (0,0)) := by
  unfold decision DerivedCall.primaryBit
  simp only [boolEquiv_natCast]
  rfl

end PCP.Lang.DerivedGrid
