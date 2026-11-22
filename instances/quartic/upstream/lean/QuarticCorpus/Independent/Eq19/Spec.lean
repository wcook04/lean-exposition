module

public import QuarticQuery.LowerBound.Planted.Coupling

/-!
# An independently authored mathematical target for equation (19)

Native validation: `research/adjudication/round3_formal.json`.

This file was written from the preprint's experiment and full display, not by
extracting a theorem type from Solution or copying Statement.lean. It does use
the project's coordinate type, tree, path and depth interfaces: those imported
interfaces are a declared semantic boundary, tested separately by examples.
It imports neither Paper.ClassicalPlanted nor any erased-zero inequality proof.

The scalar expectations below explicitly specify the product law. They do not
use the implementation's dummy, foundZero, coupledAvg, discoveredZeros or
expectedZeros definitions. A separate Bridge proves agreement with those.
-/

@[expose] public section

open scoped BigOperators

open Finset

namespace QuarticQuery.Independent.Eq19

variable {κ : Type} {ℓ r S : ℕ}

/-- One zero per column, address data unchanged, all cell bits blank. -/
def referenceInput (J : Column ℓ → Column ℓ)
    (A : Column ℓ → Fin r → BitInput κ) : BitInput (BitLoc ℓ r S κ)
  | .inl (i, j) => if j = J i then false else true
  | .inr (.inl (i, h, q)) => A i h q
  | .inr (.inr _) => false

/-- Membership is a discovery event, so repeated visits do not add discoveries. -/
def zeroWasQueried (T : QueryTree (BitLoc ℓ r S κ))
    (A : Column ℓ → Fin r → BitInput κ)
    (J : Column ℓ → Column ℓ) (i : Column ℓ) : Prop :=
  Sum.inl (i, J i) ∈ T.path (referenceInput J A)

noncomputable def hit (T : QueryTree (BitLoc ℓ r S κ))
    (A : Column ℓ → Fin r → BitInput κ)
    (J : Column ℓ → Column ℓ) (i : Column ℓ) : ℝ := by
  classical
  exact if zeroWasQueried T A J i then 1 else 0

noncomputable def zerosSeen (T : QueryTree (BitLoc ℓ r S κ))
    (A : Column ℓ → Fin r → BitInput κ)
    (J : Column ℓ → Column ℓ) : ℕ := by
  classical
  exact (univ.filter fun i => zeroWasQueried T A J i).card

noncomputable def dataWeight (μ : BitInput κ → ℝ)
    (A : Column ℓ → Fin r → BitInput κ) : ℝ :=
  ∏ i : Column ℓ, ∏ h : Fin r, μ (A i h)

noncomputable def zeroWeight (_J : Column ℓ → Column ℓ) : ℝ :=
  ∏ _i : Column ℓ, (1 / ((2 ^ ℓ : ℕ) : ℝ))

variable [Fintype κ] [DecidableEq κ]

/-- `A`, `J`, and the erased column `I` are independent; every `I` has mass `1/m`. -/
noncomputable def hitProbability (μ : BitInput κ → ℝ)
    (T : QueryTree (BitLoc ℓ r S κ)) : ℝ :=
  ∑ A : Column ℓ → Fin r → BitInput κ, dataWeight μ A *
    (∑ J : Column ℓ → Column ℓ, zeroWeight J *
      (∑ I : Column ℓ, (1 / ((2 ^ ℓ : ℕ) : ℝ)) * hit T A J I))

/-- `Z` counts distinct discovered columns in the complete dummy run. -/
noncomputable def expectedCount (μ : BitInput κ → ℝ)
    (T : QueryTree (BitLoc ℓ r S κ)) : ℝ :=
  ∑ A : Column ℓ → Fin r → BitInput κ, dataWeight μ A *
    (∑ J : Column ℓ → Column ℓ, zeroWeight J * (zerosSeen T A J : ℝ))

end QuarticQuery.Independent.Eq19
