import TorusEuler.Paper.S2.Statements

/-! # Glue: the angle `φ` of (2.4) in the library's Riccati notation

The library (`TorusEuler.ReferenceRiccati`) writes `x = ετ²/2 = tan φ` and
`s = (1 + x²)^{-1/2} = cos φ`. These identities translate the trigonometric
expressions of (2.4), (2.5) and (2.12) (`referenceAngle`, `referenceSystemMatrix`,
`ReferenceSlope`) into that notation. They are glue for the proofs of Lemmas 2.3 and 2.5
and carry no content of a numbered result. -/

open Set

namespace TorusEuler.Paper.Lib.S2a

open ReferenceRiccati

/-- `cos φ = s`, with `tan φ = ετ²/2` as in (2.4). -/
theorem cos_referenceAngle (ε τ : ℝ) :
    Real.cos (referenceAngle ε τ) = ReferenceRiccati.s ε τ := by
  rw [referenceAngle, Real.cos_arctan, ReferenceRiccati.s, ReferenceRiccati.x, one_div]

/-- `tan φ = x = ετ²/2`, (2.4). -/
theorem tan_referenceAngle' (ε τ : ℝ) :
    Real.tan (referenceAngle ε τ) = ReferenceRiccati.x ε τ := Real.tan_arctan _

/-- `sin φ = x s`. -/
theorem sin_referenceAngle (ε τ : ℝ) :
    Real.sin (referenceAngle ε τ) = ReferenceRiccati.x ε τ * ReferenceRiccati.s ε τ := by
  rw [referenceAngle, Real.sin_arctan, ReferenceRiccati.s, ReferenceRiccati.x, div_eq_mul_inv]

/-- `ετ sin 2φ` is the library's damping coefficient `2ετ x s²`. -/
theorem sin_two_referenceAngle (ε τ : ℝ) :
    ε * τ * Real.sin (2 * referenceAngle ε τ) = ReferenceRiccati.damping ε τ := by
  rw [Real.sin_two_mul, sin_referenceAngle, cos_referenceAngle, ReferenceRiccati.damping]
  ring

/-- `cos²φ (1 - ε tan φ)` is the library's driving coefficient `s²(1 - εx)`. -/
theorem driving_referenceAngle (ε τ : ℝ) :
    Real.cos (referenceAngle ε τ) ^ 2 * (1 - ε * Real.tan (referenceAngle ε τ)) =
      ReferenceRiccati.driving ε τ := by
  rw [cos_referenceAngle, tan_referenceAngle', ReferenceRiccati.driving]

/-- The Riccati problem (2.12) is the library's `Y' = rhs ε τ Y`, `Y(0) = 1`. -/
theorem referenceSlope_iff {ε : ℝ} {Y : ℝ → ℝ} : ReferenceSlope ε Y ↔
    (Y 0 = 1 ∧ ∀ τ ∈ Ici (0 : ℝ), HasDerivWithinAt Y (rhs ε τ (Y τ)) (Ici 0) τ) := by
  simp only [ReferenceSlope, driving_referenceAngle, sin_two_referenceAngle, rhs]

end TorusEuler.Paper.Lib.S2a
