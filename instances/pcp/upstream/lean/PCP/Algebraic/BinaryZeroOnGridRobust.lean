/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Algebraic.BinaryZeroOnGrid

/-!
# Robust binary zero-on-grid verification

Three answer errors bound the change in the two-check verifier. Correctors return
optional bits; every abstention rejects. The final transfer uses pointwise error
bounds over a shared uniform label and correction seed. Independence between the
three calls is unnecessary for the union bound, so independent call seeds can be
supplied as coordinates of the common seed.

The pointwise corrector guarantees are explicit hypotheses here. This module does
not assert that an arbitrary received oracle satisfies those guarantees.
-/

namespace PCP.Algebraic.BinaryZeroOnGrid

open Finset MvPolynomial BinaryPolynomialSpace Hadamard GridVanishing

section Generic

variable {S : Type*} [Fintype S]

/-- Altering three answers changes the residual pair only where an answer changes. -/
theorem checkBits_distance_le (p m₀ mZ p' m₀' mZ' : S → ZMod 2) :
    relativeDistance (fun s => checkBits (p s) (m₀ s) (mZ s))
      (fun s => checkBits (p' s) (m₀' s) (mZ' s)) ≤
        relativeDistance p p' + relativeDistance m₀ m₀' + relativeDistance mZ mZ' := by
  have hp := relativeDistance_zipWith_le Prod.mk m₀ m₀'
    (fun s => mZ s - p s) (fun s => mZ' s - p' s)
  have hs := relativeDistance_sub_le mZ p mZ' p'
  change relativeDistance (fun s => checkBits (p s) (m₀ s) (mZ s))
    (fun s => checkBits (p' s) (m₀' s) (mZ' s)) ≤ _ at hp
  linarith

/-- Optional answers are accepted only when all three are present and both checks pass. -/
def optionCheck (p m₀ mZ : Option (ZMod 2)) : Option (ZMod 2 × ZMod 2) :=
  match p, m₀, mZ with
  | some p, some m₀, some mZ => some (checkBits p m₀ mZ)
  | _, _, _ => none

@[simp] theorem optionCheck_some (p m₀ mZ : ZMod 2) :
    optionCheck (some p) (some m₀) (some mZ) = some (checkBits p m₀ mZ) := rfl

/-- The full error bound also counts abstentions; every abstention rejects the verifier. -/
theorem optionCheck_distance_le
    (p m₀ mZ p' m₀' mZ' : S → Option (ZMod 2)) :
    relativeDistance (fun s => optionCheck (p s) (m₀ s) (mZ s))
      (fun s => optionCheck (p' s) (m₀' s) (mZ' s)) ≤
        relativeDistance p p' + relativeDistance m₀ m₀' + relativeDistance mZ mZ' := by
  have hp := relativeDistance_zipWith_le Prod.mk p p' m₀ m₀'
  have hq := relativeDistance_zipWith_le
    (fun pm : Option (ZMod 2) × Option (ZMod 2) => fun z => optionCheck pm.1 pm.2 z)
    (fun s => (p s, m₀ s)) (fun s => (p' s, m₀' s)) mZ mZ'
  exact hq.trans (add_le_add hp le_rfl)

/-- A received optional-bit check inherits ideal rejection, up to its three answer errors. -/
theorem ideal_rejection_le_option_rejection_add_errors
    (p m₀ mZ : S → ZMod 2) (p' m₀' mZ' : S → Option (ZMod 2)) :
    relativeDistance (fun s => checkBits (p s) (m₀ s) (mZ s)) (fun _ => (0, 0)) ≤
      relativeDistance (fun s => optionCheck (p' s) (m₀' s) (mZ' s)) (fun _ => some (0, 0)) +
        relativeDistance p' (fun s => some (p s)) +
        relativeDistance m₀' (fun s => some (m₀ s)) +
        relativeDistance mZ' (fun s => some (mZ s)) := by
  have hb := optionCheck_distance_le p' m₀' mZ'
    (fun s => some (p s)) (fun s => some (m₀ s)) (fun s => some (mZ s))
  simp only [optionCheck_some] at hb
  have ht := relativeDistance_triangle
    (fun s => some (checkBits (p s) (m₀ s) (mZ s)))
    (fun s => optionCheck (p' s) (m₀' s) (mZ' s)) (fun _ => some (0, 0))
  rw [relativeDistance_map Option.some (Option.some_injective _)] at ht
  rw [relativeDistance_comm
    (fun s => some (checkBits (p s) (m₀ s) (mZ s)))] at ht
  linarith

end Generic

section Oracle

variable {F : Type*} [Field F] [Fintype F] {m t r : ℕ}

/-- Exact marginal-error transfer for arbitrary binary oracles, including the certificate graphs. -/
theorem rejectionRate_le_add_marginal_errors (hr : 1 ≤ r) (H : Finset F)
    (p p' : (Fin m → F) → Coefficients t r → ZMod 2)
    (M M' : ((Fin m ⊕ Fin m) → F) → Coefficients t r → ZMod 2) :
    rejectionRate hr H p M ≤ rejectionRate hr H p' M' +
      relativeDistance
        (fun s : (Fin m → F) × (Fin t → ZMod 2) => p s.1 (homogeneousIndex hr s.2))
        (fun s => p' s.1 (homogeneousIndex hr s.2)) +
      relativeDistance
        (fun s : (Fin m → F) × (Fin t → ZMod 2) => M (zeroPoint s.1) (homogeneousIndex hr s.2))
        (fun s => M' (zeroPoint s.1) (homogeneousIndex hr s.2)) +
      relativeDistance
        (fun s : (Fin m → F) × (Fin t → ZMod 2) =>
          M (recoveryPoint H s.1) (homogeneousIndex hr s.2))
        (fun s => M' (recoveryPoint H s.1) (homogeneousIndex hr s.2)) := by
  have hb := checkBits_distance_le
    (fun s : (Fin m → F) × (Fin t → ZMod 2) => p s.1 (homogeneousIndex hr s.2))
    (fun s => M (zeroPoint s.1) (homogeneousIndex hr s.2))
    (fun s => M (recoveryPoint H s.1) (homogeneousIndex hr s.2))
    (fun s => p' s.1 (homogeneousIndex hr s.2))
    (fun s => M' (zeroPoint s.1) (homogeneousIndex hr s.2))
    (fun s => M' (recoveryPoint H s.1) (homogeneousIndex hr s.2))
  have ht := relativeDistance_triangle
    (fun s : (Fin m → F) × (Fin t → ZMod 2) => check hr H p M s.1 s.2)
    (fun s => check hr H p' M' s.1 s.2) (fun _ => (0, 0))
  change relativeDistance
    (fun s : (Fin m → F) × (Fin t → ZMod 2) => check hr H p M s.1 s.2)
    (fun s => check hr H p' M' s.1 s.2) ≤ _ at hb
  unfold rejectionRate
  linarith

end Oracle

section Corrected

variable {F S : Type*} [Field F] [Fintype F] [Fintype S] {m t r d : ℕ}

/-- The actual corrected check; the three calls may share randomness. -/
noncomputable def correctedCheck (H : Finset F)
    (p : (Fin m → F) → (Fin t → ZMod 2) → S → Option (ZMod 2))
    (M : ((Fin m ⊕ Fin m) → F) → (Fin t → ZMod 2) → S → Option (ZMod 2))
    (x : Fin m → F) (w : Fin t → ZMod 2) (s : S) : Option (ZMod 2 × ZMod 2) :=
  optionCheck (p x w s) (M (zeroPoint x) w s) (M (recoveryPoint H x) w s)

/-- All abstentions reject; randomness comprises the point, label, and correction seed. -/
noncomputable def correctedRejectionRate (H : Finset F)
    (p : (Fin m → F) → (Fin t → ZMod 2) → S → Option (ZMod 2))
    (M : ((Fin m ⊕ Fin m) → F) → (Fin t → ZMod 2) → S → Option (ZMod 2)) : ℚ :=
  relativeDistance
    (fun s : (Fin m → F) × ((Fin t → ZMod 2) × S) =>
      correctedCheck H p M s.1 s.2.1 s.2.2)
    (fun _ => some (0, 0))

variable [Algebra (ZMod 2) F] [Nonempty S]

/-- Pointwise corrector guarantees control all three actual query marginals.
The hypotheses count both wrong answers and abstentions. -/
theorem rejectionRate_encode_le_corrected_add_errors (hr : 1 ≤ r)
    (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2)) (H : Finset F)
    (P : MvPolynomial (Fin m) F) (M : MvPolynomial (Fin m ⊕ Fin m) F)
    (p' : (Fin m → F) → (Fin t → ZMod 2) → S → Option (ZMod 2))
    (M' : ((Fin m ⊕ Fin m) → F) → (Fin t → ZMod 2) → S → Option (ZMod 2))
    {εP εM : ℚ}
    (hp : ∀ x, relativeDistance (fun ws : (Fin t → ZMod 2) × S => p' x ws.1 ws.2)
      (fun ws => some (linearEncode (ρ (eval x P)) ws.1)) ≤ εP)
    (hM : ∀ x, relativeDistance (fun ws : (Fin t → ZMod 2) × S => M' x ws.1 ws.2)
      (fun ws => some (linearEncode (ρ (eval x M)) ws.1)) ≤ εM) :
    rejectionRate hr H (fun x => encode r (ρ (eval x P)))
      (fun x => encode r (ρ (eval x M))) ≤ correctedRejectionRate H p' M' + εP + 2 * εM := by
  have hp' := relativeDistance_prod_le
    (fun s : (Fin m → F) × ((Fin t → ZMod 2) × S) => p' s.1 s.2.1 s.2.2)
    (fun s => some (linearEncode (ρ (eval s.1 P)) s.2.1)) hp
  have hm₀ := relativeDistance_prod_le
    (fun s : (Fin m → F) × ((Fin t → ZMod 2) × S) => M' (zeroPoint s.1) s.2.1 s.2.2)
    (fun s => some (linearEncode (ρ (eval (zeroPoint s.1) M)) s.2.1))
    (fun x => hM (zeroPoint x))
  have hmZ := relativeDistance_prod_le
    (fun s : (Fin m → F) × ((Fin t → ZMod 2) × S) =>
      M' (recoveryPoint H s.1) s.2.1 s.2.2)
    (fun s => some (linearEncode (ρ (eval (recoveryPoint H s.1) M)) s.2.1))
    (fun x => hM (recoveryPoint H x))
  have hi := ideal_rejection_le_option_rejection_add_errors
    (fun s : (Fin m → F) × ((Fin t → ZMod 2) × S) => linearEncode (ρ (eval s.1 P)) s.2.1)
    (fun s => linearEncode (ρ (eval (zeroPoint s.1) M)) s.2.1)
    (fun s => linearEncode (ρ (eval (recoveryPoint H s.1) M)) s.2.1)
    (fun s => p' s.1 s.2.1 s.2.2)
    (fun s => M' (zeroPoint s.1) s.2.1 s.2.2)
    (fun s => M' (recoveryPoint H s.1) s.2.1 s.2.2)
  have hideal : relativeDistance
      (fun s : (Fin m → F) × ((Fin t → ZMod 2) × S) =>
        checkBits (linearEncode (ρ (eval s.1 P)) s.2.1)
          (linearEncode (ρ (eval (zeroPoint s.1) M)) s.2.1)
          (linearEncode (ρ (eval (recoveryPoint H s.1) M)) s.2.1)) (fun _ => (0, 0)) =
      rejectionRate hr H (fun x => encode r (ρ (eval x P)))
        (fun x => encode r (ρ (eval x M))) := by
    let bits (x : Fin m → F) (w : Fin t → ZMod 2) :=
      checkBits (linearEncode (ρ (eval x P)) w)
        (linearEncode (ρ (eval (zeroPoint x) M)) w)
        (linearEncode (ρ (eval (recoveryPoint H x) M)) w)
    have he := relativeDistance_comp_equiv
      (Equiv.prodAssoc (Fin m → F) (Fin t → ZMod 2) S)
      (fun s : (Fin m → F) × ((Fin t → ZMod 2) × S) => bits s.1 s.2.1)
      (fun _ => (0, 0))
    simp only [Equiv.prodAssoc_apply] at he
    rw [relativeDistance_comp_fst (κ := S)
      (fun xw : (Fin m → F) × (Fin t → ZMod 2) => bits xw.1 xw.2)
      (fun _ => ((0, 0) : ZMod 2 × ZMod 2))] at he
    simpa only [bits, rejectionRate, check, encode_homogeneousIndex] using he.symm
  rw [hideal] at hi
  change _ ≤ correctedRejectionRate H p' M' + _ + _ + _ at hi
  linarith

/-- The ideal algebraic rejection bound survives optional-bit correction errors. -/
theorem correctedRejectionRate_ge_of_not_vanishesOn
    (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2)) (H : Finset F) (hH : H.Nonempty)
    (P : MvPolynomial (Fin m) F) (M : MvPolynomial (Fin m ⊕ Fin m) F)
    (hP : P.totalDegree ≤ d) (hM : M.totalDegree ≤ d) (hnot : ¬ VanishesOn H P)
    (p' : (Fin m → F) → (Fin t → ZMod 2) → S → Option (ZMod 2))
    (M' : ((Fin m ⊕ Fin m) → F) → (Fin t → ZMod 2) → S → Option (ZMod 2))
    {εP εM : ℚ}
    (hp : ∀ x, relativeDistance (fun ws : (Fin t → ZMod 2) × S => p' x ws.1 ws.2)
      (fun ws => some (linearEncode (ρ (eval x P)) ws.1)) ≤ εP)
    (hmc : ∀ x, relativeDistance (fun ws : (Fin t → ZMod 2) × S => M' x ws.1 ws.2)
      (fun ws => some (linearEncode (ρ (eval x M)) ws.1)) ≤ εM) :
    (1 - ((d * H.card : ℕ) : ℚ) / Fintype.card F) / 2 - εP - 2 * εM ≤
      correctedRejectionRate H p' M' := by
  have hi := rejectionRate_encode_ge_of_not_vanishesOn (r := 1) (by omega)
    ρ H hH P M hP hM hnot
  have hr := rejectionRate_encode_le_corrected_add_errors (r := 1) (by omega)
    ρ H P M p' M' hp hmc
  linarith

end Corrected
end PCP.Algebraic.BinaryZeroOnGrid
