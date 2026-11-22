/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Algebraic.BinaryZeroOnGridRobust
import PCP.Algebraic.BinaryLocalCorrection

/-!
# The zero-on-grid test with two actual local-correction calls

At a uniform outer point and homogeneous label, read the primary oracle once.
Correct the certificate at `(x,0)` and `(x,Z_H(x))`, using independent remaining
seeds and the shared label. Reject every abstention and test the two residuals.
The procedure uses at most `6c+19` bit queries and has perfect completeness.
-/

namespace PCP.Algebraic.BinaryZeroOnGridCorrection

open Finset MvPolynomial BinaryPolynomialSpace Hadamard GridVanishing BinaryZeroOnGrid
open BinaryLocalCorrection

variable {F : Type*} [Field F] [Algebra (ZMod 2) F] {n m c t : ℕ}

/-- The internal randomness of a correction call, with the requested label separated out. -/
abbrev CallSeed (F σ : Type*) [Monoid F] (m c t : ℕ) :=
  (σ → F) × (Fˣ × (InnerPoint F m c × InnerSeed F m c t))

/-- Restoring the requested label gives exactly the corrector's actual full sample. -/
def callSampleEquiv {σ : Type*} :
    ((Fin t → ZMod 2) × CallSeed F σ m c t) ≃ Sample F σ m c t where
  toFun s := (s.2.1, (s.2.2.1, ((s.2.2.2.1, s.1), s.2.2.2.2)))
  invFun s := (s.2.2.1.2, (s.1, (s.2.1, (s.2.2.1.1, s.2.2.2))))
  left_inv _ := rfl
  right_inv _ := rfl

/-- One actual correction call at a separately supplied homogeneous label. -/
noncomputable def call {σ : Type*} (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2))
    (nodes : Fin (c + 1) → F) (ζ : F)
    (f : (σ → F) → Coefficients t 1 → ZMod 2)
    (A : (σ → F) → RowOracle F m c t) (a : σ → F)
    (w : Fin t → ZMod 2) (s : CallSeed F σ m c t) : Option (ZMod 2) :=
  run ρ nodes ζ f A a s.1 s.2.1 s.2.2.1 w s.2.2.2

theorem call_eq_sample {σ : Type*} (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2))
    (nodes : Fin (c + 1) → F) (ζ : F)
    (f : (σ → F) → Coefficients t 1 → ZMod 2)
    (A : (σ → F) → RowOracle F m c t) (a : σ → F)
    (w : Fin t → ZMod 2) (s : CallSeed F σ m c t) :
    call ρ nodes ζ f A a w s = sample ρ nodes ζ f A a (callSampleEquiv (w, s)) := rfl

abbrev CertificatePoint (F : Type*) (n : ℕ) := (Fin n ⊕ Fin n) → F

/-- A separate auxiliary table for each requested certificate point. -/
abbrev Auxiliary (F : Type*) (n m c t : ℕ) :=
  CertificatePoint F n → CertificatePoint F n → RowOracle F m c t

/-- Two independent call seeds, with the common point and label sampled once. -/
abbrev TestSample (F : Type*) [Monoid F] (n m c t : ℕ) :=
  (Fin n → F) × ((Fin t → ZMod 2) ×
    (CallSeed F (Fin n ⊕ Fin n) m c t × CallSeed F (Fin n ⊕ Fin n) m c t))

/-- The concrete two-corrector binary grid check. -/
noncomputable def check (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2))
    (nodes : Fin (c + 1) → F) (ζ : F) (H : Finset F)
    (p : (Fin n → F) → Coefficients t 1 → ZMod 2)
    (M : CertificatePoint F n → Coefficients t 1 → ZMod 2)
    (A : Auxiliary F n m c t) (s : TestSample F n m c t) : Option (ZMod 2 × ZMod 2) :=
  optionCheck (some (p s.1 (homogeneousIndex (le_refl 1) s.2.1)))
    (call ρ nodes ζ M (A (zeroPoint s.1)) (zeroPoint s.1) s.2.1 s.2.2.1)
    (call ρ nodes ζ M (A (recoveryPoint H s.1)) (recoveryPoint H s.1) s.2.1 s.2.2.2)

/-- Tag the primary oracle separately from each target's certificate-correction queries. -/
abbrev Query (F : Type*) (n m c t : ℕ) :=
  ((Fin n → F) × Coefficients t 1) ⊕
    (CertificatePoint F n × BinaryLocalCorrection.Query F (Fin n ⊕ Fin n) m c t)

/-- A valid query list for every branch of the two actual correction calls. -/
noncomputable def queries (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2))
    (nodes : Fin (c + 1) → F) (ζ : F) (H : Finset F) (s : TestSample F n m c t) :
    List (Query F n m c t) :=
  Sum.inl (s.1, homogeneousIndex (le_refl 1) s.2.1) ::
    ((BinaryLocalCorrection.queries ρ nodes ζ (zeroPoint s.1)
      s.2.2.1.1 s.2.2.1.2.1 s.2.2.1.2.2.1 s.2.1 s.2.2.1.2.2.2).map
        (fun q => Sum.inr (zeroPoint s.1, q)) ++
      (BinaryLocalCorrection.queries ρ nodes ζ (recoveryPoint H s.1)
        s.2.2.2.1 s.2.2.2.2.1 s.2.2.2.2.2.1 s.2.1 s.2.2.2.2.2.2).map
          (fun q => Sum.inr (recoveryPoint H s.1, q)))

/-- One primary read and two `3c+9`-query calls. -/
theorem queries_length_le (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2))
    (nodes : Fin (c + 1) → F) (ζ : F) (H : Finset F) (s : TestSample F n m c t) :
    (queries ρ nodes ζ H s).length ≤ 6 * c + 19 := by
  have h₀ := BinaryLocalCorrection.queries_length_le ρ nodes ζ (zeroPoint s.1)
    s.2.2.1.1 s.2.2.1.2.1 s.2.2.1.2.2.1 s.2.1 s.2.2.1.2.2.2
  have hZ := BinaryLocalCorrection.queries_length_le ρ nodes ζ (recoveryPoint H s.1)
    s.2.2.2.1 s.2.2.2.2.1 s.2.2.2.2.2.1 s.2.1 s.2.2.2.2.2.2
  simp only [queries, List.length_cons, List.length_append, List.length_map]
  omega

/-- Read one tagged query from the actual three oracle components. -/
def read (p : (Fin n → F) → Coefficients t 1 → ZMod 2)
    (M : CertificatePoint F n → Coefficients t 1 → ZMod 2)
    (A : Auxiliary F n m c t) : Query F n m c t → ZMod 2
  | Sum.inl q => p q.1 q.2
  | Sum.inr q => BinaryLocalCorrection.read M (A q.1) q.2

/-- The concrete returned verdict depends only on the stated query list. -/
theorem check_congr (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2))
    (nodes : Fin (c + 1) → F) (ζ : F) (H : Finset F) (s : TestSample F n m c t)
    (p p' : (Fin n → F) → Coefficients t 1 → ZMod 2)
    (M M' : CertificatePoint F n → Coefficients t 1 → ZMod 2)
    (A A' : Auxiliary F n m c t)
    (he : ∀ q ∈ queries ρ nodes ζ H s, read p M A q = read p' M' A' q) :
    check ρ nodes ζ H p M A s = check ρ nodes ζ H p' M' A' s := by
  have hp := he (Sum.inl (s.1, homogeneousIndex (le_refl 1) s.2.1)) (by simp [queries])
  have h₀ := BinaryLocalCorrection.run_congr ρ nodes ζ M M'
    (A (zeroPoint s.1)) (A' (zeroPoint s.1)) (zeroPoint s.1)
    s.2.2.1.1 s.2.2.1.2.1 s.2.2.1.2.2.1 s.2.1 s.2.2.1.2.2.2 (by
      intro q hq
      exact he (Sum.inr (zeroPoint s.1, q)) (by simp [queries, hq]))
  have hZ := BinaryLocalCorrection.run_congr ρ nodes ζ M M'
    (A (recoveryPoint H s.1)) (A' (recoveryPoint H s.1)) (recoveryPoint H s.1)
    s.2.2.2.1 s.2.2.2.2.1 s.2.2.2.2.2.1 s.2.1 s.2.2.2.2.2.2 (by
      intro q hq
      exact he (Sum.inr (recoveryPoint H s.1, q)) (by simp [queries, hq]))
  simp only [read] at hp
  simp only [check, call, hp, h₀, hZ]

section Completeness

variable [NeZero m] [CharP F 2]

/-- The auxiliary proof gives the honest encoded line at each possible certificate target. -/
noncomputable def honestAuxiliary (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2))
    (M : MvPolynomial (Fin n ⊕ Fin n) F) : Auxiliary F n m c t :=
  fun a => honestTable (m := m) (c := c) ρ M a

/-- Perfect completeness for every random seed of the actual corrected test. -/
theorem check_eval (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2))
    {nodes : Fin (c + 1) → F} (hnodes : Function.Injective nodes)
    {ζ : F} (hζ : StandardLocalCorrection.GoodNodes c ζ) {H : Finset F}
    (P : MvPolynomial (Fin n) F) (M : MvPolynomial (Fin n ⊕ Fin n) F)
    (hM : M.totalDegree < m ^ c) (hcert : IsCertificate H P M)
    (s : TestSample F n m c t) :
    check ρ nodes ζ H (fun x => encode 1 (ρ (eval x P)))
      (fun x => encode 1 (ρ (eval x M)))
      (honestAuxiliary (m := m) (c := c) ρ M) s = some (0, 0) := by
  have h₀ := run_eval ρ hnodes hζ M hM (zeroPoint s.1)
    s.2.2.1.1 s.2.2.1.2.1 s.2.2.1.2.2.1 s.2.1 s.2.2.1.2.2.2
  have hZ := run_eval ρ hnodes hζ M hM (recoveryPoint H s.1)
    s.2.2.2.1 s.2.2.2.2.1 s.2.2.2.2.2.1 s.2.1 s.2.2.2.2.2.2
  have hi := check_encode_eq_zero (le_refl 1) ρ hcert s.1 s.2.1
  simp only [BinaryZeroOnGrid.check, checkBits, encode_homogeneousIndex] at hi
  simp only [check, call, honestAuxiliary, h₀, hZ, optionCheck_some,
    encode_homogeneousIndex, checkBits, hi]

end Completeness

section Finite

variable [Fintype F] [DecidableEq F]

local instance : Fintype (InnerPoint F m c) := inferInstance
local instance : Fintype (InnerSeed F m c t) := inferInstance
local instance : Fintype (CallSeed F (Fin n ⊕ Fin n) m c t) := inferInstance

/-- Normalized rejection includes either abstention or a failed residual. -/
noncomputable def rejectionRate (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2))
    (nodes : Fin (c + 1) → F) (ζ : F) (H : Finset F)
    (p : (Fin n → F) → Coefficients t 1 → ZMod 2)
    (M : CertificatePoint F n → Coefficients t 1 → ZMod 2)
    (A : Auxiliary F n m c t) : ℚ :=
  relativeDistance (check ρ nodes ζ H p M A) (fun _ => some (0, 0))

variable [NeZero m] [CharP F 2]

/-- Zero rejection for the actual honest proof and both honest correction tables. -/
theorem rejectionRate_eval (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2))
    {nodes : Fin (c + 1) → F} (hnodes : Function.Injective nodes)
    {ζ : F} (hζ : StandardLocalCorrection.GoodNodes c ζ) {H : Finset F}
    (P : MvPolynomial (Fin n) F) (M : MvPolynomial (Fin n ⊕ Fin n) F)
    (hM : M.totalDegree < m ^ c) (hcert : IsCertificate H P M) :
    rejectionRate ρ nodes ζ H (fun x => encode 1 (ρ (eval x P)))
      (fun x => encode 1 (ρ (eval x M))) (honestAuxiliary (m := m) (c := c) ρ M) = 0 := by
  apply relativeDistance_eq_zero_iff.mpr
  funext s
  exact check_eval ρ hnodes hζ P M hM hcert s

/-- A polynomial vanishing on a nonempty grid has a complete honest proof. -/
theorem exists_rejectionRate_eval_eq_zero (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2))
    {nodes : Fin (c + 1) → F} (hnodes : Function.Injective nodes)
    {ζ : F} (hζ : StandardLocalCorrection.GoodNodes c ζ) (H : Finset F) (hH : H.Nonempty)
    (P : MvPolynomial (Fin n) F) (hP : P.totalDegree < m ^ c) (hv : VanishesOn H P) :
    ∃ M : MvPolynomial (Fin n ⊕ Fin n) F,
      M.totalDegree ≤ P.totalDegree ∧
        rejectionRate ρ nodes ζ H (fun x => encode 1 (ρ (eval x P)))
          (fun x => encode 1 (ρ (eval x M))) (honestAuxiliary (m := m) (c := c) ρ M) = 0 := by
  classical
  obtain ⟨M, hdeg, hcert⟩ := (vanishesOn_iff_exists_certificate H hH P).mp hv
  exact ⟨M, hdeg, rejectionRate_eval ρ hnodes hζ P M (hdeg.trans_lt hP) hcert⟩

end Finite
end PCP.Algebraic.BinaryZeroOnGridCorrection
