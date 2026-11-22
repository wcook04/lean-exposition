/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Algebraic.HadamardDerivedOracle
import PCP.Algebraic.BinaryZeroOnGridSoundness

/-!
# Zero-on-grid verification with a fresh randomized derived primary read

Each grid sample receives its own independent Hadamard correction seed. Only the
single primary bit is replaced; the two certificate-correction calls keep their
actual shared label and independent internal seeds. The replacement adds exactly
one bit query. Soundness follows by a direct finite-sample rejection transfer.
This replaces the paper's equally valid step of fixing one good correction seed
`R` and applying Theorem 6.1 to the resulting derived oracle.
-/

namespace PCP.Algebraic.DerivedZeroOnGrid

open Finset MvPolynomial BinaryPolynomialSpace Hadamard GridVanishing BinaryZeroOnGrid
open BinaryLocalCorrection BinaryZeroOnGridCorrection

variable {F : Type*} [Field F] [Algebra (ZMod 2) F] {n m c t r : ℕ}

/-- All grid randomness except its outer point. -/
abbrev GridRandomness (F : Type*) [Monoid F] (n m c t : ℕ) :=
  (Fin t → ZMod 2) ×
    (CallSeed F (Fin n ⊕ Fin n) m c t × CallSeed F (Fin n ⊕ Fin n) m c t)

/-- A fresh independent coefficient seed is drawn after the original grid sample. -/
abbrev TestSample (F : Type*) [Monoid F] (n m c t r : ℕ) :=
  (Fin n → F) × (GridRandomness F n m c t × Coefficients t r)

/-- Forget only the newly drawn primary-correction seed. -/
def gridSeed (s : TestSample F n m c t r) : BinaryZeroOnGridCorrection.TestSample F n m c t :=
  (s.1, s.2.1)

/-- The rest of the grid verifier, with its one primary bit supplied as an argument. -/
noncomputable def withPrimaryBit (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2))
    (nodes : Fin (c + 1) → F) (ζ : F) (H : Finset F)
    (M : CertificatePoint F n → Coefficients t 1 → ZMod 2) (A : Auxiliary F n m c t)
    (s : BinaryZeroOnGridCorrection.TestSample F n m c t) (b : ZMod 2) :
    Option (ZMod 2 × ZMod 2) :=
  optionCheck (some b)
    (call ρ nodes ζ M (A (zeroPoint s.1)) (zeroPoint s.1) s.2.1 s.2.2.1)
    (call ρ nodes ζ M (A (recoveryPoint H s.1)) (recoveryPoint H s.1) s.2.1 s.2.2.2)

/-- The actual verifier uses a freshly self-corrected derived primary bit. -/
noncomputable def check (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2))
    (Q : (Fin n → F) → Polynomial F) (hQ : ∀ x, (Q x).natDegree ≤ r)
    (nodes : Fin (c + 1) → F) (ζ : F) (H : Finset F)
    (p : (Fin n → F) → Coefficients t r → ZMod 2)
    (M : CertificatePoint F n → Coefficients t 1 → ZMod 2) (A : Auxiliary F n m c t)
    (s : TestSample F n m c t r) : Option (ZMod 2 × ZMod 2) :=
  withPrimaryBit ρ nodes ζ H M A (gridSeed s)
    (HadamardDerivedOracle.answer ρ (Q s.1) (hQ s.1) (p s.1)
      (homogeneousIndex (le_refl 1) s.2.1.1) s.2.2)

/-- The primary oracle uses degree-`r` queries; certificate queries keep their original types. -/
abbrev Query (F : Type*) (n m c t r : ℕ) :=
  ((Fin n → F) × Coefficients t r) ⊕
    (CertificatePoint F n × BinaryLocalCorrection.Query F (Fin n ⊕ Fin n) m c t)

/-- Bundled actual query list for one certificate correction call. -/
noncomputable def callQueries (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2))
    (nodes : Fin (c + 1) → F) (ζ : F) (a : CertificatePoint F n)
    (w : Fin t → ZMod 2) (s : CallSeed F (Fin n ⊕ Fin n) m c t) :
    List (BinaryLocalCorrection.Query F (Fin n ⊕ Fin n) m c t) :=
  BinaryLocalCorrection.queries ρ nodes ζ a s.1 s.2.1 s.2.2.1 w s.2.2.2

/-- The two fresh primary queries followed by both unchanged certificate query lists. -/
noncomputable def queries (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2))
    (Q : (Fin n → F) → Polynomial F) (hQ : ∀ x, (Q x).natDegree ≤ r)
    (nodes : Fin (c + 1) → F) (ζ : F) (H : Finset F) (s : TestSample F n m c t r) :
    List (Query F n m c t r) :=
  (HadamardDerivedOracle.queries ρ (Q s.1) (hQ s.1)
    (homogeneousIndex (le_refl 1) s.2.1.1) s.2.2).map (fun q => Sum.inl (s.1, q)) ++
  (callQueries ρ nodes ζ (zeroPoint s.1) s.2.1.1 s.2.1.2.1).map
    (fun q => Sum.inr (zeroPoint s.1, q)) ++
  (callQueries ρ nodes ζ (recoveryPoint H s.1) s.2.1.1 s.2.1.2.2).map
    (fun q => Sum.inr (recoveryPoint H s.1, q))

/-- Two reads replace exactly one primary read, with no changes to the certificate calls. -/
theorem queries_length_eq (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2))
    (Q : (Fin n → F) → Polynomial F) (hQ : ∀ x, (Q x).natDegree ≤ r)
    (nodes : Fin (c + 1) → F) (ζ : F) (H : Finset F) (s : TestSample F n m c t r) :
    (queries ρ Q hQ nodes ζ H s).length =
      (BinaryZeroOnGridCorrection.queries ρ nodes ζ H (gridSeed s)).length + 1 := by
  simp only [queries, List.length_append, List.length_map, HadamardDerivedOracle.queries_length,
    BinaryZeroOnGridCorrection.queries, List.length_cons, gridSeed, callQueries]
  omega

/-- The actual derived-grid verifier uses at most `6c+20` bit queries. -/
theorem queries_length_le (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2))
    (Q : (Fin n → F) → Polynomial F) (hQ : ∀ x, (Q x).natDegree ≤ r)
    (nodes : Fin (c + 1) → F) (ζ : F) (H : Finset F) (s : TestSample F n m c t r) :
    (queries ρ Q hQ nodes ζ H s).length ≤ 6 * c + 20 := by
  rw [queries_length_eq]
  have h := BinaryZeroOnGridCorrection.queries_length_le ρ nodes ζ H (gridSeed s)
  omega

/-- Read an actual query from the degree-`r` primary oracle or certificate proof. -/
def read (p : (Fin n → F) → Coefficients t r → ZMod 2)
    (M : CertificatePoint F n → Coefficients t 1 → ZMod 2) (A : Auxiliary F n m c t) :
    Query F n m c t r → ZMod 2
  | Sum.inl q => p q.1 q.2
  | Sum.inr q => BinaryLocalCorrection.read M (A q.1) q.2

/-- Query dependence of the actual randomized verifier. -/
theorem check_congr (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2))
    (Q : (Fin n → F) → Polynomial F) (hQ : ∀ x, (Q x).natDegree ≤ r)
    (nodes : Fin (c + 1) → F) (ζ : F) (H : Finset F) (s : TestSample F n m c t r)
    (p p' : (Fin n → F) → Coefficients t r → ZMod 2)
    (M M' : CertificatePoint F n → Coefficients t 1 → ZMod 2) (A A' : Auxiliary F n m c t)
    (he : ∀ q ∈ queries ρ Q hQ nodes ζ H s, read p M A q = read p' M' A' q) :
    check ρ Q hQ nodes ζ H p M A s = check ρ Q hQ nodes ζ H p' M' A' s := by
  have hp := HadamardDerivedOracle.answer_congr ρ (Q s.1) (hQ s.1) (p s.1) (p' s.1)
    (homogeneousIndex (le_refl 1) s.2.1.1) s.2.2 (by
      intro q hq
      exact he (Sum.inl (s.1, q)) (by simp [queries, hq]))
  have h₀ := BinaryLocalCorrection.run_congr ρ nodes ζ M M'
    (A (zeroPoint s.1)) (A' (zeroPoint s.1)) (zeroPoint s.1)
    s.2.1.2.1.1 s.2.1.2.1.2.1 s.2.1.2.1.2.2.1 s.2.1.1 s.2.1.2.1.2.2.2 (by
      intro q hq
      exact he (Sum.inr (zeroPoint s.1, q)) (by simp [queries, callQueries, hq]))
  have hZ := BinaryLocalCorrection.run_congr ρ nodes ζ M M'
    (A (recoveryPoint H s.1)) (A' (recoveryPoint H s.1)) (recoveryPoint H s.1)
    s.2.1.2.2.1 s.2.1.2.2.2.1 s.2.1.2.2.2.2.1 s.2.1.1 s.2.1.2.2.2.2.2 (by
      intro q hq
      exact he (Sum.inr (recoveryPoint H s.1, q)) (by simp [queries, callQueries, hq]))
  simp only [check, withPrimaryBit, gridSeed, call, hp, h₀, hZ]

/-- Honest primary encodings identify the received grid check with its fixed honest counterpart. -/
theorem check_encode (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2))
    (Q : (Fin n → F) → Polynomial F) (hQ : ∀ x, (Q x).natDegree ≤ r)
    (nodes : Fin (c + 1) → F) (ζ : F) (H : Finset F) (f : (Fin n → F) → F)
    (M : CertificatePoint F n → Coefficients t 1 → ZMod 2) (A : Auxiliary F n m c t)
    (s : TestSample F n m c t r) :
    check ρ Q hQ nodes ζ H (fun x => encode r (ρ (f x))) M A s =
      BinaryZeroOnGridCorrection.check ρ nodes ζ H
        (fun x => encode 1 (ρ ((Q x).eval (f x)))) M A (gridSeed s) := by
  simp only [check, HadamardDerivedOracle.answer_encode, BinaryZeroOnGridCorrection.check,
    withPrimaryBit, gridSeed]

section Completeness

variable [NeZero m] [CharP F 2]

/-- Perfect completeness with an explicit identity for the derived outer polynomial. -/
theorem check_eval (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2))
    (Q : (Fin n → F) → Polynomial F) (hQ : ∀ x, (Q x).natDegree ≤ r)
    {nodes : Fin (c + 1) → F} (hnodes : Function.Injective nodes)
    {ζ : F} (hζ : StandardLocalCorrection.GoodNodes c ζ) {H : Finset F} (f : (Fin n → F) → F)
    (P : MvPolynomial (Fin n) F) (hvalue : ∀ x, (Q x).eval (f x) = eval x P)
    (M : MvPolynomial (Fin n ⊕ Fin n) F) (hM : M.totalDegree < m ^ c)
    (hcert : IsCertificate H P M) (s : TestSample F n m c t r) :
    check ρ Q hQ nodes ζ H (fun x => encode r (ρ (f x)))
      (fun x => encode 1 (ρ (eval x M))) (honestAuxiliary (m := m) (c := c) ρ M) s =
        some (0, 0) := by
  rw [check_encode]
  simp only [hvalue]
  exact BinaryZeroOnGridCorrection.check_eval ρ hnodes hζ P M hM hcert (gridSeed s)

end Completeness

section Finite

variable [Fintype F] [DecidableEq F]

local instance : Fintype (InnerPoint F m c) := inferInstance
local instance : Fintype (InnerSeed F m c t) := inferInstance
local instance : Fintype (CallSeed F (Fin n ⊕ Fin n) m c t) := inferInstance
local instance : Fintype (GridRandomness F n m c t) := inferInstance

/-- Actual rejection with the newly sampled primary correction seed. -/
noncomputable def rejectionRate (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2))
    (Q : (Fin n → F) → Polynomial F) (hQ : ∀ x, (Q x).natDegree ≤ r)
    (nodes : Fin (c + 1) → F) (ζ : F) (H : Finset F)
    (p : (Fin n → F) → Coefficients t r → ZMod 2)
    (M : CertificatePoint F n → Coefficients t 1 → ZMod 2) (A : Auxiliary F n m c t) : ℚ :=
  relativeDistance (check ρ Q hQ nodes ζ H p M A) (fun _ => some (0, 0))

/-- Transfer to the grid verifier with honestly derived primary answers,
using the actual fresh randomized marginal. -/
theorem rejection_transfer (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2))
    (Q : (Fin n → F) → Polynomial F) (hQ : ∀ x, (Q x).natDegree ≤ r)
    (nodes : Fin (c + 1) → F) (ζ : F) (H : Finset F)
    (p : (Fin n → F) → Coefficients t r → ZMod 2) (f : (Fin n → F) → F)
    (M : CertificatePoint F n → Coefficients t 1 → ZMod 2) (A : Auxiliary F n m c t) :
    BinaryZeroOnGridCorrection.rejectionRate ρ nodes ζ H
      (fun x => encode 1 (ρ ((Q x).eval (f x)))) M A ≤
        rejectionRate ρ Q hQ nodes ζ H p M A + 2 * HadamardDerivedOracle.fullDistance ρ p f := by
  exact HadamardDerivedOracle.rejection_transfer ρ Q hQ p f
    (fun (_ : Fin n → F) (s : GridRandomness F n m c t) =>
      homogeneousIndex (le_refl 1) s.1)
    (fun x s b => withPrimaryBit ρ nodes ζ H M A (x, s) b) (fun _ _ => some (0, 0))

/-- The coloring membership cubic can be substituted without making a fixed random oracle. -/
theorem cubic_rejection_transfer (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2))
    (nodes : Fin (c + 1) → F) (ζ : F) (H : Finset F)
    (p : (Fin n → F) → Coefficients t 3 → ZMod 2) (f : (Fin n → F) → F)
    (M : CertificatePoint F n → Coefficients t 1 → ZMod 2) (A : Auxiliary F n m c t) :
    BinaryZeroOnGridCorrection.rejectionRate ρ nodes ζ H
      (fun x => encode 1 (ρ ((f x) ^ 3 - 1))) M A ≤
        rejectionRate ρ (fun _ => HadamardDerivedOracle.cubic)
          (fun _ => HadamardDerivedOracle.natDegree_cubic_le) nodes ζ H p M A +
            2 * HadamardDerivedOracle.fullDistance ρ p f := by
  simpa only [HadamardDerivedOracle.eval_cubic] using
    rejection_transfer ρ (fun _ => HadamardDerivedOracle.cubic)
      (fun _ => HadamardDerivedOracle.natDegree_cubic_le) nodes ζ H p f M A

/-- Arbitrary point-dependent weights, including zero, are supported by the cubic transfer. -/
theorem weightedCubic_rejection_transfer (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2))
    (E : (Fin n → F) → F) (nodes : Fin (c + 1) → F) (ζ : F) (H : Finset F)
    (p : (Fin n → F) → Coefficients t 3 → ZMod 2) (f : (Fin n → F) → F)
    (M : CertificatePoint F n → Coefficients t 1 → ZMod 2) (A : Auxiliary F n m c t) :
    BinaryZeroOnGridCorrection.rejectionRate ρ nodes ζ H
      (fun x => encode 1 (ρ (E x * ((f x) ^ 3 - 1)))) M A ≤
        rejectionRate ρ (fun x => HadamardDerivedOracle.weightedCubic (E x))
          (fun x => HadamardDerivedOracle.natDegree_weightedCubic_le (E x)) nodes ζ H p M A +
            2 * HadamardDerivedOracle.fullDistance ρ p f := by
  simpa only [HadamardDerivedOracle.eval_weightedCubic] using
    rejection_transfer ρ (fun x => HadamardDerivedOracle.weightedCubic (E x))
      (fun x => HadamardDerivedOracle.natDegree_weightedCubic_le (E x)) nodes ζ H p f M A

variable [NeZero m] [CharP F 2] {D : ℕ}

/-- The actual freshly randomized derived-grid verifier has perfect completeness. -/
theorem rejectionRate_eval (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2))
    (Q : (Fin n → F) → Polynomial F) (hQ : ∀ x, (Q x).natDegree ≤ r)
    {nodes : Fin (c + 1) → F} (hnodes : Function.Injective nodes)
    {ζ : F} (hζ : StandardLocalCorrection.GoodNodes c ζ) {H : Finset F} (f : (Fin n → F) → F)
    (P : MvPolynomial (Fin n) F) (hvalue : ∀ x, (Q x).eval (f x) = eval x P)
    (M : MvPolynomial (Fin n ⊕ Fin n) F) (hM : M.totalDegree < m ^ c)
    (hcert : IsCertificate H P M) :
    rejectionRate ρ Q hQ nodes ζ H (fun x => encode r (ρ (f x)))
      (fun x => encode 1 (ρ (eval x M))) (honestAuxiliary (m := m) (c := c) ρ M) = 0 := by
  apply relativeDistance_eq_zero_iff.mpr
  funext s
  exact check_eval ρ Q hQ hnodes hζ f P hvalue M hM hcert s

/-- Soundness uses fresh primary randomness and the actual received certificate proof.
The replacement loss is explicitly multiplied by the existing grid-soundness coefficient. -/
theorem rejectionRate_lower_bound
    (hq : 2 * c < Fintype.card F)
    (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2))
    (Q : (Fin n → F) → Polynomial F) (hQ : ∀ x, (Q x).natDegree ≤ r)
    {nodes : Fin (c + 1) → F} (hnodes : GeneratorLowDegreeTest.IsGeneratorNodes nodes)
    {ζ : F} (hζ : StandardLocalCorrection.GoodNodes c ζ) (H : Finset F) (hH : H.Nonempty)
    (f : (Fin n → F) → F) (P : MvPolynomial (Fin n) F)
    (hvalue : ∀ x, (Q x).eval (f x) = eval x P)
    (M : MvPolynomial (Fin n ⊕ Fin n) F) (hP : P.totalDegree ≤ D) (hM : M.totalDegree ≤ D)
    (hdecode : c * m ^ c ≤ D) (hnot : ¬ VanishesOn H P)
    (p : (Fin n → F) → Coefficients t r → ZMod 2)
    (M' : CertificatePoint F n → Coefficients t 1 → ZMod 2) (A : Auxiliary F n m c t)
    {δP δM : ℚ} (hp : HadamardDerivedOracle.fullDistance ρ p f ≤ δP)
    (hm : BinaryLagrangeConstraint.homogeneousDistance (le_refl 1) M'
      (fun x => encode 1 (ρ (eval x M))) ≤ δM) :
    (1 - ((D * H.card : ℕ) : ℚ) / Fintype.card F) / 2 ≤
      (1 + 2 * BinaryLocalCorrection.soundnessConstant c) *
        (rejectionRate ρ Q hQ nodes ζ H p M' A + 2 * δP) + 2 * δM +
          (D : ℚ) / (Fintype.card F - 1 : ℕ) := by
  have ht := rejection_transfer ρ Q hQ nodes ζ H p f M' A
  simp only [hvalue] at ht
  have hz : BinaryLagrangeConstraint.homogeneousDistance (le_refl 1)
      (fun x => encode 1 (ρ (eval x P))) (fun x => encode 1 (ρ (eval x P))) ≤ (0 : ℚ) := by
    simp only [BinaryLagrangeConstraint.homogeneousDistance, relativeDistance_self, le_refl]
  have hg := BinaryZeroOnGridCorrection.rejectionRate_lower_bound hq ρ hnodes hζ H hH P M
    hP hM hdecode hnot (fun x => encode 1 (ρ (eval x P))) M' A hz hm
  have hcoef : 0 ≤ 1 + 2 * BinaryLocalCorrection.soundnessConstant c := by
    have h := BinaryLocalCorrection.soundnessConstant_nonneg c
    linarith
  have htransfer := mul_le_mul_of_nonneg_left
    (ht.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left hp (by norm_num)))) hcoef
  linarith

end Finite
end PCP.Algebraic.DerivedZeroOnGrid
