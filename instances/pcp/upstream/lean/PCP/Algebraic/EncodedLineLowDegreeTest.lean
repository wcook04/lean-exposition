/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Algebraic.BinaryLocalCorrection

/-!
# Low-degree testing through encoded auxiliary lines

The primary oracle uses degree-`r` Hadamard labels. Each auxiliary line uses
set-multilinear coordinates and degree-one Hadamard labels. A sample checks
primary Hadamard consistency, the inner low-degree test, and a locally
corrected line value against the primary oracle. All three checks are performed;
the inner test itself runs one of its two sub-checks, chosen by a fair coin
(`BinaryLowDegreeTest.test`). The outer parameter ranges over the whole field,
including zero, whereas the paper's NewLDT samples it from the nonzero elements.

The explicit query list certifies a finite query bound, not running time or
sampling from a fixed number of random bits.
-/

namespace PCP.Algebraic.EncodedLineLowDegreeTest

open PolynomialLine BinaryPolynomialSpace Hadamard BinaryLocalCorrection

variable {F σ : Type*} [Field F] [Algebra (ZMod 2) F] {m c t r : ℕ}

abbrev Lines (F σ : Type*) := (σ → F) × (σ → F)

/-- The auxiliary oracle explicitly uses degree-one Hadamard labels. -/
abbrev Auxiliary (F σ : Type*) (m c t : ℕ) := Lines F σ → RowOracle F m c t

/-- Line, full-field parameter, correction direction and label, and both test seeds. -/
abbrev Sample (F σ : Type*) (m c t r : ℕ) :=
  Lines F σ × (F × ((InnerPoint F m c × (Fin t → ZMod 2)) ×
    (Hadamard.TestRandomness t r × InnerSeed F m c t)))

abbrev Query (F σ : Type*) (m c t r : ℕ) :=
  ((σ → F) × Coefficients t r) ⊕ (Lines F σ × (InnerPoint F m c × Coefficients t 1))

/-- The corrected comparison bit. -/
noncomputable def corrected (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2)) (ζ : F) (H : Auxiliary F σ m c t)
    (s : Sample F σ m c t r) : ZMod 2 :=
  BinaryStandardLocalCorrection.correct c ζ ρ (H s.1)
    (SetMultilinear.evaluationPoint m c s.2.1) s.2.2.1.1 s.2.2.1.2

/-- All three checks must pass; the two tester seeds are independent. -/
noncomputable def test (hr : 1 ≤ r) (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2))
    (nodes : Fin (c + 1) → F) (ζ : F)
    (f : (σ → F) → Coefficients t r → ZMod 2) (H : Auxiliary F σ m c t)
    (s : Sample F σ m c t r) : Bool := by
  classical
  exact Hadamard.test hr (f s.1.1) s.2.2.2.1 &&
    BinaryLowDegreeTest.test (le_refl 1) ρ nodes (H s.1) s.2.2.2.2 &&
    decide (corrected ρ ζ H s =
      f (point s.1.1 s.1.2 s.2.1) (homogeneousIndex hr s.2.2.1.2))

/-- Every location read by the tester, including the primary Hadamard check. -/
noncomputable def queries (hr : 1 ≤ r) (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2))
    (nodes : Fin (c + 1) → F) (ζ : F) (s : Sample F σ m c t r) :
    List (Query F σ m c t r) :=
  (Hadamard.testQueries hr s.2.2.2.1).map (fun p => Sum.inl (s.1.1, p)) ++
    (BinaryLowDegreeTest.queries (le_refl 1) ρ nodes s.2.2.2.2).map
      (fun p => Sum.inr (s.1, p)) ++
    (BinaryStandardLocalCorrection.queries c ζ ρ
      (SetMultilinear.evaluationPoint m c s.2.1) s.2.2.1.1 s.2.2.1.2).map
        (fun p => Sum.inr (s.1, p)) ++
    [Sum.inl (point s.1.1 s.1.2 s.2.1, homogeneousIndex hr s.2.2.1.2)]

/-- A bound linear in the inner degree and primary Hadamard degree. -/
theorem queries_length_le (hr : 1 ≤ r) (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2))
    (nodes : Fin (c + 1) → F) (ζ : F) (s : Sample F σ m c t r) :
    (queries hr ρ nodes ζ s).length ≤ 2 * r + 2 * c + 12 := by
  have h := BinaryLowDegreeTest.queries_length_le (le_refl 1) ρ nodes s.2.2.2.2
  simp only [queries, List.length_append, List.length_map, Hadamard.testQueries_length,
    BinaryStandardLocalCorrection.queries_length, List.length_cons, List.length_nil]
  omega

/-- Read one indexed primary or auxiliary bit. -/
def read (f : (σ → F) → Coefficients t r → ZMod 2) (H : Auxiliary F σ m c t) :
    Query F σ m c t r → ZMod 2
  | Sum.inl p => f p.1 p.2
  | Sum.inr p => H p.1 p.2.1 p.2.2

/-- The decision depends only on the stated finite query list. -/
theorem test_congr (hr : 1 ≤ r) (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2))
    (nodes : Fin (c + 1) → F) (ζ : F) (s : Sample F σ m c t r)
    (f g : (σ → F) → Coefficients t r → ZMod 2) (H K : Auxiliary F σ m c t)
    (h : ∀ p ∈ queries hr ρ nodes ζ s, read f H p = read g K p) :
    test hr ρ nodes ζ f H s = test hr ρ nodes ζ g K s := by
  have hh := Hadamard.test_congr hr s.2.2.2.1 (f s.1.1) (g s.1.1) (by
    intro p hp
    exact h (Sum.inl (s.1.1, p)) (by simp [queries, hp]))
  have hi := BinaryLowDegreeTest.test_congr (le_refl 1) ρ nodes s.2.2.2.2 (H s.1) (K s.1)
    (by intro p hp; exact h (Sum.inr (s.1, p)) (by simp [queries, hp]))
  have hc := BinaryStandardLocalCorrection.correct_congr c ζ ρ
    (SetMultilinear.evaluationPoint m c s.2.1) s.2.2.1.1 s.2.2.1.2 (H s.1) (K s.1)
    (by intro p hp; exact h (Sum.inr (s.1, p)) (by simp [queries, hp]))
  have hf := h (Sum.inl (point s.1.1 s.1.2 s.2.1, homogeneousIndex hr s.2.2.1.2))
    (by simp [queries])
  simp only [read] at hf
  simp only [test, corrected, hh, hi, hc, hf]
  rfl

variable [NeZero m] [CharP F 2]

/-- The auxiliary encodings of all genuine line restrictions. -/
noncomputable def honestTable (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2))
    (P : MvPolynomial σ F) : Auxiliary F σ m c t :=
  fun uv => BinaryLocalCorrection.honestTable ρ P uv.1 uv.2

/-- Perfect completeness with the strict outer degree required by the inner encoding. -/
theorem test_eval (hr : 1 ≤ r) (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2))
    {nodes : Fin (c + 1) → F} (hnodes : Function.Injective nodes)
    {ζ : F} (hζ : StandardLocalCorrection.GoodNodes c ζ)
    (P : MvPolynomial σ F) (hP : P.totalDegree < m ^ c) (s : Sample F σ m c t r) :
    test hr ρ nodes ζ (fun x => encode r (ρ (MvPolynomial.eval x P)))
      (honestTable (m := m) (c := c) ρ P) s = true := by
  have hd := SetMultilinear.totalDegree_encode_le m c (restrict s.1.1 s.1.2 P)
  have hline := (natDegree_restrict_le s.1.1 s.1.2 P).trans_lt hP
  have hi := BinaryLowDegreeTest.test_eval (le_refl 1) ρ hnodes _ hd s.2.2.2.2
  have hc := BinaryStandardLocalCorrection.correct_eval ρ hζ _ hd
    (SetMultilinear.evaluationPoint m c s.2.1) s.2.2.1.1 s.2.2.1.2
  simp only [SetMultilinear.eval_encode m c _ hline, eval_restrict] at hc
  change (Hadamard.test hr (encode r (ρ (MvPolynomial.eval s.1.1 P))) s.2.2.2.1 &&
    BinaryLowDegreeTest.test (le_refl 1) ρ nodes
      (fun x => encode 1 (ρ (MvPolynomial.eval x
        (SetMultilinear.encode m c (restrict s.1.1 s.1.2 P))))) s.2.2.2.2 &&
    decide (BinaryStandardLocalCorrection.correct c ζ ρ
      (fun x => encode 1 (ρ (MvPolynomial.eval x
        (SetMultilinear.encode m c (restrict s.1.1 s.1.2 P)))))
      (SetMultilinear.evaluationPoint m c s.2.1) s.2.2.1.1 s.2.2.1.2 = _)) = true
  simp only [Hadamard.test_encode, hi, hc, encode_homogeneousIndex, decide_true, Bool.and_self]

section Finite

variable [Fintype F] [Fintype σ] [DecidableEq σ]

local instance : Fintype (InnerPoint F m c) := inferInstance
local instance : Fintype (InnerSeed F m c t) := inferInstance
local instance : Fintype (Hadamard.TestRandomness t r × InnerSeed F m c t) := inferInstance
local instance : Fintype (Sample F σ m c t r) := inferInstance

/-- Actual normalized rejection over the complete finite seed. -/
noncomputable def rejectionRate (hr : 1 ≤ r) (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2))
    (nodes : Fin (c + 1) → F) (ζ : F)
    (f : (σ → F) → Coefficients t r → ZMod 2) (H : Auxiliary F σ m c t) : ℚ :=
  relativeDistance (test hr ρ nodes ζ f H) (fun _ => true)

omit [NeZero m] [CharP F 2] in
theorem rejectionRate_nonneg (hr : 1 ≤ r) (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2))
    (nodes : Fin (c + 1) → F) (ζ : F)
    (f : (σ → F) → Coefficients t r → ZMod 2) (H : Auxiliary F σ m c t) :
    0 ≤ rejectionRate hr ρ nodes ζ f H := relativeDistance_nonneg _ _

/-- Honest rejection is zero under exactly the finite sampling used by the tester. -/
theorem rejectionRate_eval (hr : 1 ≤ r) (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2))
    {nodes : Fin (c + 1) → F} (hnodes : Function.Injective nodes)
    {ζ : F} (hζ : StandardLocalCorrection.GoodNodes c ζ)
    (P : MvPolynomial σ F) (hP : P.totalDegree < m ^ c) :
    rejectionRate hr ρ nodes ζ (fun x => encode r (ρ (MvPolynomial.eval x P)))
      (honestTable (m := m) (c := c) ρ P) = 0 := by
  rw [rejectionRate, funext (test_eval hr ρ hnodes hζ P hP), relativeDistance_self]

end Finite

end PCP.Algebraic.EncodedLineLowDegreeTest
