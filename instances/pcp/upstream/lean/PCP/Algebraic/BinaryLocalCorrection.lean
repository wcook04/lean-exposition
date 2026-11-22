/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Algebraic.BinaryStandardLocalCorrection
import PCP.Algebraic.BinaryLowDegreeTest
import PCP.Algebraic.SetMultilinearDecode

/-!
# The binary local corrector

At the requested outer point, sample a direction and a nonzero parameter. Test
the auxiliary encoded line with the binary generator low-degree test, compare its
locally corrected answer with the received point oracle, and return its locally
corrected value at parameter zero. Either failed check returns `none`.

The inner test uses an independent finite seed. Both local corrections may share
their direction and homogeneous label. This file gives the actual procedure,
its query dependence, and perfect completeness. Soundness is developed separately.
-/

namespace PCP.Algebraic.BinaryLocalCorrection

open Finset PolynomialLine BinaryPolynomialSpace Hadamard

variable {F σ : Type*} [Field F] [Algebra (ZMod 2) F] {m c t : ℕ}

abbrev InnerPoint (F : Type*) (m c : ℕ) := SetMultilinear.Variables m c → F

abbrev RowOracle (F : Type*) (m c t : ℕ) := InnerPoint F m c → Coefficients t 1 → ZMod 2

abbrev InnerSeed (F : Type*) (m c t : ℕ) :=
  BinaryLowDegreeTest.TestRandomness F (SetMultilinear.Variables m c) t 1

/-- All finite choices, including the homogeneous label whose answer is requested. -/
abbrev Sample (F σ : Type*) [Monoid F] (m c t : ℕ) :=
  (σ → F) × (Fˣ × ((InnerPoint F m c × (Fin t → ZMod 2)) × InnerSeed F m c t))

/-- A point-oracle query or a query to one auxiliary encoded line. -/
abbrev Query (F σ : Type*) (m c t : ℕ) :=
  ((σ → F) × Coefficients t 1) ⊕ ((σ → F) × (InnerPoint F m c × Coefficients t 1))

/-- The section 5 procedure; `none` denotes rejection. -/
noncomputable def run (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2))
    (nodes : Fin (c + 1) → F) (ζ : F)
    (f : (σ → F) → Coefficients t 1 → ZMod 2)
    (H : (σ → F) → RowOracle F m c t) (a b : σ → F) (z : Fˣ)
    (v : InnerPoint F m c) (w : Fin t → ZMod 2) (s : InnerSeed F m c t) :
    Option (ZMod 2) := by
  classical
  exact if BinaryLowDegreeTest.test (le_refl 1) ρ nodes (H b) s then
    if BinaryStandardLocalCorrection.correct c ζ ρ (H b)
        (SetMultilinear.evaluationPoint m c (z : F)) v w =
        f (point a b (z : F)) (homogeneousIndex (le_refl 1) w) then
      some (BinaryStandardLocalCorrection.correct c ζ ρ (H b)
        (SetMultilinear.evaluationPoint m c 0) v w)
    else none
  else none

/-- The corrector evaluated on its full finite sample. -/
noncomputable def sample (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2))
    (nodes : Fin (c + 1) → F) (ζ : F)
    (f : (σ → F) → Coefficients t 1 → ZMod 2)
    (H : (σ → F) → RowOracle F m c t) (a : σ → F)
    (s : Sample F σ m c t) : Option (ZMod 2) :=
  run ρ nodes ζ f H a s.1 s.2.1 s.2.2.1.1 s.2.2.1.2 s.2.2.2

/-- A query list valid for every branch, including both correction sums. -/
noncomputable def queries (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2))
    (nodes : Fin (c + 1) → F) (ζ : F) (a b : σ → F) (z : Fˣ)
    (v : InnerPoint F m c) (w : Fin t → ZMod 2) (s : InnerSeed F m c t) :
    List (Query F σ m c t) :=
  Sum.inl (point a b (z : F), homogeneousIndex (le_refl 1) w) ::
    ((BinaryLowDegreeTest.queries (le_refl 1) ρ nodes s).map (fun p => Sum.inr (b, p)) ++
      (BinaryStandardLocalCorrection.queries c ζ ρ (SetMultilinear.evaluationPoint m c (z : F))
        v w).map (fun p => Sum.inr (b, p)) ++
      (BinaryStandardLocalCorrection.queries c ζ ρ (SetMultilinear.evaluationPoint m c 0)
        v w).map (fun p => Sum.inr (b, p)))

/-- The weighted corrector uses a number of bit queries linear in `c`. -/
theorem queries_length_le (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2))
    (nodes : Fin (c + 1) → F) (ζ : F) (a b : σ → F) (z : Fˣ)
    (v : InnerPoint F m c) (w : Fin t → ZMod 2) (s : InnerSeed F m c t) :
    (queries ρ nodes ζ a b z v w s).length ≤ 3 * c + 9 := by
  have h := BinaryLowDegreeTest.queries_length_le (le_refl 1) ρ nodes s
  simp only [queries, List.length_cons, List.length_append, List.length_map,
    BinaryStandardLocalCorrection.queries_length]
  omega

/-- Read an indexed query from the two received oracles. -/
def read (f : (σ → F) → Coefficients t 1 → ZMod 2)
    (H : (σ → F) → RowOracle F m c t) : Query F σ m c t → ZMod 2
  | Sum.inl p => f p.1 p.2
  | Sum.inr p => H p.1 p.2.1 p.2.2

/-- The returned answer depends only on the stated queries. -/
theorem run_congr (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2))
    (nodes : Fin (c + 1) → F) (ζ : F)
    (f g : (σ → F) → Coefficients t 1 → ZMod 2)
    (H K : (σ → F) → RowOracle F m c t) (a b : σ → F) (z : Fˣ)
    (v : InnerPoint F m c) (w : Fin t → ZMod 2) (s : InnerSeed F m c t)
    (h : ∀ p ∈ queries ρ nodes ζ a b z v w s, read f H p = read g K p) :
    run ρ nodes ζ f H a b z v w s = run ρ nodes ζ g K a b z v w s := by
  have hf := h (Sum.inl (point a b (z : F), homogeneousIndex (le_refl 1) w))
    (by simp [queries])
  have ht := BinaryLowDegreeTest.test_congr (le_refl 1) ρ nodes s (H b) (K b) (by
    intro p hp
    exact h (Sum.inr (b, p)) (by simp [queries, hp]))
  have hz := BinaryStandardLocalCorrection.correct_congr c ζ ρ
    (SetMultilinear.evaluationPoint m c (z : F)) v w (H b) (K b) (by
      intro p hp
      exact h (Sum.inr (b, p)) (by simp [queries, hp]))
  have h0 := BinaryStandardLocalCorrection.correct_congr c ζ ρ
    (SetMultilinear.evaluationPoint m c 0) v w (H b) (K b) (by
      intro p hp
      exact h (Sum.inr (b, p)) (by simp [queries, hp]))
  simp only [read] at hf
  simp only [run, ht, hz, h0, hf]

variable [NeZero m]

/-- The honest auxiliary encoded line at a fixed requested outer point. -/
noncomputable def honestTable (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2))
    (P : MvPolynomial σ F) (a b : σ → F) : RowOracle F m c t :=
  fun x => encode 1 (ρ (MvPolynomial.eval x (SetMultilinear.encode m c (restrict a b P))))

variable [CharP F 2]

/-- Honest polynomial oracles always return the requested homogeneous bit. -/
theorem run_eval (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2))
    {nodes : Fin (c + 1) → F} (hnodes : Function.Injective nodes)
    {ζ : F} (hζ : StandardLocalCorrection.GoodNodes c ζ)
    (P : MvPolynomial σ F) (hP : P.totalDegree < m ^ c)
    (a b : σ → F) (z : Fˣ) (v : InnerPoint F m c)
    (w : Fin t → ZMod 2) (s : InnerSeed F m c t) :
    run ρ nodes ζ (fun x => encode 1 (ρ (MvPolynomial.eval x P)))
      (honestTable (m := m) (c := c) ρ P a) a b z v w s =
      some (linearEncode (ρ (MvPolynomial.eval a P)) w) := by
  have hd := SetMultilinear.totalDegree_encode_le m c (restrict a b P)
  have hline := (natDegree_restrict_le a b P).trans_lt hP
  have ht : BinaryLowDegreeTest.test (le_refl 1) ρ nodes
      (honestTable (m := m) (c := c) ρ P a b) s = true :=
    BinaryLowDegreeTest.test_eval (le_refl 1) ρ hnodes _ hd s
  have he (y : F) : BinaryStandardLocalCorrection.correct c ζ ρ
      (honestTable (m := m) (c := c) ρ P a b)
      (SetMultilinear.evaluationPoint m c y) v w =
      linearEncode (ρ (MvPolynomial.eval (point a b y) P)) w := by
    change BinaryStandardLocalCorrection.correct c ζ ρ
      (fun x => encode 1 (ρ (MvPolynomial.eval x (SetMultilinear.encode m c (restrict a b P)))))
      _ v w = _
    rw [BinaryStandardLocalCorrection.correct_eval ρ hζ _ hd,
      SetMultilinear.eval_encode m c _ hline, eval_restrict]
  simp only [run, ht, ↓reduceIte, he, point_zero, encode_homogeneousIndex]

end PCP.Algebraic.BinaryLocalCorrection
