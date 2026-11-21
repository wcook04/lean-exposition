import TorusEuler.Paper.S678.Vocabulary

/-! # Majorants of the order-dependent constants (package S678a)

Own glue of row 7.1 (sections/08b_induction.tex:199-215, the choice of `b`, `a`, `𝓑`
in the proof of Theorem 7.1): the constants `Γ₀(P)` of Lemmas 5.8, 5.9 and Proposition 5.11
depend on the expansion order `P`; the step `s` uses orders `P ≤ 7K(s)`, so the function `F`
of `Statement.theorem_7_1` must dominate them on that range. -/

namespace TorusEuler.Paper.Lib.S678a

open TorusEuler

noncomputable section

/-- The majorant `F(s) = ∑_{P ≤ 7K(s)} |Γ₀(P)|` of an order-dependent constant `Γ₀`
(sections/08b_induction.tex:199-215): any threshold `B` that is admissible for `F`
(`F s ≤ B s`) bounds `|Γ₀ P|` for every order `P ≤ 7K(s)` used at step `s ≥ 1`. -/
def orderMajorant (b : ℕ) (Γ₀ : ℕ → ℝ) (s : ℕ) : ℝ :=
  ∑ P ∈ Finset.range (7 * frequencyExponent b s + 1), |Γ₀ P|

/-- `|Γ₀ P| ≤ F s` for `P ≤ 7K(s)`. -/
theorem abs_le_orderMajorant (b : ℕ) (Γ₀ : ℕ → ℝ) (s P : ℕ)
    (hP : P ≤ 7 * frequencyExponent b s) : |Γ₀ P| ≤ orderMajorant b Γ₀ s :=
  Finset.single_le_sum (f := fun P => |Γ₀ P|) (fun _ _ => abs_nonneg _)
    (Finset.mem_range.2 (Nat.lt_succ_of_le hP))

end

end TorusEuler.Paper.Lib.S678a
