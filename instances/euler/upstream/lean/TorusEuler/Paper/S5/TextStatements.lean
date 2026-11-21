import TorusEuler.Paper.S5.Vocabulary
import TorusEuler.Paper.S34A.Vocabulary
import TorusEuler.Paper.SBD.Vocabulary
import TorusEuler.TruncatedParentResidual

/-!
# Statements of the displays (5.13), (5.14) of the latest manuscript

Faithful statements `Paper.Statement.Text.eq_5_13` and `eq_5_14` (displays in the proof of
Proposition 5.2, `sections/06d_mean_estimates.tex`), which the proof of Proposition 5.2 and the
joint proof of Auxiliary Lemmas 1.2 and 1.3 (`auxiliary/terminal_smoothness.tex:254, 261`) cite. Equation numbers are those of the
compiled latest manuscript (`main.aux`). Conventions are those of `TorusEuler.Paper.S5`
(`Statements.lean`): the standing parent is `S5.Parent`, the envelope radius is
`ℓ_* = 𝖣^{-a}` with `a ≥ a₀` (`S5.radius`), and constants are quantified as the TeX fixes them.
-/

open Set UnitAddTorus
open scoped ContDiff

namespace TorusEuler.Paper

open HierarchyTwistedProfile AppendixD

noncomputable section

/-- **Display (5.13)** (`cc:uf:mean:thresholds`, sections/06d_mean_estimates.tex:42, in the proof
of Proposition 5.2). Let `K = (D_aX)ᵀ D_aX` and `Ω = (D_aX)ᵀ(Mᵀ - M)D_aX` be the coefficients
(4.1), `ℓ_* = 𝖣^{-a}` and `A` the constant (4.10) of Theorem 4.2 (`D_- = 𝖣`). Then for `m ≥ 1`
`ℓ_*^m (|K|_{m,1/2} + |Ω|_{m,1/2}) ≤ C_m 𝖣^C ℓ_*^{1/2} ≤ C_m / A`.
Equation: (5.13); uses (D.2), (D.6) and the standing (5.1). Theorem 4.2 enters only through
the notation `A` of (4.10): its bound `A ≤ 𝖣^{C_A}` (06d:34-38) is the hypothesis `A ≤ D ^ CA` here,
which the citers supply.

Representation: `K`, `Ω` are the curves `meanKinetic X`, `meanVorticity U X` of the library
on `[0,T]` (labels in `ℝ³`, periodic); `|c|_{m,1/2}` is `AppendixD.holderOrderNorm m c` (the
`C^{0,1/2}` norm is the maximum of the supremum and the seminorm, as in `Statement.Text.eq_D_2`),
and the statement also asserts that the suprema in it are finite. The text shows (06d:34-38)
that `A ≤ 𝖣^{C_A}` with an absolute exponent `C_A`; the statement is made for every
`A ∈ (0, 𝖣^{C_A}]`, with the floor `a₀` of the envelope exponent chosen after `C_A` and the
constants `C`, `C_m` (the absolute exponent and the constants of the text) after `a₀` and `a`,
as in `Statement.proposition_5_2`. Writing `C_m / A` requires `A > 0`. -/
def Statement.Text.eq_5_13 : Prop :=
  ∀ CA : ℕ, ∃ a₀ : ℕ, ∀ a : ℕ, a₀ ≤ a → ∃ C : ℕ, ∃ Cm : ℕ → ℝ,
    ∀ {T : ℝ} {U : Velocity} {X : ℝ → Velocity} {pU : Pressure} {D lam : ℝ},
      0 < T → S5.Parent T U X pU D lam →
      ∀ A : ℝ, 0 < A → A ≤ D ^ CA →
      let ℓ := S5.radius D a
      let Kin : Icc (0 : ℝ) T → Vec3 → (Vec3 →L[ℝ] Vec3) := fun t => meanKinetic X t.val
      let Om : Icc (0 : ℝ) T → Vec3 → (Vec3 →L[ℝ] Vec3) := fun t => meanVorticity U X t.val
      ∀ m : ℕ, 1 ≤ m →
        (∀ w ∈ appendixCoefficientOrderWords m,
          BddAbove (hierarchyJetValues True (hierarchyLabelDirection 1) w Kin) ∧
          BddAbove (hierarchyJetValues True (hierarchyLabelDirection 1) w Om)) ∧
        ℓ ^ m * (holderOrderNorm m Kin + holderOrderNorm m Om) ≤ Cm m * D ^ C * Real.sqrt ℓ ∧
        Cm m * D ^ C * Real.sqrt ℓ ≤ Cm m / A

/-- **Display (5.14)** (`cc:uf:mean:holder-bound`, sections/06d_mean_estimates.tex:56, in the
proof of Proposition 5.2). For a solution `(B, q̄)` of the mean equation (5.11) with source `f̄`
(`B = D_aX v`, `v = z_t` the velocity of the solution of (4.9) with `L = -∫_0^t g`,
`g = (D_aX)ᵀ f̄`), `‖v‖_{[n],1/2} ≤ C_n 𝖣^C ‖g‖_{[n],1/2}` for every `n ≥ 0`, with an absolute
exponent `C`.
Equation: (5.14); standing (5.1), (5.2); uses (5.13), Theorem 4.2 and Lemma D.3, with
Proposition 5.1 and Lemma D.2(a) giving (D.6) for `K`, `Ω` and the bound `A ≤ 𝖣^C` of the
constant of Theorem 4.2 (06d:24-38).

Representation: the solution is any `S5.MeanSolution d f B q`; `v` is any smooth periodic
velocity with `B = D_aX v` (it is determined by `B`, hence is the `z_t` of the solution of (4.9),
which is unique); `‖·‖_{[n],1/2}` is `AppendixD.holderFieldNorm ℓ_* n` of the curves on `[0,T]`;
the source `f̄` is phase independent, so `g` is read at phase `0`; as in `Statement.lemma_D_1`
the norm of `g` is assumed finite, and finiteness of the norm of `v` is part of the conclusion;
`ℓ_* = 𝖣^{-a}` with `a ≥ a₀`. -/
def Statement.Text.eq_5_14 : Prop :=
  ∃ a₀ : ℕ, ∀ a : ℕ, a₀ ≤ a → ∃ C : ℕ, ∃ Cn : ℕ → ℝ,
    ∀ {T : ℝ} (hT : 0 < T) {U : Velocity} {X : ℝ → Velocity} {pU : Pressure} {k : Vec3}
      {D lam : ℝ} (d : ParentGeometry hT U X k),
      S5.Parent T U X pU D lam →
      ∀ (f B : HierarchyTwistedProfile T k Vec3) (q : HierarchyTwistedProfile T k ℝ),
        S5.MeanSolution d f B q →
        ∀ v : Velocity, ContDiffOn ℝ ∞ (Function.uncurry v) (Icc 0 T ×ˢ (univ : Set Vec3)) →
          (∀ t ∈ Icc 0 T, SpatiallyPeriodic (v t)) →
          (∀ t ∈ Icc 0 T, ∀ x s, B.val.val.val (t, x, s) = fderiv ℝ (X 0 t) x (v t x)) →
          let ℓ := S5.radius D a
          let g : Icc (0 : ℝ) T → Vec3 → Vec3 := fun t x =>
            (meanDeformation X t.val x).adjoint (f.val.val.val (t.val, x, 0))
          ∀ n : ℕ, HolderFieldNormFinite ℓ n g →
            HolderFieldNormFinite ℓ n (fun t : Icc (0 : ℝ) T => v t.val) ∧
              holderFieldNorm ℓ n (fun t : Icc (0 : ℝ) T => v t.val) ≤
                Cn n * D ^ C * holderFieldNorm ℓ n g

end

end TorusEuler.Paper
