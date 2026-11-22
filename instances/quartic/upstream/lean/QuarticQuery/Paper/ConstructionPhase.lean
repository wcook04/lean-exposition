module

public import QuarticQuery.Model.Quantum

/-!
# One bit query implements a phase query

Compiled as part of the `QuarticQuery` library target.
Toolchain: leanprover/lean4:v4.36.0-rc2, with the repository's lake manifest.

This is the local one-query assertion in the proof of Lemma 2.1(ii). It uses
the public bit oracle directly. The factor of two charged by the general
`Samples` compiler is a separate implementation bound.
-/

public section

namespace QuarticQuery.Paper

variable {ι : Type} [Fintype ι] {w : ℕ}

/-- Ledger: claim-proj-prob. Verbatim local phase-kickback assertion: one
application of the bit oracle multiplies the amplitude at index `i` by
`(-1)^(x i)` when the answer qubit is in the minus subspace. The statement is
linear and holds for arbitrary amplitudes and arbitrary entangled workspace. -/
theorem construction_bitOracle_phase_kickback
    (x : BitInput ι) (ψ : State ι w)
    (hminus : ∀ (i : ι) (z : Fin (w + 1)),
      ψ.ofLp (i, true, z) = -ψ.ofLp (i, false, z))
    (p : Basis ι w) :
    (bitOracle x ψ).ofLp p =
      (if x p.1 then (-1 : ℂ) else 1) * ψ.ofLp p := by
  obtain ⟨i, b, z⟩ := p
  rw [bitOracle_apply]
  cases hx : x i <;> cases b
  · simp only [flipPoint, hx, Bool.false_eq_true, ↓reduceIte, one_mul]
  · simp only [flipPoint, hx, Bool.false_eq_true, ↓reduceIte, one_mul]
  · simpa only [flipPoint, hx, ↓reduceIte, Bool.not_false, neg_one_mul]
      using hminus i z
  · simp only [flipPoint, hx, ↓reduceIte, Bool.not_true, neg_one_mul]
    rw [hminus, neg_neg]

/-- Ledger: claim-proj-prob. Verbatim local physical implementation: phase
kickback preserves both a normalized state and the minus subspace, so the
answer ancilla can be retained for subsequent phase queries. -/
theorem construction_bitOracle_phase_preserves
    (x : BitInput ι) (ψ : State ι w)
    (hminus : ∀ (i : ι) (z : Fin (w + 1)),
      ψ.ofLp (i, true, z) = -ψ.ofLp (i, false, z))
    (hunit : ‖ψ‖ = 1) :
    ‖bitOracle x ψ‖ = 1 ∧
      ∀ (i : ι) (z : Fin (w + 1)),
        (bitOracle x ψ).ofLp (i, true, z) =
          -(bitOracle x ψ).ofLp (i, false, z) := by
  refine ⟨(norm_bitOracle x ψ).trans hunit, ?_⟩
  intro i z
  rw [construction_bitOracle_phase_kickback x ψ hminus (i, true, z),
    construction_bitOracle_phase_kickback x ψ hminus (i, false, z)]
  rw [hminus]
  ring

end QuarticQuery.Paper
