import PCP.Complexity.ReferencePolynomialBoundSetup
import PCP.Complexity.ReferenceNP

/-!
# Polynomial bounded witnesses give reference NP membership

The witness bound is computed by a concrete unary-register setup, followed by
ComplexityLib's proved finite-certificate compiler. This directly supports
bounded existential witnesses without assuming that the verifier itself rejects
overlong certificates, and does not use the larger Cobham padding development.
-/

namespace PCP.ReferenceBoundedVerifier

open Complexity Polynomial

noncomputable def bound (p runtime : Polynomial ℕ) : Polynomial ℕ :=
  ReferencePolynomialBoundSetup.time p + C 4 * X + C 5 * p + C 20 +
    runtime.comp (C 2 * X + C 2 + p)

theorem compiler_time_le (p runtime : Polynomial ℕ) (n : ℕ) :
    WitnessTM.Verifier.time (ReferencePolynomialBoundSetup.setup p) runtime.eval n ≤
      (bound p runtime).eval n := by
  have hw : WitnessTM.Verifier.window p.eval runtime.eval n ≤
      runtime.eval (2 * n + 2 + p.eval n) := by
    unfold WitnessTM.Verifier.window
    refine Finset.sup_le ?_
    intro m hm
    have hm' : m ≤ p.eval n := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hm
    exact Complexity.polynomial_eval_mono_nat runtime (by omega)
  simp only [WitnessTM.Verifier.time, ReferencePolynomialBoundSetup.setup,
    NTM.guessBoundedTime, TM.pairBuildTime, bound, Polynomial.eval_add,
    Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_comp]
  omega

/-- The actual reference guess-and-verify machine enforces the witness-length bound. -/
theorem mem_NP_of_bounded_verifier {k : ℕ} (p runtime : Polynomial ℕ)
    (M : TM k) {L L₀ : Complexity.Language}
    (hM : M.DecidesInTime L₀ runtime.eval)
    (hchar : ∀ x, x ∈ L ↔ ∃ y : List Bool,
      y.length ≤ p.eval x.length ∧ Complexity.pair x y ∈ L₀) : L ∈ Complexity.NP := by
  let W := WitnessTM.Verifier.compile (ReferencePolynomialBoundSetup.setup p) M
  have hW := WitnessTM.Verifier.compile_decidesInTime
    (ReferencePolynomialBoundSetup.setup p) M hM
  have he : WitnessTM.Verifier.language p.eval L₀ = L := by
    ext x
    exact (hchar x).symm
  rw [he] at hW
  have hN := (W.decidesInTime_iff L
    (WitnessTM.Verifier.time (ReferencePolynomialBoundSetup.setup p) runtime.eval)).mp hW
  apply ReferenceNP.mem_iff_polynomial.mpr
  exact ⟨_, W.toNTM, bound p runtime, hN.mono (compiler_time_le p runtime)⟩

end PCP.ReferenceBoundedVerifier
