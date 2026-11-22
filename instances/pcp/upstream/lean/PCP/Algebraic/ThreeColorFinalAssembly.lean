import PCP.Algebraic.ThreeColorSeedNormalization
import PCP.Complexity.InputReductionRuntime
import PCP.Reduction.NPThreeColorRuntime

/-!
# Final assembly of the algebraic PCP route

All reduction work, public encoding conversion, and canonical randomness padding
are included. The only remaining input to `of_runtime` is the concrete
machine-time certificate for the fixed amplified three-color verifier, which
`PCP.Lang.ThreeColorRuntime.polyTimeAlg` supplies in `PCP/Theorem.lean`.
-/

namespace PCP.Algebraic.ThreeColorFinalAssembly

/-- Generic assembly keeps the fixed verifier opaque during kernel checking. -/
theorem assemble (V : Verifier) (alg : VerifierAlg) (a b q : ℕ) (targetBound : Polynomial ℕ)
    (hruntime : Machine.PolyTimeAlg alg)
    (hi : ∀ (f : List Bool → List Bool) (budget : ℕ → ℕ)
      (h : ∀ x, V.randomness (f x).length ≤ budget x.length),
      (Verifier.Reduction.verifier V f budget h).ImplementedBy
        (fun x bits answers => alg (f x) bits answers))
    (hq : V.queries = q) (hr : V.CanonicalRandomness a b)
    (hp : ∀ x, V.ReadsBelow x (targetBound.eval x.length))
    (hc : ∀ x, (ThreeColorEncoding.graph x).Colorable 3 → V.CompleteAt x)
    (hs : ∀ x, ¬ (ThreeColorEncoding.graph x).Colorable 3 → V.SoundAt x (1 / 2))
    (L : Language) (hL : InNP Machine.PolyTimeRel L) :
    ∃ (V : Verifier) (alg : VerifierAlg) (a b q : ℕ) (p : Polynomial ℕ),
      Machine.PolyTimeAlg alg ∧
      V.ImplementedBy alg ∧
      V.queries = q ∧
      V.CanonicalRandomness a b ∧
      (∀ x : List Bool, V.ReadsBelow x (p.eval x.length)) ∧
      (∀ x : List Bool, L x → V.CompleteAt x) ∧
      (∀ x : List Bool, ¬ L x → V.SoundAt x (1 / 2)) := by
  obtain ⟨f, p, P, C, d, hf⟩ := PCP.Reduction.NPThreeColorRuntime.of_inNP_program hL
  have hlen : ∀ x : List Bool, (f x).length ≤ p.eval x.length := fun x => (hf x).2.2.2
  let W := Verifier.Reduction.canonicalVerifier V hr f p hlen
  refine ⟨W, (fun x bits answers => alg (f x) bits answers),
    a * p.natDegree, a * Nat.clog 2 (p.eval 1 + 2) + b,
    q, targetBound.comp p, ?_, hi f _ _, hq, ?_, ?_, ?_, ?_⟩
  · exact Machine.InputReductionRuntime.polyTimeAlg _ hruntime f P
      (fun x => (hf x).1) (fun x => (hf x).2.1)
  · exact Verifier.Reduction.canonicalVerifier_randomness V hr f p hlen
  · exact Verifier.Reduction.canonicalVerifier_readsBelow V hr f p _ hlen hp
  · intro x hx
    apply (Verifier.Reduction.completeAt_iff V f _ _ x).mpr
    exact hc (f x) ((hf x).2.2.1.mpr hx)
  · intro x hx
    apply (Verifier.Reduction.soundAt_iff V f _ _ x (1 / 2)).mpr
    exact hs (f x) (fun hh => hx ((hf x).2.2.1.mp hh))

/-- The fixed verifier's machine certificate suffices for the unchanged final PCP statement. -/
theorem of_runtime
    (hruntime : Machine.PolyTimeAlg ComputableThreeColorAmplifiedQueryAlgorithm.algorithm)
    (L : Language) (hL : InNP Machine.PolyTimeRel L) :
    ∃ (V : Verifier) (alg : VerifierAlg) (a b q : ℕ) (p : Polynomial ℕ),
      Machine.PolyTimeAlg alg ∧
      V.ImplementedBy alg ∧
      V.queries = q ∧
      V.CanonicalRandomness a b ∧
      (∀ x : List Bool, V.ReadsBelow x (p.eval x.length)) ∧
      (∀ x : List Bool, L x → V.CompleteAt x) ∧
      (∀ x : List Bool, ¬ L x → V.SoundAt x (1 / 2)) := by
  obtain ⟨_, hq, hr, hp, hc, hs, _⟩ :=
    ComputableThreeColorAmplifiedVerifier.verification_guarantees
  exact assemble _ _ _ _ _ _ hruntime
    ComputableThreeColorAmplifiedQueryAlgorithm.reduceInput_implementedBy
    hq hr hp hc hs L hL

end PCP.Algebraic.ThreeColorFinalAssembly
