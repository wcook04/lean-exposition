import PCP.Complexity.ReferencePairFP
import Complexitylib.Models.TuringMachine.Composition
import Complexitylib.Models.TuringMachine.Combinators.Internal.Scanner

/-!
# Explicit reference decision bits for the translated verifier

The guarded function returns an empty string on malformed input. Reference
decision machines require an explicit zero on rejecting inputs, so an actual
finite scanner follows the function computation. Its output is one precisely
when the computed string contains a true bit. On the empty-or-singleton output
of our checker this is exactly the intended verdict.
-/

namespace PCP.Machine.ReferencePair

open Complexity

def outputLanguage : Complexity.Language :=
  {z | z.foldl (fun a b : Bool => a || b) false = true}

def checkerLanguage (R : List Bool → List Bool → Bool) : Complexity.Language :=
  {z | checker R z = [true]}

@[simp] theorem pair_mem_checkerLanguage (R : List Bool → List Bool → Bool)
    (x w : List Bool) :
    Complexity.pair x w ∈ checkerLanguage R ↔ R x w = true := by
  simp only [checkerLanguage, Set.mem_ofPred_eq, checker_pair, List.cons.injEq,
    and_true]

theorem checker_preimage (R : List Bool → List Bool → Bool) :
    checker R ⁻¹' outputLanguage = checkerLanguage R := by
  ext z
  simp only [Set.mem_preimage, outputLanguage, checkerLanguage, Set.mem_ofPred_eq]
  unfold checker
  cases h : Complexity.unpair? z with
  | none => simp
  | some xy => cases hR : R xy.1 xy.2 <;> simp

/-- Every concrete relation checker gives one actual reference decider with a
natural-polynomial clock. Malformed inputs are explicitly rejected with zero. -/
theorem exists_decider (R : List Bool → List Bool → Bool) (hR : PolyTimeRel R) :
    ∃ (k : ℕ) (M : Complexity.TM k) (p : Polynomial ℕ),
      M.DecidesInTime (checkerLanguage R) p.eval := by
  obtain ⟨k, M, p, hM⟩ :=
    Complexity.mem_FP_iff_computesInTime_polynomial.mp (checker_mem_FP R hR)
  let scanner := Complexity.TM.scannerTM false (fun a b : Bool => a || b)
    (fun b => if b then Complexity.Γw.one else Complexity.Γw.zero)
  have hs : scanner.DecidesInTime outputLanguage (fun n => n + 2) :=
    Complexity.TM.scannerTM_decidesInTime false (fun a b : Bool => a || b) id
      (fun _ => Iff.rfl)
  have hm : Monotone (fun n : ℕ => n + 2) := fun _ _ h => Nat.add_le_add_right h 2
  have hc := Complexity.TM.compositionTM_decidesInTime hM hs hm
  rw [checker_preimage] at hc
  refine ⟨_, Complexity.TM.compositionTM M scanner,
    Polynomial.C 5 * p + Polynomial.C 13, ?_⟩
  convert hc using 1
  funext n
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C]
  omega

end PCP.Machine.ReferencePair
