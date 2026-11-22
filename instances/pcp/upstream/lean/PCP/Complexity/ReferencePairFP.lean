import PCP.Complexity.ReferencePairTape
import Complexitylib.Interop.Mathlib.TM0.Guard

/-!
# Total canonical FP checkers from the concrete relation machines

The exact doubled-prefix pair format is a regular language. A concrete DFA guard
rejects malformed strings before the source verifier runs, supplying the all-input
runtime requirement of Complexitylib's canonical `FP` class.
-/

namespace PCP.Machine.ReferencePair

open Complexity

/-- The finite-state format validator, independent of the checked relation. -/
def format : DFA Bool Phase where
  step := fun s b => parser.next s (.bit b)
  start := .first
  accept := {.suffix}

theorem eval_suffix (z : List Bool) : format.evalFrom .suffix z = .suffix := by
  induction z with
  | nil => rfl
  | cons b z ih => exact ih

theorem eval_bad (z : List Bool) : format.evalFrom .bad z = .bad := by
  induction z with
  | nil => rfl
  | cons b z ih => exact ih

theorem eval_parse : ∀ z : List Bool,
    format.evalFrom .first z = .suffix ↔ (Complexity.unpair? z).isSome = true
  | [] => by simp [DFA.evalFrom_nil, Complexity.unpair?]
  | [b] => by cases b <;> simp [format, parser, Complexity.unpair?]
  | false :: false :: z => by
      change format.evalFrom .first z = .suffix ↔
        ((Complexity.unpair? z).map (fun xy => (false :: xy.1, xy.2))).isSome = true
      simpa only [Option.isSome_map] using eval_parse z
  | true :: true :: z => by
      change format.evalFrom .first z = .suffix ↔
        ((Complexity.unpair? z).map (fun xy => (true :: xy.1, xy.2))).isSome = true
      simpa only [Option.isSome_map] using eval_parse z
  | false :: true :: z => by
      change format.evalFrom .suffix z = .suffix ↔ (true : Bool) = true
      simp only [eval_suffix]
  | true :: false :: z => by
      change format.evalFrom .bad z = .suffix ↔ (false : Bool) = true
      simp only [eval_bad, reduceCtorEq]

/-- Exactly canonical reference pair strings pass the actual input validator. -/
theorem accepts_iff (z : List Bool) :
    z ∈ format.accepts ↔ ∃ x w, z = Complexity.pair x w := by
  change format.evalFrom .first z = .suffix ↔ _
  rw [eval_parse, Option.isSome_iff_exists]
  constructor
  · rintro ⟨⟨x, w⟩, h⟩
    exact ⟨x, w, Complexity.eq_pair_of_unpair?_eq_some h⟩
  · rintro ⟨x, w, rfl⟩
    exact ⟨(x, w), Complexity.unpair?_pair x w⟩

/-- The total binary output function: the relation's bit on pairs, empty on malformed input. -/
def checker (R : List Bool → List Bool → Bool) (z : List Bool) : List Bool :=
  match Complexity.unpair? z with
  | none => []
  | some (x, w) => [R x w]

@[simp] theorem checker_pair (R : List Bool → List Bool → Bool) (x w : List Bool) :
    checker R (Complexity.pair x w) = [R x w] := by
  simp only [checker, Complexity.unpair?_pair]

theorem checker_of_not_accepts (R : List Bool → List Bool → Bool) (z : List Bool)
    (h : z ∉ format.accepts) : checker R z = [] := by
  unfold checker
  cases hp : Complexity.unpair? z with
  | none => rfl
  | some p =>
    exact (h ((accepts_iff z).mpr ⟨p.1, p.2,
      Complexity.eq_pair_of_unpair?_eq_some hp⟩)).elim

/-- An arbitrary concrete relation verifier gives a total verifier in Complexitylib's
unchanged canonical FP class, without assuming a runtime on malformed strings. -/
theorem checker_mem_FP (R : List Bool → List Bool → Bool) (hR : PolyTimeRel R) :
    checker R ∈ Complexity.FP := by
  classical
  obtain ⟨M, p, hp⟩ := exists_pair_machine R hR
  have hg := Complexity.MathlibTM0.BinaryMachine.mem_FP_on_dfa
    (M := M) format (f := checker R) (p := p) (q := Polynomial.C 1) ?_ ?_
  · convert hg using 1
    funext z
    by_cases hz : z ∈ format.accepts
    · simp only [ite_eq_left hz]
    · simp only [ite_eq_right hz, checker_of_not_accepts R z hz]
  · intro z hz
    obtain ⟨x, w, rfl⟩ := (accepts_iff z).mp hz
    simpa only [checker_pair] using hp x w
  · intro z hz
    obtain ⟨x, w, rfl⟩ := (accepts_iff z).mp hz
    simp only [checker_pair, List.length_singleton, Polynomial.eval_C, le_refl]

end PCP.Machine.ReferencePair
