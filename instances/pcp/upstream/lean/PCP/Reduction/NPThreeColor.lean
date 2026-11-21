/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Complexity.NPCellConstraints
import PCP.Complexity.TableauIndex
import PCP.Reduction.FiniteAlphabetEncoding

/-!
# Polynomial-size three-color graph encodings for concrete NP

This assembles the real `FinTM2` witness checker, its bounded-window cell tableau,
finite lookup clauses, explicit graph gadgets, and the verifier's bitstring codec.
The resulting graph is three-colorable exactly on the source language, with a
proved polynomial output-length bound. Machine-dependent alphabet enumerations
are chosen once; every input-sized index uses arithmetic sum/product codecs.

This is a semantic reduction with a size bound, and no construction time is
claimed here. The certified polynomial-time reduction used by the final theorem is
`PCP.Reduction.NPThreeColorRuntime.of_inNP_program`, which reuses this module's size
polynomials and emits its graph through the executable `NPTableauGraphLang` program.
-/

namespace PCP.Reduction.NPThreeColor

open Turing Machine Machine.ComputationTableau Machine.NPTableau
  Machine.TableauConstraints

attribute [local instance] FinTM2.kDecidableEq FinTM2.kFin FinTM2.ΛFin FinTM2.σFin

variable {R : List Bool → List Bool → Bool} (h : Checker R) (q : Polynomial ℕ)

open Polynomial in
/-- Exact polynomial count of prefix and cell variables, including the blank variable. -/
noncomputable def variablesPoly (k : ℕ) : Polynomial ℕ :=
  (timePoly h q + 1) * (1 + C k * spacePoly h q) + 1

open Polynomial in
/-- Exact polynomial count of transition, boundary, and adjacent-witness constraints. -/
noncomputable def constraintsPoly (k : ℕ) : Polynomial ℕ :=
  1 + (timePoly h q + 1) * C (k * TM2Locality.machineWindow h.tm) + timePoly h q +
    timePoly h q * (C k * spacePoly h q) + 2 * (1 + C k * spacePoly h q) + q

@[simp] theorem variablesPoly_eval (k n : ℕ) :
    (variablesPoly h q k).eval n =
      ((timePoly h q).eval n + 1) * (1 + k * (spacePoly h q).eval n) + 1 := by
  simp [variablesPoly]

@[simp] theorem constraintsPoly_eval (k n : ℕ) :
    (constraintsPoly h q k).eval n =
      1 + ((timePoly h q).eval n + 1) * (k * TM2Locality.machineWindow h.tm) +
      (timePoly h q).eval n + (timePoly h q).eval n * (k * (spacePoly h q).eval n) +
      2 * (1 + k * (spacePoly h q).eval n) + q.eval n := by
  simp [constraintsPoly]

/-- The output polynomial retains only constants fixed by the source checker and witness bound. -/
noncomputable def outputPoly (k a : ℕ) : Polynomial ℕ :=
  FiniteDomainEncoding.outputPoly a (arity h.tm) (variablesPoly h q k) (constraintsPoly h q k)

section Supported

variable [DecidableEq h.tm.Λ] [DecidableEq h.tm.σ]
  [(k : h.tm.K) → DecidableEq (Symbol h.tm k)]
  (hs : StackSupported h.tm (haltList h.tm (output h true)).stk)
  {k a : ℕ} (eK : h.tm.K ≃ Fin k) (eA : Alphabet h.tm ≃ Fin a)

/-- The assembled graph encoder uses the actual local checker relation and arithmetic indices. -/
noncomputable def encode (x : List Bool) : List Bool :=
  FiniteAlphabetEncoding.encode eA
    (TableauIndex.variableCode eK ((timePoly h q).eval x.length) ((spacePoly h q).eval x.length))
    (TableauIndex.withWitnessCode eK ((timePoly h q).eval x.length)
      ((spacePoly h q).eval x.length) (q.eval x.length))
    (NPCellConstraints.relation h.inputAlphabet x
      (NPCellConstraints.finalRow h ((spacePoly h q).eval x.length) hs
        (NPCellConstraints.accepting_length_le h q x)))
    (NPCellConstraints.scope x)

/-- Decoding the produced bitstring preserves exactly bounded-witness acceptance. -/
theorem decode_colorable_iff (x : List Bool) :
    (Algebraic.ThreeColorEncoding.graph (encode h q hs eK eA x)).Colorable 3 ↔
      ∃ w : List Bool, w.length ≤ q.eval x.length ∧ R x w = true := by
  rw [encode, FiniteAlphabetEncoding.decode_colorable_iff]
  simp only [NPCellConstraints.relation_eq_true]
  exact NPCellConstraints.satisfiable_accepts_iff h q hs x

/-- The actual encoded adjacency matrix has a uniform polynomial bit length. -/
theorem length_encode_le (x : List Bool) :
    (encode h q hs eK eA x).length ≤ (outputPoly h q k a).eval x.length := by
  unfold encode outputPoly
  apply FiniteAlphabetEncoding.length_encode_le_polynomial
  · simp
  · simp

end Supported

/-- A fixed contradiction supplies the graph in the uniformly rejecting checker case. -/
def rejectingEncoding : List Bool :=
  FiniteBooleanEncoding.encode (v := 0) (c := 1) (k := 0)
    (fun _ _ => false) (fun _ i => Fin.elim0 i)

theorem rejectingEncoding_not_colorable :
    ¬(Algebraic.ThreeColorEncoding.graph rejectingEncoding).Colorable 3 := by
  rw [rejectingEncoding, FiniteBooleanEncoding.decode_colorable_iff]
  rintro ⟨b, hb⟩
  have hfalse := hb (0 : Fin 1)
  contradiction

include h in
/-- Each concrete checker gives one polynomial-size graph map, even if it never accepts. -/
theorem checker_reduction :
    ∃ (f : List Bool → List Bool) (p : Polynomial ℕ), ∀ x : List Bool,
      ((Algebraic.ThreeColorEncoding.graph (f x)).Colorable 3 ↔
        ∃ w : List Bool, w.length ≤ q.eval x.length ∧ R x w = true) ∧
      (f x).length ≤ p.eval x.length := by
  classical
  by_cases hs : StackSupported h.tm (haltList h.tm (output h true)).stk
  · let : Fintype (Alphabet h.tm) := Fintype.ofFinite _
    let eK := Fintype.equivFin h.tm.K
    let eA := Fintype.equivFin (Alphabet h.tm)
    refine ⟨encode h q hs eK eA,
      outputPoly h q (Fintype.card h.tm.K) (Fintype.card (Alphabet h.tm)), fun x => ?_⟩
    exact ⟨decode_colorable_iff h q hs eK eA x, length_encode_le h q hs eK eA x⟩
  · refine ⟨fun _ => rejectingEncoding, Polynomial.C rejectingEncoding.length, fun x => ?_⟩
    constructor
    · constructor
      · intro hcolor
        exact (rejectingEncoding_not_colorable hcolor).elim
      · rintro ⟨w, _, hR⟩
        exact (NPCellConstraints.never_accepts_of_unsupported h hs x w hR).elim
    · simp

/-- Exact language reduction and polynomial output size for an actual NP certificate. -/
theorem of_certificate {L : PCP.Language} (cert : PCP.NPCertificate PolyTimeRel L) :
    ∃ (f : List Bool → List Bool) (p : Polynomial ℕ), ∀ x : List Bool,
      ((Algebraic.ThreeColorEncoding.graph (f x)).Colorable 3 ↔ L x) ∧
      (f x).length ≤ p.eval x.length := by
  obtain ⟨h⟩ := cert.check_polyTime
  obtain ⟨f, p, hf⟩ := checker_reduction h cert.witnessBound
  exact ⟨f, p, fun x => ⟨(hf x).1.trans (cert.spec x).symm, (hf x).2⟩⟩

/-- Concrete NP has polynomial-size three-color encodings; construction time is not claimed
here (see `NPThreeColorRuntime`). -/
theorem of_inNP {L : PCP.Language} (hL : PCP.InNP PolyTimeRel L) :
    ∃ (f : List Bool → List Bool) (p : Polynomial ℕ), ∀ x : List Bool,
      ((Algebraic.ThreeColorEncoding.graph (f x)).Colorable 3 ↔ L x) ∧
      (f x).length ≤ p.eval x.length := by
  obtain ⟨cert⟩ := hL
  exact of_certificate cert

end PCP.Reduction.NPThreeColor
