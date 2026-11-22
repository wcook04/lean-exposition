/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Complexity.ComputationTableau
import PCP.Complexity.Encoding
import PCP.Complexity.NP

/-!
# Uniform finite tableaux for `InNP Machine.PolyTimeRel`

A concrete polynomial-time witness checker supplies a finite tableau problem for
each input. Its time and space dimensions depend only on the input length, using
the checker's actual `FinTM2` time polynomial and the certificate's witness bound.
Satisfiability is proved equivalent to membership in the original language.
The combined witness and tableau have a proved polynomial symbol-count bound.

These are exact finite computation constraints. Their conversion to bounded-arity
constraints and three-color graphs is in `PCP/Reduction/NPThreeColor.lean`; the
certified polynomial-time reduction is `PCP.Reduction.NPThreeColorRuntime.of_inNP_program`.
-/

namespace PCP.Machine.NPTableau

open Turing ComputationTableau

attribute [local instance] FinTM2.kDecidableEq FinTM2.kFin FinTM2.ΛFin FinTM2.σFin

/-- Finite choice of a bitstring of any length up to `W`, including zero. -/
abbrev BoundedWitness (W : ℕ) := (n : Fin (W + 1)) × (Fin n.val → Bool)

def witnessList {W : ℕ} (w : BoundedWitness W) : List Bool := List.ofFn w.2

theorem witnessList_length_le {W : ℕ} (w : BoundedWitness W) :
    (witnessList w).length ≤ W := by
  simpa [witnessList] using Nat.le_of_lt_succ w.1.isLt

def packWitness {W : ℕ} (w : List Bool) (hw : w.length ≤ W) : BoundedWitness W :=
  ⟨⟨w.length, Nat.lt_succ_of_le hw⟩, w.get⟩

@[simp] theorem witnessList_packWitness {W : ℕ} (w : List Bool) (hw : w.length ≤ W) :
    witnessList (packWitness w hw) = w := List.ofFn_get w

variable {R : List Bool → List Bool → Bool}

/-- A certificate for the actual fixed pair and Boolean encodings. -/
abbrev Checker (R : List Bool → List Bool → Bool) :=
  TM2ComputableInPolyTime encodePair encodeBool (fun p => R p.1 p.2)

variable (h : Checker R) (q : Polynomial ℕ)

/-- Encoded input length for a witness of maximum permitted length. -/
noncomputable def inputPoly : Polynomial ℕ := Polynomial.X + q + 1

/-- One time bound for all witnesses of a given input. -/
noncomputable def timePoly : Polynomial ℕ := h.time.comp (inputPoly q)

/-- The source machine's proved stack-growth bound at that uniform time. -/
noncomputable def spacePoly : Polynomial ℕ :=
  inputPoly q + Polynomial.C (machinePushBound h.tm) * timePoly h q

/-- Witness bits and all tableau symbols, including control and delimiters. -/
noncomputable def sizePoly : Polynomial ℕ :=
  q + (timePoly h q + 1) *
    (2 + Polynomial.C (Fintype.card h.tm.K) * (spacePoly h q + 1))

@[simp] theorem inputPoly_eval (n : ℕ) : (inputPoly q).eval n = n + q.eval n + 1 := by
  simp [inputPoly]

@[simp] theorem timePoly_eval (n : ℕ) :
    (timePoly h q).eval n = h.time.eval (n + q.eval n + 1) := by
  simp [timePoly, Polynomial.eval_comp]

@[simp] theorem spacePoly_eval (n : ℕ) :
    (spacePoly h q).eval n = n + q.eval n + 1 +
      machinePushBound h.tm * (timePoly h q).eval n := by
  simp only [spacePoly, Polynomial.eval_add, inputPoly_eval, Polynomial.eval_mul,
    Polynomial.eval_C]

def input (x w : List Bool) : List (h.tm.Γ h.tm.k₀) :=
  (encodePair (x, w)).map h.inputAlphabet.symm

def output (b : Bool) : List (h.tm.Γ h.tm.k₁) :=
  (encodeBool b).map h.outputAlphabet.symm

theorem input_length_le {x w : List Bool} (hw : w.length ≤ q.eval x.length) :
    (input h x w).length ≤ (inputPoly q).eval x.length := by
  simp only [input, List.length_map, length_encodePair, inputPoly_eval]
  omega

theorem checker_time_le {x w : List Bool} (hw : w.length ≤ q.eval x.length) :
    h.time.eval (encodePair (x, w)).length ≤ (timePoly h q).eval x.length := by
  rw [timePoly_eval]
  apply eval_mono h.time
  simpa only [length_encodePair] using
    Nat.add_le_add_right (Nat.add_le_add_left hw x.length) 1

theorem input_space_le {x w : List Bool} (hw : w.length ≤ q.eval x.length) :
    (input h x w).length + machinePushBound h.tm * (timePoly h q).eval x.length ≤
      (spacePoly h q).eval x.length := by
  rw [spacePoly_eval]
  exact Nat.add_le_add_right (by simpa using input_length_le h q hw) _

/-- The entire quantified witness type is finite; no unbounded configurations occur. -/
abbrev Assignment (x : List Bool) :=
  BoundedWitness (q.eval x.length) ×
    (Fin ((timePoly h q).eval x.length + 1) → Row h.tm ((spacePoly h q).eval x.length))

instance assignmentFinite (x : List Bool) : Finite (Assignment h q x) := inferInstance

/-- Check the actual machine's initial, adjacent and accepting final configurations. -/
def Accepts (x : List Bool) (a : Assignment h q x) : Prop :=
  Satisfies h.tm ((timePoly h q).eval x.length) ((spacePoly h q).eval x.length)
    (input h x (witnessList a.1)) (output h true) a.2

private theorem haltList_injective (tm : FinTM2) : Function.Injective (haltList tm) := by
  intro a b heq
  have hs := congrArg (fun c : tm.Cfg => c.stk tm.k₁) heq
  simpa [haltList] using hs

private theorem output_injective : Function.Injective (output h) := by
  intro a b heq
  exact encodeBool_injective ((List.map_injective_iff.mpr h.outputAlphabet.symm.injective) heq)

/-- The finite tableau accepts exactly the checker's true result for each bounded witness. -/
theorem exists_rows_iff {x w : List Bool} (hw : w.length ≤ q.eval x.length) :
    (∃ rows, Satisfies h.tm ((timePoly h q).eval x.length) ((spacePoly h q).eval x.length)
      (input h x w) (output h true) rows) ↔ R x w = true := by
  rw [exists_satisfies_iff _ _ _ _ _ (input_space_le h q hw)]
  have hout := boundedEval_initList (h.outputsFun (x, w)) (checker_time_le h q hw)
  change boundedEval h.tm ((timePoly h q).eval x.length) (initList h.tm (input h x w)) =
    haltList h.tm (output h (R x w)) at hout
  rw [hout]
  constructor
  · intro heq
    exact output_injective h (haltList_injective h.tm heq)
  · intro heq
    rw [heq]

/-- Satisfiability of the finite constraints is exactly existence of a bounded accepting witness. -/
theorem exists_accepts_iff (x : List Bool) :
    (∃ a : Assignment h q x, Accepts h q x a) ↔
      ∃ w : List Bool, w.length ≤ q.eval x.length ∧ R x w = true := by
  constructor
  · rintro ⟨⟨w, rows⟩, ha⟩
    have hw := witnessList_length_le w
    exact ⟨witnessList w, hw, (exists_rows_iff h q hw).mp ⟨rows, ha⟩⟩
  · rintro ⟨w, hw, hR⟩
    obtain ⟨rows, hrows⟩ := (exists_rows_iff h q hw).mpr hR
    refine ⟨⟨packWitness w hw, rows⟩, ?_⟩
    simpa only [Accepts, witnessList_packWitness] using hrows

/-- The actual represented witness and rows obey one polynomial symbol-count bound. -/
theorem assignment_size_le (x : List Bool) (a : Assignment h q x) :
    (witnessList a.1).length + tableauSize a.2 ≤ (sizePoly h q).eval x.length := by
  have hw := witnessList_length_le a.1
  have ht := tableauSize_le a.2
  simp only [sizePoly, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_one, Polynomial.eval_ofNat, Polynomial.eval_C]
  exact Nat.add_le_add hw ht

/-- Every concrete NP certificate yields the finite tableau characterization. -/
theorem of_certificate {L : PCP.Language} (cert : PCP.NPCertificate PolyTimeRel L) :
    ∃ h : Checker cert.check, ∀ x : List Bool,
      L x ↔ ∃ a : Assignment h cert.witnessBound x, Accepts h cert.witnessBound x a := by
  obtain ⟨h⟩ := cert.check_polyTime
  exact ⟨h, fun x => (cert.spec x).trans (exists_accepts_iff h cert.witnessBound x).symm⟩

/-- The forward bridge is stated for the concrete `FinTM2` definition of NP. -/
theorem of_inNP {L : PCP.Language} (hL : PCP.InNP PolyTimeRel L) :
    ∃ (R : List Bool → List Bool → Bool) (q : Polynomial ℕ) (h : Checker R),
      ∀ x : List Bool, L x ↔ ∃ a : Assignment h q x, Accepts h q x a := by
  obtain ⟨cert⟩ := hL
  obtain ⟨h, hh⟩ := of_certificate cert
  exact ⟨cert.check, cert.witnessBound, h, hh⟩

end PCP.Machine.NPTableau
