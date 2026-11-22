/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Reduction.NPThreeColor
import PCP.Reduction.NPTableauGraphLang
import PCP.Complexity.PolynomialPrefixLang
import PCP.Complexity.LangConstant
import PCP.Complexity.LangSymbolBridge

/-!
# Concrete polynomial-time reduction from NP to encoded three-colorability

Fixed polynomial-budget preprocessing, the genuine finite-machine tableau source
emitter, and the complete graph constructor form one actual language program.
The proved compiler and public-symbol codecs give a `PolyTimeMap` in the original
`FinTM2` model. No construction-time or reduction-correctness premise is assumed.
-/

namespace PCP.Reduction.NPThreeColorRuntime

open Turing Machine Machine.ComputationTableau Machine.NPTableau Machine.TableauConstraints
open PCP.Lang

attribute [local instance] FinTM2.kDecidableEq FinTM2.kFin FinTM2.ΛFin FinTM2.σFin

variable {R : List Bool → List Bool → Bool} (h : Checker R) (q : Polynomial ℕ)

open Polynomial in
noncomputable def costPoly (k A C D : ℕ) : Polynomial ℕ :=
  Polynomial.C A * (2 * X + 1) ^ 2 +
    Polynomial.C C * (Polynomial.C A * (2 * X + 1) +
      NPThreeColor.variablesPoly h q k + NPThreeColor.constraintsPoly h q k + 1) ^ 6 +
    Polynomial.C A * (2 * X + 1) +
    Polynomial.C D *
      (NPThreeColor.variablesPoly h q k + NPThreeColor.constraintsPoly h q k + 1) ^ 2 + 5

open Polynomial in
noncomputable def sizePoly (k D : ℕ) : Polynomial ℕ :=
  Polynomial.C D * (NPThreeColor.variablesPoly h q k + NPThreeColor.constraintsPoly h q k + 1) ^ 2

section Supported

variable [DecidableEq h.tm.Λ] [DecidableEq h.tm.σ]
  [(k : h.tm.K) → DecidableEq (Symbol h.tm k)]
  (hs : StackSupported h.tm (haltList h.tm (output h true)).stk)
  {k a : ℕ} (eK : h.tm.K ≃ Fin k) (eA : Alphabet h.tm ≃ Fin a)

noncomputable def encode (x : List Bool) : List Bool :=
  NPTableauGraphLang.encode h hs eK eA
    (T := (timePoly h q).eval x.length) (W := q.eval x.length) x
    (Machine.NPCellConstraints.accepting_length_le h q x)

/-- The algorithm's actual encoded graph is colorable exactly for bounded-witness acceptance. -/
theorem decode_colorable_iff (x : List Bool) :
    (Algebraic.ThreeColorEncoding.graph (encode h q hs eK eA x)).Colorable 3 ↔
      ∃ w : List Bool, w.length ≤ q.eval x.length ∧ R x w = true := by
  rw [encode, NPTableauGraphLang.decode_colorable_iff]
  exact Machine.NPCellConstraints.satisfiable_accepts_iff h q hs x

/-- The full bit-input construction has one program and proved polynomial cost and output size. -/
theorem exists_program : ∃ (P : Prog) (pc ps : Polynomial ℕ), ∀ x : List Bool,
    P.run (x.map Bool.toNat) = (encode h q hs eK eA x).map Bool.toNat ∧
    P.cost (x.map Bool.toNat) ≤ pc.eval x.length ∧
    listSize (P.run (x.map Bool.toNat)) ≤ ps.eval x.length := by
  obtain ⟨P, A, hP⟩ := PolynomialPrefix.exists_program (timePoly h q) (spacePoly h q) q
  obtain ⟨C, D, hcore⟩ := NPTableauGraphLang.program_bounds h hs eK eA
  refine ⟨P.compose (NPTableauGraphLang.program h hs eK eA), costPoly h q k A C D,
    sizePoly h q k D, fun x => ?_⟩
  let input := x.map Bool.toNat
  let source := Machine.NPTableauSource.input ((timePoly h q).eval x.length)
    ((spacePoly h q).eval x.length) (q.eval x.length) x
  let v := (NPThreeColor.variablesPoly h q k).eval x.length
  let c := (NPThreeColor.constraintsPoly h q k).eval x.length
  have hp := hP input
  have hrun : P.run input = source := by
    simpa only [input, source, List.length_map, Machine.NPTableauSource.input] using hp.1
  have hh := hcore ((timePoly h q).eval x.length) ((spacePoly h q).eval x.length)
    (q.eval x.length) x (Machine.NPCellConstraints.accepting_length_le h q x)
  have hcost : (NPTableauGraphLang.program h hs eK eA).cost source ≤
      C * (listSize source + v + c + 1) ^ 6 := by
    simpa only [source, v, c, NPThreeColor.variablesPoly_eval, NPThreeColor.constraintsPoly_eval,
      TableauNumericIndex.variableCount, TableauNumericIndex.constraints,
      TableauNumericIndex.boundaryOffset, TableauNumericIndex.links, TableauNumericIndex.sites]
      using hh.1
  have hsize : listSize ((NPTableauGraphLang.program h hs eK eA).run source) ≤
      D * (v + c + 1) ^ 2 := by
    simpa only [source, v, c, NPThreeColor.variablesPoly_eval, NPThreeColor.constraintsPoly_eval,
      TableauNumericIndex.variableCount, TableauNumericIndex.constraints,
      TableauNumericIndex.boundaryOffset, TableauNumericIndex.links, TableauNumericIndex.sites]
      using hh.2
  have hin : listSize input ≤ 2 * x.length := BooleanGraphLang.bitList_size_le x
  have hpre : P.cost input ≤ A * (2 * x.length + 1) ^ 2 :=
    hp.2.1.trans (Nat.mul_le_mul_left A (Nat.pow_le_pow_left (by omega) 2))
  have hsource : listSize source ≤ A * (2 * x.length + 1) := by
    rw [← hrun]
    exact hp.2.2.trans (Nat.mul_le_mul_left A (by omega))
  have hcost' : (NPTableauGraphLang.program h hs eK eA).cost source ≤
      C * (A * (2 * x.length + 1) + v + c + 1) ^ 6 :=
    hcost.trans (Nat.mul_le_mul_left C (Nat.pow_le_pow_left (by omega) 6))
  refine ⟨?_, ?_, ?_⟩
  · rw [Prog.run_compose, hrun]
    exact NPTableauGraphLang.program_run h hs eK eA x
      (Machine.NPCellConstraints.accepting_length_le h q x)
  · rw [Prog.cost_compose, hrun]
    change P.cost input + (NPTableauGraphLang.program h hs eK eA).cost source +
      listSize source + listSize ((NPTableauGraphLang.program h hs eK eA).run source) + 5 ≤ _
    calc
      _ ≤ A * (2 * x.length + 1) ^ 2 +
          C * (A * (2 * x.length + 1) + v + c + 1) ^ 6 +
          A * (2 * x.length + 1) + D * (v + c + 1) ^ 2 + 5 := by omega
      _ = (costPoly h q k A C D).eval x.length := by simp [costPoly, v, c]
  · rw [Prog.run_compose, hrun]
    simpa only [sizePoly, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
      Polynomial.eval_add, Polynomial.eval_one] using hsize

end Supported

/-- Public bitstrings and the language program use the same zero/one values. -/
theorem code_ofBits (x : List Bool) : LangSymbolBridge.code (ofBits x) = x.map Bool.toNat := by
  simp only [LangSymbolBridge.code, ofBits, List.map_map]
  congr 1
  funext b
  cases b <;> rfl

section SupportedCertificate

variable [DecidableEq h.tm.Λ] [DecidableEq h.tm.σ]
  [(k : h.tm.K) → DecidableEq (Symbol h.tm k)]
  (hs : StackSupported h.tm (haltList h.tm (output h true)).stk)
  {k a : ℕ} (eK : h.tm.K ≃ Fin k) (eA : Alphabet h.tm ≃ Fin a)

/-- An actual `FinTM2` realizes the complete construction at the unchanged public bit encoding. -/
theorem polyTimeMap : PolyTimeMap ofBits ofBits (encode h q hs eK eA) := by
  obtain ⟨P, pc, _, hP⟩ := exists_program h q hs eK eA
  obtain ⟨C, d, hC⟩ := PolynomialPrefix.exists_eval_bound pc
  apply LangSymbolBridge.polyTimeMap_of_program ofBits ofBits (encode h q hs eK eA)
    P (PCP.Lang.compile P)
  · intro x
    simpa only [code_ofBits] using (hP x).1
  · intro x
    simpa only [code_ofBits, length_ofBits] using ((hP x).2.1.trans (hC x.length))

/-- The computed encoded graph has polynomial bit length. -/
theorem length_encode_le : ∃ p : Polynomial ℕ, ∀ x : List Bool,
    (encode h q hs eK eA x).length ≤ p.eval x.length := by
  obtain ⟨P, _, ps, hP⟩ := exists_program h q hs eK eA
  refine ⟨ps, fun x => ?_⟩
  have hh := (length_le_listSize (P.run (x.map Bool.toNat))).trans (hP x).2.2
  simpa only [(hP x).1, List.length_map] using hh

end SupportedCertificate

/-- Fixed graph outputs also have a concrete machine certificate, including the rejecting case. -/
theorem polyTimeMap_constant (s : List Bool) :
    PolyTimeMap ofBits ofBits (fun _ : List Bool => s) := by
  let P := Constant.program (s.map Bool.toNat)
  apply LangSymbolBridge.polyTimeMap_of_program ofBits ofBits (fun _ => s) P (PCP.Lang.compile P)
    (c₁ := 3 * listSize (s.map Bool.toNat) + (s.map Bool.toNat).length + 1) (k₁ := 0)
  · intro x
    simpa only [code_ofBits, P] using Constant.program_run (s.map Bool.toNat) (x.map Bool.toNat)
  · intro x
    simp only [P, Constant.program_cost, pow_zero, Nat.mul_one, le_refl]

include h in
/-- Each concrete NP checker has an unconditional polynomial-time graph reduction. -/
theorem checker_reduction : ∃ (f : List Bool → List Bool) (p : Polynomial ℕ),
    PolyTimeMap ofBits ofBits f ∧ ∀ x : List Bool,
      ((Algebraic.ThreeColorEncoding.graph (f x)).Colorable 3 ↔
        ∃ w : List Bool, w.length ≤ q.eval x.length ∧ R x w = true) ∧
      (f x).length ≤ p.eval x.length := by
  classical
  by_cases hs : StackSupported h.tm (haltList h.tm (output h true)).stk
  · let : Fintype (Alphabet h.tm) := Fintype.ofFinite _
    let eK := Fintype.equivFin h.tm.K
    let eA := Fintype.equivFin (Alphabet h.tm)
    obtain ⟨p, hp⟩ := length_encode_le h q hs eK eA
    exact ⟨encode h q hs eK eA, p, polyTimeMap h q hs eK eA,
      fun x => ⟨decode_colorable_iff h q hs eK eA x, hp x⟩⟩
  · refine ⟨fun _ => NPThreeColor.rejectingEncoding,
      Polynomial.C NPThreeColor.rejectingEncoding.length,
      polyTimeMap_constant NPThreeColor.rejectingEncoding, fun x => ?_⟩
    constructor
    · constructor
      · intro hcolor
        exact (NPThreeColor.rejectingEncoding_not_colorable hcolor).elim
      · rintro ⟨w, _, hR⟩
        exact (Machine.NPCellConstraints.never_accepts_of_unsupported h hs x w hR).elim
    · simp

/-- Concrete NP certificates reduce to the actual encoded graph language in polynomial time. -/
theorem of_certificate {L : PCP.Language} (cert : PCP.NPCertificate PolyTimeRel L) :
    ∃ (f : List Bool → List Bool) (p : Polynomial ℕ), PolyTimeMap ofBits ofBits f ∧
      ∀ x : List Bool, ((Algebraic.ThreeColorEncoding.graph (f x)).Colorable 3 ↔ L x) ∧
        (f x).length ≤ p.eval x.length := by
  obtain ⟨h⟩ := cert.check_polyTime
  obtain ⟨f, p, htime, hf⟩ := checker_reduction h cert.witnessBound
  exact ⟨f, p, htime, fun x => ⟨(hf x).1.trans (cert.spec x).symm, (hf x).2⟩⟩

/-- Every language in the repository's concrete NP model has the certified graph reduction. -/
theorem of_inNP {L : PCP.Language} (hL : PCP.InNP PolyTimeRel L) :
    ∃ (f : List Bool → List Bool) (p : Polynomial ℕ), PolyTimeMap ofBits ofBits f ∧
      ∀ x : List Bool, ((Algebraic.ThreeColorEncoding.graph (f x)).Colorable 3 ↔ L x) ∧
        (f x).length ≤ p.eval x.length := by
  obtain ⟨cert⟩ := hL
  exact of_certificate cert


include h in
/-- The concrete reduction retains its exact language program for verifier composition. -/
theorem checker_program_reduction :
    ∃ (f : List Bool → List Bool) (p : Polynomial ℕ) (P : Prog) (C d : ℕ),
      ∀ x : List Bool,
        P.run (x.map Bool.toNat) = (f x).map Bool.toNat ∧
        P.cost (x.map Bool.toNat) ≤ C * (x.length + 1) ^ d ∧
        ((Algebraic.ThreeColorEncoding.graph (f x)).Colorable 3 ↔
          ∃ w : List Bool, w.length ≤ q.eval x.length ∧ R x w = true) ∧
        (f x).length ≤ p.eval x.length := by
  classical
  by_cases hs : StackSupported h.tm (haltList h.tm (output h true)).stk
  · let : Fintype (Alphabet h.tm) := Fintype.ofFinite _
    let eK := Fintype.equivFin h.tm.K
    let eA := Fintype.equivFin (Alphabet h.tm)
    obtain ⟨P, pc, ps, hP⟩ := exists_program h q hs eK eA
    obtain ⟨C, d, hC⟩ := PolynomialPrefix.exists_eval_bound pc
    refine ⟨encode h q hs eK eA, ps, P, C, d, fun x => ?_⟩
    refine ⟨(hP x).1, (hP x).2.1.trans (hC x.length),
      decode_colorable_iff h q hs eK eA x, ?_⟩
    have hh := (length_le_listSize (P.run (x.map Bool.toNat))).trans (hP x).2.2
    simpa only [(hP x).1, List.length_map] using hh
  · let s := NPThreeColor.rejectingEncoding
    refine ⟨fun _ => s, Polynomial.C s.length, Constant.program (s.map Bool.toNat),
      3 * listSize (s.map Bool.toNat) + (s.map Bool.toNat).length + 1, 0, fun x => ?_⟩
    refine ⟨Constant.program_run _ _, ?_, ?_, by simp⟩
    · simp only [Constant.program_cost, pow_zero, Nat.mul_one, le_refl]
    · constructor
      · intro hcolor
        exact (NPThreeColor.rejectingEncoding_not_colorable hcolor).elim
      · rintro ⟨w, _, hR⟩
        exact (Machine.NPCellConstraints.never_accepts_of_unsupported h hs x w hR).elim

/-- Program-bearing NP certificate reduction, ready for actual verifier preprocessing. -/
theorem of_certificate_program {L : PCP.Language} (cert : PCP.NPCertificate PolyTimeRel L) :
    ∃ (f : List Bool → List Bool) (p : Polynomial ℕ) (P : Prog) (C d : ℕ),
      ∀ x : List Bool,
        P.run (x.map Bool.toNat) = (f x).map Bool.toNat ∧
        P.cost (x.map Bool.toNat) ≤ C * (x.length + 1) ^ d ∧
        ((Algebraic.ThreeColorEncoding.graph (f x)).Colorable 3 ↔ L x) ∧
        (f x).length ≤ p.eval x.length := by
  obtain ⟨h⟩ := cert.check_polyTime
  obtain ⟨f, p, P, C, d, hf⟩ := checker_program_reduction h cert.witnessBound
  refine ⟨f, p, P, C, d, fun x => ?_⟩
  exact ⟨(hf x).1, (hf x).2.1, (hf x).2.2.1.trans (cert.spec x).symm, (hf x).2.2.2⟩

/-- Every concrete NP language has a certified program computing its encoded graph reduction. -/
theorem of_inNP_program {L : PCP.Language} (hL : PCP.InNP PolyTimeRel L) :
    ∃ (f : List Bool → List Bool) (p : Polynomial ℕ) (P : Prog) (C d : ℕ),
      ∀ x : List Bool,
        P.run (x.map Bool.toNat) = (f x).map Bool.toNat ∧
        P.cost (x.map Bool.toNat) ≤ C * (x.length + 1) ^ d ∧
        ((Algebraic.ThreeColorEncoding.graph (f x)).Colorable 3 ↔ L x) ∧
        (f x).length ≤ p.eval x.length := by
  obtain ⟨cert⟩ := hL
  exact of_certificate_program cert

end PCP.Reduction.NPThreeColorRuntime
