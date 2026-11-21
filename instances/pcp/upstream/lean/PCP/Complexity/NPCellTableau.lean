/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Complexity.TableauCells
import PCP.Complexity.WitnessInputCells
import PCP.Complexity.NPTableau

/-!
# Concrete NP checking through bounded-width tableau cells

The witness is chosen by optional initial cells and adjacent blank checks. Every
subsequent row obeys the fixed-window cell constraints. The source checker's actual
time certificate and proved stack-growth bound discharge all time, space, and
terminal-length premises in the NP specialization.
-/

namespace PCP.Machine.NPCellTableau

open Turing ComputationTableau TableauCells

attribute [local instance] FinTM2.kDecidableEq FinTM2.kFin FinTM2.ΛFin FinTM2.σFin

/-- Input-stack symbols viewed in the fixed public bit/separator alphabet. -/
def inputView {tm : FinTM2} {B : ℕ} (e : tm.Γ tm.k₀ ≃ Sym) (s : Cells tm B) :
    Fin B → Option Sym := fun j => (readCell s tm.k₀ j.val).map e

@[simp] theorem read_inputView {tm : FinTM2} {B : ℕ} (e : tm.Γ tm.k₀ ≃ Sym)
    (s : Cells tm B) (j : ℕ) :
    WitnessInputCells.read (inputView e s) j = (readCell s tm.k₀ j).map e := by
  by_cases hj : j < B
  · simp [WitnessInputCells.read, inputView, hj]
  · simp [WitnessInputCells.read, readCell, hj]

/-- The initial controls and empty work stacks are fixed; witness positions are locally free. -/
def InputBoundary {tm : FinTM2} {B : ℕ} (e : tm.Γ tm.k₀ ≃ Sym)
    (x : List Bool) (W : ℕ) (p : Prefix tm) (s : Cells tm B) : Prop :=
  (decodeRow p).l = some tm.main ∧ (decodeRow p).var = tm.initialState ∧
    (∀ k, k ≠ tm.k₀ → ∀ j : Fin B, readCell s k j.val = none) ∧
    WitnessInputCells.Holds x W (inputView e s)

/-- Every satisfying input boundary represents one genuine bounded encoded witness. -/
theorem inputBoundary_exists {tm : FinTM2} {B : ℕ} {e : tm.Γ tm.k₀ ≃ Sym}
    {x : List Bool} {W : ℕ} {p : Prefix tm} {s : Cells tm B}
    (h : InputBoundary e x W p s) (hb : x.length + 1 + W ≤ B) :
    ∃ w : List Bool, w.length ≤ W ∧
      Represents p s (initList tm ((encodePair (x, w)).map e.symm)) := by
  obtain ⟨w, hw, hg⟩ := WitnessInputCells.exists_encoded h.2.2.2 hb
  refine ⟨w, hw, h.1, h.2.1, fun k j => ?_⟩
  by_cases hk : k = tm.k₀
  · subst k
    apply Option.map_injective e.injective
    rw [← read_inputView, hg]
    simp [initList, List.getElem?_map, Option.map_map]
  · have hn : readCell s k j = none := by
      by_cases hj : j < B
      · exact h.2.2.1 k hk ⟨j, hj⟩
      · exact readCell_of_ge s k j (by omega)
    simp [hn, initList, hk]

/-- A represented encoded bounded witness satisfies the unary and adjacent input checks. -/
theorem inputBoundary_of_represents {tm : FinTM2} {B : ℕ} {e : tm.Γ tm.k₀ ≃ Sym}
    {x w : List Bool} {W : ℕ} {p : Prefix tm} {s : Cells tm B}
    (hw : w.length ≤ W)
    (h : Represents p s (initList tm ((encodePair (x, w)).map e.symm))) :
    InputBoundary e x W p s := by
  refine ⟨h.1, h.2.1, ?_, ?_⟩
  · intro k hk j
    rw [h.2.2]
    simp [initList, hk]
  · apply WitnessInputCells.holds_of_encoded hw
    intro j
    rw [read_inputView, h.2.2]
    simp [initList, List.getElem?_map, Option.map_map]

/-- Local accepting tableau checks with existential initial witness cells. -/
def Satisfies (tm : FinTM2) (e : tm.Γ tm.k₀ ≃ Sym) (T B W : ℕ)
    (x : List Bool) (final : tm.Cfg) (a : TableauCells.Assignment tm T B) : Prop :=
  InputBoundary e x W (a.1 0) (a.2 0) ∧
    (∀ i, Linked (a.1 i) (a.2 i)) ∧
    (∀ i : Fin T, Step (a.1 i.castSucc) (a.1 i.succ) (a.2 i.castSucc) (a.2 i.succ)) ∧
    Boundary (a.1 (Fin.last T)) (a.2 (Fin.last T)) final

/-- Exact semantics of the locally checked existential witness and subsequent computation. -/
theorem exists_satisfies_iff (tm : FinTM2) (e : tm.Γ tm.k₀ ≃ Sym)
    (T B W : ℕ) (x : List Bool) (final : tm.Cfg)
    (hb : x.length + 1 + W + machinePushBound tm * T ≤ B)
    (hf : ∀ k, (final.stk k).length ≤ B) :
    (∃ a, Satisfies tm e T B W x final a) ↔
      ∃ w : List Bool, w.length ≤ W ∧
        boundedEval tm T (initList tm ((encodePair (x, w)).map e.symm)) = final := by
  constructor
  · rintro ⟨a, hi, hl, ht, he⟩
    obtain ⟨w, hw, hr⟩ := inputBoundary_exists hi (by omega)
    refine ⟨w, hw, TableauCells.satisfies_boundedEval
      ⟨represents_boundary hr, hl, ht, he⟩ ?_ hf⟩
    simp only [mass_initList, List.length_map, length_encodePair]
    omega
  · rintro ⟨w, hw, he⟩
    have hs := stackSupported_initList tm ((encodePair (x, w)).map e.symm)
    have hspace : mass (initList tm ((encodePair (x, w)).map e.symm)).stk +
        machinePushBound tm * T ≤ B := by
      simp only [mass_initList, List.length_map, length_encodePair]
      omega
    obtain ⟨a, hi, hl, ht, hf'⟩ :=
      (TableauCells.exists_satisfies_iff tm T B _ final hs hspace hf).mpr he
    refine ⟨a, ?_, hl, ht, hf'⟩
    apply inputBoundary_of_represents hw
    apply boundary_represents hi
    intro k
    have hm := stack_length_le_mass tm (initList tm ((encodePair (x, w)).map e.symm)) k
    omega

variable {R : List Bool → List Bool → Bool} (h : NPTableau.Checker R) (q : Polynomial ℕ)

/-- The accepting cell tableau at the actual checker's certified uniform budgets. -/
def Accepts (x : List Bool)
    (a : TableauCells.Assignment h.tm ((NPTableau.timePoly h q).eval x.length)
      ((NPTableau.spacePoly h q).eval x.length)) : Prop :=
  Satisfies h.tm h.inputAlphabet ((NPTableau.timePoly h q).eval x.length)
    ((NPTableau.spacePoly h q).eval x.length) (q.eval x.length) x
    (haltList h.tm (NPTableau.output h true)) a

/-- The concrete NP certificate discharges every growth and terminal-bound premise. -/
theorem exists_accepts_iff (x : List Bool) :
    (∃ a, Accepts h q x a) ↔
      ∃ w : List Bool, w.length ≤ q.eval x.length ∧ R x w = true := by
  unfold Accepts
  rw [exists_satisfies_iff]
  · apply exists_congr
    intro w
    apply and_congr_right
    intro hw
    exact (ComputationTableau.exists_satisfies_iff _ _ _ _ _
      (NPTableau.input_space_le h q hw)).symm.trans (NPTableau.exists_rows_iff h q hw)
  · rw [NPTableau.spacePoly_eval]
    omega
  · intro k
    apply (stack_length_le_mass h.tm _ k).trans
    rw [mass_haltList]
    simp only [NPTableau.output, encodeBool, List.length_map, List.length_cons, List.length_nil]
    rw [NPTableau.spacePoly_eval]
    omega

/-- Concrete NP is characterized by machine-fixed-alphabet, bounded-width cell constraints. -/
theorem of_certificate {L : PCP.Language} (cert : PCP.NPCertificate PolyTimeRel L) :
    ∃ h : NPTableau.Checker cert.check, ∀ x : List Bool,
      L x ↔ ∃ a, Accepts h cert.witnessBound x a := by
  obtain ⟨h⟩ := cert.check_polyTime
  exact ⟨h, fun x => (cert.spec x).trans (exists_accepts_iff h cert.witnessBound x).symm⟩

theorem of_inNP {L : PCP.Language} (hL : PCP.InNP PolyTimeRel L) :
    ∃ (R : List Bool → List Bool → Bool) (q : Polynomial ℕ) (h : NPTableau.Checker R),
      ∀ x : List Bool, L x ↔ ∃ a, Accepts h q x a := by
  obtain ⟨cert⟩ := hL
  obtain ⟨h, hh⟩ := of_certificate cert
  exact ⟨cert.check, cert.witnessBound, h, hh⟩

end PCP.Machine.NPCellTableau
