/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Complexity.NPTableauSource
import PCP.Reduction.FiniteDomainGraphLang

/-!
# Executable graph construction from a bounded concrete checker tableau

One fixed program constructs all local constraints, expands their fixed finite
alphabet, and emits the actual encoded adjacency matrix. Both satisfiability and
polynomial charged cost are proved for the same program.
-/

namespace PCP.Reduction.NPTableauGraphLang

open Turing Machine Machine.ComputationTableau Machine.TableauConstraints Machine.NPTableauSource
open PCP.Lang

attribute [local instance] FinTM2.kDecidableEq FinTM2.kFin FinTM2.ΛFin FinTM2.σFin

variable {R : List Bool → List Bool → Bool} (h : Machine.NPTableau.Checker R)
  [DecidableEq h.tm.Λ] [DecidableEq h.tm.σ]
  [(k : h.tm.K) → DecidableEq (Symbol h.tm k)]
  (hs : StackSupported h.tm (haltList h.tm (Machine.NPTableau.output h true)).stk)
  {k a T B W : ℕ} (eK : h.tm.K ≃ Fin k) (eA : Alphabet h.tm ≃ Fin a)

def program : Prog :=
  (Machine.TableauSourceLang.program (parameters h hs eK eA)).compose
    (FiniteDomainGraphLang.program a (arity h.tm))

def encode (x : List Bool)
    (hb : ∀ s, ((haltList h.tm (Machine.NPTableau.output h true)).stk s).length ≤ B) : List Bool :=
  FiniteDomainGraphLang.encode (indexedRelation h hs eK eA (T := T) (W := W) x hb)
    (indexedScope h eK x)

/-- The same fixed program constructs the entire encoded graph. -/
theorem program_run (x : List Bool)
    (hb : ∀ s, ((haltList h.tm (Machine.NPTableau.output h true)).stk s).length ≤ B) :
    (program h hs eK eA).run (input T B W x) =
      (encode h hs eK eA (T := T) (W := W) x hb).map Bool.toNat := by
  rw [program, Prog.run_compose, Machine.NPTableauSource.program_run h hs eK eA x hb,
    FiniteDomainGraphLang.program_run]
  rfl

/-- Three-colorability of the actual output is exactly satisfiability of the checker tableau. -/
theorem decode_colorable_iff (x : List Bool)
    (hb : ∀ s, ((haltList h.tm (Machine.NPTableau.output h true)).stk s).length ≤ B) :
    (Algebraic.ThreeColorEncoding.graph (encode h hs eK eA (T := T) (W := W) x hb)).Colorable 3 ↔
      ∃ f, Machine.NPCellConstraints.Holds (T := T) (W := W) h.inputAlphabet x
        (Machine.NPCellConstraints.finalRow h B hs hb) f := by
  rw [encode, FiniteDomainGraphLang.decode_colorable_iff]
  exact indexed_satisfiable_iff h hs eK eA x hb

/-- Polynomial cost and stored output size, with constants fixed by the checker alone. -/
theorem program_bounds : ∃ C D : ℕ, ∀ (T B W : ℕ) (x : List Bool)
    (_hb : ∀ s, ((haltList h.tm (Machine.NPTableau.output h true)).stk s).length ≤ B),
    let v := Machine.TableauNumericIndex.variableCount k T B
    let c := Machine.TableauNumericIndex.constraints k
      (Machine.TM2Locality.machineWindow h.tm) T B + W
    (program h hs eK eA).cost (input T B W x) ≤
        C * (listSize (input T B W x) + v + c + 1) ^ 6 ∧
      listSize ((program h hs eK eA).run (input T B W x)) ≤ D * (v + c + 1) ^ 2 := by
  let p := parameters h hs eK eA
  obtain ⟨A, hA⟩ := Machine.TableauSourceLang.program_cost p
  obtain ⟨B₀, hB⟩ := FiniteDomainGraphLang.program_cost a (arity h.tm)
  obtain ⟨D, hD⟩ := FiniteDomainGraphLang.output_size a (arity h.tm)
  let w := Machine.TableauSourceLang.width p
  refine ⟨A * (w + 5) ^ 3 + B₀ + (w + 4) + D + 5, D, fun T B W x hb => ?_⟩
  let v := Machine.TableauNumericIndex.variableCount k T B
  let c := Machine.TableauNumericIndex.constraints k
      (Machine.TM2Locality.machineWindow h.tm) T B + W
  let source := input T B W x
  let R₀ := indexedRelation h hs eK eA (T := T) (W := W) x hb
  let s₀ := indexedScope h eK (T := T) (B := B) (W := W) x
  let M := listSize source + v + c + 1
  have hM : 1 ≤ M := by dsimp [M]; omega
  have hvc : v + c + 1 ≤ M := by dsimp [M]; omega
  have hfirst := hA source
  have hsecond := hB v c R₀ s₀
  have hsize := FiniteDomainLang.source_size_le R₀ s₀
  have hout := hD v c R₀ s₀
  have hexact : (Machine.TableauSourceLang.program p).run source =
      FiniteDomainSource.source R₀ s₀ := Machine.NPTableauSource.program_run h hs eK eA x hb
  have hcount : Machine.TableauSourceLang.outputLength p source = 2 + c * w := rfl
  have hbase : listSize source + (2 + c * w) + 2 ≤ (w + 5) * M := by
    have hc : c ≤ M := by dsimp [M]; omega
    have hS : listSize source ≤ M := by dsimp [M]; omega
    nlinarith
  have h36 : M ^ 3 ≤ M ^ 6 := Nat.pow_le_pow_right hM (by decide)
  have h26 : M ^ 2 ≤ M ^ 6 := Nat.pow_le_pow_right hM (by decide)
  have hcostFirst : (Machine.TableauSourceLang.program p).cost source ≤
      A * (w + 5) ^ 3 * M ^ 6 := by
    rw [hcount] at hfirst
    calc
      _ ≤ A * (listSize source + (2 + c * w) + 2) ^ 3 := hfirst
      _ ≤ A * ((w + 5) * M) ^ 3 := Nat.mul_le_mul_left A (Nat.pow_le_pow_left hbase 3)
      _ = A * (w + 5) ^ 3 * M ^ 3 := by ring
      _ ≤ _ := Nat.mul_le_mul_left _ h36
  have hcostSecond : (FiniteDomainGraphLang.program a (arity h.tm)).cost
      (FiniteDomainSource.source R₀ s₀) ≤ B₀ * M ^ 6 :=
    hsecond.trans (Nat.mul_le_mul_left B₀ (Nat.pow_le_pow_left hvc 6))
  have hsourceSize : listSize (FiniteDomainSource.source R₀ s₀) ≤ (w + 4) * M ^ 6 := by
    change _ ≤ (w + 4) * (v + c + 1) ^ 2 at hsize
    exact hsize.trans (Nat.mul_le_mul_left _ ((Nat.pow_le_pow_left hvc 2).trans h26))
  have houtSize : listSize ((FiniteDomainGraphLang.program a (arity h.tm)).run
      (FiniteDomainSource.source R₀ s₀)) ≤ D * M ^ 6 :=
    hout.trans (Nat.mul_le_mul_left D ((Nat.pow_le_pow_left hvc 2).trans h26))
  constructor
  · change (program h hs eK eA).cost source ≤ _
    rw [program, Prog.cost_compose, hexact]
    change (Machine.TableauSourceLang.program p).cost source +
      (FiniteDomainGraphLang.program a (arity h.tm)).cost (FiniteDomainSource.source R₀ s₀) +
      listSize (FiniteDomainSource.source R₀ s₀) +
      listSize ((FiniteDomainGraphLang.program a (arity h.tm)).run
        (FiniteDomainSource.source R₀ s₀)) + 5 ≤
      (A * (w + 5) ^ 3 + B₀ + (w + 4) + D + 5) * M ^ 6
    have hpos : 1 ≤ M ^ 6 := Nat.one_le_pow _ _ hM
    nlinarith only [hcostFirst, hcostSecond, hsourceSize, houtSize, hpos]
  · change listSize ((program h hs eK eA).run source) ≤ _
    rw [program, Prog.run_compose, hexact]
    exact hout

end PCP.Reduction.NPTableauGraphLang
