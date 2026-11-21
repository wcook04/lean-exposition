/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Complexity.HadamardRowLoop

/-!
# Complete stored Hadamard row queries

The program materializes every coefficient label and returns its canonical numeric
code, in exactly the executable verifier's query order, retaining the input seed.
-/

namespace PCP.Lang.HadamardRow

open PCP.Algebraic BinaryPolynomialSpace Hadamard BooleanCoefficientList HadamardLabel

variable {t r : ℕ}

def queries : Stmt 80 32 :=
  .seq (.copy 7 24) (.seq initialQueries (.seq factorLoop (.rev 24)))

theorem queries_decomposition (hr : 1 ≤ r) (s : TestRandomness t r) :
    (ComputableHadamardTest.queries hr s).map code =
      prefixQueries hr s ++ factorPrefix s (r - 1) := by
  simp only [ComputableHadamardTest.queries, List.map_append, List.map_cons, List.map_nil,
    List.map_flatMap, prefixQueries, unitLabel, linearLabel, ComputableHadamardTest.linearQuery,
    factorPrefix]
  rw [List.take_of_length_le (by simp)]
  congr 1

theorem queries_run (hr : 1 ≤ r) (s : TestRandomness t r) (st : State 80 32)
    (hc : Context s st) :
    Context s (queries.run st).1 ∧
      (queries.run st).1.lists 24 = (ComputableHadamardTest.queries hr s).map code := by
  let u := setList st 24 []
  have hu : Context s u := by simpa [Context, u, Function.update] using hc
  have hp := (prefix_spec hr s).output u hu
  have hpc := (prefix_spec hr s).context u hu
  dsimp only [u] at hp hpc
  simp only [queries, run_seq_fst, run_copy_fst, hc.2.2.1]
  generalize hv : (initialQueries.run (setList st 24 [])).1 = v at *
  have hf := factorLoop_run s v hpc
  generalize hw : (factorLoop.run v).1 = w at *
  refine ⟨?_, ?_⟩
  · simpa [Context, run_rev_fst, Function.update] using hf.1
  · simp only [run_rev_fst, setList_lists, Function.update_self, hf.2, hp,
      setList_lists, Function.update_self, List.append_nil, List.reverse_append,
      List.reverse_reverse, queries_decomposition]

/-- Every generated code has at most one bit per possible Boolean monomial. -/
theorem queryCodes_size (hr : 1 ≤ r) (s : TestRandomness t r) :
    listSize ((ComputableHadamardTest.queries hr s).map code) ≤
      (2 * r + 4) * (2 ^ t + 1) := by
  have hlen : (ComputableHadamardTest.queries hr s).length = 2 * r + 4 := by
    simpa only [ComputableHadamardTest.queries_eq] using testQueries_length hr s
  have hs : ∀ ps : List (Coefficients t r), listSize (ps.map code) ≤ ps.length * (2 ^ t + 1) := by
    intro ps
    induction ps with
    | nil => simp [listSize]
    | cons p ps ih =>
      have hp := code_size p
      simp only [listSize, List.map_cons, List.sum_cons] at ih ⊢
      simp only [List.length_cons, Nat.succ_mul]
      omega
  simpa only [hlen] using hs (ComputableHadamardTest.queries hr s)

end PCP.Lang.HadamardRow
