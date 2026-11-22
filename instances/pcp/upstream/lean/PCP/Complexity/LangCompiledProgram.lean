import PCP.Complexity.LangProgramMachine
import PCP.Complexity.LangStructuredCorrect

/-!
# Polynomial-time execution certificates for every compiled language program

The actual structured machine starts from the public separator-delimited input,
executes the source program, then clears all non-output tapes. Its final state is
exactly `haltList`, including reset finite control. The bound is polynomial in the
source charge plus encoded input length, with program-fixed constants.
-/

namespace PCP.Lang.Compiler

open Turing StateTransition PCP.Machine FiniteBlocks MachineLayout

/-- Every whole-program machine has its actual output trace and polynomial step bound. -/
theorem program_outputs (P : Prog) (xs : List ℕ) :
    Nonempty (TM2OutputsInTime (programMachine P) (encodeNats xs)
      (some (encodeNats (P.run xs)))
      (programCoefficient P * (P.cost xs + (encodeNats xs).length + 1) ^ degree P.body)) := by
  let finish := (P.body.run (P.init xs)).1
  let S := boundary P.body finish (fun _ : Empty => [])
  let N := listSize xs + P.cost xs + 1
  let M := (cleanup P).length
  have hN : 1 ≤ N := by dsimp [N]; omega
  have hNP : N ≤ N ^ degree P.body := by
    calc N = N ^ 1 := (pow_one N).symm
      _ ≤ N ^ degree P.body := Nat.pow_le_pow_right hN
        (by have := degree_ge_two P.body; omega)
  have hP : 1 ≤ N ^ degree P.body := one_le_pow₀ hN
  have hbody := correct P.body Empty (inputTape P) (outputTape P)
    (P.init xs) (fun _ => []) (listSize xs) (P.init_sized xs)
  have hfinish : finish.Sized (listSize xs + P.cost xs) :=
    P.body.run_sized (P.init xs) (listSize xs) (P.init_sized xs)
  let hc := BlockCleanup.evals (inputTape P) (outputTape P) (cleanup P) S
  have hcleanup : (BlockCleanup.block (cleanup P)).Executes (inputTape P) (outputTape P)
      S (BlockCleanup.clear (cleanup P) S)
      (((cleanup P).map (fun k => (S k).length)).sum + 4 * M + 1) :=
    ⟨hc.steps, hc.steps_le_m, hc.evals_in_steps⟩
  have hcleanuple := cleanup_budget P finish (listSize xs + P.cost xs) hfinish
  have hfull := Block.Executes.seq (inputTape P) (outputTape P) hbody hcleanup
  have hbound : coefficient P.body * (listSize xs + P.cost xs + 1) ^ degree P.body +
      (((cleanup P).map (fun k => (S k).length)).sum + 4 * M + 1) + 3 ≤
      programCoefficient P * N ^ degree P.body := by
    have hspace : M * (listSize xs + P.cost xs) ≤ M * N :=
      Nat.mul_le_mul_left M (by dsimp [N]; omega)
    have hconst : 4 * M ≤ 4 * M * N := by
      simpa only [Nat.mul_one] using Nat.mul_le_mul_left (4 * M) hN
    have hlinear := Nat.mul_le_mul_left (5 * M) hNP
    have hfour := Nat.mul_le_mul_left 4 hP
    change coefficient P.body * N ^ degree P.body + _ + 3 ≤ _
    dsimp only [programCoefficient]
    change _ ≤ (coefficient P.body + 5 * M + 4) * N ^ degree P.body
    change _ ≤ M * (listSize xs + P.cost xs) + 4 * M + 1 at hcleanuple
    nlinarith
  have hfull' := Block.Executes.mono (inputTape P) (outputTape P) hfull hbound
  obtain ⟨steps, hs, ht⟩ := hfull'
  refine ⟨{ steps := steps, evals_in_steps := ?_, steps_le_m := ?_ }⟩
  · change (flip Bind.bind (programMachine P).step)^[steps]
      (some (initList (programMachine P) (encodeNats xs))) =
        some (haltList (programMachine P) (encodeNats (P.run xs)))
    rw [program_init, show P.run xs = finish.lists P.outL from rfl, program_halt]
    exact ht
  · simpa only [N, listTape_length, Nat.add_comm (P.cost xs)] using hs

/-- Fixed actual machine and fixed natural polynomial constants for the full compiler bridge. -/
theorem exists_program_machine (P : Prog) :
    ∃ (tm : FinTM2) (ein : tm.Γ tm.k₀ ≃ Sym) (eout : tm.Γ tm.k₁ ≃ Sym) (c k : ℕ),
      ∀ xs : List ℕ, Nonempty (TM2OutputsInTime tm ((encodeNats xs).map ein.invFun)
        (some ((encodeNats (P.run xs)).map eout.invFun))
        (c * (P.cost xs + (encodeNats xs).length + 1) ^ k)) := by
  refine ⟨programMachine P, Equiv.refl Sym, Equiv.refl Sym, programCoefficient P, degree P.body, ?_⟩
  intro xs
  simpa only [Equiv.refl, List.map_id_fun, id_eq] using program_outputs P xs

end PCP.Lang.Compiler
