import Complexitylib.Models.TuringMachine.Witness.Verifier
import Complexitylib.Models.TuringMachine.Registers.Horner
import Mathlib.Tactic

/-!
# A realized polynomial witness-length bound

This adapts ComplexityLib's linear `WitnessBoundSetup` construction to a fixed
natural polynomial. Its existing unary-register Horner machine computes the
bound on charged work tapes. The proof follows the linear setup proof in
`Witness/BoundSetup/Internal.lean` (Samuel Schlesinger, Apache 2.0).
-/

namespace PCP.ReferencePolynomialBoundSetup

open Complexity Polynomial

noncomputable def cap (p : Polynomial ℕ) : Polynomial ℕ :=
  X + C ((TM.polyCoeffs p).sum + 1) * (X + 1) ^ (p.natDegree + 1)

noncomputable def operation (p : Polynomial ℕ) : Polynomial ℕ := C 32 * (cap p + C 2) ^ 3

noncomputable def time (p : Polynomial ℕ) : Polynomial ℕ :=
  C 2 * X + C 10 + operation p + 1 +
    C (p.natDegree + 1) * (C 4 * operation p + C 4) + 1

theorem cap_ge_input (p : Polynomial ℕ) (n : ℕ) : n ≤ (cap p).eval n := by
  simp [cap]

theorem cap_ge_prefix (p : Polynomial ℕ) (n j : ℕ) :
    TM.hornerFold n ((TM.polyCoeffs p).take j) 0 ≤ (cap p).eval n := by
  have h := TM.hornerFold_take_le n (TM.polyCoeffs p) j
  simpa only [cap, eval_add, eval_mul, eval_C, eval_pow, eval_X, eval_one,
    TM.polyCoeffs_length] using h.trans (Nat.le_add_left _ n)

theorem time_eval (p : Polynomial ℕ) (n : ℕ) :
    (time p).eval n = 2 * n + 10 + TM.opBudget ((cap p).eval n) + 1 +
      ((p.natDegree + 1) * (TM.layerBudget ((cap p).eval n) + 1) + 1) := by
  simp [time, operation, TM.opBudget, TM.layerBudget]
  ring

def machine (p : Polynomial ℕ) : TM 3 :=
  TM.seqTM TM.bumpTM (TM.seqTM (TM.inputLenRegTM 0) (TM.polyEvalTM 0 2 1 p))

private theorem reg_startInvariant (n : ℕ) : (TM.regTape n).StartInvariant := by
  refine ⟨rfl, ?_⟩
  intro j hj
  exact TM.regCells_ne_start (by omega)

theorem prepares (p : Polynomial ℕ) (x : List Bool) :
    (machine p).HoareTime (WitnessBoundSetup.fresh x)
      (WitnessBoundSetup.ready x (p.eval x.length)) ((time p).eval x.length) := by
  let inp := (Tape.init (x.map Γ.ofBool)).move Dir3.right
  let zero : Fin 3 → Tape := fun _ => TM.regTape 0
  let len := Function.update zero 0 (TM.regTape x.length)
  let result := Function.update (Function.update len 1 (TM.regTape (p.eval x.length)))
    2 (TM.regTape (p.eval x.length))
  have hp : TM.Parked inp := TM.parked_init_input x
  have hz : ∀ i, TM.Parked (zero i) := fun _ => TM.parked_regTape 0
  have hl : ∀ i, TM.Parked (len i) := by
    intro i
    by_cases hi : i = 0
    · subst i
      simp only [len, Function.update_self]
      exact TM.parked_regTape _
    · simpa [len, hi] using hz i
  have hstart : (TM.bumpTM (n := 3)).HoareTime (WitnessBoundSetup.fresh x)
      (TM.EmitPred inp zero []) 1 := by
    refine (TM.bumpTM_hoareTime x).consequence ?_ ?_ le_rfl
    · rintro i w o ⟨hi, hw, ho⟩
      exact ⟨hi, fun j => congrFun hw j, ho⟩
    · rintro i w o ⟨hi, hw, ho⟩
      exact ⟨hi, funext fun j => (hw j).eq_regT, ho⟩
  have hlen := TM.inputLenRegTM_hoareTime (0 : Fin 3) x zero []
    (fun i _ => hz i) rfl
  have hpoly := TM.polyEvalTM_hoareTime (0 : Fin 3) 2 1
    (by decide) (by decide) (by decide) p ((cap p).eval x.length) x.length 0 0
    (cap_ge_input p x.length) (Nat.zero_le _) (Nat.zero_le _)
    (fun j _ => cap_ge_prefix p x.length j) inp len [] hp hl
    (by simp [len]) (by simp [len, zero]) (by simp [len, zero])
  have htail := TM.seqTM_hoareTime _ _ hlen (TM.emitPred_transition hp hl []) hpoly
  have hfull := TM.seqTM_hoareTime _ _ hstart (TM.emitPred_transition hp hz []) htail
  refine hfull.consequence (fun _ _ _ h => h) ?_ ?_
  · rintro i w o ⟨hi, hw, ho⟩
    refine ⟨hi, ?_, ?_, ho.eq TM.outAcc_nil_init⟩
    · rw [hw]
      rfl
    · intro j
      have hr : ∃ n, result j = TM.regTape n := by
        by_cases h2 : j = 2
        · subst j
          exact ⟨p.eval x.length, by simp [result]⟩
        · by_cases h1 : j = 1
          · subst j
            exact ⟨p.eval x.length, by simp [result]⟩
          · by_cases h0 : j = 0
            · subst j
              exact ⟨x.length, by simp [result, len]⟩
            · exact ⟨0, by simp [result, len, zero, h2, h1, h0]⟩
      obtain ⟨n, hn⟩ := hr
      rw [hw]
      change (result j).head = 1 ∧ (result j).StartInvariant
      rw [hn]
      exact ⟨rfl, reg_startInvariant n⟩
  · rw [time_eval]
    omega

/-- The actual time certificate bounds every tape-head position on every prefix. -/
theorem withinSpace (p : Polynomial ℕ) (x : List Bool) :
    (machine p).HoareSafety (WitnessBoundSetup.fresh x)
      (fun inp work out =>
        (⟨(), inp, work, out⟩ : Complexity.Cfg 3 Unit).WithinDecisionSpace
          x.length ((time p).eval x.length)) := by
  intro inp work out hpre c hreach
  obtain ⟨d, haltTime, htime, hrun, hhalt, _⟩ := prepares p x _ _ _ hpre
  obtain ⟨t, ht⟩ := (machine p).reaches_to_reachesIn hreach
  have hle : t ≤ haltTime := (machine p).reachesIn_le_halt ht hrun hhalt
  rcases hpre with ⟨rfl, rfl, rfl⟩
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro j
    have hb := (machine p).work_head_reachesIn_bound ht j
    simp only [Tape.init] at hb
    dsimp only
    omega
  · have hb := (machine p).input_head_reachesIn_bound ht
    simp only [Tape.init] at hb
    dsimp only
    omega
  · have hb := (machine p).output_head_reachesIn_bound ht
    simp only [Tape.init] at hb
    dsimp only
    omega

/-- A concrete, polynomial-time setup for the polynomial witness bound. -/
noncomputable def setup (p : Polynomial ℕ) : WitnessBoundSetup 2 p.eval where
  machine := machine p
  time := (time p).eval
  space := (time p).eval
  prepares := prepares p
  withinSpace := withinSpace p

end PCP.ReferencePolynomialBoundSetup
