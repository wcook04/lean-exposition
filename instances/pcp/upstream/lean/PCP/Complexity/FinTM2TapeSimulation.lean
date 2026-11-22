import PCP.Complexity.FiniteStackSimulation
import PCP.Complexity.Recode

/-!
# A quantitative tape simulation of arbitrary `FinTM2` witnesses

The simulator has finitely many control states, preserves the complete clean-output
contract of `TM2OutputsInTime`, and has quadratic time overhead. Its tape convention
is still mathlib's marked, reversed multitrack encoding. A separate binary interface
adapter is needed before invoking Complexitylib's canonical `FP` theorem.
-/

namespace PCP.Machine.TMTime

open Turing

/-- Related simulator configurations have the same tape whenever their source stacks agree. -/
theorem trCfg_tape_eq_of_stacks_eq {K : Type*} {Γ : K → Type*} {Λ σ : Type*}
    {a b : TM2.Cfg Γ Λ σ}
    {a' b' : TM1.Cfg (TM2to1.Γ' K Γ) (TM2to1.Λ' K Γ Λ σ) σ}
    (ha : TM2to1.TrCfg a a') (hb : TM2to1.TrCfg b b') (h : a.stk = b.stk) :
    a'.Tape = b'.Tape := by
  cases ha with
  | mk L hL =>
    cases hb with
    | mk R hR =>
      have he : L = R := by
        apply ListBlank.ext
        intro i
        funext k
        have hk := congrArg (fun z : ListBlank (Option (Γ k)) => z.nth i)
          ((hL k).trans ((congrArg (fun s => ListBlank.mk ((s k).map some).reverse) h).trans
            (hR k).symm))
        simpa only [ListBlank.nth_map, proj, PointedMap.mk_val] using hk
      subst R
      rfl

section FinTM2

variable (tm : FinTM2)

/-- The tape alphabet of the simulator, including the stack-bottom flag. -/
abbrev TapeAlphabet := TM2to1.Γ' tm.K tm.Γ

/-- Complete tape representation of one nonempty-or-empty source stack. -/
def stackTape (k : tm.K) (w : List (tm.Γ k)) : Tape (TapeAlphabet tm) :=
  Tape.mk₁ (TM2to1.trInit k w)

/-- Finite target control and exact clean-output traces at the marked tape encoding. -/
structure TapeSimulation where
  /-- Number of target states minus one. -/
  states : ℕ
  /-- One fixed target transition table. -/
  code : TM0.Machine (TapeAlphabet tm) (Fin (states + 1))
  /-- A constant depending on the source machine only. -/
  overhead : ℕ
  /-- The overhead coefficient is positive. -/
  overhead_pos : 0 < overhead
  /-- Every certified source computation has the same complete final tape. -/
  outputs : ∀ (input : List (tm.Γ tm.k₀)) (output : List (tm.Γ tm.k₁)) (time : ℕ),
    TM2OutputsInTime tm input (some output) time →
    ∃ u ≤ overhead * (input.length + time + 3) ^ 2,
      ∃ a : TM0.Cfg (TapeAlphabet tm) (Fin (states + 1)),
        exec (TM0.step code) u (TM0.init (TM2to1.trInit tm.k₀ input)) = some a ∧
        TM0.step code a = none ∧ a.Tape = stackTape tm tm.k₁ output

/-- Every `FinTM2`, including those with infinite unused internal alphabets, has
the exact finite-control tape simulation above. -/
theorem exists_tapeSimulation : Nonempty (TapeSimulation tm) := by
  classical
  let : Fintype tm.Λ := tm.ΛFin
  let : Fintype tm.σ := tm.σFin
  let : Inhabited tm.Λ := ⟨tm.main⟩
  have hstmt : ∀ q : TM2.Stmt tm.Γ tm.Λ tm.σ, TM2.SupportsStmt Finset.univ q := by
    intro q
    induction q <;> simp_all [TM2.SupportsStmt]
  have hs : TM2.Supports tm.m Finset.univ := ⟨Finset.mem_univ _, fun l _ => hstmt (tm.m l)⟩
  obtain ⟨m, G, C, hC, hG⟩ := finite_compilation tm.m Finset.univ hs
  refine ⟨⟨m, G, C, hC, ?_⟩⟩
  intro input output time ht
  have ht' : StateTransition.EvalsToInTime tm.step (initList tm input)
      (some (haltList tm output)) time := ht
  obtain ⟨⟨steps, hsteps⟩, hle⟩ := ht'
  change steps ≤ time at hle
  have hi : (TM2.init tm.k₀ input : TM2.Cfg tm.Γ tm.Λ tm.σ) = initList tm input := by
    apply congrArg (TM2.Cfg.mk (some tm.main) tm.initialState)
    funext k
    by_cases hk : k = tm.k₀
    · subst k
      simp
    · simp [hk]
  have hr : exec (TM2.step tm.m) steps (TM2.init tm.k₀ input) =
      some (haltList tm output) := by
    rw [hi]
    exact (exec_eq_iterate tm.step steps (initList tm input)).trans hsteps
  obtain ⟨u, hu, a, ha, hh, b, hb, hab⟩ := hG tm.k₀ input (haltList tm output)
    steps hr rfl
  refine ⟨u, hu.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2)),
    a, ha, hh, hab.trans ?_⟩
  have hsout : (haltList tm output).stk =
      (TM2.init tm.k₁ output : TM2.Cfg tm.Γ tm.Λ tm.σ).stk := by
    funext k
    by_cases hk : k = tm.k₁
    · subst k
      simp [haltList, TM2.init]
    · simp [haltList, TM2.init, hk]
  exact trCfg_tape_eq_of_stacks_eq hb (TM2to1.trCfg_init tm.k₁ output) hsout

/-- The simulator's alphabet is finite as soon as each source alphabet is finite. -/
theorem tapeAlphabet_finite (hΓ : ∀ k, Finite (tm.Γ k)) : Finite (TapeAlphabet tm) := by
  let : Fintype tm.K := tm.kFin
  let : ∀ k, Fintype (tm.Γ k) := fun k => @Fintype.ofFinite _ (hΓ k)
  infer_instance

end FinTM2

end PCP.Machine.TMTime
