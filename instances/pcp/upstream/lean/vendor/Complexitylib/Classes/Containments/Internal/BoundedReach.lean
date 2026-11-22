/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.Containments.Internal.ReachSet
public import Complexitylib.Classes.Containments.Internal.LogSpaceBound
public import Complexitylib.Classes.L
public import Complexitylib.Classes.Containments.Internal.PolyWindow

/-!
# Acceptance is a bounded search in the configuration graph

⚠️ Unreviewed by Bolton

`Complexitylib.Classes.Containments.Internal.ConfigGraph` turns acceptance into reachability, and
`Complexitylib.Classes.Containments.Internal.ReachSet` turns reachability into a fixpoint whose
round count is the number of configuration codes. This file joins the two for a space-bounded
machine: the codes of `Complexitylib.Classes.Containments.Internal.ConfigCount` separate the
reachable configurations, so the search terminates after `Fintype.card (Code …)` rounds — and for
a log-space machine that count is polynomial.

The result is the specification `NL ⊆ P` has to implement: a language in `NL` is exactly a
polynomially bounded breadth-first search in the configuration graph, with no residual reference
to nondeterminism, traces, or time.

## Main results

- `NTM.DecidesInSpace.mono` — deciding in space is monotone in the bound
- `NTM.withinDecisionSpace_of_reachesCfg` — the space bound holds along the whole graph
- `NTM.cfgCode_inj_of_reachesCfg` — codes separate the reachable configurations
- `NTM.mem_iff_exists_mem_reachSet` — membership is a search of enough rounds
- `NL_bounded_reachability_internal` — for `NL` the round count is polynomially bounded
- `NL_subset_P_of_search_internal` — the containment, modulo one machine
-/

@[expose] public section

namespace Complexity

namespace NTM

variable {k : ℕ} {tm : NTM k}

/-- Deciding in space `S` is deciding in any larger space bound. -/
theorem DecidesInSpace.mono {L : Language} {S S' : ℕ → ℕ} (hle : ∀ n, S n ≤ S' n)
    (h : tm.DecidesInSpace L S) : tm.DecidesInSpace L S' := by
  obtain ⟨T, hdt, hsp⟩ := h
  exact ⟨T, hdt, fun x choices t' ht => (hsp x choices t' ht).mono (hle x.length)⟩

/-- **The space bound holds at every configuration of the graph.** `DecidesInSpace` states the
bound along traces no longer than the halting time; past that time a trace is frozen, so the
bound propagates to every reachable configuration. -/
theorem withinDecisionSpace_of_reachesCfg {L : Language} {S : ℕ → ℕ}
    (hdec : tm.DecidesInSpace L S) (x : List Bool) {c : Cfg k tm.Q}
    (h : tm.ReachesCfg (tm.initCfg x) c) :
    c.WithinDecisionSpace x.length (S x.length) := by
  obtain ⟨T, hdt, hsp⟩ := hdec
  obtain ⟨t, choices, rfl⟩ := exists_trace_of_reachesCfg h
  rcases Nat.lt_or_ge (T x.length) t with hlt | hge
  · -- beyond the halting time the trace is its own length-`T` prefix
    have hfrozen := tm.trace_mono (T := T x.length) (T' := t) hlt.le
      (choices := fun j => choices ⟨j.val, by omega⟩) (choices' := choices)
      (fun _ => rfl) (hdt.1 x _)
    rw [hfrozen]
    exact hsp x (fun j => choices ⟨j.val, by omega⟩) (T x.length) le_rfl
  · -- within the halting time, pad the choice sequence out to length `T`
    have hpad := hsp x (fun j => if hj : j.val < t then choices ⟨j.val, hj⟩ else false) t hge
    have heq : (fun j : Fin t => if hj : j.val < t then choices ⟨j.val, hj⟩ else false)
        = choices := by
      funext j
      simp [j.isLt]
    rw [heq] at hpad
    exact hpad

/-- The initial configuration and everything reachable from it stays inside the window. -/
theorem windowed_of_reachesCfg_init {L : Language} {S : ℕ → ℕ}
    (hdec : tm.DecidesInSpace L S) (x : List Bool) {c : Cfg k tm.Q}
    (h : tm.ReachesCfg (tm.initCfg x) c) :
    Windowed x (S x.length) c :=
  windowed_of_reachesCfg (fun _ hc' => withinDecisionSpace_of_reachesCfg hdec x hc')
    (windowed_init tm.qstart x _) h

/-- **Codes separate the reachable configurations.** This is what bounds the search: distinct
reachable configurations have distinct codes, of which there are only finitely many. -/
theorem cfgCode_inj_of_reachesCfg {L : Language} {S : ℕ → ℕ}
    (hdec : tm.DecidesInSpace L S) (x : List Bool) {c c' : Cfg k tm.Q}
    (hc : tm.ReachesCfg (tm.initCfg x) c) (hc' : tm.ReachesCfg (tm.initCfg x) c')
    (heq : cfgCode x.length (S x.length) c = cfgCode x.length (S x.length) c') :
    c = c' :=
  cfgCode_inj (windowed_of_reachesCfg_init hdec x hc)
    (withinDecisionSpace_of_reachesCfg hdec x hc)
    (windowed_of_reachesCfg_init hdec x hc')
    (withinDecisionSpace_of_reachesCfg hdec x hc') heq

/-- **Membership is a bounded breadth-first search.** An input is in the language exactly when
an accepting configuration shows up within any number of rounds of successor-closure from the
initial configuration that reaches the number of codes. Nothing here mentions traces, choices,
or time. -/
theorem mem_iff_exists_mem_reachSet {L : Language} {S : ℕ → ℕ}
    (hdec : tm.DecidesInSpace L S) (x : List Bool) {N : ℕ}
    (hN : Fintype.card (Code tm.Q k x.length (S x.length)) ≤ N) :
    x ∈ L ↔ ∃ c ∈ reachSet tm (tm.initCfg x) N,
      tm.halted c ∧ c.output.cells 1 = Γ.one := by
  rw [mem_iff_exists_accepting_reachable hdec x]
  constructor
  · rintro ⟨c, hreach, hhalt, hout⟩
    exact ⟨c, (reachesCfg_iff_mem_reachSet tm _ (cfgCode x.length (S x.length))
      (fun hc hc' => cfgCode_inj_of_reachesCfg hdec x hc hc') (N := N) hN c).mp hreach, hhalt, hout⟩
  · rintro ⟨c, hmem, hhalt, hout⟩
    exact ⟨c, reachesCfg_of_mem_reachSet tm _ _ hmem, hhalt, hout⟩

end NTM

/-- **A language in `NL` is a polynomially bounded reachability search.** This is the
specification a polynomial-time decision procedure has to implement: run the successor-closure
for `A · (|x| + 1) ^ B` rounds and look for an accepting configuration. -/
theorem NL_bounded_reachability_internal {L : Language} (hL : L ∈ NL) :
    ∃ (k : ℕ) (tm : NTM k) (A B : ℕ),
      ∀ x : List Bool, x ∈ L ↔
        ∃ c ∈ NTM.reachSet tm (tm.initCfg x) (A * (x.length + 1) ^ B),
          tm.halted c ∧ c.output.cells 1 = Γ.one := by
  obtain ⟨k, tm, S, _, hdec, hS⟩ := hL
  obtain ⟨A, B, hAB⟩ := exists_config_bound (k := k) tm.Q hS
  exact ⟨k, tm, A, B, fun x => NTM.mem_iff_exists_mem_reachSet hdec x (hAB x.length)⟩


/-- **`NL ⊆ P`, reduced to the existence of one machine.** The hypothesis carries the log-space
witness for `tm`: without it the search language is not decidable at all, let alone in polynomial
time, since the configuration graph would be unbounded. -/
theorem NL_subset_P_of_search_internal
    (h : ∀ (k : ℕ) (tm : NTM k) (S : ℕ → ℕ) (L₀ : Language) (A B : ℕ),
      tm.DecidesInSpace L₀ S → S =O (fun n => Nat.log 2 n) →
      ∃ (k' : ℕ) (M : TM k') (q : Polynomial ℕ),
        M.DecidesInTime
          {x : List Bool | ∃ c ∈ NTM.reachSet tm (tm.initCfg x) (A * (x.length + 1) ^ B),
            tm.halted c ∧ c.output.cells 1 = Γ.one}
          (fun n => q.eval n)) :
    NL ⊆ P := by
  intro L hL
  obtain ⟨k, tm, S, -, hdec, hS⟩ := hL
  obtain ⟨A, B, hAB⟩ := exists_config_bound (k := k) tm.Q hS
  obtain ⟨k', M, q, hM⟩ := h k tm S L A B hdec hS
  refine mem_P_of_polyTime M q ?_
  have hLeq : L = {x : List Bool |
      ∃ c ∈ NTM.reachSet tm (tm.initCfg x) (A * (x.length + 1) ^ B),
        tm.halted c ∧ c.output.cells 1 = Γ.one} := by
    ext x
    exact NTM.mem_iff_exists_mem_reachSet hdec x (hAB x.length)
  rw [hLeq]
  exact hM

end Complexity
