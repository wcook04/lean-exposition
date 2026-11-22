import PCP.Complexity.AmplifiedStreamStages
import PCP.Algebraic.AmplifiedSlicedAlgorithm

/-! One concrete verifier call inside the amplified answer-history protocol. -/

namespace PCP.Lang.AmplifiedStream

open PCP.Algebraic.ThreeColorAmplifiedQueryAlgorithm

/-- The concrete callback contract, to be discharged by the seven-way base program. -/
structure Correct (P : Stmt 400 128) (qs : List Bool → List Bool → List ℕ)
    (fs : List Bool → List Bool → PCP.ProofOracle → Bool) : Prop where
  run : ∀ x bits answers,
    (P.run (AmplifiedWorkspace.initial (x.map Bool.toNat) (bits.map Bool.toNat)
      (answers.map Bool.toNat))).1.lists 103 = qs x bits ∧
    (P.run (AmplifiedWorkspace.initial (x.map Bool.toNat) (bits.map Bool.toNat)
      (answers.map Bool.toNat))).1.regs 300 =
      (fs x bits (PCP.QueryTree.answersOracle (qs x bits) answers)).toNat

structure Ready (st : State 420 140) (b : ℕ) (x bits answers : List Bool) : Prop where
  budget : st.regs 400 = b
  graph : st.lists 130 = x.map Bool.toNat
  bits : st.lists 131 = bits.map Bool.toNat
  answers : st.lists 132 = answers.map Bool.toNat
  empty : st.lists 139 = []

def round (P : Stmt 400 128) : Stmt 420 140 :=
  .seq seed (.seq (AmplifiedWorkspace.call P) step)

attribute [local irreducible] AmplifiedWorkspace.call seed step

theorem call_correct (P : Stmt 400 128) (qs : List Bool → List Bool → List ℕ)
    (fs : List Bool → List Bool → PCP.ProofOracle → Bool) (hc : Correct P qs fs)
    (st : State 420 140) (x bits answers : List Bool)
    (hx : st.lists 130 = x.map Bool.toNat) (hb : st.lists 133 = bits.map Bool.toNat)
    (ha : st.lists 132 = answers.map Bool.toNat) (he : st.lists 139 = []) :
    ((AmplifiedWorkspace.call P).run st).1.lists 103 = qs x bits ∧
    ((AmplifiedWorkspace.call P).run st).1.regs 300 =
      (fs x bits (PCP.QueryTree.answersOracle (qs x bits) answers)).toNat := by
  have hr := AmplifiedWorkspace.call_result P st he
  rw [hx, hb, ha] at hr
  have hl := congrArg (fun s => s.lists 103) hr
  have hv := congrArg (fun s => s.regs 300) hr
  exact ⟨hl.trans (hc.run x bits answers).1, hv.trans (hc.run x bits answers).2⟩

theorem round_ready (P : Stmt 400 128) (st : State 420 140) (b : ℕ)
    (x bits answers : List Bool) (hs : Ready st b x bits answers) :
    Ready (round P |>.run st).1 b x (bits.drop b) answers := by
  let s := (seed.run st).1
  let u := ((AmplifiedWorkspace.call P).run s).1
  have hseed := seed_run st hs.empty
  have hes : s.lists 139 = [] := hseed.2.2.1
  have hlist (L : Fin 140) (hL : 128 ≤ L.val) (hne : L ≠ 137) :
      (step.run u).1.lists L = s.lists L :=
    (step_lists u L hne).trans (AmplifiedWorkspace.call_lists P s hes L hL)
  change Ready (step.run u).1 b x (bits.drop b) answers
  constructor
  · exact (step_budget u).trans ((AmplifiedWorkspace.call_regs P s hes 400 (by decide)).trans
      (hseed.2.2.2.trans hs.budget))
  · exact (hlist 130 (by decide) (by decide)).trans ((seed_graph st).trans hs.graph)
  · rw [hlist 131 (by decide) (by decide), hseed.1, hs.bits, hs.budget, List.map_drop]
  · exact (hlist 132 (by decide) (by decide)).trans ((seed_answers st).trans hs.answers)
  · exact (hlist 139 (by decide) (by decide)).trans hes

theorem round_run (P : Stmt 400 128) (qs : List Bool → List Bool → List ℕ)
    (fs : List Bool → List Bool → PCP.ProofOracle → Bool) (hc : Correct P qs fs)
    (st : State 420 140) (b : ℕ) (x bits answers : List Bool)
    (hs : Ready st b x bits answers) :
    (round P |>.run st).1.lists 103 = qs x (paddedBits b bits) ∧
    (round P |>.run st).1.regs 403 =
      (if answers.length < (qs x (paddedBits b bits)).length then
        (qs x (paddedBits b bits)).getD answers.length 0 else
          (fs x (paddedBits b bits)
            (PCP.QueryTree.answersOracle (qs x (paddedBits b bits)) answers)).toNat) ∧
    (round P |>.run st).1.regs 402 =
      (if answers.length < (qs x (paddedBits b bits)).length then 1 else 0) := by
  let s := (seed.run st).1
  let u := ((AmplifiedWorkspace.call P).run s).1
  have hseed := seed_run st hs.empty
  have hes : s.lists 139 = [] := hseed.2.2.1
  have hb : s.lists 133 = (paddedBits b bits).map Bool.toNat := by
    rw [hseed.2.1, hs.budget, hs.bits, paddedBits_map]
  have hc' := call_correct P qs fs hc s x (paddedBits b bits) answers
    ((seed_graph st).trans hs.graph) hb ((seed_answers st).trans hs.answers) hes
  have ha : u.lists 132 = answers.map Bool.toNat :=
    (AmplifiedWorkspace.call_lists P s hes 132 (by decide)).trans
      ((seed_answers st).trans hs.answers)
  have ht := step_run u
  change u.lists 103 = _ ∧ u.regs 300 = _ at hc'
  rw [hc'.1, hc'.2, ha, List.length_map] at ht
  exact ⟨(step_lists u 103 (by decide)).trans hc'.1, ht⟩

theorem consume_ready (st : State 420 140) (b : ℕ) (x bits answers : List Bool)
    (hs : Ready st b x bits answers) :
    Ready (consume.run st).1 b x bits (answers.drop (st.lists 103).length) := by
  constructor
  · exact (consume_budget st).trans hs.budget
  · exact (consume_graph st).trans hs.graph
  · exact (consume_bits st).trans hs.bits
  · rw [(consume_run st hs.empty).1, hs.answers, List.map_drop]
  · exact (consume_run st hs.empty).2

end PCP.Lang.AmplifiedStream
