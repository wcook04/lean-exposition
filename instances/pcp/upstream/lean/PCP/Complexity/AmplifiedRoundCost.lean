import PCP.Complexity.AmplifiedRound

/-! Charged cost of one complete copy in terms of actual callback resource bounds. -/

namespace PCP.Lang.AmplifiedStream

open PCP.Algebraic.ThreeColorAmplifiedQueryAlgorithm

theorem boolList_size (bits : List Bool) : listSize (bits.map Bool.toNat) ≤ 2*bits.length := by
  induction bits with
  | nil => simp [listSize]
  | cons b bs ih => cases b <;> simp_all [listSize] <;> omega

structure Bounded (P : Stmt 400 128) (qs : List Bool → List Bool → List ℕ)
    (N C : ℕ) : Prop where
  cost : ∀ x bits answers : List Bool, x.length ≤ N → bits.length ≤ N → answers.length ≤ N →
    (P.run (AmplifiedWorkspace.initial (x.map Bool.toNat) (bits.map Bool.toNat)
      (answers.map Bool.toNat))).2 ≤ C
  queries : ∀ x bits : List Bool, x.length ≤ N → bits.length ≤ N → listSize (qs x bits) ≤ C

attribute [local irreducible] AmplifiedWorkspace.call seed step

theorem round_cost (P : Stmt 400 128) (qs : List Bool → List Bool → List ℕ)
    (fs : List Bool → List Bool → PCP.ProofOracle → Bool) (hc : Correct P qs fs)
    (N C : ℕ) (hB : Bounded P qs N C)
    (st : State 420 140) (b : ℕ) (x bits answers : List Bool)
    (hs : Ready st b x bits answers) (hb : b ≤ N) (hx : x.length ≤ N)
    (hbits : bits.length ≤ N) (has : answers.length ≤ N) :
    ((round P).run st).2 ≤ 4000*(N+C+1)^2 := by
  let s := (seed.run st).1
  let u := ((AmplifiedWorkspace.call P).run s).1
  have hseed := seed_run st hs.empty
  have hes : s.lists 139 = [] := hseed.2.2.1
  have hxs : s.lists 130 = x.map Bool.toNat := (seed_graph st).trans hs.graph
  have hbs : s.lists 133 = (paddedBits b bits).map Bool.toNat := by
    rw [hseed.2.1, hs.budget, hs.bits, paddedBits_map]
  have has' : s.lists 132 = answers.map Bool.toNat := (seed_answers st).trans hs.answers
  have hp := call_correct P qs fs hc s x (paddedBits b bits) answers hxs hbs has' hes
  have ha : u.lists 132 = answers.map Bool.toNat :=
    (AmplifiedWorkspace.call_lists P s hes 132 (by decide)).trans has'
  change u.lists 103 = _ ∧ u.regs 300 = _ at hp
  have hq := hB.queries x (paddedBits b bits) hx (by simpa using hb)
  have hv : Nat.size (u.regs 300) ≤ 1 := by
    rw [hp.2]
    cases fs x (paddedBits b bits)
      (PCP.QueryTree.answersOracle (qs x (paddedBits b bits)) answers) <;> decide
  have hstep := step_cost u
  rw [hp.1, ha] at hstep
  have haSize : listSize (answers.map Bool.toNat) ≤ 2*N :=
    (boolList_size answers).trans (Nat.mul_le_mul_left 2 has)
  have hxSize : listSize (x.map Bool.toNat) ≤ 2*N :=
    (boolList_size x).trans (Nat.mul_le_mul_left 2 hx)
  have hbitSize : listSize (bits.map Bool.toNat) ≤ 2*N :=
    (boolList_size bits).trans (Nat.mul_le_mul_left 2 hbits)
  have hpadSize : listSize ((paddedBits b bits).map Bool.toNat) ≤ 2*N :=
    (boolList_size _).trans (Nat.mul_le_mul_left 2 (by simpa using hb))
  have hstep' : (step.run u).2 ≤ 20*(3*(N+C+1))^2 := hstep.trans
    (Nat.mul_le_mul_left 20 (Nat.pow_le_pow_left (by omega) 2))
  have hcall := AmplifiedWorkspace.call_cost P s hes
  rw [hxs, hbs, has'] at hcall
  have hbase := hB.cost x (paddedBits b bits) answers hx (by simpa using hb) has
  have hseedcost := seed_cost st hs.empty
  rw [hs.bits, hs.budget] at hseedcost
  have hseed' : (seed.run st).2 ≤ 20*(3*(N+C+1))^2 := hseedcost.trans
    (Nat.mul_le_mul_left 20 (Nat.pow_le_pow_left (by omega) 2))
  change (seed.run st).2+(((AmplifiedWorkspace.call P).run s).2+(step.run u).2+1)+1 ≤ _
  nlinarith [Nat.zero_le (N*C)]

theorem consume_cost_bound (st : State 420 140) (N C : ℕ)
    (he : st.lists 139 = []) (ha : listSize (st.lists 132) ≤ 2 * N)
    (hq : listSize (st.lists 103) ≤ C) :
    (consume.run st).2 ≤ 300*(N+C+1)^2 := by
  have h := consume_cost st he
  have hlen := (length_le_listSize (st.lists 103)).trans hq
  have hsize := (size_le_self _).trans hlen
  have hp : 20*(listSize (st.lists 132)+(st.lists 103).length+1)^2 ≤
      20*(3*(N+C+1))^2 :=
    Nat.mul_le_mul_left 20 (Nat.pow_le_pow_left (by omega) 2)
  nlinarith [Nat.zero_le (N*C)]

end PCP.Lang.AmplifiedStream
