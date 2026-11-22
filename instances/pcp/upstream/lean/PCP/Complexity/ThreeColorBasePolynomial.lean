import PCP.Complexity.ThreeColorBaseProtocolCost
import PCP.Complexity.ThreeColorBaseCostBudget
import PCP.Complexity.ThreeColorBaseQuerySize

/-! # Polynomial charged cost of the complete production base callback -/

namespace PCP.Lang.ThreeColorBaseBranches

open PCP.Algebraic ThreeColorFullFieldSampling ThreeColorBasePreflight ThreeColorBaseSetup

theorem absorb_preflight (v Cp Cb Cq S T : ℕ)
    (h : v ≤ Cp * S + (14 * Cb + 5 * Cq + 111) * T + 8) (hle : S ≤ T) (hT : 1 ≤ T) :
    v ≤ (Cp + 14 * Cb + 5 * Cq + 119) * T := by
  have hm := Nat.mul_le_mul_left Cp hle
  nlinarith only [h,hm,hT]

attribute [local irreducible] program validProgram allQueries ThreeColorBaseSeed.sample
  ThreeColorBasePreflight.costConstant

theorem program_polynomial_of_queries (Cq dq : ℕ)
    (hq : ∀ (x bits : List Bool)
      (hv : Valid (ThreeColorBaseSeed.sample (ThreeColorEncoding.vertexCount x) bits)),
      listSize (allQueries (ThreeColorEncoding.vertexCount x) x bits hv) ≤
        Cq * (x.length + 1) ^ dq) :
    ∃ C d : ℕ, ∀ (x bits bs : List Bool) (st : State 400 128), Sources x bits bs st →
      (program.run st).2 ≤ C * (x.length + bits.length + bs.length + 1) ^ d := by
  obtain ⟨Cb,db,hb⟩ := branch_input_cost
  let e := max 84 (max dq ((dq + 1) * db))
  let Cb' := Cb * (Cq + 1) ^ db
  refine ⟨ThreeColorBasePreflight.costConstant + 14 * Cb' + 5 * Cq + 119,e,?_⟩
  intro x bits bs st hs
  let n := x.length + bits.length + bs.length + 1
  have hn : x.length + bs.length + 1 ≤ n := by dsimp [n]; omega
  have hn1 : 1 ≤ n := by omega
  have hde : (dq + 1) * db ≤ e := (le_max_right dq _).trans (le_max_right 84 _)
  have hqe : dq ≤ e := (le_max_left dq _).trans (le_max_right 84 _)
  have h1 : 1 ≤ n ^ e := Nat.one_le_pow _ _ hn1
  have hvalid (hv : Valid (ThreeColorBaseSeed.sample (ThreeColorEncoding.vertexCount x) bits))
      (s : State 400 128) (hr : Ready x bits bs s) :
      (validProgram.run s).2 ≤ (14 * Cb' + 5 * Cq + 111) * n ^ e := by
    have hqs := (hq x bits hv).trans (Nat.mul_le_mul_left _
      (Nat.pow_le_pow_left (by dsimp [n]; omega : x.length + 1 ≤ n) dq))
    have h₀ := branch_history_cost Cb db Cq dq n e hb hde x bits bs [] hv hn
      (by simp [listSize])
    have h₁ := branch_history_cost Cb db Cq dq n e hb hde x bits bs _ hv hn hqs
    have hc := validProgram_cost x bits bs hv (Cb' * n ^ e) (Cb' * n ^ e) h₀ h₁ s hr
    have hqs' := hqs.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hn1 hqe))
    nlinarith only [hc,hqs',h1]
  have hp := program_cost_bound x bits bs ((14 * Cb' + 5 * Cq + 111) * n ^ e) hvalid st hs
  have hpre : (x.length + bits.length + 1) ^ 84 ≤ n ^ e :=
    (Nat.pow_le_pow_left (by dsimp [n]; omega) 84).trans
      (Nat.pow_le_pow_right hn1 (le_max_left 84 _))
  exact absorb_preflight _ ThreeColorBasePreflight.costConstant Cb' Cq _ _ hp hpre h1

theorem program_polynomial_cost : ∃ C d : ℕ, ∀ x bits bs : List Bool,
    (program.run (AmplifiedWorkspace.initial (x.map Bool.toNat) (bits.map Bool.toNat)
      (bs.map Bool.toNat))).2 ≤ C * (x.length + bits.length + bs.length + 1) ^ d := by
  obtain ⟨Cq,dq,hq⟩ := polynomial_allQueries_size
  obtain ⟨C,d,h⟩ := program_polynomial_of_queries Cq dq hq
  exact ⟨C,d,fun x bits bs => h x bits bs _ (initial_sources x bits bs)⟩

end PCP.Lang.ThreeColorBaseBranches
