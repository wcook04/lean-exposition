import PCP.Complexity.ThreeColorBasePreflight

/-! # Polynomial cardinality-setup bounds used by the complete preflight -/

namespace PCP.Lang.ThreeColorBasePreflight

open PCP.Algebraic CanonicalResourceBounds ThreeColorBaseCardinal

attribute [local irreducible] ThreeColorBaseCardinal.loadConstant

theorem tupleCost_bound (c t n B : ℕ) (hc : c ≤ 4) (ht : t ≤ B) (hn : n ≤ B) (hB : 1 ≤ B) :
    tupleCost c t n ≤ (3*ThreeColorBaseCardinal.loadConstant c+513)*B^4 := by
  have htn := Nat.mul_le_mul ht hn
  have hmid : t*(c*n)+1 ≤ 5*B^2 := by
    have h := Nat.mul_le_mul_left (t*n) hc
    have h1 : 1 ≤ B^2 := Nat.one_le_pow _ _ hB
    nlinarith only [h,htn,h1]
  have hsq := Nat.pow_le_pow_left hmid 2
  have hlin : B ≤ B^4 := Nat.le_pow (by decide)
  have hB2 : B^2 ≤ B^4 := Nat.pow_le_pow_right hB (by decide)
  have h1 : 1 ≤ B^4 := Nat.one_le_pow _ _ hB
  have hl : t+n+1 ≤ 3*B^4 := by omega
  have hh := Nat.mul_le_mul_left (ThreeColorBaseCardinal.loadConstant c) hl
  unfold tupleCost
  nlinarith only [hh,hsq,hmid,hB2,h1]

theorem labelCost_bound (r t B : ℕ) (hr : Nat.size r ≤ 2)
    (ht : t ≤ B) (hq : 2 ^ t ≤ B) (hB : 1 ≤ B) :
    labelCost r t ≤ 800000000*B^4 := by
  have harg : 2^t+Nat.size r+3 ≤ 6*B := by omega
  have hh := Nat.pow_le_pow_left harg 4
  have hlin : B ≤ B^4 := Nat.le_pow (by decide)
  have h1 : 1 ≤ B^4 := Nat.one_le_pow _ _ hB
  unfold labelCost
  nlinarith only [hh,ht,hq,hlin,h1]

def cardinalConstant : ℕ :=
  3*(ThreeColorBaseCardinal.loadConstant 1+ThreeColorBaseCardinal.loadConstant 2+
    2*ThreeColorBaseCardinal.loadConstant 4)+1600003000

theorem cardinalCost_bound (N : ℕ) :
    programCost (fieldWidth N) (dimension N) ≤ cardinalConstant*(coreBound N)^4 := by
  obtain ⟨hB,ht,hn,hq⟩ := core_bounds N
  have h1 := tupleCost_bound 1 _ _ _ (by decide) ht hn hB
  have h2 := tupleCost_bound 2 _ _ _ (by decide) ht hn hB
  have h4 := tupleCost_bound 4 _ _ _ (by decide) ht hn hB
  have hl1 := labelCost_bound 1 _ _ (by decide) ht hq hB
  have hl3 := labelCost_bound 3 _ _ (by decide) ht hq hB
  have hone : 1 ≤ (coreBound N)^4 := Nat.one_le_pow _ _ hB
  unfold programCost cardinalConstant
  nlinarith only [h1,h2,h4,hl1,hl3,hone]

theorem cardinal_input_cost (x : List Bool) (st : State 400 128)
    (hd : ThreeColorBaseSetup.Data (ThreeColorEncoding.vertexCount x) st) :
    (ThreeColorBaseCardinal.program.run st).2 ≤
      cardinalConstant*coreConstant^4*(x.length+1)^48 := by
  have h := ThreeColorBaseCardinal.program_cost _ _ st hd.width hd.dimension hd.empty
  have hb := cardinalCost_bound (ThreeColorEncoding.vertexCount x)
  have hN := ThreeColorEncoding.size_le_length x
  have hc : (coreBound (ThreeColorEncoding.vertexCount x))^4 ≤
      coreConstant^4*(x.length+1)^48 := by
    unfold coreBound
    rw [mul_pow, ← pow_mul]
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.add_le_add_right hN 1) 48)
  exact (h.trans hb).trans ((Nat.mul_le_mul_left _ hc).trans_eq (by ring))

end PCP.Lang.ThreeColorBasePreflight
