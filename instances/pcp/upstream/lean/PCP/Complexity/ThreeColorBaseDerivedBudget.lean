import PCP.Complexity.ThreeColorBaseDerivedResources

/-! One polynomial budget for the production derived-grid machine and its loader. -/

namespace PCP.Lang.ThreeColorBaseDerived

open PCP.Algebraic ThreeColorParameterChoice ThreeColorParameters CanonicalResourceBounds
  ThreeColorBaseResources

def budget (N : ℕ) (x : List Bool) (qs : List ℕ) (bs : List Bool) : ℕ :=
  fieldWidth N + 2*dimension N + 2^fieldWidth N + sourceWidth N x qs bs +
    x.length + listSize qs + bs.length +
    GridEdge.budget (fieldWidth N) (dimension N) (dimension N) x +
    QueryAddress.width (fieldWidth N) (dimension N) (dimension N) 4 + 30

attribute [local irreducible] coreConstant metadataConstant QueryAddress.widthConstant

def budgetConstant : ℕ := metadataConstant + 4*coreConstant +
  18*QueryAddress.widthConstant*coreConstant^2 + 1000*4^64 + 100

theorem budget_input_bound (x : List Bool) (qs : List ℕ) (bs : List Bool) :
    budget (ThreeColorEncoding.vertexCount x) x qs bs + 1 ≤
      budgetConstant*(x.length+listSize qs+bs.length+1)^64 := by
  let N := ThreeColorEncoding.vertexCount x
  let A := x.length+listSize qs+bs.length+1
  have hN : N ≤ x.length := ThreeColorEncoding.size_le_length x
  have hA : 1 ≤ A := by dsimp [A]; omega
  have h1 : 1 ≤ A^64 := Nat.one_le_pow _ _ hA
  have hlin : A ≤ A^64 := Nat.le_pow (by decide)
  have hxl : x.length+1 ≤ A := by dsimp [A]; omega
  have h24 : (x.length+1)^24 ≤ A^64 :=
    (Nat.pow_le_pow_left hxl 24).trans (Nat.pow_le_pow_right hA (by decide))
  have h12 : (N+1)^12 ≤ A^64 :=
    (Nat.pow_le_pow_left (by omega : N+1 ≤ A) 12).trans
      (Nat.pow_le_pow_right hA (by decide))
  have hcore : coreBound N ≤ coreConstant*A^64 := Nat.mul_le_mul_left _ h12
  obtain ⟨_,ht,hn,hq⟩ := core_bounds N
  have hmeta := (metadataWidth_input x).trans (Nat.mul_le_mul_left _ h24)
  change metadataWidth N ≤ _ at hmeta
  have he := ProductionGrid.edge_budget_polynomial x
  rw [ThreeColorCanonicalVerifier.graphOrder_eq] at he
  change GridEdge.budget (fieldWidth N) (dimension N) (dimension N) x + 1 ≤
    1000*(4*(x.length+1))^64 at he
  have he' : GridEdge.budget (fieldWidth N) (dimension N) (dimension N) x ≤
      (1000*4^64)*A^64 := by
    have hh := Nat.pow_le_pow_left hxl 64
    rw [mul_pow] at he
    exact (Nat.le_add_right _ 1).trans (he.trans (by
      have := Nat.mul_le_mul_left (1000*4^64) hh
      nlinarith only [this]))
  have hqpow : (coreBound N)^2 ≤ coreConstant^2*A^64 := by
    unfold coreBound
    rw [mul_pow,← pow_mul]
    exact Nat.mul_le_mul_left _ ((Nat.pow_le_pow_left (by omega : N+1 ≤ A) 24).trans
      (Nat.pow_le_pow_right hA (by decide)))
  have hquery := (query_width N).trans (Nat.mul_le_mul_left _ hqpow)
  have hsmall : 3*x.length+2*listSize qs+3*bs.length+32 ≤ 40*A^64 := by
    change x.length+listSize qs+bs.length+1 ≤ A^64 at hlin
    omega
  change budget N x qs bs+1 ≤ budgetConstant*A^64
  unfold budget sourceWidth budgetConstant
  nlinarith only [hcore,ht,hn,hq,hmeta,he',hquery,hsmall]

end PCP.Lang.ThreeColorBaseDerived
