import PCP.Complexity.ProductionEdgeLang
import PCP.Complexity.GridEdgeCost
import PCP.Complexity.ThreeColorParameterLang

/-!
# Polynomial input-length cost for the production public edge extension
-/

namespace PCP.Lang.ProductionGrid

open PCP.Algebraic BinaryFieldCode ThreeColorParameters ThreeColorParameterChoice

/-- Every fixed dimension multiple has polynomial grid capacity. -/
theorem capacity_polynomial (N k : ℕ) :
    size (exponent N) ^ (k * size (exponent N)) ≤ (4 * max 1 N) ^ (32*k) := by
  have hv := volume_le_log_add_one N
  have hm := Nat.mul_le_mul_left k hv
  change (2 ^ exponent N) ^ (k * 2 ^ exponent N) ≤ _
  rw [← pow_mul]
  apply (Nat.pow_le_pow_right (by decide : 1 ≤ 2) ?_).trans
    (ThreeColorResourceBounds.pow_logarithmic_le_polynomial N (32*k))
  dsimp only [volume] at hm
  nlinarith only [hm]

theorem bits_size (x : List Bool) : listSize (x.map Bool.toNat) ≤ 2*x.length := by
  induction x with
  | nil => simp [listSize]
  | cons b xs ih =>
    cases b <;> simp only [List.map_cons, listSize, List.sum_cons, List.length_cons,
      Bool.toNat_false, Bool.toNat_true, Nat.size_zero, Nat.size_one] at * <;> omega

/-- Every magnitude in the actual edge program is polynomial in its public bit-string length. -/
theorem edge_budget_polynomial (x : List Bool) :
    GridEdge.budget
      (binaryDimension (exponent (ThreeColorCanonicalVerifier.graphOrder x)))
      (size (exponent (ThreeColorCanonicalVerifier.graphOrder x)))
      (size (exponent (ThreeColorCanonicalVerifier.graphOrder x))) x + 1 ≤
        1000 * (4 * (x.length + 1)) ^ 64 := by
  let N := ThreeColorCanonicalVerifier.graphOrder x
  let a := exponent N
  let M := (4 * (x.length + 1)) ^ 64
  have hN : N ≤ x.length := ThreeColorCanonicalVerifier.graphOrder_le_length x
  have hb : 4 * max 1 N ≤ 4 * (x.length+1) := by omega
  have hsize := (ThreeColorParameter.candidate_bound N a (exponent_ge_two N) le_rfl).2.1
  have ha := (ThreeColorParameter.candidate_bound N a (exponent_ge_two N) le_rfl).1
  have ht : binaryDimension a ≤ 416 * (x.length+1) := by
    rw [binaryDimension_eq]
    nlinarith only [ha, hN]
  have hs : size a ≤ 32 * (x.length+1) := by
    change 2^a ≤ _
    nlinarith only [hsize, hN]
  have hlin : x.length+1 ≤ M := by
    apply (show x.length+1 ≤ 4*(x.length+1) by omega).trans
    exact Nat.le_self_pow (by decide : 64 ≠ 0) _
  have hp2 : size a ^ (size a + size a) ≤ M := by
    have hp := capacity_polynomial N 2
    have hpow := Nat.pow_le_pow_left hb 64
    simpa only [show 32*2 = 64 from rfl, two_mul] using hp.trans hpow
  have hp1 : size a ^ size a ≤ M := by
    have hp := capacity_polynomial N 1
    have hpow := Nat.pow_le_pow_left hb 32
    have hpow' : (4*(x.length+1))^32 ≤ M := Nat.pow_le_pow_right (by omega) (by decide)
    simpa only [mul_one, one_mul] using hp.trans (hpow.trans hpow')
  have hbits := bits_size x
  have hsM := hs.trans (Nat.mul_le_mul_left 32 hlin)
  have htM := ht.trans (Nat.mul_le_mul_left 416 hlin)
  have hpos : 1 ≤ M := Nat.one_le_pow _ _ (by omega)
  change GridEdge.budget (binaryDimension a) (size a) (size a) x + 1 ≤ 1000*M
  dsimp only [GridEdge.budget]
  omega

/-- The exact production edge routine carries a uniform polynomial charged-time certificate. -/
theorem canonical_edge_cost : ∃ C : ℕ, ∀ (x : List Bool)
    (z : Fin (size (exponent (ThreeColorCanonicalVerifier.graphOrder x)) +
      size (exponent (ThreeColorCanonicalVerifier.graphOrder x))) →
      Field (exponent (ThreeColorCanonicalVerifier.graphOrder x))) (st : State 70 20),
    GridEdge.Input (binaryDimension (exponent (ThreeColorCanonicalVerifier.graphOrder x)))
      (size (exponent (ThreeColorCanonicalVerifier.graphOrder x)))
      (size (exponent (ThreeColorCanonicalVerifier.graphOrder x))) x z st →
    (GridEdge.program.run st).2 ≤ C * (x.length+1)^448 := by
  obtain ⟨C, hC⟩ := GridEdge.program_cost
  refine ⟨C * (1000 * 4^64)^7, ?_⟩
  intro x z st hi
  have hp := hC _ _ _ (size_le_fieldCode _) x z st hi
  have hb := Nat.pow_le_pow_left (edge_budget_polynomial x) 7
  apply hp.trans (Nat.mul_le_mul_left C hb) |>.trans_eq
  simp only [mul_pow, ← pow_mul, show 64*7 = 448 from rfl, Nat.mul_assoc]

end PCP.Lang.ProductionGrid
