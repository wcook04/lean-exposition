import PCP.Complexity.OuterStoredBounds
import PCP.Complexity.ThreeColorSetupCost
import PCP.Complexity.ThreeColorSeedArithmetic

/-! Input-polynomial bounds for the actual canonical verifier's numeric parameters. -/

namespace PCP.Lang.CanonicalResourceBounds

open PCP.Algebraic ThreeColorParameterChoice ThreeColorParameters

abbrev fieldWidth (N : ℕ) : ℕ := binaryDimension (exponent N)
abbrev dimension (N : ℕ) : ℕ := size (exponent N)

def coreConstant : ℕ := ThreeColorContext.fieldConstant+500

def coreBound (N : ℕ) : ℕ := coreConstant*(N+1)^12

attribute [local irreducible] ThreeColorContext.fieldConstant

theorem core_bounds (N : ℕ) :
    1 ≤ coreBound N ∧ fieldWidth N ≤ coreBound N ∧ dimension N ≤ coreBound N ∧
      2^fieldWidth N ≤ coreBound N := by
  have hq := ThreeColorContext.field_cardinality_bound N
  have hc : ThreeColorContext.fieldConstant ≤ coreConstant := Nat.le_add_right _ _
  have hq' := hq.trans (Nat.mul_le_mul_right ((N+1)^12) hc)
  have ht : fieldWidth N ≤ 2^fieldWidth N := Nat.lt_two_pow_self.le
  have hd := size_le_fieldCode (exponent N)
  exact ⟨(Nat.two_pow_pos _).trans_le hq', ht.trans hq', hd.trans hq', hq'⟩

attribute [local irreducible] QueryAddress.widthConstant

theorem query_width (N : ℕ) :
    QueryAddress.width (fieldWidth N) (dimension N) (dimension N) 4 ≤
      18*QueryAddress.widthConstant*(coreBound N)^2 := by
  obtain ⟨hb, ht, hn, hq⟩ := core_bounds N
  have htn := Nat.mul_le_mul ht hn
  have hlin : coreBound N ≤ (coreBound N)^2 := Nat.le_pow (by decide)
  have h1 : 1 ≤ (coreBound N)^2 := Nat.one_le_pow _ _ hb
  have harg : QueryAddress.inputWidth (fieldWidth N) (dimension N) (dimension N) 4+1 ≤
      18*(coreBound N)^2 := by
    unfold QueryAddress.inputWidth
    nlinarith only [htn, hq, hlin, h1]
  exact (Nat.mul_le_mul_left QueryAddress.widthConstant harg).trans_eq (by ring)

theorem stored_width (N : ℕ) (qs : List ℕ) (bs : List Bool) (scratch : List ℕ) :
    OuterBranch.storedWidth (fieldWidth N) (dimension N) (dimension N) qs bs scratch ≤
      60*(coreBound N)^2+listSize qs+2*bs.length+listSize scratch := by
  obtain ⟨hb, ht, hn, hq⟩ := core_bounds N
  have htn := Nat.mul_le_mul ht hn
  have hlin : coreBound N ≤ (coreBound N)^2 := Nat.le_pow (by decide)
  have h1 : 1 ≤ (coreBound N)^2 := Nat.one_le_pow _ _ hb
  unfold OuterBranch.storedWidth
  nlinarith only [htn, ht, hn, hq, hlin, h1]

/-- The actual seven branch codes use no more bits than the whole finite seed. -/
theorem branch_bits (N : ℕ) (i : Fin 7) :
    SeedArithmetic.branchBits (dimension N) (dimension N) 4 (fieldWidth N) i ≤
      32000000*(N+1) := by
  have hsum := Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) =>
    Nat.zero_le (SeedArithmetic.branchBits (dimension N) (dimension N) 4 (fieldWidth N) j))
    (Finset.mem_univ i)
  rw [SeedArithmetic.branchBits_sum] at hsum
  have hb := ThreeColorBinaryVerifier.randomBits_le N
  have hlog : Nat.clog 2 N ≤ N :=
    Nat.clog_le_of_le_pow (Nat.le_of_lt (Nat.lt_pow_self (by decide)))
  exact (hsum.trans hb).trans (Nat.mul_le_mul_left _ (Nat.add_le_add_right hlog 1))

/-- A common monomial absorbs sample storage and all finite query metadata. -/
theorem combined_width (N : ℕ) (qs : List ℕ) (bs : List Bool) (scratch : List ℕ) :
    QueryAddress.width (fieldWidth N) (dimension N) (dimension N) 4 +
      OuterBranch.storedWidth (fieldWidth N) (dimension N) (dimension N) qs bs scratch ≤
      ((18*QueryAddress.widthConstant+60)*coreConstant^2+4)*
        (N+listSize qs+bs.length+listSize scratch+1)^24 := by
  have hq := query_width N
  have hs := stored_width N qs bs scratch
  let U := N+listSize qs+bs.length+listSize scratch+1
  have hU : 1 ≤ U := by dsimp [U]; omega
  have hpow : (coreBound N)^2 ≤ coreConstant^2*U^24 := by
    unfold coreBound
    rw [mul_pow, ← pow_mul]
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by dsimp [U]; omega) 24)
  have hlin : U ≤ U^24 := Nat.le_pow (by decide)
  have hlow : listSize qs+2*bs.length+listSize scratch ≤ 4*U^24 := by
    dsimp [U] at hlin ⊢
    omega
  have hmain := Nat.mul_le_mul_left (18*QueryAddress.widthConstant+60) hpow
  change _ ≤ ((18*QueryAddress.widthConstant+60)*coreConstant^2+4)*U^24
  nlinarith only [hq, hs, hmain, hlow]

end PCP.Lang.CanonicalResourceBounds
