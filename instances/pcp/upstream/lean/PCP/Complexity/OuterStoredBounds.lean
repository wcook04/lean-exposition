import PCP.Complexity.BranchQueryBounds
import PCP.Complexity.AmplifiedRoundCost

/-! Uniform stored-source bounds for every materialized outer sample. -/

namespace PCP.Lang.OuterBranch

open PCP.Algebraic BinaryFieldCode BinaryPolynomialSpace

/-- All semantic arrays have polynomial size; the unused scratch cell is charged explicitly. -/
def storedWidth (t n m : ℕ) (qs : List ℕ) (bs : List Bool) (scratch : List ℕ) : ℕ :=
  4*(t+1)*(n+m)+10*t+4*2^t+listSize qs+2*bs.length+listSize scratch+30

variable {t n m : ℕ} [NeZero t]

theorem Context.set_scratch54 (k : Kind) (a : Fin 5 → Field t) (ζ : Field t)
    (s : Sample k t n m) (qs : List ℕ) (bs : List Bool) (st : State 180 80)
    (hc : Context k a ζ s qs bs st) (scratch : List ℕ) :
    Context k a ζ s qs bs (setList st 54 scratch) := by
  constructor
  · simpa [setList, Function.update] using hc.width
  · simpa [setList, Function.update] using hc.degree
  · simpa [setList, Function.update] using hc.base
  · simpa [setList, Function.update] using hc.card
  · simpa [setList, Function.update] using hc.root
  · simpa [setList, Function.update] using hc.param
  · simpa [setList, Function.update] using hc.coin
  · simpa [setList, Function.update] using hc.interpParam
  · simpa [setList, Function.update] using hc.dimension
  · simpa [setList, Function.update] using hc.tag
  · simpa [setList, Function.update] using hc.vertices
  · simpa [setList, Function.update] using hc.pairs
  · simpa [setList, Function.update] using hc.proper
  · simpa [setList, Function.update] using hc.inner
  · simpa [setList, Function.update] using hc.affineLabels
  · simpa [setList, Function.update] using hc.cubicLabels
  · simpa [setList, Function.update] using hc.leftCode
  · simpa [setList, Function.update] using hc.rightCode
  · simpa [setList, Function.update] using hc.innerHadCode
  · simpa [setList, Function.update] using hc.modulus
  · simpa [setList, Function.update] using hc.empty
  · simpa [setList, Function.update] using hc.left
  · simpa [setList, Function.update] using hc.right
  · simpa [setList, Function.update] using hc.direction
  · simpa [setList, Function.update] using hc.label
  · simpa [setList, Function.update] using hc.nodes
  · simpa [setList, Function.update] using hc.history
  · simpa [setList, Function.update] using hc.answers
  · simpa [setList, Function.update] using hc.primaryBase
  · simpa [setList, Function.update] using hc.primaryAuxiliary
  · simpa [setList, Function.update] using hc.primaryLinear
  · simpa [setList, Function.update] using hc.primaryFactors
  · simpa [setList, Function.update] using hc.innerBase
  · simpa [setList, Function.update] using hc.innerAuxiliary
  · simpa [setList, Function.update] using hc.innerLinear
  · simpa [setList, Function.update] using hc.innerFactors
  · simpa [setList, Function.update] using hc.interpLeft
  · simpa [setList, Function.update] using hc.interpRight
  · simpa [setList, Function.update] using hc.interpLabel

theorem Context.storedBound (k : Kind) (a : Fin 5 → Field t) (ζ : Field t)
    (s : Sample k t n m) (qs : List ℕ) (bs : List Bool) (st : State 180 80)
    (hc : Context k a ζ s qs bs st) :
    StoredBound (storedWidth t n m qs bs (st.lists 54)) st := by
  let W := storedWidth t n m qs bs (st.lists 54)
  have hd : k.dimension n ≤ 4*n := by cases k <;> simp [Kind.dimension] <;> omega
  have hdeg := k.degree_le
  have htag : k.tag ≤ 3 := by cases k <;> decide
  have hbasic : t+1 ≤ W ∧ m ≤ W ∧ 4*n ≤ W ∧ 3 ≤ W ∧ 2*2^t+2 ≤ W ∧
      2*t ≤ W ∧ 5*(t+1) ≤ W ∧ listSize qs ≤ W ∧ 2*bs.length ≤ W ∧
      listSize (st.lists 54) ≤ W := by
    dsimp [W, storedWidth]
    have hmul : n+m ≤ (t+1)*(n+m) := Nat.le_mul_of_pos_left _ (by omega)
    simp only [Nat.mul_assoc]
    omega
  have hprod (d : ℕ) (hh : d ≤ 4*(n+m)) : d*(t+1) ≤ W := by
    have hh' := Nat.mul_le_mul_right (t+1) hh
    dsimp [W, storedWidth]
    nlinarith only [hh', Nat.zero_le (2^t), Nat.zero_le (listSize qs),
      Nat.zero_le bs.length, Nat.zero_le (listSize (st.lists 54)), Nat.zero_le t]
  have hp (d : ℕ) (hh : d ≤ 4*(n+m)) : Nat.size ((2^t)^d) ≤ W := by
    rw [← pow_mul, Nat.size_pow]
    have hh' := Nat.mul_le_mul_left t hh
    dsimp [W, storedWidth]
    nlinarith only [hh', Nat.zero_le (2^t), Nat.zero_le (listSize qs),
      Nat.zero_le bs.length, Nat.zero_le (listSize (st.lists 54)), Nat.zero_le t,
      Nat.zero_le n, Nat.zero_le m]
  have hl (r : ℕ) : Nat.size (2^BooleanCoefficientIndex.dimension t r) ≤ W := by
    have h := BooleanCoefficientTransform.masks_length_le t r
    rw [BooleanMask.masks_length] at h
    rw [Nat.size_pow]
    omega
  have hf (x : Field t) : Nat.size (fieldEquiv t x).val ≤ W :=
    (Nat.size_le.mpr (fieldEquiv t x).isLt).trans (by omega)
  have hpoint (x : Point k t n) : Nat.size (k.pointCode (fieldEquiv t) x) ≤ W :=
    (k.pointCode_size x).trans ((Nat.mul_le_mul_left t hd).trans (by
      have hh := hprod (4*n) (by omega)
      nlinarith only [hh, Nat.zero_le n]))
  have hcodes {d : ℕ} (x : Fin d → Field t) (hh : d ≤ 4*(n+m)) :
      listSize (List.ofFn (fun i => (fieldEquiv t (x i)).val)) ≤ W :=
    (StandardCorrection.fieldCodes_size x).trans (hprod d hh)
  have hbits (w : Fin t → ZMod 2) : listSize (List.ofFn (fun i => (w i).val)) ≤ W :=
    (InterpolationBranch.coordinateBits_size w).trans (by omega)
  have hlabel {r : ℕ} (p : Coefficients t r) :
      listSize (BooleanCoefficientList.encode p) ≤ W :=
    (HadamardLabel.encode_size p).trans (by omega)
  have hfactors {r : ℕ} (seed : Hadamard.TestRandomness t r) (hr : r ≤ 3) :
      listSize (HadamardRow.factorCodes seed) ≤ W := by
    have h := (HadamardRow.factorCodes_size seed).trans
      (Nat.mul_le_mul_right (2^t+1) (show r-1 ≤ 2 by omega))
    omega
  constructor
  · intro i hi hj
    have he : i = 120 ∨ i = 121 ∨ i = 122 ∨ i = 123 ∨ i = 124 ∨ i = 125 ∨
        i = 126 ∨ i = 127 ∨ i = 128 ∨ i = 129 ∨ i = 130 ∨ i = 131 ∨ i = 132 ∨
        i = 133 ∨ i = 134 ∨ i = 135 ∨ i = 136 ∨ i = 137 ∨ i = 138 := by omega
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [hc.width]; exact (size_le_self t).trans (by omega)
    · rw [hc.degree]; exact (size_le_self _).trans (hdeg.trans (by omega))
    · rw [hc.base]; exact (size_le_self m).trans (by omega)
    · rw [hc.card, Nat.size_pow]; exact hbasic.1
    · rw [hc.root]; exact hf _
    · rw [hc.param]; exact hf _
    · rw [hc.coin]; exact (InnerBranch.bool_size _).trans (by omega)
    · rw [hc.interpParam]; exact hf _
    · rw [hc.dimension]; exact (size_le_self _).trans (hd.trans (by omega))
    · rw [hc.tag]; exact (size_le_self _).trans (htag.trans (by omega))
    · rw [hc.vertices]; exact hp _ (by omega)
    · rw [hc.pairs]; exact hp _ (by omega)
    · rw [hc.proper]; exact hp _ (by omega)
    · rw [hc.inner]; exact hp _ (by omega)
    · rw [hc.affineLabels]; exact hl _
    · rw [hc.cubicLabels]; exact hl _
    · rw [hc.leftCode]; exact hpoint _
    · rw [hc.rightCode]; exact hpoint _
    · rw [hc.innerHadCode]
      have h : Nat.size (ThreeColorQueryIndex.innerIndex (fieldEquiv t) m 4
          (innerHadPoint s)).val ≤ t*(4*m) := by
        apply Nat.size_le.mpr
        simpa only [pow_mul] using
          (ThreeColorQueryIndex.innerIndex (fieldEquiv t) m 4 (innerHadPoint s)).isLt
      have hh := hprod (4*m) (by omega)
      exact h.trans (by nlinarith only [hh, Nat.zero_le m])
  · intro i hi hj hne
    have he : i = 40 ∨ i = 41 ∨ i = 42 ∨ i = 43 ∨ i = 44 ∨ i = 45 ∨ i = 46 ∨
        i = 47 ∨ i = 48 ∨ i = 50 ∨ i = 51 ∨ i = 52 ∨ i = 53 ∨ i = 54 ∨
        i = 55 ∨ i = 56 ∨ i = 57 ∨ i = 58 ∨ i = 59 ∨ i = 60 ∨ i = 61 := by omega
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [hc.modulus]; exact hbits _
    · rw [hc.empty]; exact Nat.zero_le _
    · rw [hc.left]; exact hcodes _ (by omega)
    · rw [hc.right]; exact hcodes _ (by omega)
    · rw [hc.direction]; exact hcodes _ (by omega)
    · rw [hc.label]; exact hbits _
    · rw [hc.nodes]; exact (StandardCorrection.fieldCodes_size _).trans (by omega)
    · rw [hc.history]; exact (by omega)
    · rw [hc.answers]; exact (AmplifiedStream.boolList_size bs).trans (by omega)
    · rw [hc.primaryBase]; exact hlabel _
    · rw [hc.primaryAuxiliary]; exact hlabel _
    · rw [hc.primaryLinear]; exact hlabel _
    · rw [hc.primaryFactors]; exact hfactors _ hdeg
    · exact (by omega)
    · rw [hc.innerBase]; exact hlabel _
    · rw [hc.innerAuxiliary]; exact hlabel _
    · rw [hc.innerLinear]; exact hlabel _
    · rw [hc.innerFactors]; exact hfactors _ (by decide)
    · rw [hc.interpLeft]; exact hcodes _ (by omega)
    · rw [hc.interpRight]; exact hcodes _ (by omega)
    · rw [hc.interpLabel]; exact hbits _

end PCP.Lang.OuterBranch
