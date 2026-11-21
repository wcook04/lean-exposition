import PCP.Complexity.HadamardRowLocation
import PCP.Complexity.ArithmeticExpressionCost

/-! Uniform bit-size bounds for every semantic physical address and payload. -/

namespace PCP.Lang.QueryAddress

open PCP.Algebraic ThreeColorVerifier BinaryPolynomialSpace BooleanCoefficientIndex
  ThreeColorQueryIndex

/-- A polynomial bound in dimensions and field cardinality, independent of the sample. -/
def inputWidth (t n m c : ℕ) : ℕ := 4*t*n+c*t*m+2^t+8

private theorem tuple_size (t d : ℕ) (v : Fin ((2 ^ t) ^ d)) : Nat.size v.val ≤ t*d := by
  apply Nat.size_le.mpr
  simpa only [pow_mul] using v.isLt

private theorem label_dimension (t r : ℕ) : dimension t r ≤ 2^t := by
  have h := BooleanCoefficientTransform.masks_length_le t r
  rwa [BooleanMask.masks_length] at h

private theorem vector_bound (t n m c tag x y u z : ℕ)
    (htag : Nat.size tag ≤ inputWidth t n m c)
    (hx : Nat.size x ≤ inputWidth t n m c) (hy : Nat.size y ≤ inputWidth t n m c)
    (hu : Nat.size u ≤ inputWidth t n m c) (hz : Nat.size z ≤ inputWidth t n m c)
    (i : Fin 11) :
    Nat.size (![tag, (2^t)^n, (2^t)^(n+n), (2^t)^((n+n)+(n+n)), (2^t)^(c*m),
      2^dimension t 1, 2^dimension t 3, x, y, u, z] i) ≤ inputWidth t n m c := by
  have hcard (d : ℕ) : Nat.size ((2^t)^d) = t*d+1 := by rw [← pow_mul, Nat.size_pow]
  have h1 := label_dimension t 1
  have h3 := label_dimension t 3
  have hpow (d : ℕ) (hd : d ≤ 4*n+c*m) :
      Nat.size ((2^t)^d) ≤ inputWidth t n m c := by
    rw [hcard]
    have h := Nat.mul_le_mul_left t hd
    dsimp [inputWidth]
    nlinarith only [h, Nat.zero_le (2^t)]
  fin_cases i
  · exact htag
  · exact hpow n (by omega)
  · exact hpow (n+n) (by omega)
  · exact hpow ((n+n)+(n+n)) (by omega)
  · exact hpow (c*m) (by omega)
  · change Nat.size (2^dimension t 1) ≤ _
    rw [Nat.size_pow]
    dsimp [inputWidth]
    omega
  · change Nat.size (2^dimension t 3) ≤ _
    rw [Nat.size_pow]
    dsimp [inputWidth]
    omega
  · exact hx
  · exact hy
  · exact hu
  · exact hz

theorem inputs_size {F : Type*} {t n m c : ℕ} (eF : F ≃ Fin (2 ^ t))
    (z : Query F n m c t) (i : Fin 11) :
    Nat.size (inputs eF (coefficientEquiv t 1) (coefficientEquiv t 3) z i) ≤
      inputWidth t n m c := by
  have hlabel (r : ℕ) (p : Coefficients t r) :
      Nat.size (coefficientEquiv t r p).val ≤ inputWidth t n m c :=
    (HadamardLabel.code_size p).trans (by dsimp [inputWidth]; omega)
  have htuple (d : ℕ) (v : Fin ((2^t)^d)) (hd : d ≤ 4*n+c*m) :
      Nat.size v.val ≤ inputWidth t n m c :=
    (tuple_size t d v).trans (by
      have h := Nat.mul_le_mul_left t hd
      dsimp [inputWidth]
      nlinarith only [h, Nat.zero_le (2^t)])
  have ht (tag : ℕ) (h : tag ≤ 7) : Nat.size tag ≤ inputWidth t n m c :=
    (size_le_self tag).trans (h.trans ((by decide : 7 ≤ 8).trans
      (Nat.le_add_left 8 _)))
  have hz : Nat.size 0 ≤ inputWidth t n m c := by simp
  have hv (x : Fin n → F) : Nat.size (vertexIndex eF n x).val ≤ inputWidth t n m c :=
    htuple n _ (by omega)
  have hp (x : PairPoint F n) : Nat.size (pairIndex eF n x).val ≤ inputWidth t n m c :=
    htuple (n+n) _ (by omega)
  have hd (x : ProperPoint F n) : Nat.size (properIndex eF n x).val ≤ inputWidth t n m c :=
    htuple ((n+n)+(n+n)) _ (by omega)
  have hi (x : BinaryLocalCorrection.InnerPoint F m c) :
      Nat.size (innerIndex eF m c x).val ≤ inputWidth t n m c := htuple (c*m) _ (by omega)
  cases z with
  | color x p =>
      exact vector_bound t n m c 0 _ 0 0 _ (ht 0 (by decide))
        (hv x) hz hz (hlabel 3 p) i
  | validCert x p =>
      exact vector_bound t n m c 1 _ 0 0 _ (ht 1 (by decide))
        (hp x) hz hz (hlabel 1 p) i
  | difference x p =>
      exact vector_bound t n m c 2 _ 0 0 _ (ht 2 (by decide))
        (hp x) hz hz (hlabel 3 p) i
  | properCert x p =>
      exact vector_bound t n m c 3 _ 0 0 _ (ht 3 (by decide))
        (hd x) hz hz (hlabel 1 p) i
  | colorLine uv x p =>
      exact vector_bound t n m c 4 _ _ _ _ (ht 4 (by decide))
        (hv uv.1) (hv uv.2) (hi x) (hlabel 1 p) i
  | validLine uv x p =>
      exact vector_bound t n m c 5 _ _ _ _ (ht 5 (by decide))
        (hp uv.1) (hp uv.2) (hi x) (hlabel 1 p) i
  | differenceLine uv x p =>
      exact vector_bound t n m c 6 _ _ _ _ (ht 6 (by decide))
        (hp uv.1) (hp uv.2) (hi x) (hlabel 1 p) i
  | properLine uv x p =>
      exact vector_bound t n m c 7 _ _ _ _ (ht 7 (by decide))
        (hd uv.1) (hd uv.2) (hi x) (hlabel 1 p) i

/-- The fixed arithmetic address expression increases bit width by only a fixed factor. -/
def widthConstant : ℕ := program.C*(program.width+program.csize+1)+1

theorem address_size {F : Type*} {t n m c : ℕ} (eF : F ≃ Fin (2 ^ t))
    (z : Query F n m c t) :
    Nat.size (ThreeColorQueryIndex.equiv eF (coefficientEquiv t 1)
      (coefficientEquiv t 3) z).val ≤ widthConstant*(inputWidth t n m c+1) := by
  rw [← term_eq]
  have h := ArithmeticExpression.eval_size_le term
    (inputs eF (coefficientEquiv t 1) (coefficientEquiv t 3) z)
    (inputWidth t n m c) (inputs_size eF z)
  exact h.trans (Nat.mul_le_mul_right _ (by dsimp [widthConstant, program]; omega))

def width (t n m c : ℕ) : ℕ := widthConstant*(inputWidth t n m c+1)

attribute [local irreducible] program ArithmeticExpression.scalar

theorem inputWidth_le_width (t n m c : ℕ) : inputWidth t n m c ≤ width t n m c := by
  have hc : 1 ≤ widthConstant := by unfold widthConstant; omega
  have h := Nat.mul_le_mul_right (inputWidth t n m c+1) hc
  simp only [one_mul] at h
  exact (Nat.le_succ _).trans h

theorem inputs_size_le {F : Type*} {t n m c W : ℕ} (eF : F ≃ Fin (2 ^ t))
    (z : Query F n m c t) (hW : width t n m c ≤ W) (i : Fin 11) :
    Nat.size (inputs eF (coefficientEquiv t 1) (coefficientEquiv t 3) z i) ≤ W :=
  (inputs_size eF z i).trans ((inputWidth_le_width t n m c).trans hW)

end PCP.Lang.QueryAddress
