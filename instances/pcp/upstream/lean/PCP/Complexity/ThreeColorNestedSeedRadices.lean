import PCP.Complexity.ThreeColorNestedSeedLang

/-! # The nested seed radix expressions agree with the actual production codecs -/

namespace PCP.Lang.NestedSeed

open ArithmeticExpression PCP.Algebraic ThreeColorSeedIndex ThreeColorSeedSize

variable {F : Type*} [Field F] [Algebra (ZMod 2) F] {t : ℕ}
variable (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2))

theorem coefficientThree_eval (n m c t : ℕ) :
    SeedArithmetic.coefficientThree.eval ![n, m, c, t] = coefficientBits t 3 := by
  have h2 : SeedArithmetic.chooseTwo.eval ![n, m, c, t] = t.choose 2 := by
    change t * (t - 1) / 2 = t.choose 2
    rw [Nat.choose_two_right]
  change 1 + t + SeedArithmetic.chooseTwo.eval ![n, m, c, t] +
    SeedArithmetic.chooseThree.eval ![n, m, c, t] = _
  rw [h2, SeedArithmetic.chooseThree_eval, coefficientBits_three]
  rfl

theorem hadamard_eval (cubic : Bool) (n m c t : ℕ) :
    (SeedArithmetic.hadamard cubic).eval ![n, m, c, t] =
      hadamardBits t (if cubic then 3 else 1) := by
  have h2 : SeedArithmetic.chooseTwo.eval ![n, m, c, t] = t.choose 2 := by
    change t * (t - 1) / 2 = t.choose 2
    rw [Nat.choose_two_right]
  cases cubic with
  | false =>
      change 3 * (1 + t) = hadamardBits t 1
      rw [hadamardBits_one]
  | true =>
      change 5 + 5 * t + 3 * SeedArithmetic.chooseTwo.eval ![n, m, c, t] +
        2 * SeedArithmetic.chooseThree.eval ![n, m, c, t] = hadamardBits t 3
      rw [h2, SeedArithmetic.chooseThree_eval, hadamardBits_three]
      rfl

theorem inner_eval (n m c t : ℕ) :
    SeedArithmetic.inner.eval ![n, m, c, t] = innerBits m c t := by
  change 1 + 3 * t * (c * m) + 2 * t +
    (SeedArithmetic.hadamard false).eval ![n, m, c, t] = _
  rw [hadamard_eval]
  rfl

theorem hadamard_size (cubic : Bool) :
    (hadamardCodec t (if cubic then 3 else 1)).size =
      2 ^ hadamardBits t (if cubic then 3 else 1) := by
  have hdim (r : ℕ) : BooleanCoefficientIndex.dimension t r = coefficientBits t r := rfl
  cases cubic
  all_goals first
  | change (hadamardCodec t 1).size = 2 ^ hadamardBits t 1
  | change (hadamardCodec t 3).size = 2 ^ hadamardBits t 3
  all_goals
    simp only [hadamardCodec, coefficientCodec, Codec.prod, Codec.piFin, hdim,
      Fin.prod_univ_succ, Fin.val_zero, Fin.val_succ, Nat.reduceSub, Nat.reduceAdd,
      Fin.prod_univ_zero, Nat.mul_one, coefficientBits_one, coefficientBits_two,
      coefficientBits_three, ← pow_add, hadamardBits_one, hadamardBits_three]
    congr 1
    ring

theorem inner_size (m c : ℕ) : (innerCodec ρ m c).size = 2 ^ innerBits m c t := by
  have hh := hadamard_size (t := t) false
  change (hadamardCodec t 1).size = 2 ^ hadamardBits t 1 at hh
  simp only [innerCodec, binaryLowDegreeCodec, Codec.prod, Codec.function,
    Codec.fin, boolCodec, fieldCodec, bitsCodec, hh,
    ← pow_mul, ← pow_add, ← Nat.pow_succ', innerBits, Nat.succ_eq_add_one]
  congr 1
  ring

theorem point_size {σ : Type*} (σc : Codec σ) :
    (σc.function (fieldCodec ρ)).size = 2 ^ (t * σc.size) := by
  simp only [Codec.function, fieldCodec, pow_mul]

theorem innerPoint_size (m c : ℕ) :
    (innerPointCodec ρ m c).size = 2 ^ (t * (c * m)) := by
  simp only [innerPointCodec, Codec.prod, Codec.fin, point_size]

theorem call_size (n m c : ℕ) :
    (callCodec ρ ((Codec.fin n).sum (Codec.fin n)) m c).size =
      2 ^ callBits.eval ![n, m, c, t] := by
  change (2 ^ t) ^ (n + n) *
    (2 ^ t * ((innerPointCodec ρ m c).size * (innerCodec ρ m c).size)) = _
  rw [innerPoint_size, inner_size]
  change _ = 2 ^ (2 * (t * n) + t + t * (c * m) +
    SeedArithmetic.inner.eval ![n, m, c, t])
  rw [inner_eval]
  simp only [← pow_mul, ← pow_add]
  congr 1
  ring

theorem pointBits_eval (n m c t : ℕ) : pointBits.eval ![n, m, c, t] = t * n := rfl

theorem innerPointBits_eval (n m c t : ℕ) :
    innerPointBits.eval ![n, m, c, t] = t * (c * m) := rfl

theorem outer_radices {σ : Type*} (σc : Codec σ) (n m c : ℕ) (cubic : Bool)
    (hn : σc.size = n) :
    (outerLayout ρ σc m c (if cubic then 3 else 1)).radices =
      List.ofFn (fun i => 2 ^ (outerTerms cubic i).eval ![n, m, c, t]) := by
  change [(innerCodec ρ m c).size, (hadamardCodec t (if cubic then 3 else 1)).size,
    (bitsCodec t).size, (innerPointCodec ρ m c).size, (fieldCodec ρ).size,
    (σc.function (fieldCodec ρ)).size, (σc.function (fieldCodec ρ)).size] = _
  rw [inner_size, hadamard_size, innerPoint_size, point_size, hn]
  simp [outerTerms, List.ofFn_succ, inner_eval, hadamard_eval, pointBits_eval,
    innerPointBits_eval, fieldCodec, bitsCodec, Term.eval]

theorem inner_radices (n m c : ℕ) :
    (innerLayout ρ m c).radices =
      List.ofFn (fun i => 2 ^ (innerTerms i).eval ![n, m, c, t]) := by
  change [(bitsCodec t).size, (fieldCodec ρ).size, (innerPointCodec ρ m c).size,
    (innerPointCodec ρ m c).size, (hadamardCodec t 1).size,
    (innerPointCodec ρ m c).size, 2] = _
  have hh := hadamard_size (t := t) false
  change (hadamardCodec t 1).size = 2 ^ hadamardBits t 1 at hh
  rw [innerPoint_size, hh]
  simp [innerTerms, List.ofFn_succ, hadamard_eval, innerPointBits_eval,
    fieldCodec, bitsCodec, Term.eval]

theorem call_radices {σ : Type*} (σc : Codec σ) (n m c : ℕ) (hn : σc.size = n) :
    (callLayout ρ σc m c).radices ++ List.replicate 3 1 =
      List.ofFn (fun i => 2 ^ (callTerms i).eval ![n, m, c, t]) := by
  change [(innerCodec ρ m c).size, (innerPointCodec ρ m c).size,
    (fieldCodec ρ).size, (σc.function (fieldCodec ρ)).size, 1, 1, 1] = _
  rw [inner_size, innerPoint_size, point_size, hn]
  simp [callTerms, List.ofFn_succ, inner_eval, pointBits_eval,
    innerPointBits_eval, fieldCodec, Term.eval]

theorem derived_radices (n m c : ℕ) :
    (derivedLayout ρ n m c).radices ++ List.replicate 2 1 =
      List.ofFn (fun i => 2 ^ (derivedTerms i).eval ![n, m, c, t]) := by
  change [(coefficientCodec t 3).size,
    (callCodec ρ ((Codec.fin n).sum (Codec.fin n)) m c).size,
    (callCodec ρ ((Codec.fin n).sum (Codec.fin n)) m c).size,
    (bitsCodec t).size, ((Codec.fin n).function (fieldCodec ρ)).size, 1, 1] = _
  rw [call_size, point_size]
  change [2 ^ coefficientBits t 3, 2 ^ callBits.eval ![n, m, c, t],
    2 ^ callBits.eval ![n, m, c, t], 2 ^ t, 2 ^ (t * n), 1, 1] = _
  simp [derivedTerms, List.ofFn_succ, coefficientThree_eval, pointBits_eval, Term.eval]

theorem difference_radices (n m c : ℕ) :
    (differenceLayout ρ n).radices ++ List.replicate 4 1 =
      List.ofFn (fun i => 2 ^ (differenceTerms i).eval ![n, m, c, t]) := by
  change [(bitsCodec t).size, ((Codec.fin n).function (fieldCodec ρ)).size,
    ((Codec.fin n).function (fieldCodec ρ)).size, 1, 1, 1, 1] = _
  rw [point_size]
  simp [differenceTerms, List.ofFn_succ, pointBits_eval, Codec.fin, bitsCodec, Term.eval]

end PCP.Lang.NestedSeed
