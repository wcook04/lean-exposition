import PCP.Complexity.ThreeColorSeedGuard

/-! Polynomial radix bounds and exact stored-code sizes for the zero guard. -/

namespace PCP.Lang.ThreeColorSeedGuard

open PCP.Algebraic ThreeColorSeedIndex ThreeColorSeedSize ThreeColorFullFieldSampling

variable {F : Type*} [Field F] [Algebra (ZMod 2) F] {t d m : ℕ}
variable (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2))

def derivedCodes (s : RawDerivedSample F d m 4 t 3) : List ℕ :=
  [(coefficientCodec t 3).equiv s.2.2 |>.val,
   (callCodec ρ ((Codec.fin d).sum (Codec.fin d)) m 4).equiv s.2.1.2.2 |>.val,
   (callCodec ρ ((Codec.fin d).sum (Codec.fin d)) m 4).equiv s.2.1.2.1 |>.val,
   (bitsCodec t).equiv s.2.1.1 |>.val,
   ((Codec.fin d).function (fieldCodec ρ)).equiv s.1 |>.val, 0, 0]

theorem derivedCodes_split (s : RawDerivedSample F d m 4 t 3) :
    (MixedRadixDecode.split ((derivedCodec ρ d m 4 3).equiv s).val
      ((NestedSeed.derivedLayout ρ d m 4).radices ++ List.replicate 2 1)).1 =
      derivedCodes ρ s := by
  rw [(NestedSeed.derivedLayout ρ d m 4).decode_padded s 2]
  rfl

theorem derivedCodes_size (s : RawDerivedSample F d m 4 t 3) :
    listSize (derivedCodes ρ s) ≤ 7*(Nat.size ((derivedCodec ρ d m 4 3).equiv s).val+1) := by
  rw [← derivedCodes_split]
  exact MixedRadixDecode.split_listSize _ _

theorem derived_code_size (s : RawDerivedSample F d m 4 t 3) (z : ℕ)
    (hz : z ∈ derivedCodes ρ s) :
    Nat.size z ≤ Nat.size ((derivedCodec ρ d m 4 3).equiv s).val := by
  apply Nat.size_le_size
  apply MixedRadixDecode.split_digit_le _
    ((NestedSeed.derivedLayout ρ d m 4).radices ++ List.replicate 2 1)
  rwa [derivedCodes_split]

def callCodes (s : RawCallSeed F (Fin d ⊕ Fin d) m 4 t) : List ℕ :=
  [(innerCodec ρ m 4).equiv s.2.2.2 |>.val,
   (innerPointCodec ρ m 4).equiv s.2.2.1 |>.val,
   (fieldCodec ρ).equiv s.2.1 |>.val,
   (((Codec.fin d).sum (Codec.fin d)).function (fieldCodec ρ)).equiv s.1 |>.val, 0, 0, 0]

theorem callCodes_split (s : RawCallSeed F (Fin d ⊕ Fin d) m 4 t) :
    (MixedRadixDecode.split
      ((callCodec ρ ((Codec.fin d).sum (Codec.fin d)) m 4).equiv s).val
      ((NestedSeed.callLayout ρ ((Codec.fin d).sum (Codec.fin d)) m 4).radices ++
        List.replicate 3 1)).1 = callCodes ρ s := by
  rw [(NestedSeed.callLayout ρ ((Codec.fin d).sum (Codec.fin d)) m 4).decode_padded s 3]
  rfl

theorem callCodes_size (s : RawCallSeed F (Fin d ⊕ Fin d) m 4 t) :
    listSize (callCodes ρ s) ≤
      7*(Nat.size ((callCodec ρ ((Codec.fin d).sum (Codec.fin d)) m 4).equiv s).val+1) := by
  rw [← callCodes_split]
  exact MixedRadixDecode.split_listSize _ _

omit [Field F] [Algebra (ZMod 2) F] in
theorem derivedTerms_bound (t d m : ℕ) (i : Fin 7) :
    (NestedSeed.derivedTerms i).eval ![d,m,4,t] ≤ 32*(t+d+m+2^t+1)^2 := by
  have h2 := Nat.choose_le_two_pow t 2
  have h3 := Nat.choose_le_two_pow t 3
  have hq := Nat.two_pow_pos t
  have hcall : NestedSeed.callBits.eval ![d,m,4,t] =
      2*(t*d)+t+t*(4*m)+innerBits m 4 t := by
    change 2*(NestedSeed.pointBits.eval ![d,m,4,t])+t+
      NestedSeed.innerPointBits.eval ![d,m,4,t]+SeedArithmetic.inner.eval ![d,m,4,t] = _
    rw [NestedSeed.pointBits_eval, NestedSeed.innerPointBits_eval, NestedSeed.inner_eval]
  fin_cases i <;>
    simp [NestedSeed.derivedTerms, hcall, NestedSeed.pointBits_eval,
      NestedSeed.coefficientThree_eval, coefficientBits_three, innerBits, hadamardBits_one,
      ArithmeticExpression.Term.eval]
  all_goals nlinarith only [h2, h3, hq, Nat.zero_le (t^2), Nat.zero_le (d^2),
    Nat.zero_le (m^2), Nat.zero_le ((2^t)^2), Nat.zero_le (t*d), Nat.zero_le (t*m),
    Nat.zero_le (t*2^t), Nat.zero_le (d*m), Nat.zero_le (d*2^t), Nat.zero_le (m*2^t)]

omit [Field F] [Algebra (ZMod 2) F] in
theorem callTerms_bound (t d m : ℕ) (i : Fin 7) :
    (NestedSeed.callTerms i).eval ![d+d,m,4,t] ≤ 32*(t+d+m+2^t+1)^2 := by
  have hq := Nat.two_pow_pos t
  fin_cases i <;>
    simp [NestedSeed.callTerms, NestedSeed.pointBits_eval, NestedSeed.innerPointBits_eval,
      NestedSeed.inner_eval, innerBits, hadamardBits_one, ArithmeticExpression.Term.eval]
  all_goals nlinarith only [hq, Nat.zero_le (t^2), Nat.zero_le (d^2),
    Nat.zero_le (m^2), Nat.zero_le ((2^t)^2), Nat.zero_le (t*d), Nat.zero_le (t*m),
    Nat.zero_le (t*2^t), Nat.zero_le (d*m), Nat.zero_le (d*2^t), Nat.zero_le (m*2^t)]

end PCP.Lang.ThreeColorSeedGuard
