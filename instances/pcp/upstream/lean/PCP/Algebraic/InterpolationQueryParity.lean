import PCP.Algebraic.ComputableBinaryLocalCorrection
import PCP.Algebraic.BinarySeedPadding

/-!
# The binary interpolation residual is query parity

The identity includes zero-weight omissions and repeated physical addresses. It
therefore applies to the actual first-match oracle of every answer history.
-/

namespace PCP.Algebraic.ComputableBinaryLagrangeConstraint

open BinaryPolynomialSpace PolynomialLine

variable {F σ : Type*} [Field F] [DecidableEq F] [Algebra (ZMod 2) F] {c t r : ℕ}

theorem filtered_sum (hr : 1 ≤ r) (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2))
    (a : Fin (c + 1) → F) (H : (σ → F) → Coefficients t r → ZMod 2)
    (u v : σ → F) (z : F) (w : Fin t → ZMod 2) (is : List (Fin (c + 1))) :
    (((is.filterMap (fun i => if FieldQueryArithmetic.interpolationWeight a z i = 0 then none
      else some (point u v (a i), BooleanCoefficientArithmetic.homogeneousIndex hr
        (FieldQueryArithmetic.scaleLabel ρ (FieldQueryArithmetic.interpolationWeight a z i) w))))
      ).map (fun p => H p.1 p.2)).sum =
    (is.map (fun i => weightedRead hr ρ (H (point u v (a i)))
      (FieldQueryArithmetic.interpolationWeight a z i) w)).sum := by
  induction is with
  | nil => rfl
  | cons i is ih =>
      by_cases h : FieldQueryArithmetic.interpolationWeight a z i = 0 <;>
        simp only [List.filterMap_cons, h, ↓reduceIte, List.map_cons, List.sum_cons,
          weightedRead, zero_add, ih]

/-- The verifier checks the parity of exactly the list it queries. -/
theorem check_eq_query_sum (hr : 1 ≤ r) (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2))
    (a : Fin (c + 1) → F) (H : (σ → F) → Coefficients t r → ZMod 2)
    (u v : σ → F) (z : F) (w : Fin t → ZMod 2) :
    check hr ρ a H u v z w =
      ((queries hr ρ a u v z w).map (fun p => H p.1 p.2)).sum := by
  rw [check, sub_eq_add_neg, ZMod.neg_eq_self_mod_two]
  simp only [queries, List.map_cons, List.sum_cons]
  rw [filtered_sum, ← List.ofFn_eq_map, List.sum_ofFn]

end PCP.Algebraic.ComputableBinaryLagrangeConstraint

namespace PCP.Algebraic.BinarySeedPadding

/-- Boolean coordinates have the same numeric cast as the public history representation. -/
theorem boolEquiv_toNat (b : Bool) : boolEquiv b = (b.toNat : ZMod 2) := by
  cases b <;> rfl

theorem bool_sum_cast {α : Type*} (xs : List α) (f : α → Bool) :
    (xs.map (fun x => boolEquiv (f x))).sum = ((xs.map (fun x => (f x).toNat)).sum : ZMod 2) := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      rw [List.map_cons, List.sum_cons, List.map_cons, List.sum_cons, Nat.cast_add, ih,
        boolEquiv_toNat]

end PCP.Algebraic.BinarySeedPadding
