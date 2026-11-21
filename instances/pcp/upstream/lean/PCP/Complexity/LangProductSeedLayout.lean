import PCP.Complexity.ThreeColorRawSeedSemantics

/-!
# Checked decomposition of nested product seed codecs

Products expose their right component first, exactly as the production codec.
Leaves may remain compound codes for a later callback-specific decoding pass.
-/

namespace PCP.Lang

open PCP.Algebraic ThreeColorSeedIndex

namespace MixedRadixDecode

theorem split_append (code : ℕ) (xs ys : List ℕ) :
    split code (xs ++ ys) =
      ((split code xs).1 ++ (split (split code xs).2 ys).1,
        (split (split code xs).2 ys).2) := by
  induction xs generalizing code with
  | nil => simp [split]
  | cons x xs ih => simp [split, ih]

end MixedRadixDecode

structure SeedLayout {A : Type*} (a : Codec A) where
  radices : List ℕ
  values : A → List ℕ
  product : radices.prod = a.size
  decode : ∀ x, (MixedRadixDecode.split (a.equiv x).val radices).1 = values x

namespace SeedLayout

variable {A B : Type*}

def leaf (a : Codec A) : SeedLayout a where
  radices := [a.size]
  values := fun x => [(a.equiv x).val]
  product := by simp
  decode := fun x => by simp [MixedRadixDecode.split, Nat.mod_eq_of_lt (a.equiv x).isLt]

theorem prod_code (a : Codec A) (b : Codec B) (x : A) (y : B) :
    ((a.prod b).equiv (x, y)).val = (b.equiv y).val + b.size * (a.equiv x).val := by
  rfl

def prod {a : Codec A} {b : Codec B} (l : SeedLayout a) (r : SeedLayout b) :
    SeedLayout (a.prod b) where
  radices := r.radices ++ l.radices
  values := fun x => r.values x.2 ++ l.values x.1
  product := by
    simp only [List.prod_append, r.product, l.product, Codec.prod]
    exact Nat.mul_comm _ _
  decode := fun ⟨x, y⟩ => by
    rw [MixedRadixDecode.split_append, prod_code]
    have hmod : ((b.equiv y).val + b.size * (a.equiv x).val) % r.radices.prod =
        (b.equiv y).val := by
      rw [r.product, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (b.equiv y).isLt]
    have hdiv : ((b.equiv y).val + b.size * (a.equiv x).val) / r.radices.prod =
        (a.equiv x).val := by
      have hp : 0 < b.size := (Nat.zero_le _).trans_lt (b.equiv y).isLt
      rw [r.product, Nat.add_mul_div_left _ _ hp, Nat.div_eq_of_lt (b.equiv y).isLt]
      simp
    simp only [MixedRadixDecode.split_quotient, hdiv, l.decode]
    rw [← RawSeed.split_mod_product, hmod, r.decode]

theorem decode_padded {a : Codec A} (l : SeedLayout a) (x : A) (k : ℕ) :
    (MixedRadixDecode.split (a.equiv x).val
      (l.radices ++ List.replicate k 1)).1 = l.values x ++ List.replicate k 0 := by
  have hz : (MixedRadixDecode.split 0 (List.replicate k 1)).1 = List.replicate k 0 := by
    induction k with
    | zero => rfl
    | succ k ih => simp [MixedRadixDecode.split, List.replicate_succ, ih]
  rw [MixedRadixDecode.split_append]
  simp only [l.decode, MixedRadixDecode.split_quotient, l.product,
    Nat.div_eq_of_lt (a.equiv x).isLt, hz]

end SeedLayout
end PCP.Lang
