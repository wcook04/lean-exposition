/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Complexity.HadamardRowSpec
import PCP.Complexity.LangSeedDecode

/-!
# Flattening the actual Hadamard seed codec

The lowest digits are the heterogeneous factor coefficients, followed by the
linear label, auxiliary label, and base label. These are the actual production
codec digits, rather than an alternate seed representation.
-/

namespace PCP.Lang.HadamardSeed

open scoped BigOperators
open PCP.Algebraic BinaryPolynomialSpace ThreeColorSeedIndex HadamardLabel

variable {t r : ℕ}

def cardinal (t a : ℕ) : ℕ := 2 ^ BooleanCoefficientIndex.dimension t a

def radices (t r : ℕ) : List ℕ :=
  (List.ofFn fun k : Fin (r - 1) => cardinal t (k.val + 1)) ++
    [cardinal t 1, cardinal t r, cardinal t r]

theorem split_append (n : ℕ) (xs ys : List ℕ) :
    (MixedRadixDecode.split n (xs ++ ys)).1 =
      (MixedRadixDecode.split n xs).1 ++
        (MixedRadixDecode.split (n / xs.prod) ys).1 := by
  induction xs generalizing n with
  | nil => simp [MixedRadixDecode.split]
  | cons x xs ih =>
      simp only [List.cons_append, MixedRadixDecode.split, List.prod_cons, List.cons_append]
      rw [ih, Nat.div_div_eq_div_mul]

theorem split_mod (n : ℕ) (xs : List ℕ) :
    (MixedRadixDecode.split (n % xs.prod) xs).1 = (MixedRadixDecode.split n xs).1 := by
  induction xs generalizing n with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.prod_cons, MixedRadixDecode.split]
      rw [Nat.mod_mod_of_dvd n (dvd_mul_right x xs.prod), Nat.mod_mul_right_div_self, ih]

theorem codecProd_div {A B : Type*} (a : Codec A) (b : Codec B) (x : A) (y : B) :
    ((a.prod b).equiv (x, y)).val / b.size = (a.equiv x).val := by
  exact congrArg (fun z : Fin a.size × Fin b.size => z.1.val)
    (finProdFinEquiv.symm_apply_apply (a.equiv x, b.equiv y))


theorem codecProd_mod {A B : Type*} (a : Codec A) (b : Codec B) (x : A) (y : B) :
    ((a.prod b).equiv (x, y)).val % b.size = (b.equiv y).val := by
  exact congrArg (fun z : Fin a.size × Fin b.size => z.2.val)
    (finProdFinEquiv.symm_apply_apply (a.equiv x, b.equiv y))

theorem split_codecProd_flat {A B : Type*} (a : Codec A) (b : Codec B) (x : A) (y : B)
    (xs ys : List ℕ) (hy : ys.prod = b.size) :
    (MixedRadixDecode.split ((a.prod b).equiv (x, y)).val (ys ++ xs)).1 =
      (MixedRadixDecode.split (b.equiv y).val ys).1 ++
        (MixedRadixDecode.split (a.equiv x).val xs).1 := by
  rw [split_append, hy, codecProd_div]
  conv_lhs => lhs; rw [← split_mod _ ys]
  rw [hy, codecProd_mod]

theorem split_coefficient (p : Coefficients t r) :
    (MixedRadixDecode.split (code p) [cardinal t r]).1 = [code p] := by
  simp only [MixedRadixDecode.split]
  exact congrArg List.singleton
    (Nat.mod_eq_of_lt (BooleanCoefficientIndex.coefficientEquiv t r p).isLt)

theorem split_factors (s : Hadamard.TestRandomness t r) :
    (MixedRadixDecode.split ((Codec.piFin fun k : Fin (r - 1) =>
      coefficientCodec t (k.val + 1)).equiv s.factor).val
        (List.ofFn fun k : Fin (r - 1) => cardinal t (k.val + 1))).1 =
      HadamardRow.factorCodes s := by
  let f : (k : Fin (r - 1)) → Fin (cardinal t (k.val + 1)) := fun k =>
    BooleanCoefficientIndex.coefficientEquiv t (k.val + 1) (s.factor k)
  let e := @finPiFinEquiv (r - 1) (fun k => cardinal t (k.val + 1))
  change (MixedRadixDecode.split (e f).val
    (List.ofFn fun k : Fin (r - 1) => cardinal t (k.val + 1))).1 = _
  have h := MixedRadixDecode.split_finPi
    (fun k : Fin (r - 1) => cardinal t (k.val + 1)) (e f)
  change _ = List.ofFn (fun k => (e.symm (e f) k).val) at h
  rw [e.symm_apply_apply] at h
  exact h


theorem split_hadamard (s : Hadamard.TestRandomness t r) :
    (MixedRadixDecode.split ((hadamardCodec t r).equiv s).val (radices t r)).1 =
      HadamardRow.factorCodes s ++ [code s.linear, code s.auxiliary, code s.base] := by
  let F := Codec.piFin fun k : Fin (r - 1) => coefficientCodec t (k.val + 1)
  let rs := List.ofFn fun k : Fin (r - 1) => cardinal t (k.val + 1)
  have hF : rs.prod = F.size := by
    simp [rs, F, Codec.piFin, cardinal, coefficientCodec, List.prod_ofFn]
  have h1 := split_codecProd_flat (coefficientCodec t 1) F s.linear s.factor
    [cardinal t 1] rs hF
  have hR1 : (rs ++ [cardinal t 1]).prod = ((coefficientCodec t 1).prod F).size := by
    simp only [List.prod_append, List.prod_cons, List.prod_nil, Nat.mul_one, hF]
    change F.size * cardinal t 1 = cardinal t 1 * F.size
    exact Nat.mul_comm _ _
  have h2 := split_codecProd_flat (coefficientCodec t r) ((coefficientCodec t 1).prod F)
    s.auxiliary (s.linear, s.factor) [cardinal t r] (rs ++ [cardinal t 1]) hR1
  have hR2 : ((rs ++ [cardinal t 1]) ++ [cardinal t r]).prod =
      ((coefficientCodec t r).prod ((coefficientCodec t 1).prod F)).size := by
    simp only [List.prod_append, List.prod_cons, List.prod_nil, Nat.mul_one, hR1]
    exact Nat.mul_comm _ _
  have h3 := split_codecProd_flat (coefficientCodec t r)
    ((coefficientCodec t r).prod ((coefficientCodec t 1).prod F))
    s.base (s.auxiliary, s.linear, s.factor) [cardinal t r]
    ((rs ++ [cardinal t 1]) ++ [cardinal t r]) hR2
  rw [h2, h1] at h3
  have hfac : (MixedRadixDecode.split (F.equiv s.factor).val rs).1 =
      HadamardRow.factorCodes s := split_factors s
  rw [hfac] at h3
  change _ = ((HadamardRow.factorCodes s ++
    (MixedRadixDecode.split (code s.linear) [cardinal t 1]).1) ++
      (MixedRadixDecode.split (code s.auxiliary) [cardinal t r]).1) ++
        (MixedRadixDecode.split (code s.base) [cardinal t r]).1 at h3
  rw [split_coefficient, split_coefficient, split_coefficient] at h3
  have hs : (s.base, s.auxiliary, s.linear, s.factor) = s := rfl
  rw [hs] at h3
  simp only [List.append_assoc, List.cons_append, List.nil_append] at h3
  exact h3

end PCP.Lang.HadamardSeed
