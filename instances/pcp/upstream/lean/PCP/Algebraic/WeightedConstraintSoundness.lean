/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Algebraic.AffineSampling
import PCP.Algebraic.PointLinePredictionConsistency

/-!
# Soundness of a weighted affine constraint

The two-dimensional grid argument of Kaufman--Sudan, specialized to one
weighted equation. No polynomial or field-cardinality assumption is used here.
The corrected word satisfies every constraint when rejection is less than
`1 / ((2*n+3)*n)`, and is within twice rejection of the received word.
-/

namespace PCP.Algebraic.WeightedConstraint

open Finset

variable {F V I : Type*} [Field F] [AddCommGroup V] [Module F V]
variable [Fintype I]

noncomputable def predict (a w : I → F) (f : V → F) (x v : V) : F :=
  ∑ i, w i * f (x + a i • v)

section Finite

variable [Fintype F] [DecidableEq F] [Fintype V]

noncomputable def rejectionRate (a w : I → F) (f : V → F) : ℚ :=
  relativeDistance (fun s : V × V => f s.1) (fun s => predict a w f s.1 s.2)

noncomputable def correction (a w : I → F) (f : V → F) (x : V) : F :=
  Plurality.value (predict a w f x)

theorem distance_correction_le (a w : I → F) (f : V → F) :
    relativeDistance f (correction a w f) ≤ 2 * rejectionRate a w f :=
  Plurality.distance_le_twice_prediction_error (predict a w f) f

omit [Fintype F] in
private theorem weighted_distance_le {R : Type*} [Fintype R]
    (w : I → F) (f g : I → R → F) :
    relativeDistance (fun s => ∑ i, w i * f i s) (fun s => ∑ i, w i * g i s) ≤
      ∑ i, relativeDistance (f i) (g i) := by
  apply (relativeDistance_sum_le _ _).trans
  exact sum_le_sum fun i _ => relativeDistance_le_of_disagreement _ _ (f i) (g i)
    (fun s h he => h (by rw [he]))

private def pairEquiv (x v : V) (a : F) (ha : a ≠ 0) : (V × V) ≃ (V × V) :=
  Equiv.prodCongr (affineSamplingEquiv x a ha) (affineSamplingEquiv v a ha)

omit [Fintype F] in
private theorem shifted_error (a w : I → F) (f : V → F) (x v : V)
    (b : F) (hb : b ≠ 0) :
    relativeDistance (fun s : V × V => f (x + b • s.1))
      (fun s => predict a w f (x + b • s.1) (v + b • s.2)) =
        rejectionRate a w f :=
  relativeDistance_comp_equiv (pairEquiv x v b hb)
    (fun s : V × V => f s.1) (fun s => predict a w f s.1 s.2)

omit [Fintype F] [DecidableEq F] [Fintype V] in
private theorem grid_comm (a w : I → F) (f : V → F) (x y z b : V) :
    (∑ i, w i * predict a w f (x + a i • y) (z + a i • b)) =
      ∑ j, w j * predict a w f (x + a j • z) (y + a j • b) := by
  simp only [predict, mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro j _
  apply sum_congr rfl
  intro i _
  have hp : x + a i • y + a j • (z + a i • b) =
      x + a j • z + a i • (y + a j • b) := by
    simp only [smul_add, smul_smul]
    rw [mul_comm (a j) (a i)]
    abel
  rw [hp]
  ring

omit [Fintype F] in
private theorem grid_error (a w : I → F) (ha : ∀ i, a i ≠ 0)
    (f : V → F) (x z : V) :
    relativeDistance (fun s : V × V => predict a w f x s.1)
      (fun s => ∑ i, w i * predict a w f (x + a i • s.1) (z + a i • s.2)) ≤
        Fintype.card I * rejectionRate a w f := by
  apply (weighted_distance_le w _ _).trans
  simp only [shifted_error a w f x z _ (ha _), sum_const, card_univ, nsmul_eq_mul]
  exact le_rfl

omit [Fintype F] in
theorem pair_error_le (a w : I → F) (ha : ∀ i, a i ≠ 0)
    (f : V → F) (x : V) :
    relativeDistance (fun s : V × V => predict a w f x s.1)
      (fun s => predict a w f x s.2) ≤
        2 * Fintype.card I * rejectionRate a w f := by
  let D : (V × V) × V → F := fun s =>
    ∑ i, w i * predict a w f (x + a i • s.1.1) (s.1.2 + a i • s.2)
  have hleft : relativeDistance (fun s : (V × V) × V => predict a w f x s.1.1) D ≤
      Fintype.card I * rejectionRate a w f := by
    let e : (V × V) × V ≃ V × (V × V) :=
      ⟨fun s => (s.1.2, (s.1.1, s.2)), fun s => ((s.2.1, s.1), s.2.2),
        fun _ => rfl, fun _ => rfl⟩
    have he := relativeDistance_comp_equiv e.symm
      (fun s : (V × V) × V => predict a w f x s.1.1) D
    rw [← he]
    apply relativeDistance_prod_le
    intro z
    exact grid_error a w ha f x z
  have hright : relativeDistance D (fun s : (V × V) × V => predict a w f x s.1.2) ≤
      Fintype.card I * rejectionRate a w f := by
    let e : (V × V) × V ≃ (V × V) × V :=
      Equiv.prodCongr (Equiv.prodComm V V) (Equiv.refl V)
    have he := relativeDistance_comp_equiv e
      (fun s : (V × V) × V => predict a w f x s.1.1) D
    have hd : (fun s => D (e s)) = D := by
      funext s
      exact grid_comm a w f x s.1.2 s.1.1 s.2
    rw [hd] at he
    rw [relativeDistance_comm]
    exact he.le.trans hleft
  have ht := relativeDistance_triangle
    (fun s : (V × V) × V => predict a w f x s.1.1) D
    (fun s => predict a w f x s.1.2)
  rw [relativeDistance_comp_fst
    (fun s : V × V => predict a w f x s.1)
    (fun s => predict a w f x s.2)] at ht
  linarith

theorem prediction_error_le (a w : I → F) (ha : ∀ i, a i ≠ 0)
    (f : V → F) (x : V) :
    relativeDistance (predict a w f x) (fun _ => correction a w f x) ≤
      2 * Fintype.card I * rejectionRate a w f :=
  (Plurality.error_le_pair_disagreement _).trans (pair_error_le a w ha f x)

theorem correction_satisfies (a w : I → F) (ha : ∀ i, a i ≠ 0)
    (f : V → F)
    (hsmall : (2 * (Fintype.card I : ℚ) + 3) * Fintype.card I *
      rejectionRate a w f < 1) (x v : V) :
    correction a w f x = predict a w (correction a w f) x v := by
  let C := correction a w f
  let D : V × V → F := fun s =>
    ∑ i, w i * predict a w f (x + a i • s.1) (v + a i • s.2)
  have hleft : relativeDistance (fun _ : V × V => C x)
      (fun s => predict a w f x s.1) ≤
      2 * Fintype.card I * rejectionRate a w f := by
    rw [relativeDistance_comm, relativeDistance_comp_fst
      (predict a w f x) (fun _ => C x)]
    exact prediction_error_le a w ha f x
  have hmid := grid_error a w ha f x v
  have hright : relativeDistance D (fun _ => predict a w C x v) ≤
      Fintype.card I * (2 * Fintype.card I * rejectionRate a w f) := by
    have hd : D = fun s : V × V =>
        ∑ i, w i * predict a w f (x + a i • v) (s.1 + a i • s.2) := by
      funext s
      exact grid_comm a w f x s.1 v s.2
    rw [hd]
    apply (weighted_distance_le w _ _).trans
    have hi (i : I) : relativeDistance
        (fun s : V × V => predict a w f (x + a i • v) (s.1 + a i • s.2))
        (fun _ => C (x + a i • v)) ≤
        2 * Fintype.card I * rejectionRate a w f := by
      rw [← relativeDistance_comp_equiv (Equiv.prodComm V V)]
      apply relativeDistance_prod_le
      intro b
      have he := relativeDistance_comp_equiv (Equiv.addRight (a i • b))
        (predict a w f (x + a i • v)) (fun _ => C (x + a i • v))
      exact he.le.trans (prediction_error_le a w ha f (x + a i • v))
    simpa using (sum_le_sum (s := (univ : Finset I)) (fun i _ => hi i))
  have ht := (relativeDistance_triangle (fun _ : V × V => C x)
      (fun s => predict a w f x s.1) D).trans (add_le_add hleft hmid)
  have ht' := (relativeDistance_triangle (fun _ : V × V => C x) D
      (fun _ => predict a w C x v)).trans (add_le_add ht hright)
  by_contra hne
  rw [relativeDistance_const, ite_eq_right hne] at ht'
  nlinarith

end Finite
end PCP.Algebraic.WeightedConstraint
