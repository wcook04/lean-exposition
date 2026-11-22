/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Algebraic.BinaryLagrangeConstraint
import PCP.Algebraic.AffineSampling

/-!
# Robustness of binary interpolation under corrupted Hadamard answers

The error parameter here is the actual normalized distance between the two
oracles on homogeneous queries, jointly over field points and binary labels.
Zero-safe weighted reads do not increase each row's error probability. A union
bound and the uniform marginal of `u + z • v` then bound the change in rejection
by `(c+2)` times this distance. In particular, rejection for an arbitrary received
binary oracle controls the field test applied to a nearby encoding.

These results concern the concrete interpolation check and do not assume a
point-versus-line soundness theorem or claim proximity to low-degree polynomials.
-/

namespace PCP.Algebraic.BinaryLagrangeConstraint

open Finset PolynomialLine BinaryPolynomialSpace Hadamard HadamardWeights

variable {F σ : Type*} [Field F] [Algebra (ZMod 2) F] {c t r : ℕ}

/-- The distance between the homogeneous-label restrictions at a fixed field point. -/
noncomputable def rowDistance (hr : 1 ≤ r)
    (H G : (σ → F) → Coefficients t r → ZMod 2) (x : σ → F) : ℚ :=
  relativeDistance (fun w => H x (homogeneousIndex hr w))
    (fun w => G x (homogeneousIndex hr w))

/-- With the field randomness fixed, disagreement can occur only at one of the
queried rows. Zero interpolation coefficients require no exception. -/
theorem check_distance_le_rows (hr : 1 ≤ r)
    (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2)) (a : Fin (c + 1) → F)
    (H G : (σ → F) → Coefficients t r → ZMod 2) (u v : σ → F) (z : F) :
    relativeDistance (check hr ρ a H u v z) (check hr ρ a G u v z) ≤
      rowDistance hr H G (point u v z) +
        ∑ i, rowDistance hr H G (point u v (a i)) := by
  apply (relativeDistance_sub_le
    (fun w => H (point u v z) (homogeneousIndex hr w))
    (fun w => ∑ i, weightedRead hr ρ (H (point u v (a i))) (LagrangeConstraint.weight a z i) w)
    (fun w => G (point u v z) (homogeneousIndex hr w))
    (fun w => ∑ i, weightedRead hr ρ (G (point u v (a i)))
      (LagrangeConstraint.weight a z i) w)).trans
  apply add_le_add le_rfl
  apply (relativeDistance_sum_le _ _).trans
  apply sum_le_sum
  intro i _
  exact relativeDistance_weightedRead_le hr ρ _ _ _

section Finite

variable [Fintype F] [DecidableEq F] [Fintype σ] [DecidableEq σ]

/-- Global error measured only on the homogeneous queries read by this check. -/
noncomputable def homogeneousDistance (hr : 1 ≤ r)
    (H G : (σ → F) → Coefficients t r → ZMod 2) : ℚ :=
  relativeDistance (fun p : (σ → F) × (Fin t → ZMod 2) => H p.1 (homogeneousIndex hr p.2))
    (fun p => G p.1 (homogeneousIndex hr p.2))

omit [Field F] [Algebra (ZMod 2) F] [DecidableEq F] in
theorem homogeneousDistance_eq_average (hr : 1 ≤ r)
    (H G : (σ → F) → Coefficients t r → ZMod 2) :
    homogeneousDistance hr H G =
      (∑ x, rowDistance hr H G x) / Fintype.card (σ → F) :=
  relativeDistance_prod _ _

omit [Algebra (ZMod 2) F] [DecidableEq F] in
/-- A uniform center makes each sampled field point uniform, including parameter
zero; the parameter is allowed to depend on the independent final field seed. -/
theorem average_point (e : (σ → F) → ℚ) (b : F → F) :
    (∑ s : ((σ → F) × (σ → F)) × F, e (point s.1.1 s.1.2 (b s.2))) /
        Fintype.card (((σ → F) × (σ → F)) × F) =
      (∑ x, e x) / Fintype.card (σ → F) := by
  have hshift (v : σ → F) (z : F) :
      ∑ u : σ → F, e (point u v (b z)) = ∑ u : σ → F, e u :=
    Equiv.sum_comp (Equiv.addRight (b z • v)) e
  have hs : (∑ s : ((σ → F) × (σ → F)) × F, e (point s.1.1 s.1.2 (b s.2))) =
      (Fintype.card (σ → F) : ℚ) * Fintype.card F * ∑ u : σ → F, e u := by
    simp only [Fintype.sum_prod_type]
    rw [sum_comm]
    calc
      _ = ∑ v : σ → F, ∑ z : F, ∑ u : σ → F, e (point u v (b z)) := by
        apply sum_congr rfl
        intro v _
        exact sum_comm
      _ = _ := by simp only [hshift, sum_const, card_univ, nsmul_eq_mul]; ring
  rw [hs]
  simp only [Fintype.card_prod, Nat.cast_mul]
  have hv : (Fintype.card (σ → F) : ℚ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hf : (Fintype.card F : ℚ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  field_simp

omit [Algebra (ZMod 2) F] [DecidableEq F] in
theorem average_rowDistance_point (hr : 1 ≤ r)
    (H G : (σ → F) → Coefficients t r → ZMod 2) (b : F → F) :
    (∑ s : ((σ → F) × (σ → F)) × F,
      rowDistance hr H G (point s.1.1 s.1.2 (b s.2))) /
        Fintype.card (((σ → F) × (σ → F)) × F) = homogeneousDistance hr H G := by
  rw [average_point, homogeneousDistance_eq_average]

omit [DecidableEq F] in
/-- Fully normalized perturbation bound for the actual binary residuals. -/
theorem distance_checks_le (hr : 1 ≤ r)
    (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2)) (a : Fin (c + 1) → F)
    (H G : (σ → F) → Coefficients t r → ZMod 2) :
    relativeDistance
      (fun s : (((σ → F) × (σ → F)) × F) × (Fin t → ZMod 2) =>
        check hr ρ a H s.1.1.1 s.1.1.2 0 s.2)
      (fun s => check hr ρ a G s.1.1.1 s.1.1.2 0 s.2) ≤
        (c + 2 : ℕ) * homogeneousDistance hr H G := by
  rw [relativeDistance_prod]
  calc
    _ ≤ (∑ s : ((σ → F) × (σ → F)) × F,
        (rowDistance hr H G (point s.1.1 s.1.2 0) +
          ∑ i, rowDistance hr H G (point s.1.1 s.1.2 (a i)))) /
            Fintype.card (((σ → F) × (σ → F)) × F) := by
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
      apply sum_le_sum
      intro s _
      exact check_distance_le_rows hr ρ a H G s.1.1 s.1.2 0
    _ = homogeneousDistance hr H G + ∑ _i : Fin (c + 1), homogeneousDistance hr H G := by
      rw [sum_add_distrib, add_div]
      apply congrArg₂ (· + ·)
      · exact average_rowDistance_point hr H G (fun _ => 0)
      · rw [sum_comm, sum_div]
        apply sum_congr rfl
        intro i _
        exact average_rowDistance_point hr H G (fun _ => a i)
    _ = _ := by simp; ring

omit [DecidableEq F] in
/-- Replacing an oracle changes rejection by at most the query count times its
normalized error on homogeneous labels. -/
theorem rejectionRate_le_add_homogeneousDistance (hr : 1 ≤ r)
    (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2)) (a : Fin (c + 1) → F)
    (H G : (σ → F) → Coefficients t r → ZMod 2) :
    rejectionRate hr ρ a G ≤ rejectionRate hr ρ a H +
      (c + 2 : ℕ) * homogeneousDistance hr H G := by
  have h := relativeDistance_triangle
    (fun s : (((σ → F) × (σ → F)) × F) × (Fin t → ZMod 2) =>
      check hr ρ a G s.1.1.1 s.1.1.2 0 s.2)
    (fun s => check hr ρ a H s.1.1.1 s.1.1.2 0 s.2) (fun _ => 0)
  have hb := distance_checks_le hr ρ a H G
  rw [relativeDistance_comm] at hb
  change rejectionRate hr ρ a G ≤ _ + rejectionRate hr ρ a H at h
  linarith

/-- Robust field-to-binary bridge for an arbitrary received oracle and any nearby
field-valued function. The error is measured on exactly the homogeneous labels. -/
theorem half_field_rejectionRate_le (hr : 1 ≤ r)
    (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2)) (a : Fin (c + 1) → F)
    (H : (σ → F) → Coefficients t r → ZMod 2) (f : (σ → F) → F) :
    (1 : ℚ) / 2 * LagrangeConstraint.rejectionRate a f ≤ rejectionRate hr ρ a H +
      (c + 2 : ℕ) * homogeneousDistance hr H (fun x => encode r (ρ (f x))) := by
  rw [← rejectionRate_encode hr ρ a f]
  exact rejectionRate_le_add_homogeneousDistance hr ρ a H _

/-- The same bridge with the field rejection probability isolated. -/
theorem field_rejectionRate_le (hr : 1 ≤ r)
    (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2)) (a : Fin (c + 1) → F)
    (H : (σ → F) → Coefficients t r → ZMod 2) (f : (σ → F) → F) :
    LagrangeConstraint.rejectionRate a f ≤ 2 * rejectionRate hr ρ a H +
      2 * (c + 2 : ℕ) * homogeneousDistance hr H (fun x => encode r (ρ (f x))) := by
  have h := half_field_rejectionRate_le hr ρ a H f
  linarith

end Finite

end PCP.Algebraic.BinaryLagrangeConstraint
