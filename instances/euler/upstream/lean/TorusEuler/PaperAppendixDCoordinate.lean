import TorusEuler.PaperAppendixD

/-! Relate the coefficient powers to the coordinate sums in Appendix D. -/

open Set
open scoped ContDiff

namespace TorusEuler

noncomputable section

variable {I A : Type*} [NormedRing A] [NormedAlgebra ℝ A]

/-- The exact-order coordinate sum, using all ordered coordinate words. -/
def appendixCoefficientCoordinateNorm (m : ℕ) (c : I → Vec3 → A) : ℝ :=
  ∑ β : Fin m → Fin 3, sSup (insert 0 (range fun p : I × Vec3 =>
    ‖iteratedFDeriv ℝ m (c p.1) p.2 (fun j => coordinateDirection (β j))‖))

/-- Bounds on all actual coordinate components, by order. Finite sums
over the distinct multi-indices obey the same bound after changing the
order-dependent prefactor. -/
def FiniteCoefficientCoordinatePower (D : ℝ) (a : ℕ) (c : I → Vec3 → A) : Prop :=
  (∀ t, ContDiff ℝ ∞ (c t)) ∧ ∃ C : ℕ → ℝ, (∀ m, 1 ≤ C m) ∧
    (∀ (m : ℕ) (β : Fin m → Fin 3), BddAbove (insert 0 (range fun p : I × Vec3 =>
      ‖iteratedFDeriv ℝ m (c p.1) p.2 (fun j : Fin m => coordinateDirection (β j))‖))) ∧
    ∀ m, appendixCoefficientCoordinateNorm m c ≤ C m * D ^ (a * (m + 1))

private theorem appendixSumCoordinateDirection (v : Vec3) :
    (∑ i, v i • coordinateDirection i) = v := by
  apply PiLp.ext
  intro j
  let ev := (EuclideanSpace.proj j : Vec3 →L[ℝ] ℝ)
  change ev (∑ i, v i • coordinateDirection i) = v j
  rw [map_sum]
  simp [ev, coordinateDirection, EuclideanSpace.single, PiLp.single_apply]

private theorem appendixOpNorm_le_coordinateSum {m : ℕ}
    (D : ContinuousMultilinearMap ℝ (fun _ : Fin m => Vec3) A) :
    ‖D‖ ≤ ∑ β : Fin m → Fin 3, ‖D (fun i => coordinateDirection (β i))‖ := by
  classical
  apply ContinuousMultilinearMap.opNorm_le_bound (Finset.sum_nonneg fun _ _ => norm_nonneg _)
  intro p
  have h := D.toMultilinearMap.map_sum (fun j i => p j i • coordinateDirection i)
  have hsum : (fun j => ∑ i, p j i • coordinateDirection i) = p :=
    funext fun j => appendixSumCoordinateDirection (p j)
  rw [hsum] at h
  change D p = ∑ β : Fin m → Fin 3, D (fun j => p j (β j) • coordinateDirection (β j)) at h
  rw [h, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun β _ => ?_)
  rw [show D (fun j => p j (β j) • coordinateDirection (β j)) =
    (∏ j, p j (β j)) • D (fun j => coordinateDirection (β j)) from
      D.toMultilinearMap.map_smul_univ _ _, norm_smul, Real.norm_eq_abs, Finset.abs_prod, mul_comm]
  exact mul_le_mul_of_nonneg_left (Finset.prod_le_prod (fun _ _ => abs_nonneg _)
    (fun j _ => PiLp.norm_apply_le (p j) (β j))) (norm_nonneg _)

/-- The two formulations of (D.6) have the same slope in derivative order. -/
theorem finiteCoefficientPower_iff_coordinate {D : ℝ} (hD : 1 ≤ D) {a : ℕ} {c : I → Vec3 → A} :
    FiniteCoefficientPower D a c ↔ FiniteCoefficientCoordinatePower D a c := by
  constructor
  · rintro ⟨hs, C, hC, h⟩
    have hpoint (m : ℕ) (β : Fin m → Fin 3) (p : I × Vec3) :
        ‖iteratedFDeriv ℝ m (c p.1) p.2 (fun j => coordinateDirection (β j))‖ ≤
          C m * D ^ (a * (m + 1)) := by
      refine (ContinuousMultilinearMap.le_opNorm _ _).trans ?_
      simpa [coordinateDirection] using h m p.1 p.2
    have hupper (m : ℕ) (β : Fin m → Fin 3) :
        C m * D ^ (a * (m + 1)) ∈ upperBounds (insert 0 (range fun p : I × Vec3 =>
          ‖iteratedFDeriv ℝ m (c p.1) p.2 (fun j => coordinateDirection (β j))‖)) := by
      rintro y (rfl | ⟨p, rfl⟩)
      · have := zero_le_one.trans hD
        exact mul_nonneg (zero_le_one.trans (hC m)) (by positivity)
      · exact hpoint m β p
    refine ⟨hs, fun m => (3 : ℝ) ^ m * C m, fun m =>
      one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num)) (hC m),
      fun m β => ⟨_, hupper m β⟩, fun m => ?_⟩
    unfold appendixCoefficientCoordinateNorm
    calc
      _ ≤ ∑ _β : Fin m → Fin 3, C m * D ^ (a * (m + 1)) :=
        Finset.sum_le_sum fun β _ => csSup_le ⟨0, mem_insert _ _⟩ (hupper m β)
      _ = _ := by simp [mul_assoc]
  · rintro ⟨hs, C, hC, hb, h⟩
    refine ⟨hs, C, hC, fun m t x => ?_⟩
    refine (appendixOpNorm_le_coordinateSum _).trans
      ((Finset.sum_le_sum fun β _ => le_csSup (hb m β) (mem_insert_of_mem _ (mem_range_self (t, x)))).trans ?_)
    exact h m

/-- The coordinate-sum version of the coefficient product bound. -/
theorem paperLemmaD2_mul_coordinate {D : ℝ} {a : ℕ} (hD : 1 ≤ D) {c d : I → Vec3 → A}
    (hc : FiniteCoefficientCoordinatePower D a c) (hd : FiniteCoefficientCoordinatePower D a d) :
    FiniteCoefficientCoordinatePower D (2 * a) (fun t x => c t x * d t x) :=
  (finiteCoefficientPower_iff_coordinate hD).mp (paperLemmaD2_mul hD
    ((finiteCoefficientPower_iff_coordinate hD).mpr hc) ((finiteCoefficientPower_iff_coordinate hD).mpr hd))

/-- The coordinate-sum version of the coefficient inverse bound. -/
theorem paperLemmaD2_inverse_coordinate [CompleteSpace A] {D : ℝ} {a : ℕ} (hD : 1 ≤ D)
    {c : I → Vec3 → A} (hc : FiniteCoefficientCoordinatePower D a c)
    (hUnit : ∀ t x, IsUnit (c t x)) (hInv : ∀ t x, ‖Ring.inverse (c t x)‖ ≤ D ^ a) :
    FiniteCoefficientCoordinatePower D (3 * a) (fun t x => Ring.inverse (c t x)) :=
  (finiteCoefficientPower_iff_coordinate hD).mp (paperLemmaD2_inverse hD
    ((finiteCoefficientPower_iff_coordinate hD).mpr hc) hUnit hInv)

/-- The ordinary label sums have the positive-order scale gain of Lemma D.2(c). -/
theorem paperLemmaD2_weighted_coordinate {D ℓ : ℝ} {a : ℕ} (hD : 1 ≤ D)
    (hℓ : 0 ≤ ℓ) (hscale : ℓ * D ^ a ≤ 1) {c : I → Vec3 → A}
    (hc : FiniteCoefficientCoordinatePower D a c) :
    ∃ C : ℕ → ℝ,
      (∀ n, (∑ m ∈ Finset.range (n + 1), ℓ ^ m * appendixCoefficientCoordinateNorm m c)
        ≤ (∑ m ∈ Finset.range (n + 1), C m) * D ^ a) ∧
      (∀ m ≥ 1, ℓ ^ m * appendixCoefficientCoordinateNorm m c ≤ C m * D ^ (2 * a) * ℓ) := by
  obtain ⟨_, C, hC, _, hbound⟩ := hc
  have hD₀ : 0 ≤ D := zero_le_one.trans hD
  have hmain (m : ℕ) : ℓ ^ m * appendixCoefficientCoordinateNorm m c ≤ C m * D ^ a := by
    calc
      _ ≤ ℓ ^ m * (C m * D ^ (a * (m + 1))) :=
        mul_le_mul_of_nonneg_left (hbound m) (pow_nonneg hℓ m)
      _ = (ℓ * D ^ a) ^ m * (C m * D ^ a) := by
        rw [mul_pow, ← pow_mul, Nat.mul_succ, pow_add]
        ring
      _ ≤ _ := mul_le_of_le_one_left (mul_nonneg (zero_le_one.trans (hC m)) (pow_nonneg hD₀ a))
        (pow_le_one₀ (mul_nonneg hℓ (pow_nonneg hD₀ a)) hscale)
  refine ⟨C, ?_, fun m hm => hierarchy_weighted_coefficient_le hD hℓ
    (zero_le_one.trans (hC m)) hscale hm (hbound m)⟩
  intro n
  rw [Finset.sum_mul]
  exact Finset.sum_le_sum fun m _ => hmain m

end

end TorusEuler
