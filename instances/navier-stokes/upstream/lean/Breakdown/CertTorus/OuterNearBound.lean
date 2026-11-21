import Breakdown.CertTorus.DecayStatements

open MeasureTheory Set

noncomputable section

namespace Breakdown.FarField

namespace Internal

theorem min_one_rpow_le_rpow {x g m : ℝ} (hx : 0 < x) (hm : 0 ≤ m) (hmg : m ≤ g) :
    min 1 (x ^ g) ≤ x ^ m := by
  rcases le_total x 1 with h | h
  · exact (min_le_right _ _).trans (Real.rpow_le_rpow_of_exponent_ge hx h hmg)
  · exact (min_le_left _ _).trans (Real.one_le_rpow h hm)

theorem nearKernel_nonneg {R τ : ℝ} (hR : 0 < R) :
    0 ≤ R ^ 3 / (R + Real.sqrt τ) ^ 4 :=
  div_nonneg (pow_nonneg hR.le 3) (pow_nonneg (add_nonneg hR.le (Real.sqrt_nonneg _)) 4)

theorem nearKernel_le_inv {R τ : ℝ} (hR : 0 < R) :
    R ^ 3 / (R + Real.sqrt τ) ^ 4 ≤ R⁻¹ := by
  have hs : 0 ≤ Real.sqrt τ := Real.sqrt_nonneg τ
  have h4 : R ^ 4 ≤ (R + Real.sqrt τ) ^ 4 := pow_le_pow_left₀ hR.le (by linarith) 4
  rw [div_le_iff₀ (pow_pos (by linarith) 4)]
  calc R ^ 3 = R⁻¹ * R ^ 4 := by field_simp
    _ ≤ R⁻¹ * (R + Real.sqrt τ) ^ 4 := mul_le_mul_of_nonneg_left h4 (inv_nonneg.mpr hR.le)

theorem nearKernel_le_sq {R τ : ℝ} (hR : 0 < R) (hτ : 0 < τ) :
    R ^ 3 / (R + Real.sqrt τ) ^ 4 ≤ R ^ 3 / τ ^ 2 := by
  have hs : 0 ≤ Real.sqrt τ := Real.sqrt_nonneg τ
  have hsq : τ ^ 2 = Real.sqrt τ ^ 4 := by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, Real.sq_sqrt hτ.le]
  apply div_le_div_of_nonneg_left (pow_nonneg hR.le 3) (pow_pos hτ 2)
  rw [hsq]
  exact pow_le_pow_left₀ hs (by linarith) 4

theorem nearMajorant_nonneg (γ τ : ℝ) {R : ℝ} (hR : 0 < R) :
    0 ≤ nearMajorant γ τ R := by
  unfold nearMajorant
  refine mul_nonneg (nearKernel_nonneg hR) (le_min zero_le_one (Real.rpow_nonneg ?_ _))
  exact div_nonneg (Real.sqrt_nonneg _) hR.le

theorem nearIntegrand_le {n : ℕ} (hn : n ≤ 2) {γ : ℝ} (hγ : 0 ≤ γ) {R τ : ℝ} (hR : 1 ≤ R)
    (hτ : 0 < τ) :
    (1 + τ) ^ (-(1 + (n : ℝ) / 2)) * nearMajorant γ τ R ≤
      R ^ (-min γ ((n : ℝ) + 1)) * (τ ^ (-(1 / 2 : ℝ)) * (R ^ 3 / (R + Real.sqrt τ) ^ 4)) := by
  have hR0 : 0 < R := by linarith
  have h1τ : 0 < 1 + τ := by linarith
  have hn' : (n : ℝ) ≤ 2 := by exact_mod_cast hn
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hm0 : 0 ≤ min γ ((n : ℝ) + 1) := le_min hγ (by linarith)
  have hmn : min γ ((n : ℝ) + 1) ≤ (n : ℝ) + 1 := min_le_right _ _
  have hmg : min γ ((n : ℝ) + 1) ≤ min γ 3 := min_le_min_left _ (by linarith)
  have hK := nearKernel_nonneg (τ := τ) hR0
  have hx : 0 < Real.sqrt (1 + τ) / R := div_pos (Real.sqrt_pos.mpr h1τ) hR0
  have hmin : min 1 ((Real.sqrt (1 + τ) / R) ^ min γ 3) ≤
      (1 + τ) ^ (min γ ((n : ℝ) + 1) / 2) * R ^ (-min γ ((n : ℝ) + 1)) := by
    refine (min_one_rpow_le_rpow hx hm0 hmg).trans (le_of_eq ?_)
    rw [Real.div_rpow (Real.sqrt_nonneg _) hR0.le, Real.sqrt_eq_rpow, ← Real.rpow_mul h1τ.le,
      Real.rpow_neg hR0.le, div_eq_mul_inv,
      show (1 / 2 : ℝ) * min γ ((n : ℝ) + 1) = min γ ((n : ℝ) + 1) / 2 by ring]
  have hexp : (1 + τ) ^ (-(1 + (n : ℝ) / 2)) * (1 + τ) ^ (min γ ((n : ℝ) + 1) / 2) ≤
      τ ^ (-(1 / 2 : ℝ)) := by
    rw [← Real.rpow_add h1τ]
    calc (1 + τ) ^ (-(1 + (n : ℝ) / 2) + min γ ((n : ℝ) + 1) / 2)
        ≤ (1 + τ) ^ (-(1 / 2 : ℝ)) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
      _ ≤ τ ^ (-(1 / 2 : ℝ)) := Real.rpow_le_rpow_of_nonpos hτ (by linarith) (by norm_num)
  unfold nearMajorant
  calc (1 + τ) ^ (-(1 + (n : ℝ) / 2)) *
        (R ^ 3 / (R + Real.sqrt τ) ^ 4 * min 1 ((Real.sqrt (1 + τ) / R) ^ min γ 3))
      ≤ (1 + τ) ^ (-(1 + (n : ℝ) / 2)) * (R ^ 3 / (R + Real.sqrt τ) ^ 4 *
          ((1 + τ) ^ (min γ ((n : ℝ) + 1) / 2) * R ^ (-min γ ((n : ℝ) + 1)))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hmin hK) (Real.rpow_nonneg h1τ.le _)
    _ = R ^ (-min γ ((n : ℝ) + 1)) * (((1 + τ) ^ (-(1 + (n : ℝ) / 2)) *
          (1 + τ) ^ (min γ ((n : ℝ) + 1) / 2)) * (R ^ 3 / (R + Real.sqrt τ) ^ 4)) := by ring
    _ ≤ R ^ (-min γ ((n : ℝ) + 1)) * (τ ^ (-(1 / 2 : ℝ)) * (R ^ 3 / (R + Real.sqrt τ) ^ 4)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hexp hK) (Real.rpow_nonneg hR0.le _)

theorem integral_Ioc_rpow_neg_half {R : ℝ} (hR : 0 < R) :
    ∫ τ in Ioc 0 (R ^ 2), τ ^ (-(1 / 2 : ℝ)) = 2 * R := by
  rw [← intervalIntegral.integral_of_le (by positivity), integral_rpow (Or.inl (by norm_num)),
    Real.zero_rpow (by norm_num),
    show -(1 / 2 : ℝ) + 1 = 1 / 2 by norm_num, ← Real.sqrt_eq_rpow, Real.sqrt_sq hR.le]
  ring

theorem integral_Ioi_rpow_neg_five_half {R : ℝ} (hR : 0 < R) :
    ∫ τ in Ioi (R ^ 2), τ ^ (-(5 / 2 : ℝ)) = 2 / 3 * (R ^ 3)⁻¹ := by
  rw [integral_Ioi_rpow_of_lt (by norm_num) (by positivity), ← Real.rpow_two,
    ← Real.rpow_mul hR.le, show (2 : ℝ) * (-(5 / 2 : ℝ) + 1) = -((3 : ℕ) : ℝ) by norm_num,
    Real.rpow_neg hR.le, Real.rpow_natCast]
  ring

theorem integrableOn_Ioc_rpow_neg_half (b : ℝ) (hb : 0 ≤ b) :
    IntegrableOn (fun τ : ℝ => τ ^ (-(1 / 2 : ℝ))) (Ioc 0 b) :=
  (intervalIntegrable_iff_integrableOn_Ioc_of_le hb).mp
    (intervalIntegral.intervalIntegrable_rpow' (by norm_num))

theorem measurable_nearIntegrand (n : ℕ) (γ R : ℝ) :
    Measurable (fun τ : ℝ => (1 + τ) ^ (-(1 + (n : ℝ) / 2)) * nearMajorant γ τ R) := by
  unfold nearMajorant
  fun_prop

end Internal

open Internal in
theorem outerNearBound_holds : OuterNearBound := by
  intro n hn γ hγ
  refine ⟨3, fun R hR => ?_⟩
  have hR0 : 0 < R := by linarith
  have hR2 : 0 < R ^ 2 := by positivity
  have hmeas := measurable_nearIntegrand n γ R
  have hsplit : Ioi (0 : ℝ) = Ioc 0 (R ^ 2) ∪ Ioi (R ^ 2) := (Ioc_union_Ioi_eq_Ioi hR2.le).symm
  have hnn : ∀ τ : ℝ, 0 < τ → 0 ≤ (1 + τ) ^ (-(1 + (n : ℝ) / 2)) * nearMajorant γ τ R :=
    fun τ hτ => mul_nonneg (Real.rpow_nonneg (by linarith) _) (nearMajorant_nonneg γ τ hR0)
  have hle1 : ∀ τ ∈ Ioc 0 (R ^ 2), (1 + τ) ^ (-(1 + (n : ℝ) / 2)) * nearMajorant γ τ R ≤
      R ^ (-min γ ((n : ℝ) + 1)) * R⁻¹ * τ ^ (-(1 / 2 : ℝ)) := by
    intro τ hτ
    refine (nearIntegrand_le hn hγ hR hτ.1).trans ?_
    have h := mul_le_mul_of_nonneg_left (nearKernel_le_inv (τ := τ) hR0)
      (Real.rpow_nonneg hτ.1.le (-(1 / 2 : ℝ)))
    calc R ^ (-min γ ((n : ℝ) + 1)) * (τ ^ (-(1 / 2 : ℝ)) * (R ^ 3 / (R + Real.sqrt τ) ^ 4))
        ≤ R ^ (-min γ ((n : ℝ) + 1)) * (τ ^ (-(1 / 2 : ℝ)) * R⁻¹) :=
          mul_le_mul_of_nonneg_left h (Real.rpow_nonneg hR0.le _)
      _ = R ^ (-min γ ((n : ℝ) + 1)) * R⁻¹ * τ ^ (-(1 / 2 : ℝ)) := by ring
  have hle2 : ∀ τ ∈ Ioi (R ^ 2), (1 + τ) ^ (-(1 + (n : ℝ) / 2)) * nearMajorant γ τ R ≤
      R ^ (-min γ ((n : ℝ) + 1)) * R ^ 3 * τ ^ (-(5 / 2 : ℝ)) := by
    intro τ hτ
    have hτ0 : 0 < τ := hR2.trans hτ
    refine (nearIntegrand_le hn hγ hR hτ0).trans ?_
    have h := mul_le_mul_of_nonneg_left (nearKernel_le_sq hR0 hτ0)
      (Real.rpow_nonneg hτ0.le (-(1 / 2 : ℝ)))
    have he : τ ^ (-(1 / 2 : ℝ)) * (R ^ 3 / τ ^ 2) = R ^ 3 * τ ^ (-(5 / 2 : ℝ)) := by
      rw [show -(5 / 2 : ℝ) = -(1 / 2) + -((2 : ℕ) : ℝ) by norm_num, Real.rpow_add hτ0,
        Real.rpow_neg hτ0.le ((2 : ℕ) : ℝ), Real.rpow_natCast]
      ring
    calc R ^ (-min γ ((n : ℝ) + 1)) * (τ ^ (-(1 / 2 : ℝ)) * (R ^ 3 / (R + Real.sqrt τ) ^ 4))
        ≤ R ^ (-min γ ((n : ℝ) + 1)) * (τ ^ (-(1 / 2 : ℝ)) * (R ^ 3 / τ ^ 2)) :=
          mul_le_mul_of_nonneg_left h (Real.rpow_nonneg hR0.le _)
      _ = R ^ (-min γ ((n : ℝ) + 1)) * R ^ 3 * τ ^ (-(5 / 2 : ℝ)) := by rw [he]; ring
  have hg1 : IntegrableOn (fun τ : ℝ => R ^ (-min γ ((n : ℝ) + 1)) * R⁻¹ * τ ^ (-(1 / 2 : ℝ)))
      (Ioc 0 (R ^ 2)) :=
    (integrableOn_Ioc_rpow_neg_half _ hR2.le).const_mul _
  have hg2 : IntegrableOn (fun τ : ℝ => R ^ (-min γ ((n : ℝ) + 1)) * R ^ 3 * τ ^ (-(5 / 2 : ℝ)))
      (Ioi (R ^ 2)) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num) hR2).const_mul _
  have hI1 : IntegrableOn (fun τ : ℝ => (1 + τ) ^ (-(1 + (n : ℝ) / 2)) * nearMajorant γ τ R)
      (Ioc 0 (R ^ 2)) :=
    Integrable.mono' hg1 hmeas.aestronglyMeasurable ((ae_restrict_iff' measurableSet_Ioc).mpr
      (Filter.Eventually.of_forall fun τ hτ => by
        rw [Real.norm_of_nonneg (hnn τ hτ.1)]; exact hle1 τ hτ))
  have hI2 : IntegrableOn (fun τ : ℝ => (1 + τ) ^ (-(1 + (n : ℝ) / 2)) * nearMajorant γ τ R)
      (Ioi (R ^ 2)) :=
    Integrable.mono' hg2 hmeas.aestronglyMeasurable ((ae_restrict_iff' measurableSet_Ioi).mpr
      (Filter.Eventually.of_forall fun τ hτ => by
        rw [Real.norm_of_nonneg (hnn τ (hR2.trans hτ))]; exact hle2 τ hτ))
  refine ⟨by rw [hsplit]; exact hI1.union hI2, ?_⟩
  rw [hsplit, setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi hI1 hI2]
  have hRm : 0 ≤ R ^ (-min γ ((n : ℝ) + 1)) := Real.rpow_nonneg hR0.le _
  calc (∫ τ in Ioc 0 (R ^ 2), (1 + τ) ^ (-(1 + (n : ℝ) / 2)) * nearMajorant γ τ R) +
        ∫ τ in Ioi (R ^ 2), (1 + τ) ^ (-(1 + (n : ℝ) / 2)) * nearMajorant γ τ R
      ≤ (∫ τ in Ioc 0 (R ^ 2), R ^ (-min γ ((n : ℝ) + 1)) * R⁻¹ * τ ^ (-(1 / 2 : ℝ))) +
          ∫ τ in Ioi (R ^ 2), R ^ (-min γ ((n : ℝ) + 1)) * R ^ 3 * τ ^ (-(5 / 2 : ℝ)) :=
        add_le_add (setIntegral_mono_on hI1 hg1 measurableSet_Ioc hle1)
          (setIntegral_mono_on hI2 hg2 measurableSet_Ioi hle2)
    _ = R ^ (-min γ ((n : ℝ) + 1)) * (8 / 3) := by
        rw [integral_const_mul, integral_const_mul, integral_Ioc_rpow_neg_half hR0,
          integral_Ioi_rpow_neg_five_half hR0]
        field_simp
        ring
    _ ≤ 3 * R ^ (-min γ ((n : ℝ) + 1)) := by linarith

end Breakdown.FarField
