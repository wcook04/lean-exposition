import Breakdown.CertTorus.DecayStatements

open MeasureTheory Set Real intervalIntegral

noncomputable section

namespace Breakdown.FarField

namespace OuterFar.Internal

lemma min_one_rpow_le {x γ c : ℝ} (hx : 0 < x) (hc : 0 ≤ c) (hcγ : c ≤ γ) :
    min 1 (x ^ γ) ≤ x ^ c := by
  rcases le_or_gt x 1 with h | h
  · exact (min_le_right _ _).trans (Real.rpow_le_rpow_of_exponent_ge hx h hcγ)
  · exact (min_le_left _ _).trans (Real.one_le_rpow h.le hc)

lemma inv_sqrt_eq {τ : ℝ} (hτ : 0 < τ) : (Real.sqrt τ)⁻¹ = τ ^ (-(1 / 2 : ℝ)) := by
  rw [Real.sqrt_eq_rpow, Real.rpow_neg hτ.le]

lemma integrand_nonneg {b γ τ R : ℝ} (hτ : 0 < τ) (hR : 0 < R) :
    0 ≤ (1 + τ) ^ (-b) * farMajorant γ τ R := by
  unfold farMajorant
  have hx : 0 < Real.sqrt (1 + τ) / R := div_pos (Real.sqrt_pos.2 (by linarith)) hR
  exact mul_nonneg (Real.rpow_nonneg (by linarith) _)
    (mul_nonneg (inv_nonneg.2 (Real.sqrt_nonneg _)) (le_min zero_le_one (Real.rpow_nonneg hx.le _)))

lemma pointwise_weight {b γ c τ R : ℝ} (hτ : 0 < τ) (hR : 0 < R) (hc : 0 ≤ c) (hcγ : c ≤ γ) :
    (1 + τ) ^ (-b) * farMajorant γ τ R ≤ R ^ (-c) * (τ ^ (-(1 / 2 : ℝ)) * (1 + τ) ^ (c / 2 - b)) := by
  have h1 : 0 < 1 + τ := by linarith
  have hx : 0 < Real.sqrt (1 + τ) / R := div_pos (Real.sqrt_pos.2 h1) hR
  have hm := min_one_rpow_le hx hc hcγ
  have hxc : (Real.sqrt (1 + τ) / R) ^ c = (1 + τ) ^ (c / 2) * R ^ (-c) := by
    rw [Real.div_rpow (Real.sqrt_nonneg _) hR.le, Real.sqrt_eq_rpow, ← Real.rpow_mul h1.le,
      Real.rpow_neg hR.le, div_eq_mul_inv, show (1 / (2 : ℝ)) * c = c / 2 by ring]
  unfold farMajorant
  rw [inv_sqrt_eq hτ]
  have hp : 0 ≤ (1 + τ) ^ (-b) * τ ^ (-(1 / 2 : ℝ)) :=
    mul_nonneg (Real.rpow_nonneg h1.le _) (Real.rpow_nonneg hτ.le _)
  calc (1 + τ) ^ (-b) * (τ ^ (-(1 / 2 : ℝ)) * min 1 ((Real.sqrt (1 + τ) / R) ^ γ))
      = ((1 + τ) ^ (-b) * τ ^ (-(1 / 2 : ℝ))) * min 1 ((Real.sqrt (1 + τ) / R) ^ γ) := by ring
    _ ≤ ((1 + τ) ^ (-b) * τ ^ (-(1 / 2 : ℝ))) * ((1 + τ) ^ (c / 2) * R ^ (-c)) := by
        rw [← hxc]; exact mul_le_mul_of_nonneg_left hm hp
    _ = R ^ (-c) * (τ ^ (-(1 / 2 : ℝ)) * ((1 + τ) ^ (-b) * (1 + τ) ^ (c / 2))) := by ring
    _ = R ^ (-c) * (τ ^ (-(1 / 2 : ℝ)) * (1 + τ) ^ (c / 2 - b)) := by
        rw [← Real.rpow_add h1, show -b + c / 2 = c / 2 - b by ring]

lemma pointwise_tail {b γ τ R : ℝ} (hτ : 0 < τ) (hb : 0 ≤ b) (hR : 0 < R) :
    (1 + τ) ^ (-b) * farMajorant γ τ R ≤ τ ^ (-(1 / 2 : ℝ) - b) := by
  have hx : 0 < Real.sqrt (1 + τ) / R := div_pos (Real.sqrt_pos.2 (by linarith)) hR
  unfold farMajorant
  rw [inv_sqrt_eq hτ]
  have h1 : (1 + τ) ^ (-b) ≤ τ ^ (-b) := Real.rpow_le_rpow_of_nonpos hτ (by linarith) (by linarith)
  have hm : min 1 ((Real.sqrt (1 + τ) / R) ^ γ) ≤ 1 := min_le_left _ _
  have hm0 : 0 ≤ min 1 ((Real.sqrt (1 + τ) / R) ^ γ) :=
    le_min zero_le_one (Real.rpow_nonneg hx.le _)
  calc (1 + τ) ^ (-b) * (τ ^ (-(1 / 2 : ℝ)) * min 1 ((Real.sqrt (1 + τ) / R) ^ γ))
      ≤ τ ^ (-b) * (τ ^ (-(1 / 2 : ℝ)) * 1) :=
        mul_le_mul h1 (mul_le_mul_of_nonneg_left hm (Real.rpow_nonneg hτ.le _))
          (mul_nonneg (Real.rpow_nonneg hτ.le _) hm0) (Real.rpow_nonneg hτ.le _)
    _ = τ ^ (-(1 / 2 : ℝ) - b) := by
        rw [mul_one, ← Real.rpow_add hτ, show -b + -(1 / 2 : ℝ) = -(1 / 2) - b by ring]

lemma split_integral {f g h : ℝ → ℝ} {T : ℝ} (hT : 0 < T)
    (hf : AEStronglyMeasurable f (volume.restrict (Ioi 0)))
    (hf0 : ∀ τ : ℝ, 0 < τ → 0 ≤ f τ)
    (hg : IntegrableOn g (Ioc 0 T)) (hh : IntegrableOn h (Ioi T))
    (hfg : ∀ τ ∈ Ioc 0 T, f τ ≤ g τ) (hfh : ∀ τ ∈ Ioi T, f τ ≤ h τ) :
    IntegrableOn f (Ioi 0) ∧
      ∫ τ in Ioi 0, f τ ≤ (∫ τ in Ioc 0 T, g τ) + ∫ τ in Ioi T, h τ := by
  have h1 : IntegrableOn f (Ioc 0 T) := by
    refine hg.mono' (hf.mono_set Ioc_subset_Ioi_self) ?_
    refine (ae_restrict_iff' measurableSet_Ioc).2 (Filter.Eventually.of_forall fun τ hτ => ?_)
    rw [Real.norm_of_nonneg (hf0 τ hτ.1)]
    exact hfg τ hτ
  have h2 : IntegrableOn f (Ioi T) := by
    refine hh.mono' (hf.mono_set (Ioi_subset_Ioi hT.le)) ?_
    refine (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun τ hτ => ?_)
    rw [Real.norm_of_nonneg (hf0 τ (hT.trans hτ))]
    exact hfh τ hτ
  have hU : Ioc 0 T ∪ Ioi T = Ioi (0 : ℝ) := Ioc_union_Ioi_eq_Ioi hT.le
  refine ⟨by rw [← hU]; exact h1.union h2, ?_⟩
  rw [← hU, setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi h1 h2]
  exact add_le_add (setIntegral_mono_on h1 hg measurableSet_Ioc hfg)
    (setIntegral_mono_on h2 hh measurableSet_Ioi hfh)

lemma integral_Ioc_rpow {a T : ℝ} (ha : -1 < a) (hT : 0 ≤ T) :
    IntegrableOn (fun τ : ℝ => τ ^ a) (Ioc 0 T) ∧
      ∫ τ in Ioc 0 T, τ ^ a = T ^ (a + 1) / (a + 1) := by
  refine ⟨(intervalIntegrable_iff_integrableOn_Ioc_of_le hT).1 (intervalIntegrable_rpow' ha), ?_⟩
  rw [← intervalIntegral.integral_of_le hT, integral_rpow (Or.inl ha),
    Real.zero_rpow (by linarith), sub_zero]

lemma integrand_measurable (b γ R : ℝ) :
    AEStronglyMeasurable (fun τ : ℝ => (1 + τ) ^ (-b) * farMajorant γ τ R)
      (volume.restrict (Ioi 0)) := by
  unfold farMajorant
  apply Measurable.aestronglyMeasurable
  fun_prop

end OuterFar.Internal

open OuterFar.Internal in
theorem outerFarBound_holds : OuterFarBound := by
  intro n _ γ hγ hγn
  have hn : (0 : ℝ) ≤ n := n.cast_nonneg
  set b : ℝ := 1 + (n : ℝ) / 2 with hb
  have hb0 : 0 ≤ b := by rw [hb]; linarith
  rcases lt_or_gt_of_ne hγn with hlt | hgt
  · have he : γ / 2 - b - 1 / 2 < -1 := by rw [hb]; linarith
    refine ⟨2 - 1 / (γ / 2 - b - 1 / 2 + 1), fun R hR => ?_⟩
    have hR0 : 0 < R := by linarith
    have hA := integral_Ioc_rpow (a := -(1 / 2 : ℝ)) (by norm_num) zero_le_one
    have hB := integrableOn_Ioi_rpow_of_lt he zero_lt_one
    have hBv := integral_Ioi_rpow_of_lt he zero_lt_one
    have key := split_integral (f := fun τ => (1 + τ) ^ (-b) * farMajorant γ τ R)
      (g := fun τ => R ^ (-γ) * τ ^ (-(1 / 2 : ℝ)))
      (h := fun τ => R ^ (-γ) * τ ^ (γ / 2 - b - 1 / 2)) zero_lt_one
      (integrand_measurable b γ R) (fun τ hτ => integrand_nonneg hτ hR0)
      (hA.1.const_mul _) (hB.const_mul _) ?_ ?_
    · refine ⟨key.1, key.2.trans (le_of_eq ?_)⟩
      rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul, hA.2, hBv, min_eq_left hlt.le,
        Real.one_rpow, Real.one_rpow]
      ring
    · intro τ hτ
      refine (pointwise_weight hτ.1 hR0 hγ le_rfl).trans ?_
      refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg hR0.le _)
      calc τ ^ (-(1 / 2 : ℝ)) * (1 + τ) ^ (γ / 2 - b)
          ≤ τ ^ (-(1 / 2 : ℝ)) * 1 :=
            mul_le_mul_of_nonneg_left
              (Real.rpow_le_one_of_one_le_of_nonpos (by linarith [hτ.1]) (by linarith))
              (Real.rpow_nonneg hτ.1.le _)
        _ = τ ^ (-(1 / 2 : ℝ)) := mul_one _
    · intro τ hτ
      have hτ0 : (0 : ℝ) < τ := zero_lt_one.trans hτ
      refine (pointwise_weight hτ0 hR0 hγ le_rfl).trans ?_
      refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg hR0.le _)
      calc τ ^ (-(1 / 2 : ℝ)) * (1 + τ) ^ (γ / 2 - b)
          ≤ τ ^ (-(1 / 2 : ℝ)) * τ ^ (γ / 2 - b) :=
            mul_le_mul_of_nonneg_left
              (Real.rpow_le_rpow_of_nonpos hτ0 (by linarith) (by linarith))
              (Real.rpow_nonneg hτ0.le _)
        _ = τ ^ (γ / 2 - b - 1 / 2) := by
            rw [← Real.rpow_add hτ0, show -(1 / 2 : ℝ) + (γ / 2 - b) = γ / 2 - b - 1 / 2 by ring]
  · set c : ℝ := min γ ((n : ℝ) + 2) with hc
    have hc0 : 0 ≤ c := le_min hγ (by linarith)
    have hcγ : c ≤ γ := min_le_left _ _
    have hc1 : (n : ℝ) + 1 < c := lt_min hgt (by linarith)
    have hc2 : c ≤ (n : ℝ) + 2 := min_le_right _ _
    have ha : -1 < c / 2 - b - 1 / 2 := by rw [hb]; linarith
    have ha' : c / 2 - b ≤ 0 := by rw [hb]; linarith
    have ht : -(1 / 2 : ℝ) - b < -1 := by rw [hb]; linarith
    refine ⟨1 / (c / 2 - b - 1 / 2 + 1) - 1 / (-(1 / 2 : ℝ) - b + 1), fun R hR => ?_⟩
    have hR0 : 0 < R := by linarith
    have hT : 0 < R ^ 2 := by positivity
    have hA := integral_Ioc_rpow ha hT.le
    have hB := integrableOn_Ioi_rpow_of_lt ht hT
    have hBv := integral_Ioi_rpow_of_lt ht hT
    have key := split_integral (f := fun τ => (1 + τ) ^ (-b) * farMajorant γ τ R)
      (g := fun τ => R ^ (-c) * τ ^ (c / 2 - b - 1 / 2))
      (h := fun τ => τ ^ (-(1 / 2 : ℝ) - b)) hT
      (integrand_measurable b γ R) (fun τ hτ => integrand_nonneg hτ hR0)
      (hA.1.const_mul _) hB ?_ ?_
    · refine ⟨key.1, key.2.trans (le_of_eq ?_)⟩
      have e1 : R ^ (-c) * (R ^ 2) ^ (c / 2 - b - 1 / 2 + 1) = R ^ (-((n : ℝ) + 1)) := by
        rw [← Real.rpow_natCast_mul hR0.le, ← Real.rpow_add hR0]
        congr 1
        rw [hb]
        push_cast
        ring
      have e2 : (R ^ 2) ^ (-(1 / 2 : ℝ) - b + 1) = R ^ (-((n : ℝ) + 1)) := by
        rw [← Real.rpow_natCast_mul hR0.le]
        congr 1
        rw [hb]
        push_cast
        ring
      rw [MeasureTheory.integral_const_mul, hA.2, hBv, min_eq_right hgt.le, mul_div_assoc', e1, e2]
      ring
    · intro τ hτ
      refine (pointwise_weight hτ.1 hR0 hc0 hcγ).trans ?_
      refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg hR0.le _)
      calc τ ^ (-(1 / 2 : ℝ)) * (1 + τ) ^ (c / 2 - b)
          ≤ τ ^ (-(1 / 2 : ℝ)) * τ ^ (c / 2 - b) :=
            mul_le_mul_of_nonneg_left
              (Real.rpow_le_rpow_of_nonpos hτ.1 (by linarith) ha')
              (Real.rpow_nonneg hτ.1.le _)
        _ = τ ^ (c / 2 - b - 1 / 2) := by
            rw [← Real.rpow_add hτ.1, show -(1 / 2 : ℝ) + (c / 2 - b) = c / 2 - b - 1 / 2 by ring]
    · intro τ hτ
      exact pointwise_tail (hT.trans hτ) hb0 hR0

end Breakdown.FarField
