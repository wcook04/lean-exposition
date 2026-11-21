import Breakdown.Cert.ExtendedNodes

open scoped ENNReal
open MeasureTheory

noncomputable section

namespace Breakdown.Cert

namespace Internal.ExtendedRowNorm

abbrev slabMeasure : Measure (ℝ × Space) := (volume.restrict (Set.Icc (0 : ℝ) 1)).prod volume

theorem slabMeasure_eq :
    slabMeasure = (volume : Measure (ℝ × Space)).restrict (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ) := by
  rw [slabMeasure, Measure.volume_eq_prod, ← Measure.prod_restrict, Measure.restrict_univ]

theorem aestronglyMeasurable_slab {F : ℝ → Space → Space} (hF : IsPeriodicField F) :
    AEStronglyMeasurable (fun z : ℝ × Space => F z.1 z.2) slabMeasure := by
  rw [slabMeasure_eq]
  exact hF.1.restrict

theorem periodLIntegral_eq_slab' {F : ℝ → Space → Space}
    (h : AEStronglyMeasurable (fun z : ℝ × Space => F z.1 z.2) volume) :
    periodLIntegral (fun σ y => ‖F σ y‖ ^ 2)
      = ∫⁻ z, ENNReal.ofReal (‖F z.1 z.2‖ ^ 2) ∂slabMeasure := by
  have hm : AEStronglyMeasurable (fun z : ℝ × Space => F z.1 z.2) slabMeasure := by
    rw [slabMeasure_eq]
    exact h.restrict
  exact (lintegral_prod (fun z : ℝ × Space => ENNReal.ofReal (‖F z.1 z.2‖ ^ 2))
    ((hm.norm.aemeasurable.pow_const 2).ennreal_ofReal)).symm

theorem periodLIntegral_eq_slab {F : ℝ → Space → Space} (hF : IsPeriodicField F) :
    periodLIntegral (fun σ y => ‖F σ y‖ ^ 2)
      = ∫⁻ z, ENNReal.ofReal (‖F z.1 z.2‖ ^ 2) ∂slabMeasure :=
  periodLIntegral_eq_slab' hF.1

theorem integrable_sq_slab {F : ℝ → Space → Space} (hF : IsPeriodicField F) :
    Integrable (fun z : ℝ × Space => ‖F z.1 z.2‖ ^ 2) slabMeasure := by
  have hm := aestronglyMeasurable_slab hF
  have hfin : ∫⁻ z, ENNReal.ofReal (‖F z.1 z.2‖ ^ 2) ∂slabMeasure ≠ ⊤ := by
    rw [← periodLIntegral_eq_slab hF]
    exact hF.2.2.ne
  refine (integrable_toReal_of_lintegral_ne_top (hm.norm.pow 2).aemeasurable.ennreal_ofReal
    hfin).congr ?_
  exact ae_of_all _ (fun z => ENNReal.toReal_ofReal (sq_nonneg _))

theorem memLp_slab {F : ℝ → Space → Space} (hF : IsPeriodicField F) :
    MemLp (fun z : ℝ × Space => F z.1 z.2) 2 slabMeasure :=
  (memLp_two_iff_integrable_sq_norm (aestronglyMeasurable_slab hF)).2 (integrable_sq_slab hF)

theorem periodPairing_eq_inner {F M : ℝ → Space → Space} (hF : IsPeriodicField F)
    (hM : IsPeriodicField M) :
    periodPairing F M = inner ℝ ((memLp_slab hF).toLp _) ((memLp_slab hM).toLp _) := by
  rw [L2.inner_def]
  have hae : (fun z : ℝ × Space => inner ℝ (((memLp_slab hF).toLp _ : ℝ × Space →₂[slabMeasure] Space) z)
      (((memLp_slab hM).toLp _ : ℝ × Space →₂[slabMeasure] Space) z))
      =ᵐ[slabMeasure] fun z => inner ℝ (F z.1 z.2) (M z.1 z.2) := by
    filter_upwards [(memLp_slab hF).coeFn_toLp, (memLp_slab hM).coeFn_toLp] with z h1 h2
    rw [h1, h2]
  have hint : Integrable (fun z : ℝ × Space => inner ℝ (F z.1 z.2) (M z.1 z.2)) slabMeasure :=
    (L2.integrable_inner _ _).congr hae
  rw [integral_congr_ae hae, slabMeasure, integral_prod _ hint]
  rfl

theorem periodNorm_eq_norm {F : ℝ → Space → Space} (hF : IsPeriodicField F) :
    periodNorm F = ‖(memLp_slab hF).toLp (fun z : ℝ × Space => F z.1 z.2)‖ := by
  rw [norm_eq_sqrt_real_inner, ← periodPairing_eq_inner hF hF, periodNorm]
  congr 1
  have hm := aestronglyMeasurable_slab hF
  have hint : Integrable (fun z : ℝ × Space => inner ℝ (F z.1 z.2) (F z.1 z.2)) slabMeasure :=
    (integrable_sq_slab hF).congr (ae_of_all _ fun z => (real_inner_self_eq_norm_sq _).symm)
  have h1 : periodPairing F F = ∫ z, ‖F z.1 z.2‖ ^ 2 ∂slabMeasure := by
    rw [show (fun z : ℝ × Space => ‖F z.1 z.2‖ ^ 2)
        = fun z : ℝ × Space => inner ℝ (F z.1 z.2) (F z.1 z.2) from
      funext fun z => (real_inner_self_eq_norm_sq _).symm, slabMeasure, integral_prod _ hint]
    rfl
  rw [h1, integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun z => sq_nonneg _) (hm.norm.pow 2),
    ← periodLIntegral_eq_slab hF]

theorem periodPairing_add_left {F F' M : ℝ → Space → Space} (hF : IsPeriodicField F)
    (hF' : IsPeriodicField F') (hM : IsPeriodicField M) (hS : IsPeriodicField fun σ y => F σ y + F' σ y) :
    periodPairing (fun σ y => F σ y + F' σ y) M = periodPairing F M + periodPairing F' M := by
  rw [periodPairing_eq_inner hS hM, periodPairing_eq_inner hF hM, periodPairing_eq_inner hF' hM,
    ← inner_add_left]
  congr 1

theorem periodPairing_neg_left (F M : ℝ → Space → Space) :
    periodPairing (fun σ y => -F σ y) M = -periodPairing F M := by
  unfold periodPairing
  simp only [inner_neg_left, integral_neg]

theorem isPeriodicField_add {F F' : ℝ → Space → Space} (hF : IsPeriodicField F)
    (hF' : IsPeriodicField F') : IsPeriodicField fun σ y => F σ y + F' σ y := by
  have hm : AEStronglyMeasurable (fun z : ℝ × Space => F z.1 z.2 + F' z.1 z.2) volume := hF.1.add hF'.1
  refine ⟨hm, fun σ y => by simp only [hF.2.1 σ y, hF'.2.1 σ y], ?_⟩
  have hL : MemLp (fun z : ℝ × Space => F z.1 z.2 + F' z.1 z.2) 2 slabMeasure :=
    (memLp_slab hF).add (memLp_slab hF')
  have hmS : AEStronglyMeasurable (fun z : ℝ × Space => F z.1 z.2 + F' z.1 z.2) slabMeasure := by
    rw [slabMeasure_eq]
    exact hm.restrict
  have hi := (memLp_two_iff_integrable_sq_norm hmS).1 hL
  rw [periodLIntegral_eq_slab' hm]
  exact hi.lintegral_lt_top

theorem weighted_sqrt_add_le {m : ℕ} (τ p q : Fin m → ℝ) (hτ : ∀ a, 0 ≤ τ a) :
    Real.sqrt (∑ a, τ a * (p a + q a) ^ 2)
      ≤ Real.sqrt (∑ a, τ a * p a ^ 2) + Real.sqrt (∑ a, τ a * q a ^ 2) := by
  set A := ∑ a, τ a * p a ^ 2
  set B := ∑ a, τ a * q a ^ 2
  set C := ∑ a, τ a * (p a * q a)
  have hA : 0 ≤ A := Finset.sum_nonneg fun a _ => mul_nonneg (hτ a) (sq_nonneg _)
  have hB : 0 ≤ B := Finset.sum_nonneg fun a _ => mul_nonneg (hτ a) (sq_nonneg _)
  have hexp : ∑ a, τ a * (p a + q a) ^ 2 = A + 2 * C + B := by
    simp only [A, B, C, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun a _ => by ring
  have hcs : C ^ 2 ≤ A * B := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun a => Real.sqrt (τ a) * p a)
      (fun a => Real.sqrt (τ a) * q a)
    have e1 : ∀ a, Real.sqrt (τ a) * p a * (Real.sqrt (τ a) * q a) = τ a * (p a * q a) := fun a => by
      have := Real.mul_self_sqrt (hτ a)
      linear_combination (p a * q a) * this
    have e2 : ∀ (a : Fin m) (x : ℝ), (Real.sqrt (τ a) * x) ^ 2 = τ a * x ^ 2 := fun a x => by
      rw [mul_pow, Real.sq_sqrt (hτ a)]
    simp only [e1, e2] at h
    exact h
  have hsA := Real.sq_sqrt hA
  have hsB := Real.sq_sqrt hB
  have hC : C ≤ Real.sqrt A * Real.sqrt B := by
    have h0 : 0 ≤ Real.sqrt A * Real.sqrt B := mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    have h2 : C ^ 2 ≤ (Real.sqrt A * Real.sqrt B) ^ 2 := by rw [mul_pow, hsA, hsB]; exact hcs
    nlinarith
  rw [hexp]
  calc Real.sqrt (A + 2 * C + B) ≤ Real.sqrt ((Real.sqrt A + Real.sqrt B) ^ 2) :=
        Real.sqrt_le_sqrt (by nlinarith)
    _ = Real.sqrt A + Real.sqrt B := Real.sqrt_sq (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))

end Internal.ExtendedRowNorm

open Internal.ExtendedRowNorm in
theorem rowNormHolds : RowNormHolds := by
  intro m e τ B he hortho hτ hτB hB F F' hF hF'
  have hS := isPeriodicField_add hF hF'
  refine ⟨?_, ?_, ?_⟩
  · unfold rowNorm
    simp only [periodPairing_add_left hF hF' (he _) hS]
    exact weighted_sqrt_add_le τ _ _ hτ
  · unfold rowNorm
    simp only [periodPairing_neg_left, neg_sq]
  · unfold rowNorm
    classical
    set x : Fin m → (ℝ × Space →₂[slabMeasure] Space) := fun a => (memLp_slab (he a)).toLp _
    have hon : Orthonormal ℝ x := by
      rw [orthonormal_iff_ite]
      intro a b
      rw [← periodPairing_eq_inner (he a) (he b)]
      convert hortho a b
    have hsumInner := hon.sum_inner_products_le (s := Finset.univ)
      (x := (memLp_slab hF).toLp (fun z : ℝ × Space => F z.1 z.2))
    have hp : ∀ a, periodPairing F (e a) ^ 2 = ‖inner ℝ (x a) ((memLp_slab hF).toLp (fun z : ℝ × Space => F z.1 z.2))‖ ^ 2 := fun a => by
      rw [Real.norm_eq_abs, sq_abs, real_inner_comm, periodPairing_eq_inner hF (he a)]
    have hsum : ∑ a, τ a * periodPairing F (e a) ^ 2 ≤ (B * periodNorm F) ^ 2 := by
      calc ∑ a, τ a * periodPairing F (e a) ^ 2 ≤ ∑ a, B ^ 2 * periodPairing F (e a) ^ 2 :=
            Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_right (hτB a) (sq_nonneg _)
        _ = B ^ 2 * ∑ a, periodPairing F (e a) ^ 2 := by rw [Finset.mul_sum]
        _ ≤ B ^ 2 * periodNorm F ^ 2 := by
            refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
            simp only [hp]
            rw [periodNorm_eq_norm hF]
            exact hsumInner
        _ = (B * periodNorm F) ^ 2 := by ring
    calc Real.sqrt (∑ a, τ a * periodPairing F (e a) ^ 2) ≤ Real.sqrt ((B * periodNorm F) ^ 2) :=
          Real.sqrt_le_sqrt hsum
      _ = B * periodNorm F := Real.sqrt_sq (mul_nonneg hB (Real.sqrt_nonneg _))

end Breakdown.Cert
