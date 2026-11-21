import Breakdown.FracCell.ReductionLossDefs
import Breakdown.FracCert.LinearStateClosed

open MeasureTheory

noncomputable section

namespace Breakdown

namespace CellCert

namespace Reduction

open SteadyCert

private theorem four_mean (x y z : ℝ) :
    x * y * z ^ 2 ≤ (x ^ 4 + y ^ 4 + 2 * z ^ 4) / 4 := by
  have h1 : x * y ≤ (x ^ 2 + y ^ 2) / 2 := by nlinarith [sq_nonneg (x - y)]
  have h2 : x * y * z ^ 2 ≤ (x ^ 2 + y ^ 2) / 2 * z ^ 2 := mul_le_mul_of_nonneg_right h1 (sq_nonneg z)
  nlinarith [sq_nonneg ((x ^ 2 + y ^ 2) / 2 - z ^ 2), sq_nonneg (x ^ 2 - y ^ 2)]

private theorem fourth_root {r : ℝ} (hr : 0 < r) : ∃ ρ : ℝ, 0 < ρ ∧ ρ ^ 4 = r :=
  ⟨r ^ (((4 : ℕ) : ℝ)⁻¹), Real.rpow_pos_of_pos hr _, Real.rpow_inv_natCast_pow hr.le (by norm_num)⟩

private theorem sum_bound {κ w : ℝ} (hκ : 0 < κ) (hw : 0 < w) (hk : 256 * (κ ^ 4 * w ^ 3) = 27)
    (a b p q : ℝ) :
    a * b * p ^ 2 + p * q * a ^ 2 ≤ κ * (w * a ^ 4 + b ^ 4 + (w * p ^ 4 + q ^ 4)) := by
  obtain ⟨ρ, hρ, hρ4⟩ := fourth_root (show 0 < 4 * κ * w / 3 by positivity)
  have hρ3 : 0 < ρ ^ 3 := by positivity
  set τ := 1 / ρ ^ 3 with hτ
  have hτ0 : 0 < τ := by positivity
  have hρτ : ρ ^ 3 * τ = 1 := by rw [hτ]; field_simp
  have hτ4 : τ ^ 4 = 4 * κ := by
    have h12 : ρ ^ 12 = (4 * κ * w / 3) ^ 3 := by rw [← hρ4]; ring
    have e1 : τ ^ 4 * ρ ^ 12 = 1 := by
      rw [show τ ^ 4 * ρ ^ 12 = (ρ ^ 3 * τ) ^ 4 by ring, hρτ]; norm_num
    have e2 : 4 * κ * ρ ^ 12 = 1 := by rw [h12]; linear_combination (1 / 27 : ℝ) * hk
    have hne : ρ ^ 12 ≠ 0 := by positivity
    exact mul_right_cancel₀ hne (e1.trans e2.symm)
  have h1 := four_mean (ρ * a) (τ * b) (ρ * p)
  have h2 := four_mean (ρ * p) (τ * q) (ρ * a)
  have e1 : ρ * a * (τ * b) * (ρ * p) ^ 2 = a * b * p ^ 2 := by
    calc _ = (ρ ^ 3 * τ) * (a * b * p ^ 2) := by ring
      _ = _ := by rw [hρτ, one_mul]
  have e2 : ρ * p * (τ * q) * (ρ * a) ^ 2 = p * q * a ^ 2 := by
    calc _ = (ρ ^ 3 * τ) * (p * q * a ^ 2) := by ring
      _ = _ := by rw [hρτ, one_mul]
  rw [e1] at h1
  rw [e2] at h2
  calc a * b * p ^ 2 + p * q * a ^ 2
      ≤ ((ρ * a) ^ 4 + (τ * b) ^ 4 + 2 * (ρ * p) ^ 4) / 4 + ((ρ * p) ^ 4 + (τ * q) ^ 4 + 2 * (ρ * a) ^ 4) / 4 :=
        add_le_add h1 h2
    _ = (3 * ρ ^ 4 / 4) * (a ^ 4 + p ^ 4) + τ ^ 4 / 4 * (b ^ 4 + q ^ 4) := by ring
    _ = _ := by rw [hρ4, hτ4]; ring

private theorem pair_bound {κ w : ℝ} (hκ : 0 < κ) (hw : 0 < w) (hk : 256 * (κ ^ 4 * w ^ 3) = 27)
    {a b p q : ℝ} (ha : 0 ≤ a) (hp : 0 ≤ p) :
    a * b * p ^ 2 + p * q * a ^ 2 ≤
      2 * κ * (Real.sqrt (w * a ^ 4 + b ^ 4) * Real.sqrt (w * p ^ 4 + q ^ 4)) := by
  rcases ha.eq_or_lt with ha0 | ha'
  · calc _ = (0 : ℝ) := by rw [← ha0]; ring
      _ ≤ _ := by positivity
  rcases hp.eq_or_lt with hp0 | hp'
  · calc _ = (0 : ℝ) := by rw [← hp0]; ring
      _ ≤ _ := by positivity
  set s := Real.sqrt (w * a ^ 4 + b ^ 4) with hsdef
  set t := Real.sqrt (w * p ^ 4 + q ^ 4) with htdef
  have hs : 0 < s := Real.sqrt_pos.2 (by positivity)
  have ht : 0 < t := Real.sqrt_pos.2 (by positivity)
  have hs2 : s ^ 2 = w * a ^ 4 + b ^ 4 := Real.sq_sqrt (by positivity)
  have ht2 : t ^ 2 = w * p ^ 4 + q ^ 4 := Real.sq_sqrt (by positivity)
  obtain ⟨m, hm, hm4⟩ := fourth_root (div_pos ht hs)
  have h := sum_bound hκ hw hk (m * a) (m * b) (p / m) (q / m)
  have hm0 : m ≠ 0 := hm.ne'
  have el : m * a * (m * b) * (p / m) ^ 2 + p / m * (q / m) * (m * a) ^ 2 = a * b * p ^ 2 + p * q * a ^ 2 := by
    field_simp
  have er : w * (m * a) ^ 4 + (m * b) ^ 4 + (w * (p / m) ^ 4 + (q / m) ^ 4) = m ^ 4 * s ^ 2 + t ^ 2 / m ^ 4 := by
    rw [hs2, ht2]; field_simp
  rw [el, er, hm4] at h
  have e3 : t / s * s ^ 2 + t ^ 2 / (t / s) = 2 * (s * t) := by field_simp; ring
  rw [e3] at h
  linarith

private theorem entry_nonneg (G : Space →L[ℝ] Space) : 0 ≤ entrySq G :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

private theorem apply_le (A : Space →L[ℝ] Space) (x : Space) : ‖A x‖ ≤ Real.sqrt (entrySq A) * ‖x‖ := by
  have h := LinearStateClosedInternal.clm_sq_le A x
  rw [← Real.sqrt_sq (norm_nonneg (A x)), ← Real.sqrt_sq (norm_nonneg x), ← Real.sqrt_mul (entry_nonneg A)]
  exact Real.sqrt_le_sqrt h

private theorem product_norm_le {u w : Space → Space} {Gu Gw : Space → (Space →L[ℝ] Space)}
    (hiu : Integrable (fun y => entrySq (Gu y))) (hiw : Integrable (fun y => entrySq (Gw y)))
    {Su Sw : ℝ} (hSu : 0 ≤ Su) (hSw : 0 ≤ Sw) (hu : ∀ᵐ y ∂volume, ‖u y‖ ≤ Su) (hw : ∀ᵐ y ∂volume, ‖w y‖ ≤ Sw) :
    l2Norm (symProduct u Gu w Gw) ≤
      (1 / 2) * (Su * Real.sqrt (∫ y, entrySq (Gw y)) + Sw * Real.sqrt (∫ y, entrySq (Gu y))) := by
  set gu : Space → ℝ := fun y => Real.sqrt (entrySq (Gu y)) with hgu
  set gw : Space → ℝ := fun y => Real.sqrt (entrySq (Gw y)) with hgw
  have hmu : AEStronglyMeasurable gu volume :=
    Real.continuous_sqrt.comp_aestronglyMeasurable hiu.aestronglyMeasurable
  have hmw : AEStronglyMeasurable gw volume :=
    Real.continuous_sqrt.comp_aestronglyMeasurable hiw.aestronglyMeasurable
  have eu : ∀ y, gu y ^ 2 = entrySq (Gu y) := fun y => Real.sq_sqrt (entry_nonneg _)
  have ew : ∀ y, gw y ^ 2 = entrySq (Gw y) := fun y => Real.sq_sqrt (entry_nonneg _)
  have hsu : Integrable (fun y => gu y ^ 2) := hiu.congr (ae_of_all _ fun y => (eu y).symm)
  have hsw : Integrable (fun y => gw y ^ 2) := hiw.congr (ae_of_all _ fun y => (ew y).symm)
  have hLu : MemLp gu 2 volume := (memLp_two_iff_integrable_sq hmu).2 hsu
  have hLw : MemLp gw 2 volume := (memLp_two_iff_integrable_sq hmw).2 hsw
  have hprod : Integrable (fun y => gu y * gw y) := hLu.integrable_mul hLw
  have iu : ∫ y, gu y ^ 2 = ∫ y, entrySq (Gu y) := integral_congr_ae (ae_of_all _ eu)
  have iw : ∫ y, gw y ^ 2 = ∫ y, entrySq (Gw y) := integral_congr_ae (ae_of_all _ ew)
  set Xu := Real.sqrt (∫ y, entrySq (Gu y)) with hXu
  set Xw := Real.sqrt (∫ y, entrySq (Gw y)) with hXw
  have hXu0 : 0 ≤ Xu := Real.sqrt_nonneg _
  have hXw0 : 0 ≤ Xw := Real.sqrt_nonneg _
  have hXu2 : Xu ^ 2 = ∫ y, entrySq (Gu y) := Real.sq_sqrt (integral_nonneg fun y => entry_nonneg _)
  have hXw2 : Xw ^ 2 = ∫ y, entrySq (Gw y) := Real.sq_sqrt (integral_nonneg fun y => entry_nonneg _)
  have hCst : ∫ y, gu y * gw y ≤ Xu * Xw := by
    have h2 : ENNReal.ofReal 2 = 2 := by norm_num
    have hH := integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
      (ae_of_all _ fun y => Real.sqrt_nonneg (entrySq (Gu y)))
      (ae_of_all _ fun y => Real.sqrt_nonneg (entrySq (Gw y))) (by rw [h2]; exact hLu) (by rw [h2]; exact hLw)
    simp_rw [Real.rpow_two] at hH
    rw [iu, iw, ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow] at hH
    exact hH
  have hpt : ∀ᵐ y ∂volume, ‖symProduct u Gu w Gw y‖ ^ 2 ≤ ((1 / 2) * (Su * gw y + Sw * gu y)) ^ 2 := by
    filter_upwards [hu, hw] with y hy1 hy2
    have hb : ‖symProduct u Gu w Gw y‖ ≤ (1 / 2) * (Su * gw y + Sw * gu y) := by
      unfold symProduct
      rw [norm_smul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      calc ‖Gw y (u y) + Gu y (w y)‖ ≤ ‖Gw y (u y)‖ + ‖Gu y (w y)‖ := norm_add_le _ _
        _ ≤ gw y * ‖u y‖ + gu y * ‖w y‖ := add_le_add (apply_le _ _) (apply_le _ _)
        _ ≤ gw y * Su + gu y * Sw :=
          add_le_add (mul_le_mul_of_nonneg_left hy1 (Real.sqrt_nonneg _))
            (mul_le_mul_of_nonneg_left hy2 (Real.sqrt_nonneg _))
        _ = _ := by ring
    exact pow_le_pow_left₀ (norm_nonneg _) hb 2
  have efun : (fun y => ((1 / 2) * (Su * gw y + Sw * gu y)) ^ 2) =
      fun y => ((Su ^ 2 / 4) * gw y ^ 2 + (Su * Sw / 2) * (gu y * gw y)) + (Sw ^ 2 / 4) * gu y ^ 2 := by
    funext y; ring
  have hR : Integrable (fun y => ((1 / 2) * (Su * gw y + Sw * gu y)) ^ 2) := by
    rw [efun]
    exact ((hsw.const_mul _).add (hprod.const_mul _)).add (hsu.const_mul _)
  have hI : ∫ y, ((1 / 2) * (Su * gw y + Sw * gu y)) ^ 2 =
      (Su ^ 2 / 4) * Xw ^ 2 + (Su * Sw / 2) * (∫ y, gu y * gw y) + (Sw ^ 2 / 4) * Xu ^ 2 := by
    have i1 : Integrable (fun y => (Su ^ 2 / 4) * gw y ^ 2 + (Su * Sw / 2) * (gu y * gw y)) :=
      (hsw.const_mul _).add (hprod.const_mul _)
    rw [efun, integral_add i1 (hsu.const_mul _),
      integral_add (hsw.const_mul _) (hprod.const_mul _), integral_const_mul, integral_const_mul,
      integral_const_mul, iu, iw, hXu2, hXw2]
  have hle : ∫ y, ‖symProduct u Gu w Gw y‖ ^ 2 ≤ ((1 / 2) * (Su * Xw + Sw * Xu)) ^ 2 := by
    calc ∫ y, ‖symProduct u Gu w Gw y‖ ^ 2 ≤ ∫ y, ((1 / 2) * (Su * gw y + Sw * gu y)) ^ 2 :=
          integral_mono_of_nonneg (ae_of_all _ fun y => sq_nonneg _) hR hpt
      _ = _ := hI
      _ ≤ (Su ^ 2 / 4) * Xw ^ 2 + (Su * Sw / 2) * (Xu * Xw) + (Sw ^ 2 / 4) * Xu ^ 2 := by
          have := mul_le_mul_of_nonneg_left hCst (by positivity : (0 : ℝ) ≤ Su * Sw / 2)
          linarith
      _ = _ := by ring
  unfold l2Norm
  calc Real.sqrt (∫ y, ‖symProduct u Gu w Gw y‖ ^ 2) ≤ Real.sqrt (((1 / 2) * (Su * Xw + Sw * Xu)) ^ 2) :=
        Real.sqrt_le_sqrt hle
    _ = _ := Real.sqrt_sq (by positivity)

theorem productConst_of_supNorm (hS : SupNormStatement) {k N : ℕ} (d : FracCertData k N) (hw : 0 < d.weightMin)
    (hlow : ∀ y, d.weightMin ≤ d.weight y) (hmeas : Measurable d.weight) (hhigh : ∀ y, d.weight y ≤ d.weightMax)
    (hbound : (2 * Real.pi) ^ (-(1 : ℝ) / 2) * (27 / 256 : ℝ) ^ ((1 : ℝ) / 4) * d.weightMin ^ (-(3 : ℝ) / 4)
      ≤ d.productConst) :
    ∀ u Gu Hu, IsSecondOrderField d.order u Gu Hu → ∀ w Gw Hw, IsSecondOrderField d.order w Gw Hw →
      l2Norm (symProduct u Gu w Gw) ≤ d.productConst * Real.sqrt (d.energy Gu Hu) * Real.sqrt (d.energy Gw Hw) := by
  intro u Gu Hu hU w Gw Hw hW
  set w0 := d.weightMin with hw0
  set κ : ℝ := (27 / 256 : ℝ) ^ ((1 : ℝ) / 4) * w0 ^ (-(3 : ℝ) / 4) with hκdef
  set c : ℝ := (2 * Real.pi) ^ (-(1 : ℝ) / 2) with hcdef
  have hκ : 0 < κ := by positivity
  have hc : 0 < c := by positivity
  have hk : 256 * (κ ^ 4 * w0 ^ 3) = 27 := by
    have e1 : ((27 / 256 : ℝ) ^ ((1 : ℝ) / 4)) ^ 4 = 27 / 256 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num
    have e2 : (w0 ^ (-(3 : ℝ) / 4)) ^ 4 = (w0 ^ 3)⁻¹ := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hw.le,
        show (-(3 : ℝ)) / 4 * ((4 : ℕ) : ℝ) = -((3 : ℕ) : ℝ) by norm_num, Real.rpow_neg hw.le, Real.rpow_natCast]
    have hw3 : w0 ^ 3 ≠ 0 := by positivity
    calc 256 * (κ ^ 4 * w0 ^ 3) =
        256 * (((27 / 256 : ℝ) ^ ((1 : ℝ) / 4)) ^ 4 * ((w0 ^ (-(3 : ℝ) / 4)) ^ 4 * w0 ^ 3)) := by
          rw [hκdef]; ring
      _ = 27 := by rw [e1, e2, inv_mul_cancel₀ hw3]; norm_num
  have hcsq : c = Real.sqrt (1 / (2 * Real.pi)) := by
    rw [hcdef, Real.sqrt_eq_rpow, one_div, Real.inv_rpow (by positivity), ← Real.rpow_neg (by positivity)]
    congr 1
    ring
  have q4 : ∀ t : ℝ, 0 ≤ t → Real.sqrt (Real.sqrt t) ^ 4 = t := fun t ht => by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, Real.sq_sqrt (Real.sqrt_nonneg _), Real.sq_sqrt ht]
  have hfield : ∀ v G H, IsSecondOrderField d.order v G H →
      (∀ᵐ y ∂volume, ‖v y‖ ≤ c * (Real.sqrt (Real.sqrt (∫ z, entrySq (G z))) *
        Real.sqrt (Real.sqrt (∫ z, ‖secondTrace (H z)‖ ^ 2)))) ∧
      w0 * Real.sqrt (Real.sqrt (∫ z, entrySq (G z))) ^ 4 +
        Real.sqrt (Real.sqrt (∫ z, ‖secondTrace (H z)‖ ^ 2)) ^ 4 ≤ d.energy G H := by
    intro v G H hv
    refine ⟨?_, ?_⟩
    · have e : c * (Real.sqrt (Real.sqrt (∫ z, entrySq (G z))) *
          Real.sqrt (Real.sqrt (∫ z, ‖secondTrace (H z)‖ ^ 2))) =
          Real.sqrt (1 / (2 * Real.pi) * Real.sqrt (∫ z, entrySq (G z)) *
            Real.sqrt (∫ z, ‖secondTrace (H z)‖ ^ 2)) := by
        rw [hcsq, ← Real.sqrt_mul (Real.sqrt_nonneg _), ← Real.sqrt_mul (by positivity), mul_assoc]
      rw [e]
      filter_upwards [hS d.order v G H hv] with y hy
      have := Real.sqrt_le_sqrt hy
      rwa [Real.sqrt_sq (norm_nonneg _)] at this
    · have hint : Integrable (fun y => d.weight y * entrySq (G y)) :=
        hv.gradient_two.bdd_mul (c := d.weightMax) hmeas.aestronglyMeasurable
          (ae_of_all _ fun y => by rw [Real.norm_of_nonneg (hw.le.trans (hlow y))]; exact hhigh y)
      have hmono : w0 * ∫ y, entrySq (G y) ≤ ∫ y, d.weight y * entrySq (G y) := by
        rw [← integral_const_mul]
        exact integral_mono (hv.gradient_two.const_mul _) hint
          fun y => mul_le_mul_of_nonneg_right (hlow y) (entry_nonneg _)
      rw [q4 _ (integral_nonneg fun y => entry_nonneg _), q4 _ (integral_nonneg fun y => sq_nonneg _)]
      show _ ≤ weightedEnergy d.weight G H
      unfold weightedEnergy
      linarith
  obtain ⟨hu1, hu2⟩ := hfield u Gu Hu hU
  obtain ⟨hw1, hw2⟩ := hfield w Gw Hw hW
  set au := Real.sqrt (Real.sqrt (∫ z, entrySq (Gu z)))
  set bu := Real.sqrt (Real.sqrt (∫ z, ‖secondTrace (Hu z)‖ ^ 2))
  set aw := Real.sqrt (Real.sqrt (∫ z, entrySq (Gw z)))
  set bw := Real.sqrt (Real.sqrt (∫ z, ‖secondTrace (Hw z)‖ ^ 2))
  have hau : 0 ≤ au := Real.sqrt_nonneg _
  have hbu : 0 ≤ bu := Real.sqrt_nonneg _
  have haw : 0 ≤ aw := Real.sqrt_nonneg _
  have hbw : 0 ≤ bw := Real.sqrt_nonneg _
  have hau2 : au ^ 2 = Real.sqrt (∫ z, entrySq (Gu z)) := Real.sq_sqrt (Real.sqrt_nonneg _)
  have haw2 : aw ^ 2 = Real.sqrt (∫ z, entrySq (Gw z)) := Real.sq_sqrt (Real.sqrt_nonneg _)
  have hP := product_norm_le hU.gradient_two hW.gradient_two (by positivity) (by positivity) hu1 hw1
  rw [← hau2, ← haw2] at hP
  have hpair := pair_bound hκ hw hk (b := bu) (q := bw) hau haw
  have hEu := Real.sqrt_le_sqrt hu2
  have hEw := Real.sqrt_le_sqrt hw2
  have hcκ : c * κ ≤ d.productConst := by rw [hcdef, hκdef, ← mul_assoc]; exact hbound
  calc l2Norm (symProduct u Gu w Gw) ≤ (1 / 2) * (c * (au * bu) * aw ^ 2 + c * (aw * bw) * au ^ 2) := hP
    _ = c * ((au * bu * aw ^ 2 + aw * bw * au ^ 2) / 2) := by ring
    _ ≤ c * (κ * (Real.sqrt (w0 * au ^ 4 + bu ^ 4) * Real.sqrt (w0 * aw ^ 4 + bw ^ 4))) := by
        apply mul_le_mul_of_nonneg_left _ hc.le
        linarith
    _ = (c * κ) * Real.sqrt (w0 * au ^ 4 + bu ^ 4) * Real.sqrt (w0 * aw ^ 4 + bw ^ 4) := by ring
    _ ≤ d.productConst * Real.sqrt (d.energy Gu Hu) * Real.sqrt (d.energy Gw Hw) := by
        have h0 : 0 ≤ c * κ := by positivity
        apply mul_le_mul (mul_le_mul hcκ hEu (Real.sqrt_nonneg _) (h0.trans hcκ)) hEw (Real.sqrt_nonneg _)
        exact mul_nonneg (h0.trans hcκ) (Real.sqrt_nonneg _)

end Reduction

end CellCert

end Breakdown
