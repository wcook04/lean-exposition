import Breakdown.FracCell.ReductionPointwiseDefs

open MeasureTheory

noncomputable section

namespace Breakdown

namespace CellCert

namespace Reduction

open SteadyCert Assembly CellAnalysis

private lemma turn_lower (k : ℝ) (hk : 1 ≤ |k|) (v : Fin 3 → ℂ) :
    (|k| - 1) ^ 2 * vecSq v ≤ vecSq (turnVec k v) := by
  have h2 : ∀ z : ℂ, ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
    intro z; rw [Complex.sq_norm, Complex.normSq_apply]; ring
  simp only [vecSq, turnVec, Fin.sum_univ_three, h2]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons, Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.mul_re,
    Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
  rcases abs_cases k with ⟨hk', hk0⟩ | ⟨hk', hk0⟩ <;> rw [hk'] at hk ⊢
  · nlinarith [mul_nonneg hk0 (sq_nonneg ((v 0).im + (v 1).re)), mul_nonneg hk0 (sq_nonneg ((v 0).re - (v 1).im)),
      mul_nonneg hk0 (sq_nonneg ((v 0).im - (v 1).re)), mul_nonneg hk0 (sq_nonneg ((v 0).re + (v 1).im)),
      mul_nonneg (by linarith : (0:ℝ) ≤ 2 * k - 1) (sq_nonneg (v 2).re),
      mul_nonneg (by linarith : (0:ℝ) ≤ 2 * k - 1) (sq_nonneg (v 2).im)]
  · nlinarith [mul_nonneg (neg_nonneg.mpr hk0.le) (sq_nonneg ((v 0).im + (v 1).re)),
      mul_nonneg (neg_nonneg.mpr hk0.le) (sq_nonneg ((v 0).re - (v 1).im)),
      mul_nonneg (neg_nonneg.mpr hk0.le) (sq_nonneg ((v 0).im - (v 1).re)),
      mul_nonneg (neg_nonneg.mpr hk0.le) (sq_nonneg ((v 0).re + (v 1).im)),
      mul_nonneg (by linarith : (0:ℝ) ≤ -2 * k - 1) (sq_nonneg (v 2).re),
      mul_nonneg (by linarith : (0:ℝ) ≤ -2 * k - 1) (sq_nonneg (v 2).im)]

private lemma lin_range {r a b X : ℝ} (ha : a ≤ r) (hb : r ≤ b) :
    r * X ≤ max (a * X) (b * X) := by
  rcases le_total 0 X with h | h
  · exact le_trans (mul_le_mul_of_nonneg_right hb h) (le_max_right _ _)
  · exact le_trans (mul_le_mul_of_nonpos_right ha h) (le_max_left _ _)

private lemma hbase {r rLo rHi A B lam k0 k' ℓ ps pc pv C Q V x y r2 u ke ac sb sq E : ℝ}
    (hr0 : 0 ≤ rLo) (hrLo : rLo ≤ r) (hrHi : r ≤ rHi) (hC : 0 ≤ C) (hQ : 0 ≤ Q)
    (hxy : x * y ≤ r2 * Q * u) (hVb : V ≤ r2 ^ 2 * Q * u ^ 2) (hu : 0 ≤ u) (huue : u ≤ (ke - 1)⁻¹) (hr2 : 0 ≤ r2)
    (hk0 : 0 ≤ k0) (hk' : 0 ≤ k') (hℓ : 0 < ℓ) (hps : 0 ≤ ps) (hpv : 0 ≤ pv)
    (hac : max (rLo * (lam + pc - A)) (rHi * (lam + pc - A)) ≤ ac)
    (hsb : max (rLo * (k' * ℓ - B)) (rHi * (k' * ℓ - B)) ≤ sb) (hsq : rHi * k' / ℓ ≤ sq)
    (hE : A * C + B * Q - (lam * C + 2 * k0 * (x * y) + k' * (ℓ * Q + V / ℓ)) - (ps * Q + pc * C + pv * V) ≤ E) :
    0 ≤ r * E + ac * C + (sb + rHi * ps + 2 * k0 * rHi * r2 / (ke - 1) + (sq + rHi * pv) * r2 ^ 2 / (ke - 1) ^ 2) * Q := by
  set ue := (ke - 1)⁻¹ with hue
  have hr : 0 ≤ r := le_trans hr0 hrLo
  have hrh : 0 ≤ rHi := le_trans hr hrHi
  have h1 : r * (lam + pc - A) ≤ ac := le_trans (lin_range hrLo hrHi) hac
  have h2 : r * (k' * ℓ - B) ≤ sb := le_trans (lin_range hrLo hrHi) hsb
  have e1 : 2 * k0 * rHi * r2 / (ke - 1) = 2 * k0 * rHi * r2 * ue := by
    rw [hue, div_eq_mul_inv]
  have e2 : (sq + rHi * pv) * r2 ^ 2 / (ke - 1) ^ 2 = (sq + rHi * pv) * r2 ^ 2 * ue ^ 2 := by
    rw [hue, inv_pow, div_eq_mul_inv]
  rw [e1, e2]
  have hkl : k' / ℓ * ℓ = k' := div_mul_cancel₀ _ hℓ.ne'
  have hVl : V / ℓ ≤ r2 ^ 2 * Q * u ^ 2 / ℓ := div_le_div_of_nonneg_right hVb hℓ.le
  have hq0 : 0 ≤ k' / ℓ := div_nonneg hk' hℓ.le
  have hsq' : r * (k' / ℓ) ≤ sq := by
    have : rHi * k' / ℓ = rHi * (k' / ℓ) := by ring
    linarith [mul_le_mul_of_nonneg_right hrHi hq0]
  have hE' : (A - lam - pc) * C + (B - k' * ℓ - ps) * Q - 2 * k0 * (r2 * u) * Q
      - (k' / ℓ + pv) * (r2 ^ 2 * u ^ 2) * Q ≤ E := by
    have a1 : k' * (V / ℓ) = k' / ℓ * V := by ring
    have a2 : k0 * (x * y) ≤ k0 * (r2 * Q * u) := mul_le_mul_of_nonneg_left hxy hk0
    have a3 : (k' / ℓ + pv) * V ≤ (k' / ℓ + pv) * (r2 ^ 2 * Q * u ^ 2) :=
      mul_le_mul_of_nonneg_left hVb (by positivity)
    have a4 : k' * (ℓ * Q + V / ℓ) = k' * ℓ * Q + k' / ℓ * V := by ring
    linarith
  have hrE := mul_le_mul_of_nonneg_left hE' hr
  have u2 : u ^ 2 ≤ ue ^ 2 := pow_le_pow_left₀ hu huue 2
  have b1 : r * (2 * k0 * (r2 * u)) ≤ 2 * k0 * rHi * r2 * ue := by
    have : 0 ≤ 2 * k0 * r2 := by positivity
    have h := mul_le_mul_of_nonneg_left (mul_le_mul hrHi huue hu hrh) this
    linarith
  have b2 : r * ((k' / ℓ + pv) * (r2 ^ 2 * u ^ 2)) ≤ (sq + rHi * pv) * r2 ^ 2 * ue ^ 2 := by
    have c1 : r * (k' / ℓ + pv) ≤ sq + rHi * pv := by
      linarith [mul_le_mul_of_nonneg_right hrHi hpv]
    have c2 : 0 ≤ r * (k' / ℓ + pv) := by positivity
    have c3 : r2 ^ 2 * u ^ 2 ≤ r2 ^ 2 * ue ^ 2 := mul_le_mul_of_nonneg_left u2 (sq_nonneg _)
    have c4 : 0 ≤ sq + rHi * pv := le_trans c2 c1
    have := mul_le_mul c1 c3 (by positivity) c4
    linarith
  have b3 : r * ps ≤ rHi * ps := mul_le_mul_of_nonneg_right hrHi hps
  have f1 : 0 ≤ (ac - r * (lam + pc - A)) * C := mul_nonneg (by linarith) hC
  have f2 : 0 ≤ (sb + rHi * ps + 2 * k0 * rHi * r2 * ue + (sq + rHi * pv) * r2 ^ 2 * ue ^ 2
      - r * (k' * ℓ - B) - r * ps - r * (2 * k0 * (r2 * u)) - r * ((k' / ℓ + pv) * (r2 ^ 2 * u ^ 2))) * Q :=
    mul_nonneg (by linarith) hQ
  linarith

private lemma natAbs_real (n : ℤ) : ((n.natAbs : ℕ) : ℝ) = |(n : ℝ)| := by
  rw [← Int.cast_natCast, Int.natCast_natAbs, Int.cast_abs]

theorem unresolvedPointwise_of : UnresolvedPointwiseStatement := by
  intro α k N c K S W hK hF hT n hn p hp hp1 s v hs hturn
  have hpr : p.1 ∈ Set.Icc K.r₁ K.r₂ := (Set.mem_prod.mp hp).1
  have hp0 : 0 ≤ p.1 := le_trans hK.r_order.1 hpr.1
  have hr2 : 0 ≤ K.r₂ := le_trans hp0 hpr.2
  have hrange := hT.range_spec p hp hp1
  have hcn := hT.consts_nonneg
  have hpen := hT.penalties_nonneg
  have hnR : n ∉ Finset.Icc (-(W.J : ℤ)) W.J := hF.resolved_eq ▸ hn
  have hnJ : W.J + 1 ≤ n.natAbs := by
    simp only [Finset.mem_Icc, not_and_or, not_le] at hnR
    omega
  have hord : (3 : ℝ) ≤ c.order := by exact_mod_cast hT.order_ge
  have hκ : modeNumber c.order n = |(n : ℝ)| * c.order := by
    simp only [modeNumber, azimuth, abs_mul, Nat.abs_cast]
  have hnR1 : (1 : ℝ) ≤ |(n : ℝ)| := by
    rw [← natAbs_real]; exact_mod_cast (by omega : 1 ≤ n.natAbs)
  have hκ3 : 3 ≤ modeNumber c.order n := by
    rw [hκ]; nlinarith
  have hke : 3 ≤ W.kEff c.order n ∧ W.kEff c.order n ≤ modeNumber c.order n := by
    unfold WeightData.kEff
    split_ifs with h
    · exact ⟨hκ3, le_rfl⟩
    · simp only [not_le] at h
      have h' : W.J + W.JB + 1 ≤ n.natAbs := by omega
      have h'' : ((W.J + W.JB + 1 : ℕ) : ℝ) ≤ |(n : ℝ)| := by
        rw [← natAbs_real]; exact_mod_cast h'
      have h1 : (1 : ℝ) ≤ ((W.J + W.JB + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ W.J + W.JB + 1)
      constructor
      · nlinarith
      · rw [hκ]; exact mul_le_mul_of_nonneg_right h'' (by positivity)
  have hQ0 : 0 ≤ sumSq s := Finset.sum_nonneg (fun a _ => Finset.sum_nonneg (fun b _ => by positivity))
  have hC0 : 0 ≤ curlSq s := Finset.sum_nonneg (fun a _ => by positivity)
  have hVpos : 0 ≤ vecSq v := Finset.sum_nonneg (fun a _ => by positivity)
  have hVt : (modeNumber c.order n - 1) ^ 2 * vecSq v ≤ K.r₂ ^ 2 * sumSq s := by
    have h1 := turn_lower (azimuth c.order n) (by unfold modeNumber at hκ3; linarith) v
    rw [hturn] at h1
    have h2 : vecSq (fun a => (p.1 : ℂ) * s a 1) = p.1 ^ 2 * ∑ a, ‖s a 1‖ ^ 2 := by
      simp only [vecSq, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs, Finset.mul_sum]
    have h3 : ∑ a, ‖s a 1‖ ^ 2 ≤ sumSq s := Finset.sum_le_sum (fun a _ =>
      Finset.single_le_sum (f := fun b => ‖s a b‖ ^ 2) (fun b _ => by positivity) (Finset.mem_univ 1))
    have h4 : p.1 ^ 2 ≤ K.r₂ ^ 2 := pow_le_pow_left₀ hp0 hpr.2 2
    have h5 := mul_le_mul h4 h3 (Finset.sum_nonneg (fun a _ => by positivity)) (sq_nonneg _)
    have h6 : modeNumber c.order n = |azimuth c.order n| := rfl
    rw [h6]; linarith
  set κ := modeNumber c.order n with hκdef
  set x := Real.sqrt (sumSq s) with hx
  set y := Real.sqrt (vecSq v) with hy
  have hκ1 : 0 < κ - 1 := by linarith
  set u := (κ - 1)⁻¹ with hu
  have hu0 : 0 ≤ u := inv_nonneg.mpr hκ1.le
  have hyx : (κ - 1) * y ≤ K.r₂ * x := by
    have := Real.sqrt_le_sqrt hVt
    rwa [Real.sqrt_mul (sq_nonneg _), Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hκ1.le, Real.sqrt_sq hr2] at this
  have hxx : x * x = sumSq s := Real.mul_self_sqrt hQ0
  have hcu : (κ - 1) * u = 1 := mul_inv_cancel₀ hκ1.ne'
  have hxy : x * y ≤ K.r₂ * sumSq s * u := by
    have e : x * y = ((κ - 1) * y) * x * u := by
      calc x * y = x * y * ((κ - 1) * u) := by rw [hcu, mul_one]
        _ = _ := by ring
    rw [e, ← hxx]
    have hx0 : 0 ≤ x := Real.sqrt_nonneg _
    have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hyx hx0) hu0
    linarith
  have hVb : vecSq v ≤ K.r₂ ^ 2 * sumSq s * u ^ 2 := by
    have e : vecSq v = (κ - 1) ^ 2 * vecSq v * u ^ 2 := by
      calc vecSq v = vecSq v * ((κ - 1) * u) ^ 2 := by rw [hcu]; ring
        _ = _ := by ring
    rw [e]
    exact mul_le_mul_of_nonneg_right hVt (sq_nonneg _)
  have huue : u ≤ (W.kEff c.order n - 1)⁻¹ := by
    rw [hu]; exact inv_anti₀ (by linarith [hke.1]) (by linarith [hke.2])
  set ps' : ℝ := if n ∈ S.band then 0 else S.penaltyStrain with hps'
  set pc' : ℝ := if n ∈ S.band then 0 else S.penaltyCurl with hpc'
  set pv' : ℝ := if n ∈ S.band then 0 else S.penaltyVelocity with hpv'
  have hps0 : 0 ≤ ps' := by rw [hps']; split_ifs <;> linarith [hpen.1]
  have hpv0 : 0 ≤ pv' := by rw [hpv']; split_ifs <;> linarith [hpen.2.2]
  have hpenE : (if n ∈ S.band then 0 else S.penalty s v) = ps' * sumSq s + pc' * curlSq s + pv' * vecSq v := by
    rw [hps', hpc', hpv']; by_cases hb : n ∈ S.band <;> simp [hb, CellScalars.penalty]
  have hsA : S.strainAbsorb n = W.strainBase + W.rHi * ps' + 2 * W.meanConst * W.rHi * K.r₂ / (W.kEff c.order n - 1)
      + (W.strainQuad + W.rHi * pv') * K.r₂ ^ 2 / (W.kEff c.order n - 1) ^ 2 := by
    rw [hF.strain_form, if_neg hn, hps', hpv']; unfold WeightData.strainAt
    by_cases hb : n ∈ S.band <;> simp [hb]
  have hac : max (W.rLo * (W.lamMax + pc' - (1 - 3 / (4 * α) - c.curlWeight)))
      (W.rHi * (W.lamMax + pc' - (1 - 3 / (4 * α) - c.curlWeight))) ≤ S.curlAbsorb n := by
    rw [hF.curl_form, if_neg hn, hpc']
    by_cases hb : n ∈ S.band
    · simpa [hb] using hT.curl_band_ge
    · simpa [hb] using hT.curl_out_ge
  have hE : (1 - 3 / (4 * α) - c.curlWeight) * curlSq s + (c.curlWeight - c.coercivity * W.weightMax) * sumSq s
      - (W.lamMax * curlSq s + 2 * W.meanConst * (x * y) + W.waveConst * (S.splitLength * sumSq s + vecSq v / S.splitLength))
      - (ps' * sumSq s + pc' * curlSq s + pv' * vecSq v)
      ≤ CellScalars.densityForm c α p s
        - supremumLoss (S.strainBound p) (S.meanGradBound p) (S.waveGradBound p) S.splitLength s v
        - (if n ∈ S.band then 0 else S.penalty s v) := by
    rw [hpenE]
    unfold CellScalars.densityForm supremumLoss
    have hxy0 : 0 ≤ x * y := mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    have hT0 : 0 ≤ S.splitLength * sumSq s + vecSq v / S.splitLength :=
      add_nonneg (mul_nonneg hT.splitLength_pos.le hQ0) (div_nonneg hVpos hT.splitLength_pos.le)
    have w1 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hT.weight_le p hp) hcn.2.2) hQ0
    have w2 := mul_le_mul_of_nonneg_right (hT.lam_le p hp) hC0
    have w3 := mul_le_mul_of_nonneg_right (hT.mean_le p hp) hxy0
    have w4 := mul_le_mul_of_nonneg_right (hT.wave_le p hp) hT0
    have e3 : Exterior.traceFreeConst * S.meanGradBound p * x * y
        = Exterior.traceFreeConst * S.meanGradBound p * (x * y) := by ring
    rw [← hx, ← hy, e3]
    linarith
  have key := hbase (r := CellScalars.rHat K p) (rLo := W.rLo) (rHi := W.rHi) hT.range_pos hrange.1 hrange.2 hC0 hQ0
    hxy hVb hu0 huue hr2 hcn.1 hcn.2.1 hT.splitLength_pos hps0 hpv0 hac hT.strain_base_ge hT.strain_quad_ge hE
  rw [hsA]
  linarith [key]

end Reduction

end CellCert

end Breakdown
