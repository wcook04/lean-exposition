import Breakdown.FracCell.SharpYChargeSt

open MeasureTheory

noncomputable section

namespace Breakdown

namespace CellCert

namespace CellAnalysis

open SteadyCert Assembly SharpParts

namespace SharpYChargeInternal

private theorem charge_point (S : CellScalars) (Cl : CellClasses) (p : ℝ × ℝ)
    (hβ : ∀ i, 0 < Cl.shareWeight i) (hℓ : 0 < S.splitLength)
    (hp : (∑ i, (1 / 2) * Exterior.traceFreeConst * Cl.gradDev i p * S.splitLength / Cl.shareWeight i) ≤ S.penaltyStrain ∧
      (∑ i, (Cl.strainDev i p / Cl.shareWeight i + 2 * Cl.rowWeight i * Cl.velocityDev i p ^ 2)) ≤ S.penaltyCurl ∧
      (∑ i, ((1 / 2) * Exterior.traceFreeConst * Cl.gradDev i p / (S.splitLength * Cl.shareWeight i)
        + 2 * Cl.rowWeight i * Cl.curlDev i p ^ 2)) ≤ S.penaltyVelocity)
    (s : Fin 3 → Fin 3 → ℂ) (v : Fin 3 → ℂ) :
    (∑ i, Cl.classLoss S.splitLength i p s v / Cl.shareWeight i)
      + ∑ i, 2 * Cl.rowWeight i * (Cl.velocityDev i p ^ 2 * curlSq s + Cl.curlDev i p ^ 2 * vecSq v)
      ≤ S.penalty s v := by
  have e : ∀ i, Cl.classLoss S.splitLength i p s v / Cl.shareWeight i
      + 2 * Cl.rowWeight i * (Cl.velocityDev i p ^ 2 * curlSq s + Cl.curlDev i p ^ 2 * vecSq v)
      = sumSq s * ((1 / 2) * Exterior.traceFreeConst * Cl.gradDev i p * S.splitLength / Cl.shareWeight i)
        + curlSq s * (Cl.strainDev i p / Cl.shareWeight i + 2 * Cl.rowWeight i * Cl.velocityDev i p ^ 2)
        + vecSq v * ((1 / 2) * Exterior.traceFreeConst * Cl.gradDev i p / (S.splitLength * Cl.shareWeight i)
          + 2 * Cl.rowWeight i * Cl.curlDev i p ^ 2) := by
    intro i
    have h1 := (hβ i).ne'
    have h2 := hℓ.ne'
    unfold CellClasses.classLoss
    field_simp
    ring
  rw [← Finset.sum_add_distrib, Finset.sum_congr rfl (fun i _ => e i), Finset.sum_add_distrib,
    Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]
  have h1 : 0 ≤ sumSq s := by unfold sumSq; positivity
  have h2 : 0 ≤ curlSq s := by unfold curlSq; positivity
  have h3 : 0 ≤ vecSq v := by unfold vecSq; positivity
  unfold CellScalars.penalty
  nlinarith [mul_le_mul_of_nonneg_left hp.1 h1, mul_le_mul_of_nonneg_left hp.2.1 h2,
    mul_le_mul_of_nonneg_left hp.2.2 h3]

private theorem rect_meas (K : CellBox) : MeasurableSet K.rect := measurableSet_Icc.prod measurableSet_Icc

end SharpYChargeInternal

open SharpYChargeInternal in
theorem penaltyCharge_of (h : ChargeRegularStatement) : PenaltyChargeStatement := by
  intro α h1 h2 k N c hc K S B Cl slots R hd hw x hx
  obtain ⟨iC, iR, iP, sC, sR, sP, eQ⟩ := h α h1 h2 c hc K S B Cl R hd hw x hx
  have pt : ∀ n, (∫ p in K.rect, p.1 * classDensity c K S x Cl n p)
      + (∫ p in K.rect, p.1 * rowChargeDensity c S x Cl n p)
      ≤ ∫ p in K.rect, p.1 * penaltyDensity c K S x n p := by
    intro n
    rw [← integral_add (iC n) (iR n)]
    refine setIntegral_mono_on ((iC n).add (iR n)) (iP n) (rect_meas K) ?_
    intro p hp
    have r0 : 0 ≤ p.1 := le_trans hd.box.r_order.1 hp.1.1
    rw [← mul_add]
    refine mul_le_mul_of_nonneg_left ?_ r0
    by_cases hn : n ∈ S.resolved ∪ S.band
    · simp [classDensity, rowChargeDensity, penaltyDensity, hn]
    · have hr : n ∉ S.resolved := fun h => hn (Finset.mem_union_left _ h)
      have gs : sharpGrad c K S x n p = fun a b => gradMode c.order n x.2.1 a b p := by
        funext a b; simp [sharpGrad, lowGrad, hr]
      have vs : sharpVel c K S x n p = modeVec c.order n x.1 p.1 p.2 := by
        funext a; simp [sharpVel, lowVel, hr]
      simp only [classDensity, rowChargeDensity, penaltyDensity, hn, if_false, gs, vs]
      exact charge_point S Cl p (fun i => (hd.class_weights_pos i).1) hd.scalars.splitLength_pos
        (hd.penalty_ge p hp) _ _
  unfold classSum penaltySum
  rw [eQ, ← sC.tsum_add sR]
  exact (sC.add sR).tsum_le_tsum pt sP


namespace SharpYChargeDensity

private theorem sesq_add (M : Matrix (Fin 12) (Fin 12) ℂ) (U V : Fin 12 → ℂ) :
    sesqValue M (U + V) = sesqValue M U
      + (∑ i, ∑ j, ((starRingEnd ℂ) (U i) * M i j * V j + (starRingEnd ℂ) (V i) * M i j * U j)).re
      + sesqValue M V := by
  have h : ∀ i j, (starRingEnd ℂ) ((U + V) i) * M i j * (U + V) j
      = (starRingEnd ℂ) (U i) * M i j * U j
        + ((starRingEnd ℂ) (U i) * M i j * V j + (starRingEnd ℂ) (V i) * M i j * U j)
        + (starRingEnd ℂ) (V i) * M i j * V j := by
    intro i j
    simp only [Pi.add_apply, map_add]
    ring
  unfold sesqValue
  simp only [h, Finset.sum_add_distrib, Complex.add_re]

private theorem lw_rhat (K : CellBox) (p : ℝ × ℝ) : K.lineWeight p.1 * CellScalars.rHat K p = p.1 := by
  unfold CellScalars.rHat
  by_cases h : K.lineWeight p.1 = 0
  · have : p.1 = 0 := by
      unfold CellBox.lineWeight at h
      split_ifs at h
      · exact h
      · exact absurd h one_ne_zero
    rw [h, this]; simp
  · field_simp

private theorem lw_nonneg (K : CellBox) (hK : IsCellBox K) (p : ℝ × ℝ) (hp : p ∈ K.rect) : 0 ≤ K.lineWeight p.1 := by
  unfold CellBox.lineWeight
  split_ifs
  · exact le_trans hK.r_order.1 hp.1.1
  · exact zero_le_one

private theorem grad_split {k N : ℕ} (c : FracCellData k N) (K : CellBox) (S : CellScalars) (x : FieldTuple k) (n : ℤ)
    (p : ℝ × ℝ) :
    pairVec (fun a b => gradMode c.order n x.2.1 a b p) (modeVec c.order n x.1 p.1 p.2)
      = pairVec (lowGrad c K S x n p) (lowVel c K S x n p) + pairVec (sharpGrad c K S x n p) (sharpVel c K S x n p) := by
  funext i
  simp only [pairVec, Pi.add_apply, sharpGrad, sharpVel]
  split_ifs <;> ring

private theorem rect_meas (K : CellBox) : MeasurableSet K.rect := measurableSet_Icc.prod measurableSet_Icc

private theorem first_ne_zero_ae (K : CellBox) : ∀ᵐ p ∂(volume.restrict K.rect), p.1 ≠ 0 := by
  have hnull : (volume : Measure (ℝ × ℝ)) {p : ℝ × ℝ | p.1 = 0} = 0 := by
    have e : {p : ℝ × ℝ | p.1 = 0} = ({0} : Set ℝ) ×ˢ (Set.univ : Set ℝ) := by
      ext p; simp
    rw [e, Measure.volume_eq_prod, Measure.prod_prod]
    simp
  exact ae_restrict_of_ae (ae_iff.mpr (by simpa using hnull))

private theorem int_comb3 {s : Set (ℝ × ℝ)} {f2 f3 f5 g : ℝ × ℝ → ℝ}
    (i2 : IntegrableOn f2 s) (i3 : IntegrableOn f3 s) (i5 : IntegrableOn f5 s) (ig : IntegrableOn g s)
    (h : ∀ᵐ p ∂(volume.restrict s), f2 p + f3 p - f5 p ≤ g p) :
    (∫ p in s, f2 p) + (∫ p in s, f3 p) - (∫ p in s, f5 p) ≤ ∫ p in s, g p := by
  have m : (∫ p in s, (f2 p + f3 p - f5 p)) ≤ ∫ p in s, g p :=
    setIntegral_mono_ae_restrict (by exact (i2.add i3).sub i5) ig h
  have e1 : (∫ p in s, (f2 p + f3 p - f5 p)) = (∫ p in s, (f2 p + f3 p)) - ∫ p in s, f5 p :=
    integral_sub (by exact i2.add i3) i5
  have e2 : (∫ p in s, (f2 p + f3 p)) = (∫ p in s, f2 p) + ∫ p in s, f3 p := integral_add i2 i3
  linarith

private theorem int_comb4 {s : Set (ℝ × ℝ)} {f1 f2 f3 f4 f5 g : ℝ × ℝ → ℝ}
    (i1 : IntegrableOn f1 s) (i2 : IntegrableOn f2 s) (i3 : IntegrableOn f3 s) (i4 : IntegrableOn f4 s)
    (i5 : IntegrableOn f5 s) (ig : IntegrableOn g s)
    (h : ∀ᵐ p ∂(volume.restrict s), f1 p + f2 p + f3 p + f4 p - f5 p ≤ g p) :
    (∫ p in s, f1 p) + (∫ p in s, f2 p) + (∫ p in s, f3 p) + (∫ p in s, f4 p) - (∫ p in s, f5 p)
      ≤ ∫ p in s, g p := by
  have m : (∫ p in s, (f1 p + f2 p + f3 p + f4 p - f5 p)) ≤ ∫ p in s, g p :=
    setIntegral_mono_ae_restrict (by exact (((i1.add i2).add i3).add i4).sub i5) ig h
  have e1 : (∫ p in s, (f1 p + f2 p + f3 p + f4 p - f5 p)) = (∫ p in s, (f1 p + f2 p + f3 p + f4 p)) - ∫ p in s, f5 p :=
    integral_sub (by exact ((i1.add i2).add i3).add i4) i5
  have e2 : (∫ p in s, (f1 p + f2 p + f3 p + f4 p)) = (∫ p in s, (f1 p + f2 p + f3 p)) + ∫ p in s, f4 p :=
    integral_add (by exact (i1.add i2).add i3) i4
  have e3 : (∫ p in s, (f1 p + f2 p + f3 p)) = (∫ p in s, (f1 p + f2 p)) + ∫ p in s, f3 p :=
    integral_add (by exact i1.add i2) i3
  have e4 : (∫ p in s, (f1 p + f2 p)) = (∫ p in s, f1 p) + ∫ p in s, f2 p := integral_add i1 i2
  linarith

end SharpYChargeDensity

open SharpYChargeDensity in
theorem sharpDensity_of (hR : DensityRegularStatement) (hF : SharpFieldStatement) : SharpDensityStatement := by
  intro α h1 h2 k N c hc K S B Cl slots R hd hw x hx
  obtain ⟨iA, iS, iP, iB, iL, iC, sA, sS, sP, sB⟩ := hR α h1 h2 c hc K S B Cl R hd hw x hx
  obtain ⟨tf, tv⟩ := hF α h1 h2 c hc K S B Cl R hd hw x hx
  classical
  set Lo : ℤ → ℝ := fun n => if n ∈ S.resolved then
    (∫ p in K.rect, p.1 * lowMatrixDensity c K S x n p) + ∫ p in K.rect, p.1 * matrixCrossDensity c K S x n p
    else 0 with hLo
  have sL : Summable Lo := summable_of_ne_finset_zero (s := S.resolved) (fun n hn => by simp [hLo, hn])
  have eL : lowMatrixSum c K S x + matrixCross c K S x = ∑' n, Lo n := by
    rw [tsum_eq_sum (s := S.resolved) (fun n hn => by simp [hLo, hn])]
    unfold lowMatrixSum matrixCross
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun n hn => by simp [hLo, hn])
  have pt : ∀ n, Lo n + (∫ p in K.rect, p.1 * supDensity c K S x n p)
      + (∫ p in K.rect, p.1 * penaltyDensity c K S x n p)
      - (∫ p in K.rect, K.lineWeight p.1 * absorbDensity c K S x n p)
      ≤ ∫ p in K.rect, p.1 * densityAt c x α n p := by
    intro n
    by_cases hn : n ∈ S.resolved
    · simp only [hLo, hn, if_true]
      refine int_comb4 (iL n hn) (iC n hn) (iS n) (iP n) (iB n) (iA n) ?_
      filter_upwards [ae_restrict_mem (rect_meas K), tf n, first_ne_zero_ae K] with p hp htf hr0
      have r0 : 0 ≤ p.1 := le_trans hd.box.r_order.1 hp.1.1
      have hpen : penaltyDensity c K S x n p = 0 := by simp [penaltyDensity, hn]
      have hM := hd.scalars.localMatrix_le n hn p hp (fun a b => gradMode c.order n x.2.1 a b p)
        (modeVec c.order n x.1 p.1 p.2)
      rw [grad_split c K S x n p, sesq_add] at hM
      have hP := hd.scalars.resolved_pointwise n hn p hp hr0 (sharpGrad c K S x n p) (sharpVel c K S x n p) htf
      have hq := mul_nonneg (lw_nonneg K hd.box p hp) hP
      rw [mul_add, mul_add, mul_add, ← mul_assoc, lw_rhat] at hq
      have hM' := mul_le_mul_of_nonneg_left hM r0
      simp only [lowMatrixDensity, matrixCrossDensity, supDensity, absorbDensity, densityAt, hpen, hn, if_true,
        CellScalars.pairLoss] at hq hM' ⊢
      nlinarith [hq, hM']
    · simp only [hLo, hn, if_false]
      rw [zero_add]
      refine int_comb3 (iS n) (iP n) (iB n) (iA n) ?_
      filter_upwards [ae_restrict_mem (rect_meas K), tf n, tv n hn, first_ne_zero_ae K] with p hp htf htv hr0
      have gs : sharpGrad c K S x n p = fun a b => gradMode c.order n x.2.1 a b p := by
        funext a b; simp [sharpGrad, lowGrad, hn]
      have vs : sharpVel c K S x n p = modeVec c.order n x.1 p.1 p.2 := by
        funext a; simp [sharpVel, lowVel, hn]
      have hP := hd.scalars.unresolved_pointwise n hn p hp hr0 (fun a b => gradMode c.order n x.2.1 a b p)
        (modeVec c.order n x.1 p.1 p.2) (by rw [← gs]; exact htf) htv
      have hq := mul_nonneg (lw_nonneg K hd.box p hp) hP
      rw [mul_add, mul_add, ← mul_assoc, lw_rhat] at hq
      by_cases hb : n ∈ S.band
      · have hpen : penaltyDensity c K S x n p = 0 := by simp [penaltyDensity, hb]
        simp only [supDensity, absorbDensity, densityAt, hpen, hn, hb, if_true, if_false, gs, vs] at hq ⊢
        nlinarith [hq]
      · have hnb : n ∉ S.resolved ∪ S.band := by simp [hn, hb]
        have hpen : penaltyDensity c K S x n p = S.penalty (fun a b => gradMode c.order n x.2.1 a b p)
            (modeVec c.order n x.1 p.1 p.2) := by simp only [penaltyDensity, hnb, if_false, gs, vs]
        simp only [supDensity, absorbDensity, densityAt, hpen, hn, hb, if_false, gs, vs] at hq ⊢
        nlinarith [hq]
  have key := (((sL.add sS).add sP).sub sB).tsum_le_tsum pt sA
  rw [Summable.tsum_sub ((sL.add sS).add sP) sB, Summable.tsum_add (sL.add sS) sP, Summable.tsum_add sL sS] at key
  unfold supSum penaltySum absorbSum densitySum
  rw [eL]
  linarith

theorem sharpYCharge_of (hX : ModeExpansionStatement) (hD : SharpDensityStatement) (hS : SharpSupremumStatement)
    (hC : SharpCrossStatement) (hK : ClassCrossStatement) (hP : PenaltyChargeStatement)
    (hE : SharpEnergyTailStatement) : SharpYChargeStatement := by
  intro α h1 h2 k N c hc K S B Cl slots R hd hw x hx ζ
  have e1 := hX α h1 h2 c hc K S B Cl R hd hw x hx ζ
  have e2 := hD α h1 h2 c hc K S B Cl R hd hw x hx
  have e3 := hS α h1 h2 c hc K S B Cl R hd hw x hx
  have e4 := hC α h1 h2 c hc K S B Cl R hd hw x hx ζ
  have e5 := hK α h1 h2 c hc K S B Cl R hd hw x hx
  have e6 := hP α h1 h2 c hc K S B Cl R hd hw x hx
  have e7 := hE α h1 h2 c hc K S B Cl R hd hw x hx
  unfold CellScalars.localCellForm
  linarith

theorem sharpYCharge_of_regular (hX : ModeExpansionStatement) (hD : SharpDensityStatement)
    (hS : SharpSupremumStatement) (hC : SharpCrossStatement) (hK : ClassCrossStatement) (hR : ChargeRegularStatement)
    (hE : SharpEnergyTailStatement) : SharpYChargeStatement :=
  sharpYCharge_of hX hD hS hC hK (penaltyCharge_of hR) hE

theorem sharpYCharge_of_leaves (hX : ModeExpansionStatement) (hDR : DensityRegularStatement)
    (hF : SharpFieldStatement) (hS : SharpSupremumStatement) (hC : SharpCrossStatement) (hK : ClassCrossStatement)
    (hR : ChargeRegularStatement) (hE : SharpEnergyTailStatement) : SharpYChargeStatement :=
  sharpYCharge_of hX (sharpDensity_of hDR hF) hS hC hK (penaltyCharge_of hR) hE

end CellAnalysis

end CellCert

end Breakdown
