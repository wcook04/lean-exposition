import Breakdown.Cert.CoerciveSmoothPieceEpsSumSecondPartialsField
import Breakdown.Cert.CoerciveSmoothPairingSplitClass
import Breakdown.Cert.CoerciveFieldModes

open scoped ContDiff ENNReal
open MeasureTheory

noncomputable section

namespace Breakdown

namespace Coercive

namespace Internal.ModeSumSecondPartials

private theorem modeVel_neg_apply (ι : ℤ × ℤ) (X : ℝ → Space → Space) (σ : ℝ) (y : Space) (i : Fin 3) :
    modeVel ι (fun s x => -X s x) σ y i = -modeVel ι X σ y i := by
  have e : ∀ τ φ : ℝ, axialRot (-φ) (-X (σ + τ) (axialRot φ y)) i
      = -axialRot (-φ) (X (σ + τ) (axialRot φ y)) i := by
    intro τ φ
    have h := (SmoothBaseInternal.rotMap (-φ)).map_neg (X (σ + τ) (axialRot φ y))
    rw [SmoothBaseInternal.rotMap_apply, SmoothBaseInternal.rotMap_apply] at h
    rw [h]
    rfl
  simp only [modeVel, modeAverage, e, Complex.ofReal_neg, mul_neg, intervalIntegral.integral_neg]

private theorem re_I_cdot_eq (a : ℝ) (x l : Fin 3 → ℂ) (P Q LP LQ : Space)
    (hx : ∀ i, x i = ((P i : ℝ) : ℂ) + ((Q i : ℝ) : ℂ) * Complex.I)
    (hl : ∀ i, l i = -(((LP i : ℝ) : ℂ) + ((LQ i : ℝ) : ℂ) * Complex.I)) :
    (Complex.I * (a : ℂ) * cdot x l).re = a * (inner ℝ LP Q - inner ℝ LQ P) := by
  simp only [cdot, Fin.sum_univ_three, hx, hl, PiLp.inner_apply]
  simp [Complex.mul_re, Complex.mul_im]
  ring

private theorem cnormSq_parts (x : Fin 3 → ℂ) (P Q : Space)
    (hx : ∀ i, x i = ((P i : ℝ) : ℂ) + ((Q i : ℝ) : ℂ) * Complex.I) :
    cnormSq x = ‖P‖ ^ 2 + ‖Q‖ ^ 2 := by
  simp only [cnormSq, hx, SmoothBaseInternal.space_norm_sq, Fin.sum_univ_three, Complex.sq_norm,
    Complex.normSq_apply]
  simp
  ring

private theorem cnormSq_neg_parts (x : Fin 3 → ℂ) (P Q : Space)
    (hx : ∀ i, x i = -(((P i : ℝ) : ℂ) + ((Q i : ℝ) : ℂ) * Complex.I)) :
    cnormSq x = ‖P‖ ^ 2 + ‖Q‖ ^ 2 := by
  simp only [cnormSq, hx, SmoothBaseInternal.space_norm_sq, Fin.sum_univ_three, Complex.sq_norm,
    Complex.normSq_apply]
  simp
  ring

private theorem sum_smul_unit_apply (c : Fin 3 → ℝ) (i : Fin 3) :
    (∑ l : Fin 3, c l • unitVector l) i = c i := by
  fin_cases i <;> simp [unitVector, Fin.sum_univ_three]

private theorem flux_sum_le (D : Space →L[ℝ] ℝ) (P Q : Space) (A B : Fin 3 → Space) :
    |∑ l : Fin 3, D (unitVector l) * (inner ℝ (A l) Q - inner ℝ (B l) P)|
      ≤ ‖D‖ * (Real.sqrt (∑ l : Fin 3, (‖A l‖ ^ 2 + ‖B l‖ ^ 2)) * Real.sqrt (‖P‖ ^ 2 + ‖Q‖ ^ 2)) := by
  set c : Fin 3 → ℝ := fun l => inner ℝ (A l) Q - inner ℝ (B l) P with hc
  have hsum : ∑ l : Fin 3, D (unitVector l) * c l = D (∑ l : Fin 3, c l • unitVector l) := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [map_smul, smul_eq_mul, mul_comm]
  have hcl : ∀ l, c l ^ 2 ≤ (‖A l‖ ^ 2 + ‖B l‖ ^ 2) * (‖P‖ ^ 2 + ‖Q‖ ^ 2) := by
    intro l
    have h1 : |c l| ≤ ‖A l‖ * ‖Q‖ + ‖B l‖ * ‖P‖ :=
      (abs_sub _ _).trans (add_le_add (abs_real_inner_le_norm _ _) (abs_real_inner_le_norm _ _))
    have h2 : c l ^ 2 ≤ (‖A l‖ * ‖Q‖ + ‖B l‖ * ‖P‖) ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) h1 2
    nlinarith [sq_nonneg (‖A l‖ * ‖P‖ - ‖B l‖ * ‖Q‖)]
  have hnorm : ‖∑ l : Fin 3, c l • unitVector l‖ = Real.sqrt (∑ l : Fin 3, c l ^ 2) := by
    rw [← Real.sqrt_sq (norm_nonneg _), SmoothBaseInternal.space_norm_sq]
    simp only [sum_smul_unit_apply]
  have hle : ‖∑ l : Fin 3, c l • unitVector l‖
      ≤ Real.sqrt (∑ l : Fin 3, (‖A l‖ ^ 2 + ‖B l‖ ^ 2)) * Real.sqrt (‖P‖ ^ 2 + ‖Q‖ ^ 2) := by
    rw [hnorm, ← Real.sqrt_mul (Finset.sum_nonneg fun l _ => by positivity)]
    refine Real.sqrt_le_sqrt ?_
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum fun l _ => hcl l
  show |∑ l : Fin 3, D (unitVector l) * c l| ≤ _
  rw [hsum, ← Real.norm_eq_abs]
  exact (D.le_opNorm _).trans (mul_le_mul_of_nonneg_left hle (norm_nonneg _))

private theorem weighted_prod_le {c r s t B : ℝ} (hc : 0 ≤ c) (hr : 1 ≤ r) (hs : 0 ≤ s) (ht : 0 ≤ t)
    (hcB : r * c ≤ B) : c * (s * t) ≤ B * (s ^ 2 + t ^ 2 / r ^ 2) / 2 := by
  have hr0 : 0 < r := by linarith
  have hB : 0 ≤ B := le_trans (mul_nonneg hr0.le hc) hcB
  have h1 : c ≤ B / r := by
    rw [le_div_iff₀ hr0]
    linarith [mul_comm r c]
  have h2 : s * (t / r) ≤ (s ^ 2 + t ^ 2 / r ^ 2) / 2 := by
    have h3 := sq_nonneg (s - t / r)
    have e : (t / r) ^ 2 = t ^ 2 / r ^ 2 := div_pow t r 2
    nlinarith [h3, e]
  calc c * (s * t) ≤ (B / r) * (s * t) := mul_le_mul_of_nonneg_right h1 (mul_nonneg hs ht)
    _ = B * (s * (t / r)) := by field_simp
    _ ≤ B * ((s ^ 2 + t ^ 2 / r ^ 2) / 2) := mul_le_mul_of_nonneg_left h2 hB
    _ = B * (s ^ 2 + t ^ 2 / r ^ 2) / 2 := by ring

private theorem opNorm_sq_le (A : Space →L[ℝ] Space) : ‖A‖ ^ 2 ≤ 3 * matSq A := by
  have h := Internal.PerturbationFacts.opNorm_le_sum_apply A
  unfold matSq
  simp only [Fin.sum_univ_three] at h ⊢
  have h0 := norm_nonneg A
  have h1 : ‖A‖ ^ 2 ≤ (‖A (unitVector 0)‖ + ‖A (unitVector 1)‖ + ‖A (unitVector 2)‖) ^ 2 :=
    pow_le_pow_left₀ h0 h 2
  nlinarith [sq_nonneg (‖A (unitVector 0)‖ - ‖A (unitVector 1)‖),
    sq_nonneg (‖A (unitVector 1)‖ - ‖A (unitVector 2)‖), sq_nonneg (‖A (unitVector 0)‖ - ‖A (unitVector 2)‖)]

private theorem continuous_ssp {f : Space → Space} (hf : ContDiff ℝ 2 f) :
    Continuous (fun y => secondDerivTrace (fderiv ℝ (fun x => fderiv ℝ f x) y)) := by
  have h1 : ContDiff ℝ 1 (fun x => fderiv ℝ f x) := hf.fderiv_right (by norm_num)
  have h2 : Continuous (fun x => fderiv ℝ (fun x => fderiv ℝ f x) x) := h1.continuous_fderiv (by norm_num)
  unfold secondDerivTrace
  exact continuous_finsetSum _ fun j _ => (h2.clm_apply continuous_const).clm_apply continuous_const

private theorem inner_pair_le (A B P Q : Space) :
    |inner ℝ A Q - inner ℝ B P| ≤ ‖A‖ * ‖Q‖ + ‖B‖ * ‖P‖ :=
  (abs_sub _ _).trans (add_le_add (abs_real_inner_le_norm _ _) (abs_real_inner_le_norm _ _))

private theorem slice_bound (hSsp : WeightedSumSecondPartialsPairingHolds) {P : ℝ}
    {v : ℝ → Space → Space} (hv : IsSmoothPerturbation P v) (a : Space → ℝ) {K : NNReal}
    (ha : LipschitzWith K a) {B : ℝ} (haB : ∀ y, (1 + ‖y‖) ^ 2 * |a y| ≤ B)
    (hgB : ∀ y, (1 + ‖y‖) * ‖fderiv ℝ a y‖ ≤ B) (ι : ℤ × ℤ) (σ : ℝ)
    (hV : Integrable (fun y => cnormSq (modeVel ι (SmoothWeightSplit.scaledField v) σ y)))
    (hG : Integrable (fun y => cnormSq (modeGrad ι (gradField v) σ y)))
    (hH : Integrable (fun y => cnormSq (modeVel ι (fun s x => -secondDerivTrace (secondDerivField v s x)) σ y))) :
      Integrable (fun y => (Complex.I * (a y : ℂ) * cdot (modeVel ι v σ y)
        (modeVel ι (fun s x => -secondDerivTrace (secondDerivField v s x)) σ y)).re) ∧
      Integrable (fun y => ‖fderiv ℝ a y‖ * gradAmp (gradField v) ι σ y * velAmp v ι σ y) ∧
      |∫ y, (Complex.I * (a y : ℂ) * cdot (modeVel ι v σ y)
          (modeVel ι (fun s x => -secondDerivTrace (secondDerivField v s x)) σ y)).re|
        ≤ ∫ y, ‖fderiv ℝ a y‖ * gradAmp (gradField v) ι σ y * velAmp v ι σ y := by
  obtain ⟨hp2, hq2, hLp, hLq⟩ := SmoothPieceEpsSumSecondPartials.field_mode_sumSecondPartials hv.smooth ι σ
  have hfv : ContDiff ℝ ∞ fun p : ℝ × ℝ × Space => v (σ + p.1) p.2.2 :=
    hv.smooth.comp ((contDiff_const.add contDiff_fst).prodMk contDiff_snd.snd)
  obtain ⟨-, -, hDp0, hDq0⟩ := SmoothBaseInternal.mode_field ι (f := fun τ _ => v (σ + τ)) hfv
  set p : Space → Space := fun y => reVec (modeVel ι v σ y) with hp_def
  set q : Space → Space := fun y => imVec (modeVel ι v σ y) with hq_def
  have hDp : ∀ y, fderiv ℝ p y = reMat (modeGrad ι (gradField v) σ y) := fun y => hDp0 y
  have hDq : ∀ y, fderiv ℝ q y = imMat (modeGrad ι (gradField v) σ y) := fun y => hDq0 y
  set Lp : Space → Space := fun y => secondDerivTrace (fderiv ℝ (fun x => fderiv ℝ p x) y) with hLp_def
  set Lq : Space → Space := fun y => secondDerivTrace (fderiv ℝ (fun x => fderiv ℝ q x) y) with hLq_def
  have hB0 : 0 ≤ B := le_trans (mul_nonneg (by positivity) (abs_nonneg _)) (haB 0)
  have hXi : ∀ y i, modeVel ι v σ y i = ((p y i : ℝ) : ℂ) + ((q y i : ℝ) : ℂ) * Complex.I := by
    intro y i
    simp only [hp_def, hq_def]
    rw [SmoothBaseInternal.reVec_apply, SmoothBaseInternal.imVec_apply, Complex.re_add_im]
  have hLi : ∀ y i, modeVel ι (fun s x => -secondDerivTrace (secondDerivField v s x)) σ y i
      = -(((Lp y i : ℝ) : ℂ) + ((Lq y i : ℝ) : ℂ) * Complex.I) := by
    intro y i
    rw [modeVel_neg_apply]
    simp only [hLp_def, hLq_def]
    rw [hLp y, hLq y, SmoothBaseInternal.reVec_apply, SmoothBaseInternal.imVec_apply, Complex.re_add_im]
  have e1 : ∀ y, (Complex.I * (a y : ℂ) * cdot (modeVel ι v σ y)
      (modeVel ι (fun s x => -secondDerivTrace (secondDerivField v s x)) σ y)).re
      = a y * (inner ℝ (Lp y) (q y) - inner ℝ (Lq y) (p y)) := fun y =>
    re_I_cdot_eq _ _ _ _ _ _ _ (hXi y) (hLi y)
  have eV : ∀ y, cnormSq (modeVel ι v σ y) = ‖p y‖ ^ 2 + ‖q y‖ ^ 2 := fun y => cnormSq_parts _ _ _ (hXi y)
  have eH : ∀ y, cnormSq (modeVel ι (fun s x => -secondDerivTrace (secondDerivField v s x)) σ y)
      = ‖Lp y‖ ^ 2 + ‖Lq y‖ ^ 2 := fun y => cnormSq_neg_parts _ _ _ (hLi y)
  have eG : ∀ y, cnormSq (modeGrad ι (gradField v) σ y)
      = ∑ l : Fin 3, (‖fderiv ℝ p y (unitVector l)‖ ^ 2 + ‖fderiv ℝ q y (unitVector l)‖ ^ 2) := by
    intro y
    rw [← SmoothBaseInternal.matNorm_re_im, ← hDp y, ← hDq y, Finset.sum_add_distrib]
    rfl
  have eW : ∀ y, cnormSq (modeVel ι (SmoothWeightSplit.scaledField v) σ y)
      = (‖p y‖ ^ 2 + ‖q y‖ ^ 2) / (1 + ‖y‖) ^ 2 := by
    intro y
    have h : cnormSq (modeVel ι (SmoothWeightSplit.scaledField v) σ y)
        = ((1 + ‖y‖)⁻¹) ^ 2 * cnormSq (modeVel ι v σ y) := by
      simp only [cnormSq, SmoothWeightSplit.modeVel_scaled, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        mul_pow, sq_abs, Finset.mul_sum]
    rw [h, eV y, inv_pow, inv_mul_eq_div]
  have hW : Integrable (fun y => (‖p y‖ ^ 2 + ‖q y‖ ^ 2) / (1 + ‖y‖) ^ 2) :=
    hV.congr (Filter.Eventually.of_forall eW)
  have hpc : Continuous p := hp2.continuous
  have hqc : Continuous q := hq2.continuous
  have hpd : Continuous (fun y => fderiv ℝ p y) := hp2.continuous_fderiv (by norm_num)
  have hqd : Continuous (fun y => fderiv ℝ q y) := hq2.continuous_fderiv (by norm_num)
  have hLpc : Continuous Lp := continuous_ssp hp2
  have hLqc : Continuous Lq := continuous_ssp hq2
  have hac : Continuous a := ha.continuous
  have hDam : AEStronglyMeasurable (fun y => ‖fderiv ℝ a y‖) volume :=
    (measurable_fderiv ℝ a).norm.aestronglyMeasurable
  have hr : ∀ y : Space, (1 : ℝ) ≤ 1 + ‖y‖ := fun y => le_add_of_nonneg_right (norm_nonneg _)
  have hra : ∀ y, (1 + ‖y‖) * |a y| ≤ B := by
    intro y
    have h1 : (1 + ‖y‖) * |a y| ≤ (1 + ‖y‖) ^ 2 * |a y| := by
      refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
      nlinarith [hr y]
    exact h1.trans (haB y)
  have hmatSq : ∀ y, ‖fderiv ℝ p y‖ ^ 2 + ‖fderiv ℝ q y‖ ^ 2 ≤ 3 * cnormSq (modeGrad ι (gradField v) σ y) := by
    intro y
    rw [eG y, Finset.sum_add_distrib]
    have h1 := opNorm_sq_le (fderiv ℝ p y)
    have h2 := opNorm_sq_le (fderiv ℝ q y)
    unfold matSq at h1 h2
    linarith
  have hGn : ∀ y, 0 ≤ cnormSq (modeGrad ι (gradField v) σ y) := fun y => by
    rw [eG y]; positivity
  have int1 : Integrable (fun y => a y * (inner ℝ (secondDerivTrace (fderiv ℝ (fun x => fderiv ℝ p x) y)) (q y)
      - inner ℝ (secondDerivTrace (fderiv ℝ (fun x => fderiv ℝ q x) y)) (p y))) := by
    refine (((hH.add hW).const_mul B).div_const 2).mono'
      (hac.mul (((continuous_inner).comp (hLpc.prodMk hqc)).sub
        ((continuous_inner).comp (hLqc.prodMk hpc)))).aestronglyMeasurable
      (Filter.Eventually.of_forall fun y => ?_)
    show ‖a y * (inner ℝ (Lp y) (q y) - inner ℝ (Lq y) (p y))‖ ≤ _
    have k1 := weighted_prod_le (abs_nonneg (a y)) (hr y) (norm_nonneg (Lp y)) (norm_nonneg (q y)) (hra y)
    have k2 := weighted_prod_le (abs_nonneg (a y)) (hr y) (norm_nonneg (Lq y)) (norm_nonneg (p y)) (hra y)
    rw [Real.norm_eq_abs, abs_mul, Pi.add_apply, eH y]
    calc |a y| * |inner ℝ (Lp y) (q y) - inner ℝ (Lq y) (p y)|
        ≤ |a y| * (‖Lp y‖ * ‖q y‖ + ‖Lq y‖ * ‖p y‖) :=
          mul_le_mul_of_nonneg_left (inner_pair_le _ _ _ _) (abs_nonneg _)
      _ = |a y| * (‖Lp y‖ * ‖q y‖) + |a y| * (‖Lq y‖ * ‖p y‖) := by ring
      _ ≤ B * (‖Lp y‖ ^ 2 + ‖q y‖ ^ 2 / (1 + ‖y‖) ^ 2) / 2
          + B * (‖Lq y‖ ^ 2 + ‖p y‖ ^ 2 / (1 + ‖y‖) ^ 2) / 2 := add_le_add k1 k2
      _ = B * (‖Lp y‖ ^ 2 + ‖Lq y‖ ^ 2 + (‖p y‖ ^ 2 + ‖q y‖ ^ 2) / (1 + ‖y‖) ^ 2) / 2 := by ring
  have hXc : Continuous (fun y => ‖fderiv ℝ p y‖ * ‖q y‖ + ‖fderiv ℝ q y‖ * ‖p y‖) :=
    (hpd.norm.mul hqc.norm).add (hqd.norm.mul hpc.norm)
  have hXn : ∀ y, 0 ≤ ‖fderiv ℝ p y‖ * ‖q y‖ + ‖fderiv ℝ q y‖ * ‖p y‖ := fun y => by positivity
  have gradBound : ∀ c y, 0 ≤ c → (1 + ‖y‖) * c ≤ B →
      c * (‖fderiv ℝ p y‖ * ‖q y‖ + ‖fderiv ℝ q y‖ * ‖p y‖)
        ≤ B * (3 * cnormSq (modeGrad ι (gradField v) σ y) + (‖p y‖ ^ 2 + ‖q y‖ ^ 2) / (1 + ‖y‖) ^ 2) / 2 := by
    intro c y hc hcB
    have k1 := weighted_prod_le hc (hr y) (norm_nonneg (fderiv ℝ p y)) (norm_nonneg (q y)) hcB
    have k2 := weighted_prod_le hc (hr y) (norm_nonneg (fderiv ℝ q y)) (norm_nonneg (p y)) hcB
    have hf := hmatSq y
    calc c * (‖fderiv ℝ p y‖ * ‖q y‖ + ‖fderiv ℝ q y‖ * ‖p y‖)
        = c * (‖fderiv ℝ p y‖ * ‖q y‖) + c * (‖fderiv ℝ q y‖ * ‖p y‖) := by ring
      _ ≤ B * (‖fderiv ℝ p y‖ ^ 2 + ‖q y‖ ^ 2 / (1 + ‖y‖) ^ 2) / 2
          + B * (‖fderiv ℝ q y‖ ^ 2 + ‖p y‖ ^ 2 / (1 + ‖y‖) ^ 2) / 2 := add_le_add k1 k2
      _ = B * ((‖fderiv ℝ p y‖ ^ 2 + ‖fderiv ℝ q y‖ ^ 2) + (‖p y‖ ^ 2 + ‖q y‖ ^ 2) / (1 + ‖y‖) ^ 2) / 2 := by
          ring
      _ ≤ B * (3 * cnormSq (modeGrad ι (gradField v) σ y) + (‖p y‖ ^ 2 + ‖q y‖ ^ 2) / (1 + ‖y‖) ^ 2) / 2 := by
          gcongr
  have hGW : Integrable (fun y => B * (3 * cnormSq (modeGrad ι (gradField v) σ y)
      + (‖p y‖ ^ 2 + ‖q y‖ ^ 2) / (1 + ‖y‖) ^ 2) / 2) :=
    (((hG.const_mul 3).add hW).const_mul B).div_const 2
  have int2 : Integrable (fun y => ‖fderiv ℝ a y‖ * (‖fderiv ℝ p y‖ * ‖q y‖ + ‖fderiv ℝ q y‖ * ‖p y‖)) := by
    refine hGW.mono' (hDam.mul hXc.aestronglyMeasurable) (Filter.Eventually.of_forall fun y => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (norm_nonneg _) (hXn y))]
    exact gradBound _ y (norm_nonneg _) (hgB y)
  have int3 : Integrable (fun y => |a y| * (‖fderiv ℝ p y‖ * ‖q y‖ + ‖fderiv ℝ q y‖ * ‖p y‖) / (1 + ‖y‖)) := by
    refine hGW.mono' (((hac.abs.mul hXc).div (continuous_const.add continuous_norm)
        (fun y => by show (1 : ℝ) + ‖y‖ ≠ 0; positivity)).aestronglyMeasurable) (Filter.Eventually.of_forall fun y => ?_)
    have h0 : 0 ≤ |a y| * (‖fderiv ℝ p y‖ * ‖q y‖ + ‖fderiv ℝ q y‖ * ‖p y‖) := mul_nonneg (abs_nonneg _) (hXn y)
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg h0 (by positivity))]
    exact (div_le_self h0 (hr y)).trans (gradBound _ y (abs_nonneg _) (hra y))
  have eGA : ∀ y, gradAmp (gradField v) ι σ y
      = Real.sqrt (∑ l : Fin 3, (‖fderiv ℝ p y (unitVector l)‖ ^ 2 + ‖fderiv ℝ q y (unitVector l)‖ ^ 2)) := by
    intro y
    unfold gradAmp
    rw [eG y]
  have eVA : ∀ y, velAmp v ι σ y = Real.sqrt (‖p y‖ ^ 2 + ‖q y‖ ^ 2) := by
    intro y
    unfold velAmp
    rw [eV y]
  have hGAc : Continuous (fun y => gradAmp (gradField v) ι σ y) := by
    rw [funext eGA]
    exact Real.continuous_sqrt.comp (continuous_finsetSum _ fun l _ =>
      ((hpd.clm_apply continuous_const).norm.pow 2).add ((hqd.clm_apply continuous_const).norm.pow 2))
  have hVAc : Continuous (fun y => velAmp v ι σ y) := by
    rw [funext eVA]
    exact Real.continuous_sqrt.comp ((hpc.norm.pow 2).add (hqc.norm.pow 2))
  have intE : Integrable (fun y => ‖fderiv ℝ a y‖ * gradAmp (gradField v) ι σ y * velAmp v ι σ y) := by
    refine (((hG.add hW).const_mul B).div_const 2).mono'
      ((hDam.mul hGAc.aestronglyMeasurable).mul hVAc.aestronglyMeasurable)
      (Filter.Eventually.of_forall fun y => ?_)
    have hGA0 : 0 ≤ gradAmp (gradField v) ι σ y := Real.sqrt_nonneg _
    have hVA0 : 0 ≤ velAmp v ι σ y := Real.sqrt_nonneg _
    have k := weighted_prod_le (norm_nonneg (fderiv ℝ a y)) (hr y) hGA0 hVA0 (hgB y)
    have s1 : gradAmp (gradField v) ι σ y ^ 2 = cnormSq (modeGrad ι (gradField v) σ y) := by
      unfold gradAmp; exact Real.sq_sqrt (hGn y)
    have s2 : velAmp v ι σ y ^ 2 = ‖p y‖ ^ 2 + ‖q y‖ ^ 2 := by
      rw [eVA y]; exact Real.sq_sqrt (by positivity)
    rw [s1, s2] at k
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), mul_assoc]
    exact k
  refine ⟨int1.congr (Filter.Eventually.of_forall fun y => (e1 y).symm), intE, ?_⟩
  have hL := hSsp a K p q ha hp2 hq2 int1 int2 int3
  have eI : (∫ y, (Complex.I * (a y : ℂ) * cdot (modeVel ι v σ y)
      (modeVel ι (fun s x => -secondDerivTrace (secondDerivField v s x)) σ y)).re)
      = ∫ y, a y * (inner ℝ (secondDerivTrace (fderiv ℝ (fun x => fderiv ℝ p x) y)) (q y)
        - inner ℝ (secondDerivTrace (fderiv ℝ (fun x => fderiv ℝ q x) y)) (p y)) :=
    integral_congr_ae (Filter.Eventually.of_forall e1)
  rw [eI, hL, abs_neg, ← Real.norm_eq_abs]
  refine norm_integral_le_of_norm_le intE (Filter.Eventually.of_forall fun y => ?_)
  rw [Real.norm_eq_abs, eGA y, eVA y, mul_assoc]
  exact flux_sum_le _ _ _ _ _

theorem sumSecondPartials_mode_bound (hPars : ModeSquareSumHolds) (hSsp : WeightedSumSecondPartialsPairingHolds) {P : ℝ}
    {v : ℝ → Space → Space} (hv : IsSmoothPerturbation P v) (a : Space → ℝ) {K : NNReal}
    (ha : LipschitzWith K a) {B : ℝ} (haB : ∀ y, (1 + ‖y‖) ^ 2 * |a y| ≤ B)
    (hgB : ∀ y, (1 + ‖y‖) * ‖fderiv ℝ a y‖ ≤ B) (ι : ℤ × ℤ) :
    ∀ᵐ σ ∂(volume.restrict (Set.Icc (0 : ℝ) 1)),
      Integrable (fun y => (Complex.I * (a y : ℂ) * cdot (modeVel ι v σ y)
        (modeVel ι (fun s x => -secondDerivTrace (secondDerivField v s x)) σ y)).re) ∧
      Integrable (fun y => ‖fderiv ℝ a y‖ * gradAmp (gradField v) ι σ y * velAmp v ι σ y) ∧
      |∫ y, (Complex.I * (a y : ℂ) * cdot (modeVel ι v σ y)
          (modeVel ι (fun s x => -secondDerivTrace (secondDerivField v s x)) σ y)).re|
        ≤ ∫ y, ‖fderiv ℝ a y‖ * gradAmp (gradField v) ι σ y * velAmp v ι σ y := by
  have hVs := ModeL2Internal.integrable_cnormSq_modeVel hPars (SmoothWeightSplit.scaledField_square hv) ι
  have hN := SmoothPairingClass.negSsp_solenoidal_self hv
  have hHs := ModeL2Internal.integrable_cnormSq_modeVel hPars
    (X := fun s x => -secondDerivTrace (secondDerivField v s x)) ⟨hN.1, hN.2.1, hN.2.2.1⟩ ι
  have hgc : Continuous (fun z : ℝ × Space => gradField v z.1 z.2) := by
    have h1 : ContDiff ℝ 2 (fun z : ℝ × Space => fderiv ℝ (v z.1) z.2) :=
      ContDiff.fderiv (f := fun (z : ℝ × Space) (y : Space) => v z.1 y) (g := fun z => z.2)
        (hv.smooth.comp (contDiff_fst.fst.prodMk contDiff_snd)) contDiff_snd (BaseDensityInternal.top_add_le 2)
    exact h1.continuous
  have hg2 : periodLIntegral (fun σ y => matSq (gradField v σ y)) < ⊤ := by
    refine SmoothWeightSplit.periodLIntegral_lt_top_of_le (by norm_num : (0 : ℝ) ≤ 3) (fun σ y => ?_)
      (hv.derivatives_finite 1 le_rfl)
    rw [SmoothBaseInternal.norm_iter_one]
    exact SmoothWeightSplit.matSq_le_three_sq _
  have hGs := FieldModes.integrable_cnormSq_modeGrad hPars hgc.aestronglyMeasurable
    (FieldModes.gradField_periodic hv.periodic) hg2 ι
  filter_upwards [hVs.prod_right_ae, hGs.prod_right_ae, hHs.prod_right_ae] with σ h1 h2 h3
  exact slice_bound hSsp hv a ha haB hgB ι σ h1 h2 h3

end Internal.ModeSumSecondPartials

end Coercive

end Breakdown
