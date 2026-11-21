import Breakdown.FracCell.OffAxisCoreSt
import Breakdown.FracCell.OffAxisCoreNorm
import Breakdown.FracCell.FieldWitnessRect

open MeasureTheory Polynomial

noncomputable section

namespace Breakdown

namespace CellCert

namespace Spectral

open SteadyCert

namespace Internal.OffAxisCore

theorem shape_sub (g : CellBlock) (a b : Fin 2 → Fin 3 → Fin 2 → ℝ → ℝ → ℝ) (y : Space) :
    shapeField g a y - shapeField g b y = shapeField g (fun s c t r z => a s c t r z - b s c t r z) y := by
  classical
  unfold shapeField
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Set.indicator_apply, Set.indicator_apply, Set.indicator_apply]
  split_ifs
  · simp only [← Finset.sum_sub_distrib, ← sub_smul, ← mul_sub]
  · simp

theorem cont_slice {F : ℝ → ℝ → ℝ} (hF : Continuous fun p : ℝ × ℝ => F p.1 p.2) (r : ℝ) :
    Continuous fun z => F r z :=
  hF.comp (continuous_const.prodMk continuous_id)

theorem cont_inner {F : ℝ → ℝ → ℝ} (hF : Continuous fun p : ℝ × ℝ => F p.1 p.2) (c d : ℝ) :
    Continuous fun r => ∫ z in c..d, F r z :=
  intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' (f := F) hF c d

theorem rect_mono {F G : ℝ → ℝ → ℝ} (hF : Continuous fun p : ℝ × ℝ => F p.1 p.2)
    (hG : Continuous fun p : ℝ × ℝ => G p.1 p.2) {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d)
    (h : ∀ r ∈ Set.Icc a b, ∀ z ∈ Set.Icc c d, F r z ≤ G r z) :
    (∫ r in a..b, ∫ z in c..d, F r z) ≤ ∫ r in a..b, ∫ z in c..d, G r z := by
  refine intervalIntegral.integral_mono_on hab ((cont_inner hF c d).intervalIntegrable _ _)
    ((cont_inner hG c d).intervalIntegrable _ _) fun r hr => ?_
  exact intervalIntegral.integral_mono_on hcd ((cont_slice hF r).intervalIntegrable _ _)
    ((cont_slice hG r).intervalIntegrable _ _) fun z hz => h r hr z hz

theorem rect_add {F G : ℝ → ℝ → ℝ} (hF : Continuous fun p : ℝ × ℝ => F p.1 p.2)
    (hG : Continuous fun p : ℝ × ℝ => G p.1 p.2) (a b c d : ℝ) :
    (∫ r in a..b, ∫ z in c..d, (F r z + G r z))
      = (∫ r in a..b, ∫ z in c..d, F r z) + ∫ r in a..b, ∫ z in c..d, G r z := by
  have e : ∀ r, (∫ z in c..d, (F r z + G r z)) = (∫ z in c..d, F r z) + ∫ z in c..d, G r z := fun r =>
    intervalIntegral.integral_add ((cont_slice hF r).intervalIntegrable _ _)
      ((cont_slice hG r).intervalIntegrable _ _)
  simp only [e]
  exact intervalIntegral.integral_add ((cont_inner hF c d).intervalIntegrable _ _)
    ((cont_inner hG c d).intervalIntegrable _ _)

theorem rect_mul (k : ℝ) (F : ℝ → ℝ → ℝ) (a b c d : ℝ) :
    (∫ r in a..b, ∫ z in c..d, k * F r z) = k * ∫ r in a..b, ∫ z in c..d, F r z := by
  simp only [intervalIntegral.integral_const_mul]

theorem partial_r {Q : ℝ → ℝ → ℝ} (hQ : ContDiff ℝ 1 (Function.uncurry Q)) :
    Continuous fun p : ℝ × ℝ => deriv (fun x => Q x p.2) p.1 := by
  have hd : ∀ p : ℝ × ℝ, deriv (fun x => Q x p.2) p.1 = fderiv ℝ (Function.uncurry Q) p (1, 0) := by
    intro p
    have h1 : HasFDerivAt (Function.uncurry Q) (fderiv ℝ (Function.uncurry Q) p) (p.1, p.2) :=
      (hQ.differentiable one_ne_zero p).hasFDerivAt
    have h2 : HasDerivAt (fun x : ℝ => ((x, p.2) : ℝ × ℝ)) ((1, 0) : ℝ × ℝ) p.1 :=
      (hasDerivAt_id p.1).prodMk (hasDerivAt_const p.1 p.2)
    exact (h1.comp_hasDerivAt p.1 h2).deriv
  simp only [hd]
  exact (hQ.continuous_fderiv one_ne_zero).clm_apply continuous_const

theorem partial_z {Q : ℝ → ℝ → ℝ} (hQ : ContDiff ℝ 1 (Function.uncurry Q)) :
    Continuous fun p : ℝ × ℝ => deriv (fun x => Q p.1 x) p.2 := by
  have hd : ∀ p : ℝ × ℝ, deriv (fun x => Q p.1 x) p.2 = fderiv ℝ (Function.uncurry Q) p (0, 1) := by
    intro p
    have h1 : HasFDerivAt (Function.uncurry Q) (fderiv ℝ (Function.uncurry Q) p) (p.1, p.2) :=
      (hQ.differentiable one_ne_zero p).hasFDerivAt
    have h2 : HasDerivAt (fun x : ℝ => ((p.1, x) : ℝ × ℝ)) ((0, 1) : ℝ × ℝ) p.2 :=
      (hasDerivAt_const p.2 p.1).prodMk (hasDerivAt_id p.2)
    exact (h1.comp_hasDerivAt p.2 h2).deriv
  simp only [hd]
  exact (hQ.continuous_fderiv one_ne_zero).clm_apply continuous_const

theorem rect_step {P Q : ℝ → ℝ → ℝ} (hP : Continuous fun p : ℝ × ℝ => P p.1 p.2)
    (hQ : ContDiff ℝ 1 (Function.uncurry Q))
    {r0 r1 z0 z1 lam a B w : ℝ} (hr0 : 0 < r0) (hr : r0 < r1) (hz : z0 < z1) (hlam : 0 < lam)
    (ha : 0 ≤ a) (hB : 0 ≤ B) (hw : 0 ≤ w)
    (hI : (∫ r in r0..r1, ∫ z in z0..z1, ((P r z - Q r z) ^ 2
            + lam⁻¹ * (deriv (fun s => Q s z) r ^ 2 + deriv (fun t => Q r t) z ^ 2 + a * Q r z ^ 2)))
          ≤ B * ∫ r in r0..r1, ∫ z in z0..z1, P r z ^ 2) :
    w * (∫ r in r0..r1, ∫ z in z0..z1, (P r z - Q r z) ^ 2 * r)
      + 1 / lam * (w * ∫ r in r0..r1, ∫ z in z0..z1,
          (deriv (fun x => Q x z) r ^ 2 + deriv (fun x => Q r x) z ^ 2 + a * Q r z ^ 2) * r)
      ≤ r1 / r0 * B * (w * ∫ r in r0..r1, ∫ z in z0..z1, P r z ^ 2 * r) := by
  have cQ : Continuous fun p : ℝ × ℝ => Q p.1 p.2 := hQ.continuous
  have cX : Continuous fun p : ℝ × ℝ => (P p.1 p.2 - Q p.1 p.2) ^ 2 := (hP.sub cQ).pow 2
  have cY : Continuous fun p : ℝ × ℝ =>
      deriv (fun x => Q x p.2) p.1 ^ 2 + deriv (fun x => Q p.1 x) p.2 ^ 2 + a * Q p.1 p.2 ^ 2 :=
    (((partial_r hQ).pow 2).add ((partial_z hQ).pow 2)).add (continuous_const.mul (cQ.pow 2))
  have cXr : Continuous fun p : ℝ × ℝ => (P p.1 p.2 - Q p.1 p.2) ^ 2 * p.1 := cX.mul continuous_fst
  have cYr : Continuous fun p : ℝ × ℝ => lam⁻¹ * ((deriv (fun x => Q x p.2) p.1 ^ 2
      + deriv (fun x => Q p.1 x) p.2 ^ 2 + a * Q p.1 p.2 ^ 2) * p.1) :=
    continuous_const.mul (cY.mul continuous_fst)
  have cZ : Continuous fun p : ℝ × ℝ => (P p.1 p.2 - Q p.1 p.2) ^ 2 + lam⁻¹ * (deriv (fun x => Q x p.2) p.1 ^ 2
      + deriv (fun x => Q p.1 x) p.2 ^ 2 + a * Q p.1 p.2 ^ 2) :=
    cX.add (continuous_const.mul cY)
  have cP2 : Continuous fun p : ℝ × ℝ => P p.1 p.2 ^ 2 := hP.pow 2
  have cP2r : Continuous fun p : ℝ × ℝ => r0⁻¹ * (P p.1 p.2 ^ 2 * p.1) :=
    continuous_const.mul ((hP.pow 2).mul continuous_fst)
  have hZnn : ∀ r z, 0 ≤ (P r z - Q r z) ^ 2 + lam⁻¹ * (deriv (fun x => Q x z) r ^ 2
      + deriv (fun x => Q r x) z ^ 2 + a * Q r z ^ 2) := fun r z =>
    add_nonneg (sq_nonneg _) (mul_nonneg (inv_nonneg.2 hlam.le)
      (add_nonneg (add_nonneg (sq_nonneg _) (sq_nonneg _)) (mul_nonneg ha (sq_nonneg _))))
  have s1 : (∫ r in r0..r1, ∫ z in z0..z1, (P r z - Q r z) ^ 2 * r)
      + 1 / lam * (∫ r in r0..r1, ∫ z in z0..z1,
          (deriv (fun x => Q x z) r ^ 2 + deriv (fun x => Q r x) z ^ 2 + a * Q r z ^ 2) * r)
      = ∫ r in r0..r1, ∫ z in z0..z1, r * ((P r z - Q r z) ^ 2 + lam⁻¹ * (deriv (fun x => Q x z) r ^ 2
          + deriv (fun x => Q r x) z ^ 2 + a * Q r z ^ 2)) := by
    rw [one_div, ← rect_mul lam⁻¹, ← rect_add cXr cYr]
    congr 1
    funext r
    congr 1
    funext z
    ring
  have s2 : (∫ r in r0..r1, ∫ z in z0..z1, r * ((P r z - Q r z) ^ 2 + lam⁻¹ * (deriv (fun x => Q x z) r ^ 2
          + deriv (fun x => Q r x) z ^ 2 + a * Q r z ^ 2)))
      ≤ ∫ r in r0..r1, ∫ z in z0..z1, r1 * ((P r z - Q r z) ^ 2 + lam⁻¹ * (deriv (fun x => Q x z) r ^ 2
          + deriv (fun x => Q r x) z ^ 2 + a * Q r z ^ 2)) := by
    refine rect_mono ?_ ?_ hr.le hz.le fun r hr' z _ => mul_le_mul_of_nonneg_right hr'.2 (hZnn r z)
    · exact continuous_fst.mul cZ
    · exact continuous_const.mul cZ
  have s3 : (∫ r in r0..r1, ∫ z in z0..z1, P r z ^ 2)
      ≤ ∫ r in r0..r1, ∫ z in z0..z1, r0⁻¹ * (P r z ^ 2 * r) := by
    refine rect_mono cP2 cP2r hr.le hz.le fun r hr' z _ => ?_
    have h1 : 1 ≤ r0⁻¹ * r := by
      rw [inv_mul_eq_div, le_div_iff₀ hr0]
      linarith [hr'.1]
    nlinarith [sq_nonneg (P r z)]
  rw [rect_mul r1] at s2
  rw [rect_mul r0⁻¹] at s3
  have hr1 : 0 ≤ r1 := by linarith
  calc w * (∫ r in r0..r1, ∫ z in z0..z1, (P r z - Q r z) ^ 2 * r)
        + 1 / lam * (w * ∫ r in r0..r1, ∫ z in z0..z1,
          (deriv (fun x => Q x z) r ^ 2 + deriv (fun x => Q r x) z ^ 2 + a * Q r z ^ 2) * r)
        = w * ((∫ r in r0..r1, ∫ z in z0..z1, (P r z - Q r z) ^ 2 * r)
        + 1 / lam * (∫ r in r0..r1, ∫ z in z0..z1,
          (deriv (fun x => Q x z) r ^ 2 + deriv (fun x => Q r x) z ^ 2 + a * Q r z ^ 2) * r)) := by ring
    _ ≤ w * (r1 * (B * ∫ r in r0..r1, ∫ z in z0..z1, P r z ^ 2)) := by
        rw [s1]
        refine mul_le_mul_of_nonneg_left (s2.trans (mul_le_mul_of_nonneg_left hI hr1)) hw
    _ ≤ w * (r1 * (B * (r0⁻¹ * ∫ r in r0..r1, ∫ z in z0..z1, P r z ^ 2 * r))) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left s3 hB) hr1) hw
    _ = r1 / r0 * B * (w * ∫ r in r0..r1, ∫ z in z0..z1, P r z ^ 2 * r) := by
        rw [div_eq_mul_inv]
        ring

theorem smoothing_congr {g : CellBlock} {lam bound : ℝ} {φ φ₀ : Space → Space}
    (h : BlockSmoothing g lam bound φ₀) (he : φ =ᵐ[volume] φ₀) : BlockSmoothing g lam bound φ := by
  obtain ⟨ψ, Dψ, k1, k2, k3, k4, k5, ⟨f, hf, hF⟩, k7⟩ := h
  have hz : (0 : Space → Space) =ᵐ[volume] fun y => φ y - φ₀ y := he.mono fun y hy => by simp [hy]
  refine ⟨fun y => ψ y + (φ y - φ₀ y), Dψ, k1.add (MemLp.zero.ae_eq hz), k2, k3, fun T hT j => ?_, k5,
    ⟨f, hf, fun y => ?_⟩, ?_⟩
  · rw [← k4 T hT j]
    refine integral_congr_ae (he.mono fun y hy => ?_)
    simp [hy]
  · refine Eq.trans ?_ (hF y)
    show φ y - (ψ y + (φ y - φ₀ y)) = φ₀ y - ψ y
    abel
  · have e1 : (fun y => ‖φ y - (ψ y + (φ y - φ₀ y))‖ ^ 2) = fun y => ‖φ₀ y - ψ y‖ ^ 2 := by
      funext y
      congr 2
      abel
    have e2 : ∫ y, ‖φ y‖ ^ 2 = ∫ y, ‖φ₀ y‖ ^ 2 := integral_congr_ae (he.mono fun y hy => by simp [hy])
    rw [e1, e2]
    exact k7

theorem smoothing_of_everywhere {g : CellBlock} {lam bound : ℝ}
    (H : ∀ φ : Space → Space, (∃ A : Fin 2 → Fin 3 → Fin 2 → ℝ[X][X],
      (∀ s c t, (A s c t).natDegree ≤ g.degree ∧ ∀ j, ((A s c t).coeff j).natDegree ≤ g.degree) ∧
      (g.onAxis = true → ∀ s t, X ∣ A s 0 t ∧ X ∣ A s 1 t) ∧
      ∀ y, φ y = ∑ s : Fin 2, Set.indicator (cellSolid g s)
        (fun w => ∑ c : Fin 3, (∑ t : Fin 2, trigMode t (g.mode * angleCoord w)
          * twoVarEval (A s c t) (radialCoord w) (w 2)) • frameVector c w) y) →
      MemLp φ 2 volume → BlockSmoothing g lam bound φ)
    (φ : Space → Space) (hφ : IsBlockField g φ) (hL : MemLp φ 2 volume) : BlockSmoothing g lam bound φ := by
  obtain ⟨A, h1, h2, h3⟩ := hφ
  exact smoothing_congr (H _ ⟨A, h1, h2, fun y => rfl⟩ (hL.ae_eq h3)) h3

end Internal.OffAxisCore

open Internal.OffAxisCore

theorem offAxisCore_of_rect (h : RectOffStatement) (hN : ShapeNormStatement) (hG : ShapeGradStatement) :
    OffAxisCoreStatement := by
  intro g lam vr vz hlam _ hRin hR hZ hZ0 hcr hcz
  refine smoothing_of_everywhere fun φ hφ _ => ?_
  obtain ⟨A, hAdeg, -, hA⟩ := hφ
  have ha : 0 ≤ (g.mode + 1 : ℝ) ^ 2 / g.innerRadius ^ 2 := by positivity
  have hlo : ∀ s : Fin 2, solidLower g s < solidUpper g s := by
    intro s
    fin_cases s <;> simp [solidLower, solidUpper] <;> linarith
  have hlen : ∀ s : Fin 2, solidUpper g s - solidLower g s = g.upperHeight - g.lowerHeight := by
    intro s
    fin_cases s
    · simp [solidLower, solidUpper]
    · simp only [solidLower, solidUpper]
      simp
      ring
  have hcz' : ∀ s : Fin 2,
      IntervalCertificate g.degree (lam * (solidUpper g s - solidLower g s) ^ 2 / 4) vz := by
    intro s
    rw [hlen]
    exact hcz
  have hrect := fun s c t => h g.degree g.innerRadius g.outerRadius (solidLower g s) (solidUpper g s) lam vr vz
    ((g.mode + 1 : ℝ) ^ 2 / g.innerRadius ^ 2) hlam hR (hlo s) ha hcr (hcz' s) (A s c t)
    (hAdeg s c t).1 (hAdeg s c t).2
  choose Q hQc hQ0 hQ1 hQ2 hQ3 hQI using hrect
  have hB : 0 ≤ vr + vz + ratioFn lam ((g.mode + 1 : ℝ) ^ 2 / g.innerRadius ^ 2) := by
    have hone : ∀ j, ((1 : ℝ[X][X]).coeff j).natDegree ≤ g.degree := by
      intro j
      rw [Polynomial.coeff_one]
      split_ifs <;> simp
    obtain ⟨Q1, -, -, -, -, -, hI1⟩ := h g.degree g.innerRadius g.outerRadius (solidLower g 0) (solidUpper g 0)
      lam vr vz ((g.mode + 1 : ℝ) ^ 2 / g.innerRadius ^ 2) hlam hR (hlo 0) ha hcr (hcz' 0) 1
      (by simp) hone
    have htv : ∀ r z, twoVarEval 1 r z = 1 := fun r z => by simp [twoVarEval]
    simp only [htv, one_pow, intervalIntegral.integral_const, smul_eq_mul, mul_one] at hI1
    have hnn : 0 ≤ ∫ r in g.innerRadius..g.outerRadius, ∫ z in solidLower g 0..solidUpper g 0,
        ((1 - Q1 r z) ^ 2 + lam⁻¹ * (deriv (fun s => Q1 s z) r ^ 2 + deriv (fun t => Q1 r t) z ^ 2
          + (g.mode + 1 : ℝ) ^ 2 / g.innerRadius ^ 2 * Q1 r z ^ 2)) :=
      intervalIntegral.integral_nonneg hR.le fun r _ => intervalIntegral.integral_nonneg (hlo 0).le
        fun z _ => add_nonneg (sq_nonneg _) (mul_nonneg (inv_nonneg.2 hlam.le)
          (add_nonneg (add_nonneg (sq_nonneg _) (sq_nonneg _)) (mul_nonneg ha (sq_nonneg _))))
    have hpos : 0 < (g.outerRadius - g.innerRadius) * (solidUpper g 0 - solidLower g 0) :=
      mul_pos (by linarith) (by linarith [hlo 0])
    by_contra hneg
    nlinarith [mul_neg_of_neg_of_pos (not_le.1 hneg) hpos]
  have cP : ∀ s c t, Continuous fun p : ℝ × ℝ => twoVarEval (A s c t) p.1 p.2 := fun s c t =>
    Internal.SpectralBlocksField.twoVar_continuous (A s c t)
  have hφeq : ∀ y, φ y = shapeField g (fun s c t r z => twoVarEval (A s c t) r z) y := fun y => by
    rw [hA y]
    rfl
  have hdiff : ∀ y, φ y - shapeField g Q y
      = shapeField g (fun s c t r z => twoVarEval (A s c t) r z - Q s c t r z) y := fun y => by
    rw [hφeq y, shape_sub]
  obtain ⟨hψ2, -⟩ := hN g Q hRin hR hZ hZ0 fun s c t => (hQc s c t).continuous
  obtain ⟨-, hEP⟩ := hN g (fun s c t r z => twoVarEval (A s c t) r z) hRin hR hZ hZ0 fun s c t => cP s c t
  obtain ⟨-, hED⟩ := hN g (fun s c t r z => twoVarEval (A s c t) r z - Q s c t r z) hRin hR hZ hZ0
    fun s c t => (cP s c t).sub (hQc s c t).continuous
  obtain ⟨D, hDm, hDi, hDw, hDmode, hDE⟩ := hG g Q hRin hR hZ hZ0 hQc hQ0 hQ1 hQ2 hQ3
  refine ⟨shapeField g Q, D, hψ2, hDm, hDi, hDw, hDmode,
    ⟨fun s c t r z => twoVarEval (A s c t) r z - Q s c t r z,
      fun s c t => ((cP s c t).sub (hQc s c t).continuous).measurable, fun y => ?_⟩, ?_⟩
  · show φ y - shapeField g Q y = _
    rw [hdiff y]
    rfl
  have e1 : (∫ y, ‖φ y - shapeField g Q y‖ ^ 2)
      = ∫ y, ‖shapeField g (fun s c t r z => twoVarEval (A s c t) r z - Q s c t r z) y‖ ^ 2 := by
    simp only [hdiff]
  have e2 : (∫ y, ‖φ y‖ ^ 2) = ∫ y, ‖shapeField g (fun s c t r z => twoVarEval (A s c t) r z) y‖ ^ 2 := by
    simp only [← hφeq]
  rw [e1, e2, hED, hEP]
  have hw : ∀ t, 0 ≤ trigWeight g.mode t := fun t =>
    intervalIntegral.integral_nonneg (by linarith [Real.pi_pos]) fun θ _ => sq_nonneg _
  have key : ∀ s c t, trigWeight g.mode t * (∫ r in g.innerRadius..g.outerRadius,
        ∫ z in solidLower g s..solidUpper g s, (twoVarEval (A s c t) r z - Q s c t r z) ^ 2 * r)
      + 1 / lam * (trigWeight g.mode t * ∫ r in g.innerRadius..g.outerRadius,
        ∫ z in solidLower g s..solidUpper g s,
          (deriv (fun x => Q s c t x z) r ^ 2 + deriv (fun w => Q s c t r w) z ^ 2
            + (g.mode + 1 : ℝ) ^ 2 / g.innerRadius ^ 2 * Q s c t r z ^ 2) * r)
      ≤ g.outerRadius / g.innerRadius * (vr + vz + ratioFn lam ((g.mode + 1 : ℝ) ^ 2 / g.innerRadius ^ 2))
        * (trigWeight g.mode t * ∫ r in g.innerRadius..g.outerRadius,
          ∫ z in solidLower g s..solidUpper g s, twoVarEval (A s c t) r z ^ 2 * r) := fun s c t =>
    rect_step (P := fun r z => twoVarEval (A s c t) r z) (cP s c t) (hQc s c t) hRin hR (hlo s) hlam ha hB
      (hw t) (hQI s c t)
  calc (∑ s : Fin 2, ∑ c : Fin 3, ∑ t : Fin 2, trigWeight g.mode t * ∫ r in g.innerRadius..g.outerRadius,
          ∫ z in solidLower g s..solidUpper g s, (twoVarEval (A s c t) r z - Q s c t r z) ^ 2 * r)
        + 1 / lam * ∫ y, entrySq (D y)
      ≤ (∑ s : Fin 2, ∑ c : Fin 3, ∑ t : Fin 2, trigWeight g.mode t * ∫ r in g.innerRadius..g.outerRadius,
          ∫ z in solidLower g s..solidUpper g s, (twoVarEval (A s c t) r z - Q s c t r z) ^ 2 * r)
        + 1 / lam * ∑ s : Fin 2, ∑ c : Fin 3, ∑ t : Fin 2, trigWeight g.mode t *
          ∫ r in g.innerRadius..g.outerRadius, ∫ z in solidLower g s..solidUpper g s,
            (deriv (fun x => Q s c t x z) r ^ 2 + deriv (fun w => Q s c t r w) z ^ 2
              + (g.mode + 1 : ℝ) ^ 2 / g.innerRadius ^ 2 * Q s c t r z ^ 2) * r :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left hDE (one_div_nonneg.2 hlam.le))
    _ ≤ _ := by
        simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
        exact Finset.sum_le_sum fun s _ => Finset.sum_le_sum fun c _ => Finset.sum_le_sum fun t _ => key s c t

theorem offAxisCore_of_grad (h : RectOffStatement) (hG : ShapeGradStatement) : OffAxisCoreStatement :=
  offAxisCore_of_rect h shapeNorm_holds hG

end Spectral

end CellCert

end Breakdown
