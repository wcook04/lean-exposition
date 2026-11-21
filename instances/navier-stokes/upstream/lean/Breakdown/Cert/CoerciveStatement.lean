import Breakdown.Cert.Statement

open scoped ContDiff ENNReal
open MeasureTheory

noncomputable section

namespace Breakdown

def CoerciveClause {k : ℕ} (d : CertificateData k) : Prop :=
  ∀ p ∈ d.box, ∀ v G H g, IsPerturbation d.symmetries (d.period p) v G H g →
    ∀ (κ : Fin k → ℝ) (F : ℝ → Space → Space),
      AEStronglyMeasurable (fun z : ℝ × Space => F z.1 z.2) volume → IsTimePeriodic F →
      periodLIntegral (fun σ y => ‖F σ y‖ ^ 2) < ⊤ →
      IsRightSide (d.profile p) d.actuator κ v G g F →
      Real.sqrt (weightedEnergy d.weightFn G H + ∑ i, κ i ^ 2) ≤
        d.coerciveL2 * periodNorm F + d.coerciveBall * periodBallNorm d.ballRadius F
          + d.coercivePin * vecNorm (fun i => pinValue (d.pin i) G)

theorem coerciveClause_of_isCertificate {k : ℕ} {d : CertificateData k} (h : IsCertificate d) :
    CoerciveClause d :=
  h.coercive

def periodPairing (F M : ℝ → Space → Space) : ℝ :=
  ∫ σ in Set.Icc (0 : ℝ) 1, ∫ y, inner ℝ (F σ y) (M σ y)

structure MultiplierInequality {k : ℕ} (d : CertificateData k) (c cμ t a K : ℝ) : Prop where
  c_pos : 0 < c
  cμ_nonneg : 0 ≤ cμ
  t_nonneg : 0 ≤ t
  a_nonneg : 0 ≤ a
  K_nonneg : 0 ≤ K
  bound : ∀ p ∈ d.box, ∀ v G H g, IsPerturbation d.symmetries (d.period p) v G H g →
    ∀ (κ : Fin k → ℝ) (F : ℝ → Space → Space),
      AEStronglyMeasurable (fun z : ℝ × Space => F z.1 z.2) volume → IsTimePeriodic F →
      periodLIntegral (fun σ y => ‖F σ y‖ ^ 2) < ⊤ →
      IsRightSide (d.profile p) d.actuator κ v G g F →
      ∃ (M : ℝ → Space → Space) (n : ℝ),
        AEStronglyMeasurable (fun z : ℝ × Space => M z.1 z.2) volume ∧
        periodLIntegral (fun σ y => ‖M σ y‖ ^ 2) < ⊤ ∧ 0 ≤ n ∧
        periodNorm M ≤ a * Real.sqrt (c * weightedEnergy d.weightFn G H + cμ * n ^ 2) ∧
        c * (weightedEnergy d.weightFn G H + ∑ i, κ i ^ 2) + cμ * n ^ 2 ≤
          periodPairing F M + c * K ^ 2 * periodBallNorm d.ballRadius F ^ 2
            + t * vecNorm (fun i => pinValue (d.pin i) G) ^ 2

theorem periodPairing_abs_le {F M : ℝ → Space → Space}
    (hF : AEStronglyMeasurable (fun z : ℝ × Space => F z.1 z.2) volume)
    (hM : AEStronglyMeasurable (fun z : ℝ × Space => M z.1 z.2) volume)
    (hF2 : periodLIntegral (fun σ y => ‖F σ y‖ ^ 2) < ⊤)
    (hM2 : periodLIntegral (fun σ y => ‖M σ y‖ ^ 2) < ⊤) :
    |periodPairing F M| ≤ periodNorm F * periodNorm M := by
  set μ : Measure (ℝ × Space) := (volume.restrict (Set.Icc (0 : ℝ) 1)).prod volume with hμ
  have hμ' : μ = (volume : Measure (ℝ × Space)).restrict (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ) := by
    rw [hμ, Measure.volume_eq_prod, ← Measure.prod_restrict, Measure.restrict_univ]
  set f : ℝ × Space → Space := fun z => F z.1 z.2 with hf
  set m : ℝ × Space → Space := fun z => M z.1 z.2 with hm
  have hFμ : AEStronglyMeasurable f μ := by rw [hμ']; exact hF.restrict
  have hMμ : AEStronglyMeasurable m μ := by rw [hμ']; exact hM.restrict
  have hlin : ∀ (u : ℝ × Space → Space), AEStronglyMeasurable u μ →
      ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ENNReal.ofReal (‖u (σ, y)‖ ^ 2)
        = ∫⁻ z, ENNReal.ofReal (‖u z‖ ^ 2) ∂μ := by
    intro u hu
    rw [hμ]
    exact (lintegral_prod (fun z => ENNReal.ofReal (‖u z‖ ^ 2))
      ((hu.norm.aemeasurable.pow_const 2).ennreal_ofReal)).symm
  have hsq : ∀ (u : ℝ × Space → Space), AEStronglyMeasurable u μ →
      ∫⁻ z, ENNReal.ofReal (‖u z‖ ^ 2) ∂μ < ⊤ → Integrable (fun z => ‖u z‖ ^ 2) μ := by
    intro u hu hfin
    refine (integrable_toReal_of_lintegral_ne_top (hu.norm.pow 2).aemeasurable.ennreal_ofReal
      hfin.ne).congr ?_
    exact ae_of_all _ (fun z => ENNReal.toReal_ofReal (sq_nonneg _))
  have hFl : ∫⁻ z, ENNReal.ofReal (‖f z‖ ^ 2) ∂μ < ⊤ := by rw [← hlin f hFμ]; exact hF2
  have hMl : ∫⁻ z, ENNReal.ofReal (‖m z‖ ^ 2) ∂μ < ⊤ := by rw [← hlin m hMμ]; exact hM2
  have hFi := hsq f hFμ hFl
  have hMi := hsq m hMμ hMl
  have hbd : ∀ z, ‖f z‖ * ‖m z‖ ≤ (‖f z‖ ^ 2 + ‖m z‖ ^ 2) / 2 := fun z => by
    nlinarith [sq_nonneg (‖f z‖ - ‖m z‖)]
  have hprod : Integrable (fun z => ‖f z‖ * ‖m z‖) μ := by
    refine Integrable.mono' ((hFi.add hMi).div_const 2) (hFμ.norm.mul hMμ.norm) (ae_of_all _ fun z => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))]
    exact hbd z
  have hinner : Integrable (fun z => inner ℝ (f z) (m z)) μ := by
    refine Integrable.mono' hprod (hFμ.inner hMμ) (ae_of_all _ fun z => ?_)
    rw [Real.norm_eq_abs]
    exact abs_real_inner_le_norm _ _
  have hpair : periodPairing F M = ∫ z, inner ℝ (f z) (m z) ∂μ := by
    rw [hμ, integral_prod _ hinner]
    rfl
  have hFL : MemLp (fun z => ‖f z‖) (ENNReal.ofReal 2) μ := by
    rw [show ENNReal.ofReal 2 = 2 by norm_num]
    exact ((memLp_two_iff_integrable_sq_norm hFμ).2 hFi).norm
  have hML : MemLp (fun z => ‖m z‖) (ENNReal.ofReal 2) μ := by
    rw [show ENNReal.ofReal 2 = 2 by norm_num]
    exact ((memLp_two_iff_integrable_sq_norm hMμ).2 hMi).norm
  have hH := integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
    (ae_of_all _ fun z => norm_nonneg (f z)) (ae_of_all _ fun z => norm_nonneg (m z)) hFL hML
  have hnF : ∫ z, ‖f z‖ ^ (2 : ℝ) ∂μ = (periodLIntegral (fun σ y => ‖F σ y‖ ^ 2)).toReal := by
    have e : (fun z => ‖f z‖ ^ (2 : ℝ)) = fun z => ‖f z‖ ^ 2 := by
      funext z; exact Real.rpow_two _
    rw [e, integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun z => sq_nonneg _)
      (hFμ.norm.pow 2), ← hlin f hFμ]
    rfl
  have hnM : ∫ z, ‖m z‖ ^ (2 : ℝ) ∂μ = (periodLIntegral (fun σ y => ‖M σ y‖ ^ 2)).toReal := by
    have e : (fun z => ‖m z‖ ^ (2 : ℝ)) = fun z => ‖m z‖ ^ 2 := by
      funext z; exact Real.rpow_two _
    rw [e, integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun z => sq_nonneg _)
      (hMμ.norm.pow 2), ← hlin m hMμ]
    rfl
  rw [hnF, hnM, ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow] at hH
  rw [hpair, ← Real.norm_eq_abs]
  refine (norm_integral_le_integral_norm _).trans ?_
  refine (integral_mono hinner.norm hprod (fun z => ?_)).trans hH
  exact abs_real_inner_le_norm _ _

theorem le_add_of_sq_le {x a b : ℝ} (_hx : 0 ≤ x) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h : x ^ 2 ≤ a * x + b ^ 2) : x ≤ a + b := by
  by_contra hne
  have hlt : a + b < x := lt_of_not_ge hne
  nlinarith [mul_nonneg ha _hx, mul_nonneg hb _hx, mul_nonneg hb hb]

theorem coercive_scalar_core {c cμ t a K E S NF NB hh NM n Pr : ℝ} (hc : 0 < c) (hcμ : 0 ≤ cμ)
    (ht : 0 ≤ t) (ha : 0 ≤ a) (hK : 0 ≤ K) (hE : 0 ≤ E) (hS : 0 ≤ S) (hNF : 0 ≤ NF) (hNB : 0 ≤ NB)
    (hh0 : 0 ≤ hh) (hMnorm : NM ≤ a * Real.sqrt (c * E + cμ * n ^ 2)) (hpair : Pr ≤ NF * NM)
    (hineq : c * (E + S) + cμ * n ^ 2 ≤ Pr + c * K ^ 2 * NB ^ 2 + t * hh ^ 2) :
    Real.sqrt (E + S) ≤ a / Real.sqrt c * NF + K * NB + Real.sqrt (t / c) * hh := by
  have hYin : 0 ≤ c * (E + S) + cμ * n ^ 2 := by positivity
  obtain ⟨Y, hY⟩ : ∃ Y, Y = Real.sqrt (c * (E + S) + cμ * n ^ 2) := ⟨_, rfl⟩
  have hY0 : 0 ≤ Y := hY ▸ Real.sqrt_nonneg _
  have hYsq : Y ^ 2 = c * (E + S) + cμ * n ^ 2 := hY ▸ Real.sq_sqrt hYin
  have hMY : NM ≤ a * Y := by
    refine hMnorm.trans (mul_le_mul_of_nonneg_left ?_ ha)
    rw [hY]
    exact Real.sqrt_le_sqrt (by nlinarith [mul_nonneg hc.le hS])
  have hB20 : 0 ≤ c * K ^ 2 * NB ^ 2 + t * hh ^ 2 := by positivity
  obtain ⟨b, hb⟩ : ∃ b, b = Real.sqrt (c * K ^ 2 * NB ^ 2 + t * hh ^ 2) := ⟨_, rfl⟩
  have hb0 : 0 ≤ b := hb ▸ Real.sqrt_nonneg _
  have hbsq : b ^ 2 = c * K ^ 2 * NB ^ 2 + t * hh ^ 2 := hb ▸ Real.sq_sqrt hB20
  have h1 : NF * NM ≤ NF * (a * Y) := mul_le_mul_of_nonneg_left hMY hNF
  have hYle : Y ≤ a * NF + b := by
    refine le_add_of_sq_le hY0 (mul_nonneg ha hNF) hb0 ?_
    rw [hYsq, hbsq]
    linarith
  have hsc := Real.sqrt_pos.2 hc
  have hsc2 : Real.sqrt c ^ 2 = c := Real.sq_sqrt hc.le
  have hst2 : Real.sqrt t ^ 2 = t := Real.sq_sqrt ht
  have hbB : b ≤ Real.sqrt c * K * NB + Real.sqrt t * hh := by
    rw [hb]
    refine Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
    have hx : 0 ≤ Real.sqrt c * K * NB * (Real.sqrt t * hh) := by positivity
    have e1 : (Real.sqrt c * K * NB) ^ 2 = c * K ^ 2 * NB ^ 2 := by
      rw [mul_pow, mul_pow, hsc2]
    have e2 : (Real.sqrt t * hh) ^ 2 = t * hh ^ 2 := by
      rw [mul_pow, hst2]
    have e3 : (Real.sqrt c * K * NB + Real.sqrt t * hh) ^ 2
        = (Real.sqrt c * K * NB) ^ 2 + (Real.sqrt t * hh) ^ 2
          + 2 * (Real.sqrt c * K * NB * (Real.sqrt t * hh)) := by ring
    rw [e3, e1, e2]
    linarith
  have hZY : Real.sqrt c * Real.sqrt (E + S) ≤ Y := by
    rw [← Real.sqrt_mul hc.le, hY]
    exact Real.sqrt_le_sqrt (le_add_of_nonneg_right (mul_nonneg hcμ (sq_nonneg n)))
  have e1 : Real.sqrt c * (a / Real.sqrt c * NF) = a * NF := by field_simp
  have e2 : Real.sqrt c * (Real.sqrt (t / c) * hh) = Real.sqrt t * hh := by
    rw [Real.sqrt_div' t hc.le]
    field_simp
  have hmain : Real.sqrt c * Real.sqrt (E + S) ≤
      Real.sqrt c * (a / Real.sqrt c * NF + K * NB + Real.sqrt (t / c) * hh) := by
    rw [mul_add, mul_add, e1, e2]
    nlinarith [hZY, hYle, hbB]
  exact le_of_mul_le_mul_left hmain hsc

theorem coerciveClause_of_multiplierInequality {k : ℕ} {d : CertificateData k} {c cμ t a K : ℝ}
    (h : MultiplierInequality d c cμ t a K) (hL2 : a / Real.sqrt c ≤ d.coerciveL2)
    (hBall : K ≤ d.coerciveBall) (hPin : Real.sqrt (t / c) ≤ d.coercivePin) :
    CoerciveClause d := by
  intro p hp v G H g hv κ F hFm hFp hF2 hR
  obtain ⟨M, n, hMm, hM2, hn, hMnorm, hineq⟩ := h.bound p hp v G H g hv κ F hFm hFp hF2 hR
  have hpair : periodPairing F M ≤ periodNorm F * periodNorm M :=
    (le_abs_self _).trans (periodPairing_abs_le hFm hMm hF2 hM2)
  have hbase := coercive_scalar_core h.c_pos h.cμ_nonneg h.t_nonneg h.a_nonneg h.K_nonneg
    (ENNReal.toReal_nonneg : 0 ≤ weightedEnergy d.weightFn G H)
    (Finset.sum_nonneg (fun i _ => sq_nonneg (κ i))) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    (Real.sqrt_nonneg _) hMnorm hpair hineq
  refine hbase.trans ?_
  have hNF : 0 ≤ periodNorm F := Real.sqrt_nonneg _
  have hNB : 0 ≤ periodBallNorm d.ballRadius F := Real.sqrt_nonneg _
  have hh0 : 0 ≤ vecNorm (fun i => pinValue (d.pin i) G) := Real.sqrt_nonneg _
  exact add_le_add (add_le_add (mul_le_mul_of_nonneg_right hL2 hNF) (mul_le_mul_of_nonneg_right hBall hNB))
    (mul_le_mul_of_nonneg_right hPin hh0)

def axialRot (φ : ℝ) (y : Space) : Space :=
  (Real.cos φ * y 0 - Real.sin φ * y 1) • unitVector 0
    + (Real.sin φ * y 0 + Real.cos φ * y 1) • unitVector 1 + y 2 • unitVector 2

def alternatingSymbol (i j l : Fin 3) : ℝ :=
  (((i : ℕ) : ℝ) - ((j : ℕ) : ℝ)) * (((j : ℕ) : ℝ) - ((l : ℕ) : ℝ)) * (((l : ℕ) : ℝ) - ((i : ℕ) : ℝ)) / 2

def modeAverage {β : Type*} (ι : ℤ × ℤ) (f : ℝ → ℝ → β → ℝ) (b : β) : ℂ :=
  (1 / (2 * Real.pi) : ℂ) * ∫ τ in (0 : ℝ)..1, ∫ φ in (0 : ℝ)..(2 * Real.pi),
    Complex.exp (-(((2 * Real.pi * ι.1 * τ + ι.2 * φ : ℝ) : ℂ) * Complex.I)) * ((f τ φ b : ℝ) : ℂ)

def modeVel (ι : ℤ × ℤ) (v : ℝ → Space → Space) (σ : ℝ) (y : Space) : Fin 3 → ℂ :=
  modeAverage ι (fun τ φ i => axialRot (-φ) (v (σ + τ) (axialRot φ y)) i)

def modeGrad (ι : ℤ × ℤ) (G : ℝ → Space → (Space →L[ℝ] Space)) (σ : ℝ) (y : Space) :
    Fin 3 × Fin 3 → ℂ :=
  modeAverage ι (fun τ φ ij =>
    axialRot (-φ) (G (σ + τ) (axialRot φ y) (axialRot φ (unitVector ij.2))) ij.1)

def modeSecondDeriv (ι : ℤ × ℤ) (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (σ : ℝ) (y : Space) :
    Fin 3 × Fin 3 × Fin 3 → ℂ :=
  modeAverage ι (fun τ φ ijl =>
    axialRot (-φ) (H (σ + τ) (axialRot φ y) (axialRot φ (unitVector ijl.2.1))
      (axialRot φ (unitVector ijl.2.2))) ijl.1)

def cnormSq {β : Type*} [Fintype β] (x : β → ℂ) : ℝ := ∑ b, ‖x b‖ ^ 2

def curlOfGrad (g : Fin 3 × Fin 3 → ℂ) (i : Fin 3) : ℂ :=
  ∑ j : Fin 3, ∑ l : Fin 3, (alternatingSymbol i j l : ℂ) * g (l, j)

def curlGradOfSecondDeriv (h : Fin 3 × Fin 3 × Fin 3 → ℂ) (il : Fin 3 × Fin 3) : ℂ :=
  ∑ j : Fin 3, ∑ m : Fin 3, (alternatingSymbol il.1 j m : ℂ) * h (m, il.2, j)

def cylRadius (y : Space) : ℝ := Real.sqrt (y 0 ^ 2 + y 1 ^ 2)

def IsAxisymmetric (f : Space → ℝ) : Prop := ∀ φ y, f (axialRot φ y) = f y

def shiftedFrequency (P : ℝ) (rate : Space → ℝ) (ι : ℤ × ℤ) (y : Space) : ℝ :=
  2 * Real.pi * ι.1 / P + ι.2 * rate y

def meanField (W : ℝ → Space → Space) (y : Space) : Space :=
  ∑ i : Fin 3, (modeVel (0, 0) W 0 y i).re • unitVector i

def relativeVelocity (W : ℝ → Space → Space) (rate : Space → ℝ) (y : Space) : Space :=
  meanField W y + (1 / 2 : ℝ) • y - rate y • (-(y 1) • unitVector 0 + y 0 • unitVector 1)

def curlVec (G : Space →L[ℝ] Space) : Space :=
  ∑ i : Fin 3, (∑ j : Fin 3, ∑ l : Fin 3, alternatingSymbol i j l * G (unitVector j) l) • unitVector i

def vortGrad (DDW : Space →L[ℝ] Space →L[ℝ] Space) (j m : Fin 3) : ℝ :=
  ∑ a : Fin 3, ∑ b : Fin 3, alternatingSymbol j a b * DDW (unitVector m) (unitVector a) b

def stretchForm (W : ℝ → Space → Space) (v : ℝ → Space → Space)
    (G : ℝ → Space → (Space →L[ℝ] Space)) (σ : ℝ) (y : Space) : ℝ :=
  -(∑ i : Fin 3, ∑ j : Fin 3, curlVec (G σ y) i
      * ((fderiv ℝ (W σ) y (unitVector j) i + fderiv ℝ (W σ) y (unitVector i) j) / 2) * curlVec (G σ y) j)
    + ∑ j : Fin 3, (∑ m : Fin 3, v σ y m * vortGrad (fderiv ℝ (fun x => fderiv ℝ (W σ) x) y) j m)
        * curlVec (G σ y) j
    + (1 / 2 : ℝ) * ∑ i : Fin 3, ∑ m : Fin 3, ∑ l : Fin 3, ∑ j : Fin 3,
        alternatingSymbol i m l * vortGrad (fderiv ℝ (fun x => fderiv ℝ (W σ) x) y) j m
          * G σ y (unitVector j) i * v σ y l

structure FlowBounds (C : Type) where
  perpSpeed : C → Space → ℝ
  meanVort : Space → ℝ
  meanVortGrad : Space → ℝ
  meanStretch : Space → ℝ
  meanGrad : Space → ℝ
  wave0 : Space → ℝ
  wave1 : Space → ℝ
  waveVort : Space → ℝ
  wave2 : Space → ℝ
  waveStretch : Space → ℝ
  waveVortGrad : Space → ℝ

structure ModeWeights (C : Type) where
  classOf : ℤ × ℤ → C
  waves : Finset (ℤ × ℤ)
  rate : C → Space → ℝ
  epsW : C → Space → ℝ
  muW : C → Space → ℝ
  convD : C → Space → ℝ
  convZ : C → Space → ℝ
  share1 : C → Space → ℝ
  share2 : Space → ℝ
  share4 : Space → ℝ
  len : Space → ℝ
  len2 : Space → ℝ
  eta : C → ℝ
  etaMin : ℝ
  c : ℝ
  cμ : ℝ

namespace ModeWeights

variable {C : Type} (m : ModeWeights C) (P : ℝ) (b : FlowBounds C) (w : Space → ℝ)

def eps (ι : ℤ × ℤ) (y : Space) : ℝ := |m.epsW (m.classOf ι) y|

def mu (ι : ℤ × ℤ) (y : Space) : ℝ := |m.muW (m.classOf ι) y|

def dop (ι : ℤ × ℤ) (y : Space) : ℝ := shiftedFrequency P (m.rate (m.classOf ι)) ι y

def epsGrad (ι : ℤ × ℤ) (y : Space) : ℝ := ‖fderiv ℝ (m.epsW (m.classOf ι)) y‖

def muGrad (ι : ℤ × ℤ) (y : Space) : ℝ := ‖fderiv ℝ (m.muW (m.classOf ι)) y‖

def epsNb (ι : ℤ × ℤ) (y : Space) : ℝ :=
  ((m.waves.sup fun α => ‖m.epsW (m.classOf (ι + α)) y‖₊ : NNReal) : ℝ)

def muNb (ι : ℤ × ℤ) (y : Space) : ℝ :=
  ((m.waves.sup fun α => ‖m.muW (m.classOf (ι + α)) y‖₊ : NNReal) : ℝ)

open Classical in
def ind (p : Prop) : ℝ := if p then 1 else 0

def shareHat (ι : ℤ × ℤ) (y : Space) : ℝ :=
  m.share1 (m.classOf ι) y * ind (0 < m.eps ι y + m.epsGrad ι y) + m.share2 y * ind (0 < m.epsNb ι y)

def secondDerivNorm (f : Space → ℝ) (y : Space) : ℝ := ‖iteratedFDeriv ℝ 2 f y‖

def coefA (ι : ℤ × ℤ) (y : Space) : ℝ :=
  1 / 4 + m.eps ι y * |m.dop P ι y|
    - (m.eps ι y * b.perpSpeed (m.classOf ι) y + m.epsGrad ι y) ^ 2 / (4 * m.share1 (m.classOf ι) y)
    - m.eps ι y ^ 2 * b.wave0 y ^ 2 / (4 * m.share2 y)
    - m.eps ι y * ((1 / 2) * b.meanVort y + |m.rate (m.classOf ι) y| + (1 / 2) * b.wave1 y
      + (1 / 2) * b.waveVort y + (1 / 2) * m.len2 y * b.wave2 y)

def coefAA (ι : ℤ × ℤ) (y : Space) : ℝ :=
  m.convZ (m.classOf ι) y - Real.sqrt 2 * m.eps ι y * b.meanVort y - secondDerivNorm (m.convD (m.classOf ι)) y
    - m.c * w y - m.epsNb ι y * (b.wave1 y + (1 / 2) * b.waveVort y) - m.share4 y * ind (0 < m.muNb ι y)

def penalty (ι : ℤ × ℤ) (y : Space) : ℝ :=
  (b.meanGrad y ^ 2 / m.eta (m.classOf ι) + (1 / 2) * m.eta (m.classOf ι) * m.mu ι y ^ 2)
      * ind (∃ x, m.muW (m.classOf ι) x ≠ 0)
    + (b.wave1 y ^ 2 / m.etaMin) * ind (∃ α ∈ m.waves, ∃ x, m.muW (m.classOf (ι + α)) x ≠ 0)

def coefB (ι : ℤ × ℤ) (y : Space) : ℝ :=
  (1 - m.cμ) * m.mu ι y * |m.dop P ι y| - m.mu ι y * |m.rate (m.classOf ι) y|
    - m.mu ι y ^ 2 * b.wave0 y ^ 2 / (4 * m.share4 y) - secondDerivNorm (m.convZ (m.classOf ι)) y
    - (1 / 2) * m.epsNb ι y * b.wave2 y / m.len2 y - m.penalty b ι y

def coefC (ι : ℤ × ℤ) (y : Space) : ℝ :=
  Real.sqrt 2 * m.eps ι y * b.meanVortGrad y + m.mu ι y * b.perpSpeed (m.classOf ι) y + m.muGrad ι y

def modeDensity (ι : ℤ × ℤ) (y : Space) (x2 xc x1 xo x0 : ℝ) : ℝ :=
  (m.convD (m.classOf ι) y - m.c) * x2 ^ 2 + (1 - m.shareHat ι y - m.convD (m.classOf ι) y) * xc ^ 2
    + (m.coefA P b ι y - m.convZ (m.classOf ι) y) * xo ^ 2 + m.coefAA b w ι y * x1 ^ 2
    + m.coefB P b ι y * x0 ^ 2 - m.coefC b ι y * x1 * x0

def modeTerm (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (ι : ℤ × ℤ) (σ : ℝ) (y : Space) : ℝ :=
  m.modeDensity P b w ι y (Real.sqrt (cnormSq (modeSecondDeriv ι H σ y)))
    (Real.sqrt (cnormSq (curlGradOfSecondDeriv (modeSecondDeriv ι H σ y))))
    (Real.sqrt (cnormSq (modeGrad ι G σ y))) (Real.sqrt (cnormSq (curlOfGrad (modeGrad ι G σ y))))
    (Real.sqrt (cnormSq (modeVel ι v σ y)))

def frequencySeminormSq (v : ℝ → Space → Space) : ℝ≥0∞ :=
  ∑' ι : ℤ × ℤ, ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y,
    ENNReal.ofReal (m.mu ι y * |m.dop P ι y| * cnormSq (modeVel ι v σ y))

end ModeWeights

namespace ModeWeights

variable {C : Type} (m : ModeWeights C) (P : ℝ) (b : FlowBounds C) (w : Space → ℝ)

structure IsAdmissible (w₀ epsSup epsGradSup ratio : ℝ) : Prop where
  finite_classes : Finite C
  c_pos : 0 < m.c
  c_lt_one : m.c < 1
  cμ_pos : 0 < m.cμ
  cμ_lt_one : m.cμ < 1
  period_pos : 0 < P
  weight_pos : 0 < w₀
  weight_lower : ∀ y, w₀ ≤ w y
  weight_measurable : Measurable w
  weight_axi : IsAxisymmetric w
  waves_neg : ∀ α ∈ m.waves, -α ∈ m.waves
  waves_ne_zero : (0, 0) ∉ m.waves
  epsW_odd : ∀ ι y, m.epsW (m.classOf (-ι)) y = -m.epsW (m.classOf ι) y
  muW_odd : ∀ ι y, m.muW (m.classOf (-ι)) y = -m.muW (m.classOf ι) y
  rate_even : ∀ ι y, m.rate (m.classOf (-ι)) y = m.rate (m.classOf ι) y
  convD_even : ∀ ι y, m.convD (m.classOf (-ι)) y = m.convD (m.classOf ι) y
  convZ_even : ∀ ι y, m.convZ (m.classOf (-ι)) y = m.convZ (m.classOf ι) y
  share1_even : ∀ ι y, m.share1 (m.classOf (-ι)) y = m.share1 (m.classOf ι) y
  eta_even : ∀ ι, m.eta (m.classOf (-ι)) = m.eta (m.classOf ι)
  epsW_increment : ∀ c, ∃ K, LipschitzWith K (m.epsW c)
  muW_increment : ∀ c, ∃ K, LipschitzWith K (m.muW c)
  epsW_axi : ∀ c, IsAxisymmetric (m.epsW c)
  muW_axi : ∀ c, IsAxisymmetric (m.muW c)
  rate_axi : ∀ c, IsAxisymmetric (m.rate c)
  convD_axi : ∀ c, IsAxisymmetric (m.convD c)
  convZ_axi : ∀ c, IsAxisymmetric (m.convZ c)
  share1_axi : ∀ c, IsAxisymmetric (m.share1 c)
  share2_axi : IsAxisymmetric m.share2
  share4_axi : IsAxisymmetric m.share4
  len_axi : IsAxisymmetric m.len
  len2_axi : IsAxisymmetric m.len2
  rate_measurable : ∀ c, Measurable (m.rate c)
  share1_measurable : ∀ c, Measurable (m.share1 c)
  share2_measurable : Measurable m.share2
  share4_measurable : Measurable m.share4
  len_measurable : Measurable m.len
  len2_measurable : Measurable m.len2
  rate_bounded : ∃ B, ∀ c y, |m.rate c y| ≤ B
  epsW_sign : ∀ ι y, 0 ≤ m.dop P ι y * m.epsW (m.classOf ι) y
  muW_sign : ∀ ι y, 0 ≤ m.dop P ι y * m.muW (m.classOf ι) y
  epsW_le : ∀ c y, |m.epsW c y| ≤ epsSup
  epsW_grad_le : ∀ c y, ‖fderiv ℝ (m.epsW c) y‖ ≤ epsGradSup
  epsW_decay : ∃ B, ∀ c y, ‖y‖ * |m.epsW c y| ≤ B
  muW_decay : ∃ B, ∀ c y, |m.muW c y| ≤ B ∧ ‖y‖ ^ 2 * |m.muW c y| ≤ B
    ∧ ‖y‖ * ‖fderiv ℝ (m.muW c) y‖ ≤ B
  mu_ratio : ∀ ι y, m.mu ι y ≤ ratio * |m.dop P ι y|
  ratio_nonneg : 0 ≤ ratio
  convD_smooth : ∀ c, ContDiff ℝ 2 (m.convD c)
  convZ_smooth : ∀ c, ContDiff ℝ 2 (m.convZ c)
  convD_nonneg : ∀ c y, 0 ≤ m.convD c y
  convD_decay : ∃ B, ∀ c y, ∀ j ≤ 2, ‖y‖ ^ j * ‖iteratedFDeriv ℝ j (m.convD c) y‖ ≤ B
  convZ_decay : ∃ B, ∀ c y, ∀ j ≤ 2, (1 + ‖y‖) ^ j * ‖iteratedFDeriv ℝ j (m.convZ c) y‖ ≤ B
  share1_nonneg : ∀ c y, 0 ≤ m.share1 c y
  share1_pos : ∀ ι y, 0 < m.eps ι y + m.epsGrad ι y → 0 < m.share1 (m.classOf ι) y
  share2_pos : ∀ y, 0 < m.share2 y
  share4_pos : ∀ y, 0 < m.share4 y
  len_pos : ∀ y, 0 < m.len y
  len2_pos : ∀ y, 0 < m.len2 y
  share4_bounded : ∃ B, ∀ y, m.share4 y ≤ B
  len_bounded : ∃ B, ∀ y, b.waveVortGrad y * m.len y ≤ B ∧ ‖y‖ ^ 2 * b.waveVortGrad y / m.len y ≤ B
  len2_bounded : ∃ B, ∀ y, m.len2 y * b.wave2 y * epsSup ≤ B ∧ ‖y‖ ^ 2 * b.wave2 y * epsSup / m.len2 y ≤ B
  eta_pos : ∀ c, 0 < m.eta c
  etaMin_pos : 0 < m.etaMin
  etaMin_le : ∀ c, m.etaMin ≤ m.eta c
  conv_le : ∀ ι y, m.convD (m.classOf ι) y ≤ 1 - m.shareHat ι y

end ModeWeights

def gradField (W : ℝ → Space → Space) : ℝ → Space → (Space →L[ℝ] Space) :=
  fun σ y => fderiv ℝ (W σ) y

def secondDerivField (W : ℝ → Space → Space) : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space) :=
  fun σ y => fderiv ℝ (fun x => fderiv ℝ (W σ) x) y

def symPartForm (G : Space →L[ℝ] Space) (u : Space) : ℝ := inner ℝ u (G u)

structure FlowBounds.IsValid {C : Type} (b : FlowBounds C) (m : ModeWeights C)
    (W : ℝ → Space → Space) : Prop where
  harmonics : ∀ σ y i, W σ y i = (modeVel (0, 0) W σ y i).re
    + ∑ α ∈ m.waves, (modeVel α W σ y i).re
  perpSpeed_ge : ∀ c y, ‖relativeVelocity W (m.rate c) y‖ ≤ b.perpSpeed c y
  meanVort_ge : ∀ y, ‖curlVec (fderiv ℝ (meanField W) y)‖ ≤ b.meanVort y
  meanVortGrad_ge : ∀ y, ‖fderiv ℝ (fun x => curlVec (fderiv ℝ (meanField W) x)) y‖ ≤ b.meanVortGrad y
  meanStretch_ge : ∀ y u, symPartForm (fderiv ℝ (meanField W) y) u ≤ b.meanStretch y * ‖u‖ ^ 2
  meanGrad_ge : ∀ y, ‖fderiv ℝ (meanField W) y‖ ≤ b.meanGrad y
  wave0_ge : ∀ σ y, ∑ α ∈ m.waves, Real.sqrt (cnormSq (modeVel α W σ y)) ≤ b.wave0 y
  wave1_ge : ∀ σ y, ∑ α ∈ m.waves, Real.sqrt (cnormSq (modeGrad α (gradField W) σ y)) ≤ b.wave1 y
  waveVort_ge : ∀ σ y, ∑ α ∈ m.waves,
    Real.sqrt (cnormSq (curlOfGrad (modeGrad α (gradField W) σ y))) ≤ b.waveVort y
  wave2_ge : ∀ σ y, ∑ α ∈ m.waves,
    Real.sqrt (cnormSq (curlGradOfSecondDeriv (modeSecondDeriv α (secondDerivField W) σ y))) ≤ b.wave2 y
  waveStretch_ge : ∀ σ φ y u,
    |symPartForm (fderiv ℝ (W σ) (axialRot φ y) - fderiv ℝ (meanField W) (axialRot φ y)) u|
      ≤ b.waveStretch y * ‖u‖ ^ 2
  waveVortGrad_ge : ∀ σ φ y, ‖fderiv ℝ (fun x => curlVec (fderiv ℝ (W σ) x)) (axialRot φ y)
      - fderiv ℝ (fun x => curlVec (fderiv ℝ (meanField W) x)) (axialRot φ y)‖ ≤ b.waveVortGrad y

def IsPeriodicTestField (ψ : ℝ → Space → Space) : Prop :=
  ContDiff ℝ ∞ (fun z : ℝ × Space => ψ z.1 z.2) ∧ IsTimePeriodic ψ ∧
    (∃ R, ∀ σ y, R < ‖y‖ → ψ σ y = 0) ∧ ∀ σ y, divergenceAt (ψ σ) y = 0

def IsPeriodicTestPotential (q : ℝ → Space → ℝ) : Prop :=
  ContDiff ℝ ∞ (fun z : ℝ × Space => q z.1 z.2) ∧ IsTimePeriodic q ∧
    ∃ R, ∀ σ y, R < ‖y‖ → q σ y = 0

def cdot (x z : Fin 3 → ℂ) : ℂ := ∑ i, x i * (starRingEnd ℂ) (z i)

def cdotMat (x z : Fin 3 × Fin 3 → ℂ) : ℂ := ∑ i, x i * (starRingEnd ℂ) (z i)

namespace ModeWeights

variable {C : Type} (m : ModeWeights C) (P : ℝ) (b : FlowBounds C) (w : Space → ℝ)

def IsMultiplierField (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (M : ℝ → Space → Space) : Prop :=
  AEStronglyMeasurable (fun z : ℝ × Space => M z.1 z.2) volume ∧ IsTimePeriodic M ∧
    periodLIntegral (fun σ y => ‖M σ y‖ ^ 2) < ⊤ ∧
    (∀ q, IsPeriodicTestPotential q →
      ∫ σ in Set.Icc (0 : ℝ) 1, ∫ y, inner ℝ (M σ y) (gradientAt (q σ) y) = 0) ∧
    ∀ ψ, IsPeriodicTestField ψ →
      ∫ σ in Set.Icc (0 : ℝ) 1, ∫ y, inner ℝ (M σ y) (ψ σ y) =
        (∫ σ in Set.Icc (0 : ℝ) 1, ∫ y, inner ℝ (-secondDerivTrace (H σ y)) (ψ σ y))
          + ∑' ι : ℤ × ℤ, ∫ σ in Set.Icc (0 : ℝ) 1, ∫ y,
            ((Complex.I * (m.epsW (m.classOf ι) y : ℂ)
                * cdot (curlOfGrad (modeGrad ι G σ y)) (curlOfGrad (modeGrad ι (gradField ψ) σ y))).re
              + (Complex.I * (m.muW (m.classOf ι) y : ℂ) * cdot (modeVel ι v σ y) (modeVel ι ψ σ y)).re)

def densityPos (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (W : ℝ → Space → Space) (σ : ℝ) (y : Space) :
    ℝ≥0∞ :=
  (∑' ι : ℤ × ℤ, ENNReal.ofReal (m.modeTerm P b w v G H ι σ y)) + ENNReal.ofReal (stretchForm W v G σ y)

def densityNeg (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (W : ℝ → Space → Space) (σ : ℝ) (y : Space) :
    ℝ≥0∞ :=
  (∑' ι : ℤ × ℤ, ENNReal.ofReal (-m.modeTerm P b w v G H ι σ y))
    + ENNReal.ofReal (-stretchForm W v G σ y)

def multiplierConstant (w₀ epsSup epsGradSup ratio : ℝ) : ℝ :=
  Real.sqrt ((1 + epsSup + epsGradSup / Real.sqrt w₀) ^ 2 / m.c + ratio / m.cμ)

def multiplierGap {k : ℕ} (act : Fin k → ℝ → Space → Space) (v : ℝ → Space → Space)
    (G : ℝ → Space → (Space →L[ℝ] Space)) (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space))
    (κ : Fin k → ℝ) (F M : ℝ → Space → Space) : ℝ :=
  periodPairing F M - m.c * weightedEnergy w G H - m.cμ * (m.frequencySeminormSq P v).toReal
    - ∑ i, κ i * periodPairing (act i) M

def diagonalDensity (θc A B Cc x2 x1 x0 : ℝ) : ℝ := θc * x2 ^ 2 + A * x1 ^ 2 + B * x0 ^ 2 - Cc * x1 * x0

theorem diagonalDensity_nonneg {θc A B Cc : ℝ} (hθ : 0 ≤ θc) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hC : Cc ^ 2 ≤ 4 * A * B) (x2 x1 x0 : ℝ) : 0 ≤ diagonalDensity θc A B Cc x2 x1 x0 := by
  unfold diagonalDensity
  rcases eq_or_lt_of_le hA with h | h
  · subst h
    have : Cc = 0 := by nlinarith [sq_nonneg Cc]
    subst this
    nlinarith [mul_nonneg hθ (sq_nonneg x2), mul_nonneg hB (sq_nonneg x0)]
  · have key : 0 ≤ 4 * A * (A * x1 ^ 2 + B * x0 ^ 2 - Cc * x1 * x0) := by
      nlinarith [sq_nonneg (2 * A * x1 - Cc * x0), mul_nonneg (sub_nonneg.2 hC) (sq_nonneg x0)]
    have : 0 ≤ A * x1 ^ 2 + B * x0 ^ 2 - Cc * x1 * x0 := by
      by_contra hne
      have hne' := lt_of_not_ge hne
      nlinarith
    nlinarith [mul_nonneg hθ (sq_nonneg x2)]

theorem azimuthalDensity_nonneg {θc A B Cc kk r α : ℝ}
    (hθ : 0 ≤ θc) (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    (hA' : 0 ≤ A + θc * (kk - 2) ^ 2 / r ^ 2)
    (hB' : 0 ≤ B + α * (A + θc * (kk - 2) ^ 2 / r ^ 2) * (kk - 1) ^ 2 / r ^ 2)
    (hC : Cc ^ 2 ≤ 4 * (1 - α) * (A + θc * (kk - 2) ^ 2 / r ^ 2)
      * (B + α * (A + θc * (kk - 2) ^ 2 / r ^ 2) * (kk - 1) ^ 2 / r ^ 2))
    {x2 x1 x0 : ℝ}
    (hg1 : (kk - 1) ^ 2 / r ^ 2 * x0 ^ 2 ≤ x1 ^ 2) (hg2 : (kk - 2) ^ 2 / r ^ 2 * x1 ^ 2 ≤ x2 ^ 2) :
    0 ≤ diagonalDensity θc A B Cc x2 x1 x0 := by
  have e2 : θc * (kk - 2) ^ 2 / r ^ 2 = θc * ((kk - 2) ^ 2 / r ^ 2) := by ring
  have e1 : ∀ u : ℝ, u * (kk - 1) ^ 2 / r ^ 2 = u * ((kk - 1) ^ 2 / r ^ 2) := fun u => by ring
  rw [e2] at hA' hB' hC
  rw [e1] at hB' hC
  generalize (kk - 2) ^ 2 / r ^ 2 = q2 at hA' hB' hC hg2
  generalize (kk - 1) ^ 2 / r ^ 2 = q1 at hB' hC hg1
  have key := diagonalDensity_nonneg (θc := 0) (A := (1 - α) * (A + θc * q2))
    (B := B + α * (A + θc * q2) * q1) (Cc := Cc) (le_refl (0 : ℝ))
    (mul_nonneg (sub_nonneg.2 hα1) hA') hB' (by nlinarith [hC]) x2 x1 x0
  unfold diagonalDensity at key ⊢
  have k1 : θc * (q2 * x1 ^ 2) ≤ θc * x2 ^ 2 := mul_le_mul_of_nonneg_left hg2 hθ
  have k2 : α * (A + θc * q2) * (q1 * x0 ^ 2) ≤ α * (A + θc * q2) * x1 ^ 2 :=
    mul_le_mul_of_nonneg_left hg1 (mul_nonneg hα0 hA')
  nlinarith [key, k1, k2]

def stretchCharge (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space)) (ι : ℤ × ℤ)
    (σ : ℝ) (y : Space) : ℝ :=
  (b.meanStretch y + b.waveStretch y) * cnormSq (curlOfGrad (modeGrad ι G σ y))
    + (Real.sqrt 2 + 1 / 2) * b.meanVortGrad y * Real.sqrt (cnormSq (modeVel ι v σ y))
        * Real.sqrt (cnormSq (modeGrad ι G σ y))
    + (1 / 2) * (Real.sqrt 2 + 1 / 2) * b.waveVortGrad y
        * (m.len y * cnormSq (modeGrad ι G σ y) + cnormSq (modeVel ι v σ y) / m.len y)

theorem le_of_ennreal_bounds {X Y : ℝ} {Dp Dn : ℝ≥0∞} (hn : Dn < ⊤)
    (h1 : Dp + ENNReal.ofReal (-X) ≤ ENNReal.ofReal X + Dn)
    (h2 : ENNReal.ofReal Y + Dn ≤ Dp + ENNReal.ofReal (-Y)) : Y ≤ X := by
  have hp : Dp < ⊤ := lt_of_le_of_lt (le_trans le_self_add h1)
    (ENNReal.add_lt_top.2 ⟨ENNReal.ofReal_lt_top, hn⟩)
  rw [← ENNReal.ofReal_toReal hp.ne, ← ENNReal.ofReal_toReal hn.ne] at h1 h2
  have hp0 : 0 ≤ Dp.toReal := ENNReal.toReal_nonneg
  have hn0 : 0 ≤ Dn.toReal := ENNReal.toReal_nonneg
  rcases le_total X 0 with hX | hX <;> rcases le_total Y 0 with hY | hY
  · rw [ENNReal.ofReal_of_nonpos hX, ← ENNReal.ofReal_add hp0 (by linarith), zero_add,
      ENNReal.ofReal_le_ofReal_iff hn0] at h1
    rw [ENNReal.ofReal_of_nonpos hY, zero_add, ← ENNReal.ofReal_add hp0 (by linarith),
      ENNReal.ofReal_le_ofReal_iff (by linarith)] at h2
    linarith
  · rw [ENNReal.ofReal_of_nonpos hX, ← ENNReal.ofReal_add hp0 (by linarith), zero_add,
      ENNReal.ofReal_le_ofReal_iff hn0] at h1
    rw [ENNReal.ofReal_of_nonpos (by linarith : -Y ≤ 0), add_zero, ← ENNReal.ofReal_add hY hn0,
      ENNReal.ofReal_le_ofReal_iff hp0] at h2
    linarith
  · rw [ENNReal.ofReal_of_nonpos (by linarith : -X ≤ 0), add_zero, ← ENNReal.ofReal_add hX hn0,
      ENNReal.ofReal_le_ofReal_iff (by linarith)] at h1
    linarith
  · rw [ENNReal.ofReal_of_nonpos (by linarith : -X ≤ 0), add_zero, ← ENNReal.ofReal_add hX hn0,
      ENNReal.ofReal_le_ofReal_iff (by linarith)] at h1
    rw [ENNReal.ofReal_of_nonpos (by linarith : -Y ≤ 0), add_zero, ← ENNReal.ofReal_add hY hn0,
      ENNReal.ofReal_le_ofReal_iff hp0] at h2
    linarith

end ModeWeights

structure EpsPiece where
  modes : Set (ℤ × ℤ)
  frame : ℝ
  wt : Space → ℝ
  share1 : Space → ℝ
  share2 : Space → ℝ
  len : Space → ℝ
  t0 : Space → ℝ
  t1 : Space → ℝ
  t2 : Space → ℝ
  t3 : Space → ℝ
  scale : Space → ℝ
  speed : Space → ℝ

structure MuPiece where
  modes : Set (ℤ × ℤ)
  frame : ℝ
  wt : Space → ℝ
  share : Space → ℝ
  t4 : Space → ℝ
  eta : ℝ
  speed : Space → ℝ

structure HarmonicBounds where
  harmonics : Finset (ℤ × ℤ)
  ampW : ℤ × ℤ → Space → ℝ
  ampGradW : ℤ × ℤ → Space → ℝ
  ampVort : ℤ × ℤ → Space → ℝ
  ampGradVort : ℤ × ℤ → Space → ℝ
  supVort : Space → ℝ
  supGradVort : Space → ℝ

structure PieceWeights (C : Type) (nE nM : ℕ) where
  classOf : ℤ × ℤ → C
  convD : C → Space → ℝ
  convZ : C → Space → ℝ
  epsP : Fin nE → EpsPiece
  muP : Fin nM → MuPiece
  c : ℝ
  cμ : ℝ

namespace PieceWeights

open Classical in
def sgn (T : Set (ℤ × ℤ)) (ι : ℤ × ℤ) : ℝ := if ι ∈ T then 1 else if -ι ∈ T then -1 else 0

def inPiece (T : Set (ℤ × ℤ)) (ι : ℤ × ℤ) : Prop := ι ∈ T ∨ -ι ∈ T

open Classical in
def fwdSum (h : HarmonicBounds) (T : Set (ℤ × ℤ)) (amp : ℤ × ℤ → Space → ℝ) (ι : ℤ × ℤ) (y : Space) : ℝ :=
  ∑ β ∈ h.harmonics, if ι + β ∈ T then amp β y else 0

open Classical in
def backSum (h : HarmonicBounds) (T : Set (ℤ × ℤ)) (amp : ℤ × ℤ → Space → ℝ) (ι : ℤ × ℤ) (y : Space) : ℝ :=
  ∑ β ∈ h.harmonics, if ι - β ∈ T then 0 else amp β y

open Classical in
def inward (h : HarmonicBounds) (T : Set (ℤ × ℤ)) (amp : ℤ × ℤ → Space → ℝ) (ι : ℤ × ℤ) (y : Space) : ℝ :=
  if ι ∈ T then backSum h T amp ι y else if -ι ∈ T then backSum h T amp (-ι) y else 0

open Classical in
def outward (h : HarmonicBounds) (T : Set (ℤ × ℤ)) (amp : ℤ × ℤ → Space → ℝ) (ι : ℤ × ℤ) (y : Space) : ℝ :=
  (if ι ∈ T then 0 else fwdSum h T amp ι y) + (if -ι ∈ T then 0 else fwdSum h T amp (-ι) y)

def harmonicSum (h : HarmonicBounds) (y : Space) : ℝ := ∑ β ∈ h.harmonics, h.ampGradW β y

def frameFreq (P a : ℝ) (ι : ℤ × ℤ) : ℝ := 2 * Real.pi * ι.1 / P + a * ι.2

variable {C : Type} {nE nM : ℕ} (m : PieceWeights C nE nM) (P : ℝ) (h : HarmonicBounds)
  (w : Space → ℝ)

def wtGrad (f : Space → ℝ) (y : Space) : ℝ := ‖fderiv ℝ f y‖

open Classical in
def shareHat (ι : ℤ × ℤ) (y : Space) : ℝ :=
  ∑ β : Fin nE, ((m.epsP β).share1 y * ModeWeights.ind (inPiece (m.epsP β).modes ι)
      * ModeWeights.ind (0 < (m.epsP β).wt y + wtGrad (m.epsP β).wt y)
    + (m.epsP β).share2 y * ModeWeights.ind (0 < (m.epsP β).wt y)
      * outward h (m.epsP β).modes h.ampW ι y / (m.epsP β).scale y)

open Classical in
def coefA (ι : ℤ × ℤ) (y : Space) : ℝ :=
  1 / 4 + (∑ β : Fin nE, ModeWeights.ind (inPiece (m.epsP β).modes ι) *
      ((m.epsP β).wt y * |frameFreq P (m.epsP β).frame ι|
        - ((m.epsP β).wt y * (m.epsP β).speed y + wtGrad (m.epsP β).wt y) ^ 2 / (4 * (m.epsP β).share1 y)
        - (m.epsP β).wt y ^ 2 * (m.epsP β).scale y * inward h (m.epsP β).modes h.ampW ι y
            / (4 * (m.epsP β).share2 y)
        - (m.epsP β).wt y * (|(m.epsP β).frame| + (1 / 2) * (1 + (m.epsP β).t0 y) * h.supVort y
          + (1 / 2) * (m.epsP β).len y * h.supGradVort y
          + (1 / 2) * (m.epsP β).t1 y * inward h (m.epsP β).modes h.ampGradW ι y
          + (1 / 2) * (m.epsP β).t2 y * inward h (m.epsP β).modes h.ampGradVort ι y
          + (1 / 2) * (m.epsP β).t3 y * inward h (m.epsP β).modes h.ampVort ι y)))
    - ∑ β : Fin nE, (m.epsP β).wt y * outward h (m.epsP β).modes h.ampGradW ι y / (2 * (m.epsP β).t1 y)

open Classical in
def coefAA (ι : ℤ × ℤ) (y : Space) : ℝ :=
  m.convZ (m.classOf ι) y - ModeWeights.secondDerivNorm (m.convD (m.classOf ι)) y - m.c * w y
    - (∑ β : Fin nE, (m.epsP β).wt y * (ModeWeights.ind (inPiece (m.epsP β).modes ι) * h.supVort y
        / (2 * (m.epsP β).t0 y) + outward h (m.epsP β).modes h.ampVort ι y / (2 * (m.epsP β).t3 y)))
    - ∑ β : Fin nM, (ModeWeights.ind (inPiece (m.muP β).modes ι)
        * ModeWeights.ind (0 < (m.muP β).wt y + wtGrad (m.muP β).wt y) * (m.muP β).share y
        + (m.muP β).wt y * outward h (m.muP β).modes h.ampW ι y / (2 * (m.muP β).t4 y))

open Classical in
def coefB (ι : ℤ × ℤ) (y : Space) : ℝ :=
  -ModeWeights.secondDerivNorm (m.convZ (m.classOf ι)) y
    - (∑ β : Fin nE, (m.epsP β).wt y * (ModeWeights.ind (inPiece (m.epsP β).modes ι) * h.supGradVort y
        / (2 * (m.epsP β).len y) + outward h (m.epsP β).modes h.ampGradVort ι y / (2 * (m.epsP β).t2 y)))
    + (∑ β : Fin nM, ModeWeights.ind (inPiece (m.muP β).modes ι) *
        ((1 - m.cμ) * (m.muP β).wt y * |frameFreq P (m.muP β).frame ι|
          - ((m.muP β).wt y * (m.muP β).speed y + wtGrad (m.muP β).wt y) ^ 2 / (4 * (m.muP β).share y)
          - (m.muP β).wt y * |(m.muP β).frame|
          - (1 / 2) * (m.muP β).t4 y * (m.muP β).wt y * inward h (m.muP β).modes h.ampW ι y
          - (1 / 2) * (m.muP β).eta * (m.muP β).wt y ^ 2
          - harmonicSum h y * (harmonicSum h y - inward h (m.muP β).modes h.ampGradW ι y) / (2 * (m.muP β).eta)))
    - ∑ β : Fin nM, harmonicSum h y * outward h (m.muP β).modes h.ampGradW ι y / (2 * (m.muP β).eta)

def modeDensity (ι : ℤ × ℤ) (y : Space) (x2 xc x1 xo x0 : ℝ) : ℝ :=
  (m.convD (m.classOf ι) y - m.c) * x2 ^ 2 + (1 - m.shareHat h ι y - m.convD (m.classOf ι) y) * xc ^ 2
    + (m.coefA P h ι y - m.convZ (m.classOf ι) y) * xo ^ 2 + m.coefAA h w ι y * x1 ^ 2
    + m.coefB P h ι y * x0 ^ 2

def modeTerm (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (ι : ℤ × ℤ) (σ : ℝ) (y : Space) : ℝ :=
  m.modeDensity P h w ι y (Real.sqrt (cnormSq (modeSecondDeriv ι H σ y)))
    (Real.sqrt (cnormSq (curlGradOfSecondDeriv (modeSecondDeriv ι H σ y))))
    (Real.sqrt (cnormSq (modeGrad ι G σ y))) (Real.sqrt (cnormSq (curlOfGrad (modeGrad ι G σ y))))
    (Real.sqrt (cnormSq (modeVel ι v σ y)))

def seminormSq (v : ℝ → Space → Space) : ℝ≥0∞ :=
  ∑ β : Fin nM, ∑' ι : ℤ × ℤ, ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y,
    ENNReal.ofReal (|sgn (m.muP β).modes ι| * |frameFreq P (m.muP β).frame ι| * (m.muP β).wt y
      * cnormSq (modeVel ι v σ y))

def IsMultiplierField (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (M : ℝ → Space → Space) : Prop :=
  AEStronglyMeasurable (fun z : ℝ × Space => M z.1 z.2) volume ∧ IsTimePeriodic M ∧
    periodLIntegral (fun σ y => ‖M σ y‖ ^ 2) < ⊤ ∧
    (∀ q, IsPeriodicTestPotential q →
      ∫ σ in Set.Icc (0 : ℝ) 1, ∫ y, inner ℝ (M σ y) (gradientAt (q σ) y) = 0) ∧
    ∀ ψ, IsPeriodicTestField ψ →
      ∫ σ in Set.Icc (0 : ℝ) 1, ∫ y, inner ℝ (M σ y) (ψ σ y) =
        (∫ σ in Set.Icc (0 : ℝ) 1, ∫ y, inner ℝ (-secondDerivTrace (H σ y)) (ψ σ y))
          + ∑' ι : ℤ × ℤ, ∫ σ in Set.Icc (0 : ℝ) 1, ∫ y,
            ((∑ β : Fin nE, (Complex.I * ((sgn (m.epsP β).modes ι * (m.epsP β).wt y : ℝ) : ℂ)
                * cdot (curlOfGrad (modeGrad ι G σ y)) (curlOfGrad (modeGrad ι (gradField ψ) σ y))).re)
              + ∑ β : Fin nM, (Complex.I * ((sgn (m.muP β).modes ι * (m.muP β).wt y : ℝ) : ℂ)
                * cdot (modeVel ι v σ y) (modeVel ι ψ σ y)).re)

def densityPos (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (W : ℝ → Space → Space) (σ : ℝ) (y : Space) :
    ℝ≥0∞ :=
  (∑' ι : ℤ × ℤ, ENNReal.ofReal (m.modeTerm P h w v G H ι σ y)) + ENNReal.ofReal (stretchForm W v G σ y)

def densityNeg (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (W : ℝ → Space → Space) (σ : ℝ) (y : Space) :
    ℝ≥0∞ :=
  (∑' ι : ℤ × ℤ, ENNReal.ofReal (-m.modeTerm P h w v G H ι σ y))
    + ENNReal.ofReal (-stretchForm W v G σ y)

def multiplierGap {k : ℕ} (act : Fin k → ℝ → Space → Space) (v : ℝ → Space → Space)
    (G : ℝ → Space → (Space →L[ℝ] Space)) (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space))
    (κ : Fin k → ℝ) (F M : ℝ → Space → Space) : ℝ :=
  periodPairing F M - m.c * weightedEnergy w G H - m.cμ * (m.seminormSq P v).toReal
    - ∑ i, κ i * periodPairing (act i) M

structure IsAdmissible (W : ℝ → Space → Space) (w₀ epsSup epsGradSup ratio : ℝ) : Prop where
  finite_classes : Finite C
  c_pos : 0 < m.c
  c_lt_one : m.c < 1
  cμ_pos : 0 < m.cμ
  cμ_lt_one : m.cμ < 1
  period_pos : 0 < P
  weight_pos : 0 < w₀
  weight_lower : ∀ y, w₀ ≤ w y
  weight_measurable : Measurable w
  weight_axi : IsAxisymmetric w
  harmonics_neg : ∀ β ∈ h.harmonics, -β ∈ h.harmonics
  harmonics_zero : (0, 0) ∈ h.harmonics
  harmonics_span : ∀ σ y i, W σ y i = ∑ β ∈ h.harmonics, (modeVel β W σ y i).re
  ampW_ge : ∀ β ∈ h.harmonics, ∀ σ y, Real.sqrt (cnormSq (modeVel β W σ y)) ≤ h.ampW β y
  ampGradW_ge : ∀ β ∈ h.harmonics, ∀ σ y,
    Real.sqrt (cnormSq (modeGrad β (gradField W) σ y)) ≤ h.ampGradW β y
  ampVort_ge : ∀ β ∈ h.harmonics, ∀ σ y,
    Real.sqrt (cnormSq (curlOfGrad (modeGrad β (gradField W) σ y))) ≤ h.ampVort β y
  ampGradVort_ge : ∀ β ∈ h.harmonics, ∀ σ y,
    Real.sqrt (cnormSq (curlGradOfSecondDeriv (modeSecondDeriv β (secondDerivField W) σ y))) ≤ h.ampGradVort β y
  supVort_ge : ∀ σ φ y, ‖curlVec (fderiv ℝ (W σ) (axialRot φ y))‖ ≤ h.supVort y
  supGradVort_ge : ∀ σ φ y,
    ‖fderiv ℝ (fun x => curlVec (fderiv ℝ (W σ) x)) (axialRot φ y)‖ ≤ h.supGradVort y
  epsSpeed_ge : ∀ β σ φ y, ‖W σ (axialRot φ y) + (1 / 2 : ℝ) • axialRot φ y
    - (m.epsP β).frame • (-(axialRot φ y 1) • unitVector 0 + axialRot φ y 0 • unitVector 1)‖
      ≤ (m.epsP β).speed y
  muSpeed_ge : ∀ β σ φ y, ‖W σ (axialRot φ y) + (1 / 2 : ℝ) • axialRot φ y
    - (m.muP β).frame • (-(axialRot φ y 1) • unitVector 0 + axialRot φ y 0 • unitVector 1)‖
      ≤ (m.muP β).speed y
  eps_oneSided : ∀ β, ∃ Ωs > 0, ∀ ι ∈ (m.epsP β).modes, Ωs ≤ frameFreq P (m.epsP β).frame ι
  mu_oneSided : ∀ β, ∃ Ωs > 0, ∀ ι ∈ (m.muP β).modes, Ωs ≤ frameFreq P (m.muP β).frame ι
  mu_ratio : ∀ y ι, (∑ β : Fin nM, |sgn (m.muP β).modes ι| * (m.muP β).wt y) ^ 2
    ≤ ratio * ∑ β : Fin nM, |sgn (m.muP β).modes ι| * |frameFreq P (m.muP β).frame ι| * (m.muP β).wt y
  ratio_nonneg : 0 ≤ ratio
  eps_wt_nonneg : ∀ β y, 0 ≤ (m.epsP β).wt y
  mu_wt_nonneg : ∀ β y, 0 ≤ (m.muP β).wt y
  eps_increment : ∀ β, ∃ K, LipschitzWith K (m.epsP β).wt
  mu_increment : ∀ β, ∃ K, LipschitzWith K (m.muP β).wt
  eps_axi : ∀ β, IsAxisymmetric (m.epsP β).wt
  mu_axi : ∀ β, IsAxisymmetric (m.muP β).wt
  eps_sum_le : ∀ y, ∑ β : Fin nE, (m.epsP β).wt y ≤ epsSup
  eps_grad_sum_le : ∀ y, ∑ β : Fin nE, wtGrad (m.epsP β).wt y ≤ epsGradSup
  eps_decay : ∃ B, ∀ β y, ‖y‖ * (m.epsP β).wt y ≤ B
  mu_decay : ∃ B, ∀ β y, (m.muP β).wt y ≤ B ∧ ‖y‖ ^ 2 * (m.muP β).wt y ≤ B
    ∧ ‖y‖ * wtGrad (m.muP β).wt y ≤ B
  eps_free_pos : ∀ β y, 0 < (m.epsP β).share1 y ∧ 0 < (m.epsP β).share2 y ∧ 0 < (m.epsP β).len y
    ∧ 0 < (m.epsP β).t0 y ∧ 0 < (m.epsP β).t1 y ∧ 0 < (m.epsP β).t2 y ∧ 0 < (m.epsP β).t3 y
    ∧ 0 < (m.epsP β).scale y
  mu_free_pos : ∀ β y, 0 < (m.muP β).share y ∧ 0 < (m.muP β).t4 y
  mu_eta_pos : ∀ β, 0 < (m.muP β).eta
  eps_free_measurable : ∀ β, Measurable (m.epsP β).share1 ∧ Measurable (m.epsP β).share2
    ∧ Measurable (m.epsP β).len ∧ Measurable (m.epsP β).t0 ∧ Measurable (m.epsP β).t1
    ∧ Measurable (m.epsP β).t2 ∧ Measurable (m.epsP β).t3 ∧ Measurable (m.epsP β).scale
  mu_free_measurable : ∀ β, Measurable (m.muP β).share ∧ Measurable (m.muP β).t4
  eps_free_axi : ∀ β, IsAxisymmetric (m.epsP β).share1 ∧ IsAxisymmetric (m.epsP β).share2
    ∧ IsAxisymmetric (m.epsP β).len ∧ IsAxisymmetric (m.epsP β).t0 ∧ IsAxisymmetric (m.epsP β).t1
    ∧ IsAxisymmetric (m.epsP β).t2 ∧ IsAxisymmetric (m.epsP β).t3 ∧ IsAxisymmetric (m.epsP β).scale
  mu_free_axi : ∀ β, IsAxisymmetric (m.muP β).share ∧ IsAxisymmetric (m.muP β).t4
  convD_even : ∀ ι y, m.convD (m.classOf (-ι)) y = m.convD (m.classOf ι) y
  convZ_even : ∀ ι y, m.convZ (m.classOf (-ι)) y = m.convZ (m.classOf ι) y
  convD_smooth : ∀ c, ContDiff ℝ 2 (m.convD c)
  convZ_smooth : ∀ c, ContDiff ℝ 2 (m.convZ c)
  convD_nonneg : ∀ c y, 0 ≤ m.convD c y
  convD_axi : ∀ c, IsAxisymmetric (m.convD c)
  convZ_axi : ∀ c, IsAxisymmetric (m.convZ c)
  convD_decay : ∃ B, ∀ c y, ∀ j ≤ 2, ‖y‖ ^ j * ‖iteratedFDeriv ℝ j (m.convD c) y‖ ≤ B
  convZ_decay : ∃ B, ∀ c y, ∀ j ≤ 2, (1 + ‖y‖) ^ j * ‖iteratedFDeriv ℝ j (m.convZ c) y‖ ≤ B
  conv_le : ∀ ι y, m.convD (m.classOf ι) y ≤ 1 - m.shareHat h ι y

end PieceWeights

end Breakdown
