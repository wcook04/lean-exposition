import Breakdown.Cert.CoerciveModeRotation
import Breakdown.Cert.CoerciveRotation

open scoped ENNReal
open MeasureTheory

noncomputable section

namespace Breakdown

namespace Coercive

namespace Internal.FieldModes

open Internal.ModeRotation

abbrev slab : Measure (ℝ × Space) := (volume.restrict (Set.Icc (0 : ℝ) 1)).prod (volume : Measure Space)

def IsSquareField (F : ℝ → Space → Space) : Prop :=
  AEStronglyMeasurable (fun z : ℝ × Space => F z.1 z.2) volume ∧ IsTimePeriodic F ∧
    periodLIntegral (fun σ y => ‖F σ y‖ ^ 2) < ⊤

abbrev orbitDomain : Measure (((ℝ × Space) × ℝ) × ℝ) :=
  ((volume : Measure (ℝ × Space)).prod (volume.restrict (Set.Ioc (0 : ℝ) 1))).prod
    (volume.restrict (Set.Ioc (0 : ℝ) (2 * Real.pi)))

theorem aestronglyMeasurable_orbit {E : Type*} [NormedAddCommGroup E] {u : ℝ × Space → E}
    (hu : AEStronglyMeasurable u volume) :
    AEStronglyMeasurable (fun w : ((ℝ × Space) × ℝ) × ℝ => u (orbitMap (w.1.2, w.2) w.1.1)) orbitDomain := by
  have hRot := axialRotationHolds_proof
  have hS : MeasurePreserving (fun w : (ℝ × ℝ) × (ℝ × Space) => (w.1, orbitMap w.1 w.2))
      (boxMeasure.prod volume) (boxMeasure.prod volume) :=
    (MeasurePreserving.id boxMeasure).skew_product continuous_orbitMap.measurable
      (Filter.Eventually.of_forall fun p => (measurePreserving_orbitMap hRot p).map_eq)
  have hF : AEStronglyMeasurable (fun w : (ℝ × ℝ) × (ℝ × Space) => u (orbitMap w.1 w.2))
      (boxMeasure.prod volume) :=
    hu.comp_snd.comp_measurePreserving hS
  have hE : MeasurePreserving (fun w : ((ℝ × Space) × ℝ) × ℝ => ((w.1.2, w.2), w.1.1))
      orbitDomain (boxMeasure.prod volume) :=
    (Measure.measurePreserving_swap (μ := (volume : Measure (ℝ × Space))) (ν := boxMeasure)).comp
      (measurePreserving_prodAssoc (volume : Measure (ℝ × Space))
        (volume.restrict (Set.Ioc (0 : ℝ) 1)) (volume.restrict (Set.Ioc (0 : ℝ) (2 * Real.pi))))
  exact hF.comp_measurePreserving hE

theorem aestronglyMeasurable_modeAverage {β : Type*} (ι : ℤ × ℤ) (b : β)
    (F : ℝ × Space → ℝ → ℝ → β → ℝ)
    (hF : AEStronglyMeasurable (fun w : ((ℝ × Space) × ℝ) × ℝ => F w.1.1 w.1.2 w.2 b) orbitDomain) :
    AEStronglyMeasurable (fun z : ℝ × Space => modeAverage ι (F z) b) volume := by
  have h1 : AEStronglyMeasurable (fun w : ((ℝ × Space) × ℝ) × ℝ =>
      expFactor ι w.1.2 w.2 * ((F w.1.1 w.1.2 w.2 b : ℝ) : ℂ)) orbitDomain :=
    ((continuous_expFactor ι).comp (continuous_fst.snd.prodMk continuous_snd)).aestronglyMeasurable.mul
      (Complex.continuous_ofReal.comp_aestronglyMeasurable hF)
  have h3 := h1.integral_prod_right'.integral_prod_right'
  refine (h3.const_mul (1 / (2 * Real.pi) : ℂ)).congr (ae_of_all _ fun z => ?_)
  simp only
  rw [modeAverage_eq, intervalIntegral.integral_of_le zero_le_one]
  congr 1
  refine integral_congr_ae (ae_of_all _ fun τ => ?_)
  simp only
  rw [intervalIntegral.integral_of_le (by positivity)]

theorem aestronglyMeasurable_modeAverage_comp {E : Type*} [NormedAddCommGroup E] {β : Type*}
    (ι : ℤ × ℤ) (b : β) (c : ℝ → E → β → ℝ) (hc : Continuous (fun p : ℝ × E => c p.1 p.2 b))
    {Y : ℝ → Space → E} (hY : AEStronglyMeasurable (fun z : ℝ × Space => Y z.1 z.2) volume) :
    AEStronglyMeasurable (fun z : ℝ × Space =>
      modeAverage ι (fun τ φ j => c φ (Y (z.1 + τ) (axialRot φ z.2)) j) b) volume := by
  refine aestronglyMeasurable_modeAverage ι b (fun z τ φ j => c φ (Y (z.1 + τ) (axialRot φ z.2)) j) ?_
  have ho := aestronglyMeasurable_orbit hY
  have hm : AEStronglyMeasurable (fun w : ((ℝ × Space) × ℝ) × ℝ =>
      ((w.2, Y (orbitMap (w.1.2, w.2) w.1.1).1 (orbitMap (w.1.2, w.2) w.1.1).2) : ℝ × E)) orbitDomain :=
    continuous_snd.aestronglyMeasurable.prodMk ho
  exact hc.comp_aestronglyMeasurable hm

theorem aestronglyMeasurable_modeVel {X : ℝ → Space → Space}
    (hX : AEStronglyMeasurable (fun z : ℝ × Space => X z.1 z.2) volume) (ι : ℤ × ℤ) (i : Fin 3) :
    AEStronglyMeasurable (fun z : ℝ × Space => modeVel ι X z.1 z.2 i) volume := by
  have hc : Continuous (fun q : ℝ × Space => axialRot (-q.1) q.2 i) := by
    unfold axialRot
    fun_prop
  exact aestronglyMeasurable_modeAverage_comp ι i (fun φ x j => axialRot (-φ) x j) hc hX

theorem aestronglyMeasurable_modeGrad {G : ℝ → Space → (Space →L[ℝ] Space)}
    (hG : AEStronglyMeasurable (fun z : ℝ × Space => G z.1 z.2) volume) (ι : ℤ × ℤ)
    (ij : Fin 3 × Fin 3) :
    AEStronglyMeasurable (fun z : ℝ × Space => modeGrad ι G z.1 z.2 ij) volume := by
  have hc : Continuous (fun q : ℝ × (Space →L[ℝ] Space) =>
      axialRot (-q.1) (q.2 (axialRot q.1 (unitVector ij.2))) ij.1) := by
    unfold axialRot
    fun_prop
  exact aestronglyMeasurable_modeAverage_comp (E := Space →L[ℝ] Space) ι ij
    (fun (φ : ℝ) (A : Space →L[ℝ] Space) (kl : Fin 3 × Fin 3) =>
      axialRot (-φ) (A (axialRot φ (unitVector kl.2))) kl.1) hc hG

theorem cnormSq_nonneg {β : Type*} [Fintype β] (x : β → ℂ) : 0 ≤ cnormSq x :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)

theorem continuous_cnormSq {β : Type*} [Fintype β] : Continuous (fun x : β → ℂ => cnormSq x) := by
  unfold cnormSq
  fun_prop

theorem slab_eq : slab = (volume : Measure (ℝ × Space)).restrict (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ) := by
  show (volume.restrict (Set.Icc (0 : ℝ) 1)).prod (volume : Measure Space) = _
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict, Measure.restrict_univ]

theorem aemeasurable_modeGrad {G : ℝ → Space → (Space →L[ℝ] Space)}
    (hm : AEStronglyMeasurable (fun z : ℝ × Space => G z.1 z.2) volume) (ι : ℤ × ℤ) :
    AEMeasurable (fun z : ℝ × Space => modeGrad ι G z.1 z.2) slab := by
  rw [slab_eq]
  exact (aemeasurable_pi_iff.2 fun ij => (aestronglyMeasurable_modeGrad hm ι ij).aemeasurable).restrict

theorem aemeasurable_modeVel {X : ℝ → Space → Space}
    (hm : AEStronglyMeasurable (fun z : ℝ × Space => X z.1 z.2) volume) (ι : ℤ × ℤ) :
    AEMeasurable (fun z : ℝ × Space => modeVel ι X z.1 z.2) slab := by
  rw [slab_eq]
  exact (aemeasurable_pi_iff.2 fun i => (aestronglyMeasurable_modeVel hm ι i).aemeasurable).restrict

theorem periodLIntegral_lt_top_of_support {f : ℝ → Space → ℝ}
    (hc : Continuous (fun z : ℝ × Space => f z.1 z.2)) {R : ℝ} (hs : ∀ σ y, R < ‖y‖ → f σ y = 0) :
    periodLIntegral f < ⊤ := by
  have hK : IsCompact (Set.Icc (0 : ℝ) 1 ×ˢ Metric.closedBall (0 : Space) R) :=
    isCompact_Icc.prod (isCompact_closedBall 0 R)
  obtain ⟨Cst, hC⟩ := hK.exists_bound_of_continuousOn hc.continuousOn
  have hpt : ∀ σ ∈ Set.Icc (0 : ℝ) 1, ∀ y, ENNReal.ofReal (f σ y) ≤
      (Metric.closedBall (0 : Space) R).indicator (fun _ => ENNReal.ofReal Cst) y := by
    intro σ hσ y
    by_cases hy : y ∈ Metric.closedBall (0 : Space) R
    · rw [Set.indicator_of_mem hy]
      apply ENNReal.ofReal_le_ofReal
      have := hC (σ, y) ⟨hσ, hy⟩
      exact (le_abs_self _).trans (by simpa [Real.norm_eq_abs] using this)
    · rw [Set.indicator_of_notMem hy]
      have : R < ‖y‖ := by simpa [Metric.mem_closedBall, dist_zero_right, not_le] using hy
      simp [hs σ y this]
  unfold periodLIntegral
  calc ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ENNReal.ofReal (f σ y)
      ≤ ∫⁻ σ in Set.Icc (0 : ℝ) 1, ENNReal.ofReal Cst * volume (Metric.closedBall (0 : Space) R) := by
        refine setLIntegral_mono' measurableSet_Icc (fun σ hσ => ?_)
        calc ∫⁻ y, ENNReal.ofReal (f σ y)
            ≤ ∫⁻ y, (Metric.closedBall (0 : Space) R).indicator (fun _ => ENNReal.ofReal Cst) y :=
              lintegral_mono (hpt σ hσ)
          _ = _ := lintegral_indicator_const measurableSet_closedBall _
    _ < ⊤ := by
        rw [setLIntegral_const]
        exact ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top measure_closedBall_lt_top)
          (by simp)

theorem integrable_cnormSq_modeGrad (hPars : ModeSquareSumHolds) {G : ℝ → Space → (Space →L[ℝ] Space)}
    (hm : AEStronglyMeasurable (fun z : ℝ × Space => G z.1 z.2) volume) (hp : IsTimePeriodic G)
    (h2 : periodLIntegral (fun σ y => matSq (G σ y)) < ⊤) (ι : ℤ × ℤ) :
    Integrable (fun z : ℝ × Space => cnormSq (modeGrad ι G z.1 z.2)) slab := by
  have hmeas : AEMeasurable (fun z : ℝ × Space => cnormSq (modeGrad ι G z.1 z.2)) slab :=
    continuous_cnormSq.measurable.comp_aemeasurable (aemeasurable_modeGrad hm ι)
  have hL : ∫⁻ z, ENNReal.ofReal (cnormSq (modeGrad ι G z.1 z.2)) ∂slab < ⊤ := by
    rw [lintegral_prod _ hmeas.ennreal_ofReal]
    calc ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ENNReal.ofReal (cnormSq (modeGrad ι G (σ, y).1 (σ, y).2))
        ≤ ∑' κ : ℤ × ℤ, ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ENNReal.ofReal (cnormSq (modeGrad κ G σ y)) :=
          ENNReal.le_tsum (f := fun κ : ℤ × ℤ =>
            ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ENNReal.ofReal (cnormSq (modeGrad κ G σ y))) ι
      _ = periodLIntegral (fun σ y => matSq (G σ y)) := (hPars.2.1 G hm hp h2).symm
      _ < ⊤ := h2
  exact (integrable_toReal_of_lintegral_ne_top hmeas.ennreal_ofReal hL.ne).congr
    (ae_of_all _ fun z => ENNReal.toReal_ofReal (cnormSq_nonneg _))

theorem summable_integral_cnormSq_modeGrad (hPars : ModeSquareSumHolds)
    {G : ℝ → Space → (Space →L[ℝ] Space)}
    (hm : AEStronglyMeasurable (fun z : ℝ × Space => G z.1 z.2) volume) (hp : IsTimePeriodic G)
    (h2 : periodLIntegral (fun σ y => matSq (G σ y)) < ⊤) :
    Summable (fun ι : ℤ × ℤ => ∫ z, cnormSq (modeGrad ι G z.1 z.2) ∂slab) := by
  have e : ∀ ι : ℤ × ℤ, (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ENNReal.ofReal (cnormSq (modeGrad ι G σ y))).toReal
      = ∫ z, cnormSq (modeGrad ι G z.1 z.2) ∂slab := by
    intro ι
    have hI := integrable_cnormSq_modeGrad hPars hm hp h2 ι
    rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun z => cnormSq_nonneg _) hI.1,
      lintegral_prod _ hI.1.aemeasurable.ennreal_ofReal]
  refine (ENNReal.summable_toReal ?_).congr e
  rw [← hPars.2.1 G hm hp h2]
  exact h2.ne

theorem integrable_cnormSq_modeVel (hPars : ModeSquareSumHolds) {X : ℝ → Space → Space}
    (hX : IsSquareField X) (ι : ℤ × ℤ) :
    Integrable (fun z : ℝ × Space => cnormSq (modeVel ι X z.1 z.2)) slab := by
  obtain ⟨hm, hp, h2⟩ := hX
  have hmeas : AEMeasurable (fun z : ℝ × Space => cnormSq (modeVel ι X z.1 z.2)) slab :=
    continuous_cnormSq.measurable.comp_aemeasurable (aemeasurable_modeVel hm ι)
  have hL : ∫⁻ z, ENNReal.ofReal (cnormSq (modeVel ι X z.1 z.2)) ∂slab < ⊤ := by
    rw [lintegral_prod _ hmeas.ennreal_ofReal]
    calc ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ENNReal.ofReal (cnormSq (modeVel ι X (σ, y).1 (σ, y).2))
        ≤ ∑' κ : ℤ × ℤ, ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ENNReal.ofReal (cnormSq (modeVel κ X σ y)) :=
          ENNReal.le_tsum (f := fun κ : ℤ × ℤ =>
            ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ENNReal.ofReal (cnormSq (modeVel κ X σ y))) ι
      _ = periodLIntegral (fun σ y => ‖X σ y‖ ^ 2) := (hPars.1 X hm hp h2).symm
      _ < ⊤ := h2
  exact (integrable_toReal_of_lintegral_ne_top hmeas.ennreal_ofReal hL.ne).congr
    (ae_of_all _ fun z => ENNReal.toReal_ofReal (cnormSq_nonneg _))

theorem summable_integral_cnormSq_modeVel (hPars : ModeSquareSumHolds) {X : ℝ → Space → Space}
    (hX : IsSquareField X) :
    Summable (fun ι : ℤ × ℤ => ∫ z, cnormSq (modeVel ι X z.1 z.2) ∂slab) := by
  have e : ∀ ι : ℤ × ℤ, (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ENNReal.ofReal (cnormSq (modeVel ι X σ y))).toReal
      = ∫ z, cnormSq (modeVel ι X z.1 z.2) ∂slab := by
    intro ι
    have hI := integrable_cnormSq_modeVel hPars hX ι
    rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun z => cnormSq_nonneg _) hI.1,
      lintegral_prod _ hI.1.aemeasurable.ennreal_ofReal]
  refine (ENNReal.summable_toReal ?_).congr e
  rw [← hPars.1 X hX.1 hX.2.1 hX.2.2]
  exact hX.2.2.ne

theorem tsum_integral_cnormSq_modeVel (hPars : ModeSquareSumHolds) {X : ℝ → Space → Space}
    (hX : IsSquareField X) :
    ∑' ι : ℤ × ℤ, ∫ z, cnormSq (modeVel ι X z.1 z.2) ∂slab =
      (periodLIntegral (fun σ y => ‖X σ y‖ ^ 2)).toReal := by
  have e : ∀ ι : ℤ × ℤ, ∫ z, cnormSq (modeVel ι X z.1 z.2) ∂slab =
      (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ENNReal.ofReal (cnormSq (modeVel ι X σ y))).toReal := by
    intro ι
    have hI := integrable_cnormSq_modeVel hPars hX ι
    rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun z => cnormSq_nonneg _) hI.1,
      lintegral_prod _ hI.1.aemeasurable.ennreal_ofReal]
  have hP := hPars.1 X hX.1 hX.2.1 hX.2.2
  have hfin : ∀ ι : ℤ × ℤ,
      (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ENNReal.ofReal (cnormSq (modeVel ι X σ y))) ≠ ⊤ := by
    intro ι
    refine ne_top_of_le_ne_top hX.2.2.ne ?_
    rw [hP]
    exact ENNReal.le_tsum (f := fun κ : ℤ × ℤ =>
      ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ENNReal.ofReal (cnormSq (modeVel κ X σ y))) ι
  rw [tsum_congr e, ← ENNReal.tsum_toReal_eq hfin, ← hP]

theorem sq_sqrt_bound {s X Y : ℝ} (hX : 0 ≤ X) (hY : 0 ≤ Y)
    (h : ∀ t : ℝ, 0 < t → s ≤ (t * X + Y / t) / 2) : s ≤ Real.sqrt X * Real.sqrt Y := by
  rcases eq_or_lt_of_le hX with hX0 | hXp
  · rw [← hX0, Real.sqrt_zero, zero_mul]
    by_contra hs
    push Not at hs
    have h1 := h ((Y + 1) / s) (by positivity)
    rw [← hX0, mul_zero, zero_add, div_div_eq_mul_div] at h1
    have h2 : Y * s / (Y + 1) / 2 < s := by
      rw [div_div, div_lt_iff₀ (by positivity)]
      nlinarith
    linarith
  rcases eq_or_lt_of_le hY with hY0 | hYp
  · rw [← hY0, Real.sqrt_zero, mul_zero]
    by_contra hs
    push Not at hs
    have h1 := h (s / X) (by positivity)
    rw [← hY0, zero_div, add_zero, div_mul_cancel₀ _ hXp.ne'] at h1
    linarith
  · have ha := Real.sqrt_pos.2 hXp
    have hb := Real.sqrt_pos.2 hYp
    set a := Real.sqrt X with ha_def
    set c := Real.sqrt Y with hc_def
    have hXa : X = a ^ 2 := (Real.sq_sqrt hX).symm
    have hYc : Y = c ^ 2 := (Real.sq_sqrt hY).symm
    have h1 := h (c / a) (div_pos hb ha)
    rw [hXa, hYc] at h1
    have e : (c / a * a ^ 2 + c ^ 2 / (c / a)) / 2 = a * c := by
      field_simp
      ring
    linarith

theorem sqrt_mul_sqrt_le_of_pos {a c t : ℝ} (ha : 0 ≤ a) (hc : 0 ≤ c) (ht : 0 < t) :
    Real.sqrt a * Real.sqrt c ≤ (t * a + c / t) / 2 := by
  have hx := Real.sq_sqrt ha
  have hy := Real.sq_sqrt hc
  set x := Real.sqrt a
  set y := Real.sqrt c
  have key : 0 ≤ (t * x - y) ^ 2 / t := div_nonneg (sq_nonneg _) ht.le
  have eq : (t * x - y) ^ 2 / t = t * x ^ 2 + y ^ 2 / t - 2 * (x * y) := by
    field_simp
    ring
  rw [← hx, ← hy]
  linarith

theorem tsum_sqrt_mul_le {f h : ℤ × ℤ → ℝ} (hf0 : ∀ i, 0 ≤ f i) (hh0 : ∀ i, 0 ≤ h i)
    (hf : Summable f) (hh : Summable h) :
    Summable (fun i => Real.sqrt (f i) * Real.sqrt (h i)) ∧
      ∑' i, Real.sqrt (f i) * Real.sqrt (h i) ≤ Real.sqrt (∑' i, f i) * Real.sqrt (∑' i, h i) := by
  have amgm : ∀ i, ∀ t : ℝ, 0 < t → Real.sqrt (f i) * Real.sqrt (h i) ≤ (t * f i + h i / t) / 2 :=
    fun i t ht => sqrt_mul_sqrt_le_of_pos (hf0 i) (hh0 i) ht
  have hs : Summable (fun i => Real.sqrt (f i) * Real.sqrt (h i)) := by
    refine Summable.of_nonneg_of_le (fun i => mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
      (fun i => ?_) ((hf.add hh).div_const 2)
    have := amgm i 1 one_pos
    rw [one_mul, div_one] at this
    exact this
  refine ⟨hs, sq_sqrt_bound (tsum_nonneg hf0) (tsum_nonneg hh0) (fun t ht => ?_)⟩
  calc ∑' i, Real.sqrt (f i) * Real.sqrt (h i) ≤ ∑' i, (t * f i + h i / t) / 2 :=
        Summable.tsum_le_tsum (fun i => amgm i t ht) hs (((hf.mul_left t).add (hh.div_const t)).div_const 2)
    _ = (t * ∑' i, f i + (∑' i, h i) / t) / 2 := by
        rw [tsum_div_const, (hf.mul_left t).tsum_add (hh.div_const t), tsum_mul_left, tsum_div_const]

theorem isSquareField_of_continuous {X : ℝ → Space → Space}
    (hc : Continuous (fun z : ℝ × Space => X z.1 z.2)) (hp : IsTimePeriodic X) {R : ℝ}
    (hs : ∀ σ y, R < ‖y‖ → X σ y = 0) : IsSquareField X := by
  refine ⟨hc.aestronglyMeasurable, hp, periodLIntegral_lt_top_of_support
    ((continuous_norm.comp hc).pow 2) (R := R) (fun σ y hy => ?_)⟩
  simp [hs σ y hy]

theorem norm_cdot_le (x z : Fin 3 → ℂ) : ‖cdot x z‖ ≤ (cnormSq x + cnormSq z) / 2 := by
  unfold cdot cnormSq
  refine (norm_sum_le _ _).trans ?_
  rw [← Finset.sum_add_distrib, Finset.sum_div]
  refine Finset.sum_le_sum (fun i _ => ?_)
  rw [norm_mul, Complex.norm_conj]
  nlinarith [sq_nonneg (‖x i‖ - ‖z i‖)]

theorem curlOfGrad_apply (g : Fin 3 × Fin 3 → ℂ) :
    curlOfGrad g 0 = g (2, 1) - g (1, 2) ∧ curlOfGrad g 1 = g (0, 2) - g (2, 0) ∧
      curlOfGrad g 2 = g (1, 0) - g (0, 1) := by
  refine ⟨?_, ?_, ?_⟩ <;> norm_num [curlOfGrad, alternatingSymbol, Fin.sum_univ_three] <;> ring

theorem norm_sub_sq_le (a b : ℂ) : ‖a - b‖ ^ 2 ≤ 2 * ‖a‖ ^ 2 + 2 * ‖b‖ ^ 2 := by
  have h := norm_sub_le a b
  have h2 : ‖a - b‖ ^ 2 ≤ (‖a‖ + ‖b‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h 2
  nlinarith [sq_nonneg (‖a‖ - ‖b‖)]

theorem cnormSq_curlOfGrad_le (g : Fin 3 × Fin 3 → ℂ) : cnormSq (curlOfGrad g) ≤ 2 * cnormSq g := by
  obtain ⟨h0, h1, h2⟩ := curlOfGrad_apply g
  unfold cnormSq
  rw [Fin.sum_univ_three, h0, h1, h2, Fintype.sum_prod_type]
  simp only [Fin.sum_univ_three]
  nlinarith [norm_sub_sq_le (g (2, 1)) (g (1, 2)), norm_sub_sq_le (g (0, 2)) (g (2, 0)),
    norm_sub_sq_le (g (1, 0)) (g (0, 1)), sq_nonneg ‖g (0, 0)‖, sq_nonneg ‖g (1, 1)‖,
    sq_nonneg ‖g (2, 2)‖]

theorem abs_re_I_mul_le (e : ℝ) (c : ℂ) : |(Complex.I * (e : ℂ) * c).re| ≤ |e| * ‖c‖ := by
  refine (Complex.abs_re_le_norm _).trans ?_
  rw [norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]

theorem abs_curlTerm_le (e : ℝ) (a b : Fin 3 × Fin 3 → ℂ) :
    |(Complex.I * (e : ℂ) * cdot (curlOfGrad a) (curlOfGrad b)).re| ≤ |e| * (cnormSq a + cnormSq b) := by
  refine (abs_re_I_mul_le e _).trans (mul_le_mul_of_nonneg_left ?_ (abs_nonneg e))
  refine (norm_cdot_le _ _).trans ?_
  linarith [cnormSq_curlOfGrad_le a, cnormSq_curlOfGrad_le b]

theorem abs_velTerm_le (e : ℝ) (a b : Fin 3 → ℂ) :
    |(Complex.I * (e : ℂ) * cdot a b).re| ≤ |e| * ((cnormSq a + cnormSq b) / 2) :=
  (abs_re_I_mul_le e _).trans (mul_le_mul_of_nonneg_left (norm_cdot_le a b) (abs_nonneg e))

theorem gradField_periodic {ψ : ℝ → Space → Space} (hp : IsTimePeriodic ψ) :
    IsTimePeriodic (gradField ψ) := by
  intro σ y
  unfold gradField
  rw [show ψ (σ + 1) = ψ σ from funext (hp σ)]

theorem gradField_eq_zero {ψ : ℝ → Space → Space} {R : ℝ} (hs : ∀ σ y, R < ‖y‖ → ψ σ y = 0)
    (σ : ℝ) (y : Space) (hy : R < ‖y‖) : gradField ψ σ y = 0 := by
  unfold gradField
  have h : ψ σ =ᶠ[nhds y] fun _ => (0 : Space) := by
    filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hy] with x hx
    exact hs σ x hx
  rw [h.fderiv_eq]
  exact fderiv_const_apply _

def ballPart (R : ℝ) (v : ℝ → Space → Space) (σ : ℝ) (y : Space) : Space :=
  (Metric.closedBall (0 : Space) R).indicator (v σ) y

theorem isSquareField_ballPart (hLoc : PerturbationLocalSquareIntegrabilityHolds)
    {Γ : Set Symmetry} {P : ℝ} {v : ℝ → Space → Space} {G : ℝ → Space → (Space →L[ℝ] Space)}
    {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)} {g : ℝ → Space → Space}
    (hv : IsPerturbation Γ P v G H g) (R : ℝ) : IsSquareField (ballPart R v) := by
  refine ⟨?_, ?_, ?_⟩
  · have e : (fun z : ℝ × Space => ballPart R v z.1 z.2) =
        (Set.univ ×ˢ Metric.closedBall (0 : Space) R).indicator (fun z : ℝ × Space => v z.1 z.2) := by
      funext z
      unfold ballPart Set.indicator
      by_cases h : z.2 ∈ Metric.closedBall (0 : Space) R <;> simp [h]
    rw [e]
    exact hv.measurable_velocity.indicator (MeasurableSet.univ.prod measurableSet_closedBall)
  · intro σ y
    unfold ballPart
    rw [show v (σ + 1) = v σ from funext (hv.periodic_velocity σ)]
  · have e : ∀ σ, ∫⁻ y, ENNReal.ofReal (‖ballPart R v σ y‖ ^ 2) =
        ∫⁻ y in Metric.closedBall (0 : Space) R, ENNReal.ofReal (‖v σ y‖ ^ 2) := by
      intro σ
      rw [← lintegral_indicator measurableSet_closedBall]
      congr 1
      funext y
      unfold ballPart
      by_cases hy : y ∈ Metric.closedBall (0 : Space) R
      · simp only [Set.indicator_of_mem hy]
      · simp only [Set.indicator_of_notMem hy, norm_zero]
        simp
    unfold periodLIntegral
    simp_rw [e]
    exact hLoc Γ P v G H g hv R

theorem modeVel_ballPart {R : ℝ} (v : ℝ → Space → Space) (ι : ℤ × ℤ) (σ : ℝ) {y : Space}
    (hy : ‖y‖ ≤ R) : modeVel ι (ballPart R v) σ y = modeVel ι v σ y := by
  unfold modeVel
  congr 1
  funext τ φ i
  have hm : axialRot φ y ∈ Metric.closedBall (0 : Space) R := by
    rw [mem_closedBall_zero_iff, RotationInternal.axialRot_norm]
    exact hy
  simp only [ballPart, Set.indicator_of_mem hm]

theorem axialRot_zero_vec (φ : ℝ) : axialRot φ (0 : Space) = 0 := by
  simpa using RotationInternal.axialRot_map_smul φ (0 : ℝ) (0 : Space)

theorem modeVel_eq_zero {X : ℝ → Space → Space} {R : ℝ} (hs : ∀ σ y, R < ‖y‖ → X σ y = 0)
    (ι : ℤ × ℤ) (σ : ℝ) {y : Space} (hy : R < ‖y‖) : modeVel ι X σ y = 0 := by
  have h0 : ∀ τ φ, X (σ + τ) (axialRot φ y) = 0 := fun τ φ =>
    hs _ _ (by rw [RotationInternal.axialRot_norm]; exact hy)
  funext i
  simp only [modeVel, modeAverage, h0, axialRot_zero_vec, PiLp.zero_apply, Complex.ofReal_zero, mul_zero,
    intervalIntegral.integral_zero, Pi.zero_apply]

theorem modeGrad_eq_zero {G : ℝ → Space → (Space →L[ℝ] Space)} {R : ℝ}
    (hs : ∀ σ y, R < ‖y‖ → G σ y = 0) (ι : ℤ × ℤ) (σ : ℝ) {y : Space} (hy : R < ‖y‖) :
    modeGrad ι G σ y = 0 := by
  have h0 : ∀ τ φ, G (σ + τ) (axialRot φ y) = 0 := fun τ φ =>
    hs _ _ (by rw [RotationInternal.axialRot_norm]; exact hy)
  funext ij
  simp only [modeGrad, modeAverage, h0, zero_apply, axialRot_zero_vec, PiLp.zero_apply,
    Complex.ofReal_zero, mul_zero, intervalIntegral.integral_zero, Pi.zero_apply]

end Internal.FieldModes

end Coercive

end Breakdown
