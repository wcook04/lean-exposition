import Breakdown.Cert.CoerciveRotation

open scoped ContDiff ENNReal
open MeasureTheory

noncomputable section

namespace Breakdown

namespace Coercive

namespace ModeL2Internal

abbrev slab : Measure (ℝ × Space) := (volume.restrict (Set.Icc (0 : ℝ) 1)).prod (volume : Measure Space)

def IsSquareField (F : ℝ → Space → Space) : Prop :=
  AEStronglyMeasurable (fun z : ℝ × Space => F z.1 z.2) volume ∧ IsTimePeriodic F ∧
    periodLIntegral (fun σ y => ‖F σ y‖ ^ 2) < ⊤

theorem continuous_coord (i : Fin 3) : Continuous (fun y : Space => y i) :=
  (EuclideanSpace.proj i : Space →L[ℝ] ℝ).continuous

theorem continuous_axialRot_pair : Continuous (fun p : ℝ × Space => axialRot p.1 p.2) := by
  have h0 : Continuous (fun p : ℝ × Space => p.2 0) := (continuous_coord 0).comp continuous_snd
  have h1 : Continuous (fun p : ℝ × Space => p.2 1) := (continuous_coord 1).comp continuous_snd
  have h2 : Continuous (fun p : ℝ × Space => p.2 2) := (continuous_coord 2).comp continuous_snd
  have hc : Continuous (fun p : ℝ × Space => Real.cos p.1) := Real.continuous_cos.comp continuous_fst
  have hs : Continuous (fun p : ℝ × Space => Real.sin p.1) := Real.continuous_sin.comp continuous_fst
  unfold axialRot
  exact ((((hc.mul h0).sub (hs.mul h1)).smul continuous_const).add
    (((hs.mul h0).add (hc.mul h1)).smul continuous_const)).add (h2.smul continuous_const)

theorem measurePreserving_shiftRot (τ φ : ℝ) :
    MeasurePreserving (fun z : ℝ × Space => (z.1 + τ, axialRot φ z.2)) volume volume := by
  obtain ⟨R, hRy⟩ := axialRotationHolds_proof.1 φ
  have h1 : MeasurePreserving (Prod.map (· + τ) R) ((volume : Measure ℝ).prod (volume : Measure Space))
      ((volume : Measure ℝ).prod (volume : Measure Space)) :=
    (measurePreserving_add_right (volume : Measure ℝ) τ).prod R.measurePreserving
  have h2 : (fun z : ℝ × Space => (z.1 + τ, axialRot φ z.2)) = Prod.map (· + τ) R := by
    funext z
    simp [Prod.map, hRy]
  rw [h2, Measure.volume_eq_prod]
  exact h1

theorem quasiMeasurePreserving_shiftRot (ν : Measure (ℝ × ℝ)) [SFinite ν] :
    Measure.QuasiMeasurePreserving
      (fun p : (ℝ × Space) × (ℝ × ℝ) => (p.1.1 + p.2.1, axialRot p.2.2 p.1.2))
      ((volume : Measure (ℝ × Space)).prod ν) volume := by
  have hpair : Continuous (fun p : (ℝ × Space) × (ℝ × ℝ) => (p.2.2, p.1.2)) :=
    continuous_snd.snd.prodMk continuous_fst.snd
  have hc : Continuous (fun p : (ℝ × Space) × (ℝ × ℝ) => axialRot p.2.2 p.1.2) := by
    have h := continuous_axialRot_pair.comp hpair
    exact h
  have hm : Measurable (fun p : (ℝ × Space) × (ℝ × ℝ) => (p.1.1 + p.2.1, axialRot p.2.2 p.1.2)) :=
    ((continuous_fst.fst.add continuous_snd.fst).prodMk hc).measurable
  refine ⟨hm, ?_⟩
  refine Measure.AbsolutelyContinuous.mk fun N hN h0 => ?_
  rw [Measure.map_apply hm hN, Measure.prod_apply_symm (hm hN)]
  have hz : ∀ b : ℝ × ℝ, (volume : Measure (ℝ × Space))
      ((fun x => (x, b)) ⁻¹' ((fun p : (ℝ × Space) × (ℝ × ℝ) =>
        (p.1.1 + p.2.1, axialRot p.2.2 p.1.2)) ⁻¹' N)) = 0 := fun b => by
    change (volume : Measure (ℝ × Space)) ((fun z : ℝ × Space => (z.1 + b.1, axialRot b.2 z.2)) ⁻¹' N) = 0
    rw [(measurePreserving_shiftRot b.1 b.2).measure_preimage hN.nullMeasurableSet, h0]
  simp [hz]

theorem quasiMeasurePreserving_shiftRot_nested :
    Measure.QuasiMeasurePreserving
      (fun p : ((ℝ × Space) × ℝ) × ℝ => (p.1.1.1 + p.1.2, axialRot p.2 p.1.1.2))
      (((volume : Measure (ℝ × Space)).prod volume).prod volume) volume :=
  (quasiMeasurePreserving_shiftRot ((volume : Measure ℝ).prod (volume : Measure ℝ))).comp
    (measurePreserving_prodAssoc (volume : Measure (ℝ × Space)) (volume : Measure ℝ)
      (volume : Measure ℝ)).quasiMeasurePreserving

theorem aestronglyMeasurable_comp_shiftRot_nested
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (c : ℝ → E → ℝ)
    (hc : Continuous (fun p : ℝ × E => c p.1 p.2)) (Y : ℝ → Space → E)
    (hY : AEStronglyMeasurable (fun z : ℝ × Space => Y z.1 z.2) volume) :
    AEStronglyMeasurable
      (fun p : ((ℝ × Space) × ℝ) × ℝ => c p.2 (Y (p.1.1.1 + p.1.2) (axialRot p.2 p.1.1.2)))
      (((volume : Measure (ℝ × Space)).prod volume).prod volume) := by
  have h1 := hY.comp_quasiMeasurePreserving quasiMeasurePreserving_shiftRot_nested
  have h2 : AEStronglyMeasurable (fun p : ((ℝ × Space) × ℝ) × ℝ => p.2)
      (((volume : Measure (ℝ × Space)).prod volume).prod volume) := continuous_snd.aestronglyMeasurable
  exact hc.comp_aestronglyMeasurable (h2.prodMk h1)

theorem aestronglyMeasurable_modeAverage (ι : ℤ × ℤ) (f : ((ℝ × Space) × ℝ) × ℝ → ℝ)
    (hf : AEStronglyMeasurable f (((volume : Measure (ℝ × Space)).prod volume).prod volume)) :
    AEStronglyMeasurable (fun z : ℝ × Space => modeAverage ι (fun τ φ (_ : Unit) => f ((z, τ), φ)) ())
      volume := by
  unfold modeAverage
  simp only [intervalIntegral.integral_of_le zero_le_one,
    intervalIntegral.integral_of_le (by positivity : (0 : ℝ) ≤ 2 * Real.pi)]
  refine aestronglyMeasurable_const.mul ?_
  have hac : (((volume : Measure (ℝ × Space)).prod (volume.restrict (Set.Ioc (0 : ℝ) 1))).prod
      (volume.restrict (Set.Ioc (0 : ℝ) (2 * Real.pi)))) ≪
      (((volume : Measure (ℝ × Space)).prod volume).prod volume) :=
    (Measure.AbsolutelyContinuous.rfl.prod (Measure.absolutelyContinuous_of_le Measure.restrict_le_self)).prod
      (Measure.absolutelyContinuous_of_le Measure.restrict_le_self)
  have h1 : AEStronglyMeasurable (fun p : ((ℝ × Space) × ℝ) × ℝ =>
      Complex.exp (-(((2 * Real.pi * ι.1 * p.1.2 + ι.2 * p.2 : ℝ) : ℂ) * Complex.I)) * ((f p : ℝ) : ℂ))
      (((volume : Measure (ℝ × Space)).prod (volume.restrict (Set.Ioc (0 : ℝ) 1))).prod
        (volume.restrict (Set.Ioc (0 : ℝ) (2 * Real.pi)))) := by
    refine (Continuous.aestronglyMeasurable (by fun_prop)).mul ?_
    exact Complex.continuous_ofReal.comp_aestronglyMeasurable (hf.mono_ac hac)
  exact h1.integral_prod_right'.integral_prod_right'

theorem continuous_rotCoord (i : Fin 3) : Continuous (fun p : ℝ × Space => axialRot (-p.1) p.2 i) := by
  have h1 : Continuous (fun p : ℝ × Space => (-p.1, p.2)) := continuous_fst.neg.prodMk continuous_snd
  have h2 := continuous_axialRot_pair.comp h1
  have h3 := (continuous_coord i).comp h2
  exact h3

theorem continuous_rotGradCoord (ij : Fin 3 × Fin 3) :
    Continuous (fun p : ℝ × (Space →L[ℝ] Space) =>
      axialRot (-p.1) (p.2 (axialRot p.1 (unitVector ij.2))) ij.1) := by
  have h0 : Continuous (fun p : ℝ × (Space →L[ℝ] Space) => (p.1, unitVector ij.2)) :=
    continuous_fst.prodMk continuous_const
  have h1 := continuous_axialRot_pair.comp h0
  have h2 : Continuous (fun p : ℝ × (Space →L[ℝ] Space) => p.2 (axialRot p.1 (unitVector ij.2))) :=
    continuous_snd.clm_apply h1
  have h3 : Continuous (fun p : ℝ × (Space →L[ℝ] Space) => (-p.1, p.2 (axialRot p.1 (unitVector ij.2)))) :=
    continuous_fst.neg.prodMk h2
  have h4 := continuous_axialRot_pair.comp h3
  have h5 := (continuous_coord ij.1).comp h4
  exact h5

theorem aestronglyMeasurable_modeVel {X : ℝ → Space → Space}
    (hX : AEStronglyMeasurable (fun z : ℝ × Space => X z.1 z.2) volume) (ι : ℤ × ℤ) (i : Fin 3) :
    AEStronglyMeasurable (fun z : ℝ × Space => modeVel ι X z.1 z.2 i) volume := by
  have h := aestronglyMeasurable_modeAverage ι
    (fun p : ((ℝ × Space) × ℝ) × ℝ => axialRot (-p.2) (X (p.1.1.1 + p.1.2) (axialRot p.2 p.1.1.2)) i)
    (aestronglyMeasurable_comp_shiftRot_nested (fun φ e => axialRot (-φ) e i) (continuous_rotCoord i) X hX)
  exact h

theorem aestronglyMeasurable_modeGrad {G : ℝ → Space → (Space →L[ℝ] Space)}
    (hG : AEStronglyMeasurable (fun z : ℝ × Space => G z.1 z.2) volume) (ι : ℤ × ℤ) (ij : Fin 3 × Fin 3) :
    AEStronglyMeasurable (fun z : ℝ × Space => modeGrad ι G z.1 z.2 ij) volume := by
  have h := aestronglyMeasurable_modeAverage ι
    (fun p : ((ℝ × Space) × ℝ) × ℝ =>
      axialRot (-p.2) (G (p.1.1.1 + p.1.2) (axialRot p.2 p.1.1.2) (axialRot p.2 (unitVector ij.2))) ij.1)
    (aestronglyMeasurable_comp_shiftRot_nested
      (fun (φ : ℝ) (A : Space →L[ℝ] Space) => axialRot (-φ) (A (axialRot φ (unitVector ij.2))) ij.1)
      (continuous_rotGradCoord ij) G hG)
  exact h

theorem slab_ac : slab ≪ (volume : Measure (ℝ × Space)) := by
  rw [Measure.volume_eq_prod]
  exact Measure.AbsolutelyContinuous.prod (Measure.absolutelyContinuous_of_le Measure.restrict_le_self)
    Measure.AbsolutelyContinuous.rfl

theorem slab_ae_mem : ∀ᵐ z ∂slab, z.1 ∈ Set.Icc (0 : ℝ) 1 := by
  rw [ae_iff]
  have e : {a : ℝ × Space | ¬ a.1 ∈ Set.Icc (0 : ℝ) 1} = (Set.Icc (0 : ℝ) 1)ᶜ ×ˢ Set.univ := by
    ext a
    simp
  rw [e, Measure.prod_prod, Measure.restrict_apply measurableSet_Icc.compl, Set.compl_inter_self,
    measure_empty, zero_mul]

theorem periodLIntegral_eq_slab (f : ℝ → Space → ℝ)
    (hf : AEStronglyMeasurable (fun z : ℝ × Space => f z.1 z.2) slab) :
    periodLIntegral f = ∫⁻ z, ENNReal.ofReal (f z.1 z.2) ∂slab := by
  have hm : AEMeasurable (fun z : ℝ × Space => ENNReal.ofReal (f z.1 z.2)) slab :=
    hf.aemeasurable.ennreal_ofReal
  unfold periodLIntegral
  rw [lintegral_prod _ hm]

theorem toReal_periodLIntegral (f : ℝ → Space → ℝ)
    (hf : AEStronglyMeasurable (fun z : ℝ × Space => f z.1 z.2) slab) (hnn : ∀ σ y, 0 ≤ f σ y) :
    (periodLIntegral f).toReal = ∫ z, f z.1 z.2 ∂slab := by
  rw [periodLIntegral_eq_slab f hf]
  exact (integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun (z : ℝ × Space) => hnn z.1 z.2) hf).symm

theorem integrable_of_periodLIntegral (f : ℝ → Space → ℝ)
    (hf : AEStronglyMeasurable (fun z : ℝ × Space => f z.1 z.2) slab) (hnn : ∀ σ y, 0 ≤ f σ y)
    (hfin : periodLIntegral f < ⊤) : Integrable (fun z : ℝ × Space => f z.1 z.2) slab := by
  rw [periodLIntegral_eq_slab f hf] at hfin
  exact (lintegral_ofReal_ne_top_iff_integrable hf (ae_of_all _ fun (z : ℝ × Space) => hnn z.1 z.2)).1 hfin.ne

theorem cnormSq_nonneg {β : Type*} [Fintype β] (x : β → ℂ) : 0 ≤ cnormSq x :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem cdot_sub_right (a b c : Fin 3 → ℂ) : cdot a b - cdot a c = cdot a (b - c) := by
  unfold cdot
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Pi.sub_apply, map_sub, mul_sub]

theorem cnormSq_sub (a b : Fin 3 → ℂ) :
    cnormSq (a - b) = cnormSq a + cnormSq b - 2 * (cdot a b).re := by
  unfold cnormSq cdot
  rw [Complex.re_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Pi.sub_apply, Complex.sq_norm, Complex.normSq_sub]

theorem mul_le_half_sq (x y : ℝ) {t : ℝ} (ht : 0 < t) : x * y ≤ (t * x ^ 2 + y ^ 2 / t) / 2 := by
  have h : (t * x ^ 2 + y ^ 2 / t) / 2 = (t * x ^ 2 * t + y ^ 2) / (2 * t) := by
    field_simp
  rw [h, le_div_iff₀ (by positivity)]
  nlinarith [sq_nonneg (t * x - y)]

theorem norm_cdot_le (a b : Fin 3 → ℂ) {t : ℝ} (ht : 0 < t) :
    ‖cdot a b‖ ≤ (t * cnormSq a + cnormSq b / t) / 2 := by
  unfold cdot cnormSq
  calc ‖∑ i, a i * (starRingEnd ℂ) (b i)‖ ≤ ∑ i, ‖a i * (starRingEnd ℂ) (b i)‖ := norm_sum_le _ _
    _ = ∑ i, ‖a i‖ * ‖b i‖ := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [norm_mul, Complex.norm_conj]
    _ ≤ ∑ i, (t * ‖a i‖ ^ 2 + ‖b i‖ ^ 2 / t) / 2 :=
        Finset.sum_le_sum fun i _ => mul_le_half_sq _ _ ht
    _ = (t * ∑ i, ‖a i‖ ^ 2 + (∑ i, ‖b i‖ ^ 2) / t) / 2 := by
        rw [← Finset.sum_div, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_div]

theorem abs_re_weighted_le (w : ℝ) (a b : Fin 3 → ℂ) {t : ℝ} (ht : 0 < t) :
    |(Complex.I * (w : ℂ) * cdot a b).re| ≤ |w| * ((t * cnormSq a + cnormSq b / t) / 2) := by
  refine (Complex.abs_re_le_norm _).trans ?_
  rw [norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (norm_cdot_le a b ht) (abs_nonneg w)

theorem aestronglyMeasurable_cdot {μ : Measure (ℝ × Space)} {a b : ℝ × Space → Fin 3 → ℂ}
    (ha : ∀ i, AEStronglyMeasurable (fun z => a z i) μ) (hb : ∀ i, AEStronglyMeasurable (fun z => b z i) μ) :
    AEStronglyMeasurable (fun z => cdot (a z) (b z)) μ := by
  unfold cdot
  exact Finset.aestronglyMeasurable_fun_sum _
    (fun i _ => (ha i).mul (Complex.continuous_conj.comp_aestronglyMeasurable (hb i)))

theorem aestronglyMeasurable_cnormSq {μ : Measure (ℝ × Space)} {a : ℝ × Space → Fin 3 → ℂ}
    (ha : ∀ i, AEStronglyMeasurable (fun z => a z i) μ) :
    AEStronglyMeasurable (fun z => cnormSq (a z)) μ := by
  unfold cnormSq
  exact Finset.aestronglyMeasurable_fun_sum _ (fun i _ => (ha i).norm.pow 2)

theorem integrable_cnormSq_modeVel (hPars : ModeSquareSumHolds) {X : ℝ → Space → Space}
    (hX : IsSquareField X) (ι : ℤ × ℤ) :
    Integrable (fun z : ℝ × Space => cnormSq (modeVel ι X z.1 z.2)) slab := by
  have hP := hPars.1 X hX.1 hX.2.1 hX.2.2
  have hm : AEStronglyMeasurable (fun z : ℝ × Space => cnormSq (modeVel ι X z.1 z.2)) slab :=
    (aestronglyMeasurable_cnormSq (fun i => aestronglyMeasurable_modeVel hX.1 ι i)).mono_ac slab_ac
  have hle : periodLIntegral (fun σ y => cnormSq (modeVel ι X σ y)) ≤
      periodLIntegral (fun σ y => ‖X σ y‖ ^ 2) := by
    rw [hP]
    exact ENNReal.le_tsum ι
  exact integrable_of_periodLIntegral (fun σ y => cnormSq (modeVel ι X σ y)) hm
    (fun σ y => cnormSq_nonneg _) (lt_of_le_of_lt hle hX.2.2)

theorem hasSum_cnormSq_modeVel (hPars : ModeSquareSumHolds) {X : ℝ → Space → Space}
    (hX : IsSquareField X) :
    HasSum (fun ι : ℤ × ℤ => ∫ z, cnormSq (modeVel ι X z.1 z.2) ∂slab)
      (periodLIntegral (fun σ y => ‖X σ y‖ ^ 2)).toReal := by
  have hP := hPars.1 X hX.1 hX.2.1 hX.2.2
  have hm : ∀ ι : ℤ × ℤ, AEStronglyMeasurable (fun z : ℝ × Space => cnormSq (modeVel ι X z.1 z.2)) slab :=
    fun ι => (aestronglyMeasurable_cnormSq (fun i => aestronglyMeasurable_modeVel hX.1 ι i)).mono_ac slab_ac
  have hP' : periodLIntegral (fun σ y => ‖X σ y‖ ^ 2) =
      ∑' ι : ℤ × ℤ, periodLIntegral (fun σ y => cnormSq (modeVel ι X σ y)) := hP
  have hA : ∀ ι : ℤ × ℤ, periodLIntegral (fun σ y => cnormSq (modeVel ι X σ y)) ≠ ⊤ := fun ι =>
    ne_top_of_le_ne_top hX.2.2.ne (hP' ▸ ENNReal.le_tsum ι)
  have hfun : (fun ι : ℤ × ℤ => ∫ z, cnormSq (modeVel ι X z.1 z.2) ∂slab) =
      fun ι => (periodLIntegral (fun σ y => cnormSq (modeVel ι X σ y))).toReal :=
    funext fun ι => (toReal_periodLIntegral (fun σ y => cnormSq (modeVel ι X σ y)) (hm ι)
      (fun σ y => cnormSq_nonneg _)).symm
  rw [hfun, hP', ENNReal.tsum_toReal_eq hA]
  exact (ENNReal.summable_toReal (hP' ▸ hX.2.2.ne)).hasSum

theorem integrable_re_cdot_modeVel (hPars : ModeSquareSumHolds) {X Y : ℝ → Space → Space}
    (hX : IsSquareField X) (hY : IsSquareField Y) (ι : ℤ × ℤ) :
    Integrable (fun z : ℝ × Space => (cdot (modeVel ι X z.1 z.2) (modeVel ι Y z.1 z.2)).re) slab := by
  have hm : AEStronglyMeasurable (fun z : ℝ × Space => (cdot (modeVel ι X z.1 z.2) (modeVel ι Y z.1 z.2)).re)
      slab :=
    (Complex.continuous_re.comp_aestronglyMeasurable (aestronglyMeasurable_cdot
      (fun i => aestronglyMeasurable_modeVel hX.1 ι i) (fun i => aestronglyMeasurable_modeVel hY.1 ι i))).mono_ac
      slab_ac
  refine ((integrable_cnormSq_modeVel hPars hX ι).add (integrable_cnormSq_modeVel hPars hY ι)).mono' hm
    (ae_of_all _ fun z => ?_)
  rw [Real.norm_eq_abs]
  have h1 := (Complex.abs_re_le_norm (cdot (modeVel ι X z.1 z.2) (modeVel ι Y z.1 z.2))).trans
    (norm_cdot_le (modeVel ι X z.1 z.2) (modeVel ι Y z.1 z.2) one_pos)
  have h2 := cnormSq_nonneg (modeVel ι X z.1 z.2)
  have h3 := cnormSq_nonneg (modeVel ι Y z.1 z.2)
  simp only [one_mul, div_one] at h1
  show _ ≤ cnormSq (modeVel ι X z.1 z.2) + cnormSq (modeVel ι Y z.1 z.2)
  linarith

theorem integrable_cnormSq_modeVel_sub (hPars : ModeSquareSumHolds) {X Y : ℝ → Space → Space}
    (hX : IsSquareField X) (hY : IsSquareField Y) (ι : ℤ × ℤ) :
    Integrable (fun z : ℝ × Space => cnormSq (modeVel ι X z.1 z.2 - modeVel ι Y z.1 z.2)) slab := by
  refine (((integrable_cnormSq_modeVel hPars hX ι).add (integrable_cnormSq_modeVel hPars hY ι)).sub
    ((integrable_re_cdot_modeVel hPars hX hY ι).const_mul 2)).congr (ae_of_all _ fun z => ?_)
  exact (cnormSq_sub _ _).symm

theorem hasSum_cnormSq_modeVel_sub (hPars : ModeSquareSumHolds) {X Y : ℝ → Space → Space}
    (hX : IsSquareField X) (hY : IsSquareField Y) :
    HasSum (fun ι : ℤ × ℤ => ∫ z, cnormSq (modeVel ι X z.1 z.2 - modeVel ι Y z.1 z.2) ∂slab)
      (periodLIntegral (fun σ y => ‖X σ y - Y σ y‖ ^ 2)).toReal := by
  have hsX := hasSum_cnormSq_modeVel hPars hX
  have hsY := hasSum_cnormSq_modeVel hPars hY
  have hpol := hPars.2.2.2 X Y hX.1 hY.1 hX.2.1 hY.2.1 hX.2.2 hY.2.2
  have hterm : ∀ ι : ℤ × ℤ, ∫ z, cnormSq (modeVel ι X z.1 z.2 - modeVel ι Y z.1 z.2) ∂slab =
      (∫ z, cnormSq (modeVel ι X z.1 z.2) ∂slab) + (∫ z, cnormSq (modeVel ι Y z.1 z.2) ∂slab)
        - 2 * ∫ σ in Set.Icc (0 : ℝ) 1, ∫ y, (cdot (modeVel ι X σ y) (modeVel ι Y σ y)).re := by
    intro ι
    have hiX := integrable_cnormSq_modeVel hPars hX ι
    have hiY := integrable_cnormSq_modeVel hPars hY ι
    have hiR := integrable_re_cdot_modeVel hPars hX hY ι
    have e1 : ∫ σ in Set.Icc (0 : ℝ) 1, ∫ y, (cdot (modeVel ι X σ y) (modeVel ι Y σ y)).re =
        ∫ z, (cdot (modeVel ι X z.1 z.2) (modeVel ι Y z.1 z.2)).re ∂slab := (integral_prod _ hiR).symm
    have hS : Integrable (fun z : ℝ × Space => cnormSq (modeVel ι X z.1 z.2) + cnormSq (modeVel ι Y z.1 z.2))
        slab := hiX.add hiY
    rw [e1, ← integral_const_mul, ← integral_add hiX hiY, ← integral_sub hS (hiR.const_mul 2)]
    exact integral_congr_ae (ae_of_all _ fun z => cnormSq_sub _ _)
  have hmX : AEStronglyMeasurable (fun z : ℝ × Space => X z.1 z.2) slab := hX.1.mono_ac slab_ac
  have hmY : AEStronglyMeasurable (fun z : ℝ × Space => Y z.1 z.2) slab := hY.1.mono_ac slab_ac
  have hnX := integrable_of_periodLIntegral (fun σ y => ‖X σ y‖ ^ 2) (hmX.norm.pow 2)
    (fun _ _ => sq_nonneg _) hX.2.2
  have hnY := integrable_of_periodLIntegral (fun σ y => ‖Y σ y‖ ^ 2) (hmY.norm.pow 2)
    (fun _ _ => sq_nonneg _) hY.2.2
  have hin : Integrable (fun z : ℝ × Space => inner ℝ (X z.1 z.2) (Y z.1 z.2)) slab := by
    refine (hnX.add hnY).mono' (hmX.inner hmY) (ae_of_all _ fun z => ?_)
    rw [Real.norm_eq_abs]
    have h1 := abs_real_inner_le_norm (X z.1 z.2) (Y z.1 z.2)
    have h2 := norm_nonneg (X z.1 z.2)
    have h3 := norm_nonneg (Y z.1 z.2)
    show _ ≤ ‖X z.1 z.2‖ ^ 2 + ‖Y z.1 z.2‖ ^ 2
    nlinarith [sq_nonneg (‖X z.1 z.2‖ - ‖Y z.1 z.2‖)]
  have hval : (periodLIntegral (fun σ y => ‖X σ y - Y σ y‖ ^ 2)).toReal =
      (periodLIntegral (fun σ y => ‖X σ y‖ ^ 2)).toReal + (periodLIntegral (fun σ y => ‖Y σ y‖ ^ 2)).toReal
        - 2 * ∫ σ in Set.Icc (0 : ℝ) 1, ∫ y, inner ℝ (X σ y) (Y σ y) := by
    have e1 : ∫ σ in Set.Icc (0 : ℝ) 1, ∫ y, inner ℝ (X σ y) (Y σ y) =
        ∫ z, inner ℝ (X z.1 z.2) (Y z.1 z.2) ∂slab := (integral_prod _ hin).symm
    have hS : Integrable (fun z : ℝ × Space => ‖X z.1 z.2‖ ^ 2 + ‖Y z.1 z.2‖ ^ 2) slab := hnX.add hnY
    have hmD : AEStronglyMeasurable (fun z : ℝ × Space => ‖X z.1 z.2 - Y z.1 z.2‖ ^ 2) slab :=
      (hmX.sub hmY).norm.pow 2
    rw [e1, toReal_periodLIntegral (fun σ y => ‖X σ y - Y σ y‖ ^ 2) hmD (fun _ _ => sq_nonneg _),
      toReal_periodLIntegral (fun σ y => ‖X σ y‖ ^ 2) (hmX.norm.pow 2) (fun _ _ => sq_nonneg _),
      toReal_periodLIntegral (fun σ y => ‖Y σ y‖ ^ 2) (hmY.norm.pow 2) (fun _ _ => sq_nonneg _),
      ← integral_const_mul, ← integral_add hnX hnY, ← integral_sub hS (hin.const_mul 2)]
    refine integral_congr_ae (ae_of_all _ fun z => ?_)
    show ‖X z.1 z.2 - Y z.1 z.2‖ ^ 2 = ‖X z.1 z.2‖ ^ 2 + ‖Y z.1 z.2‖ ^ 2 - 2 * inner ℝ (X z.1 z.2) (Y z.1 z.2)
    rw [norm_sub_sq_real]
    ring
  rw [funext hterm, hval]
  exact (hsX.add hsY).sub (hpol.mul_left 2)

def weightedModeTerm (wt : ℤ × ℤ → Space → ℝ) (U X : ℝ → Space → Space) (ι : ℤ × ℤ) : ℝ :=
  ∫ σ in Set.Icc (0 : ℝ) 1, ∫ y, (Complex.I * (wt ι y : ℂ) * cdot (modeVel ι U σ y) (modeVel ι X σ y)).re

theorem integrable_weightedMode (hPars : ModeSquareSumHolds) (wt : ℤ × ℤ → Space → ℝ)
    (hwm : ∀ ι, Measurable (wt ι)) {B : ℝ} (hB : ∀ ι y, |wt ι y| ≤ B) {U X : ℝ → Space → Space}
    (hU : IsSquareField U) (hX : IsSquareField X) (ι : ℤ × ℤ) :
    Integrable (fun z : ℝ × Space =>
      (Complex.I * (wt ι z.2 : ℂ) * cdot (modeVel ι U z.1 z.2) (modeVel ι X z.1 z.2)).re) slab := by
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB ι 0)
  have hw : AEStronglyMeasurable (fun z : ℝ × Space => ((wt ι z.2 : ℝ) : ℂ)) slab :=
    (Complex.measurable_ofReal.comp ((hwm ι).comp measurable_snd)).aestronglyMeasurable
  have hc : AEStronglyMeasurable (fun z : ℝ × Space => cdot (modeVel ι U z.1 z.2) (modeVel ι X z.1 z.2)) slab :=
    (aestronglyMeasurable_cdot (fun i => aestronglyMeasurable_modeVel hU.1 ι i)
      (fun i => aestronglyMeasurable_modeVel hX.1 ι i)).mono_ac slab_ac
  have hm : AEStronglyMeasurable (fun z : ℝ × Space =>
      (Complex.I * (wt ι z.2 : ℂ) * cdot (modeVel ι U z.1 z.2) (modeVel ι X z.1 z.2)).re) slab :=
    Complex.continuous_re.comp_aestronglyMeasurable ((aestronglyMeasurable_const.mul hw).mul hc)
  refine (((integrable_cnormSq_modeVel hPars hU ι).add (integrable_cnormSq_modeVel hPars hX ι)).const_mul B).mono'
    hm (ae_of_all _ fun z => ?_)
  rw [Real.norm_eq_abs]
  have h1 := abs_re_weighted_le (wt ι z.2) (modeVel ι U z.1 z.2) (modeVel ι X z.1 z.2) one_pos
  have h2 := cnormSq_nonneg (modeVel ι U z.1 z.2)
  have h3 := cnormSq_nonneg (modeVel ι X z.1 z.2)
  simp only [one_mul, div_one] at h1
  show _ ≤ B * (cnormSq (modeVel ι U z.1 z.2) + cnormSq (modeVel ι X z.1 z.2))
  have h4 : |wt ι z.2| * ((cnormSq (modeVel ι U z.1 z.2) + cnormSq (modeVel ι X z.1 z.2)) / 2) ≤
      B * (cnormSq (modeVel ι U z.1 z.2) + cnormSq (modeVel ι X z.1 z.2)) :=
    mul_le_mul (hB ι z.2) (by linarith) (by positivity) hB0
  linarith

theorem weightedModeTerm_eq (hPars : ModeSquareSumHolds) (wt : ℤ × ℤ → Space → ℝ)
    (hwm : ∀ ι, Measurable (wt ι)) {B : ℝ} (hB : ∀ ι y, |wt ι y| ≤ B) {U X : ℝ → Space → Space}
    (hU : IsSquareField U) (hX : IsSquareField X) (ι : ℤ × ℤ) :
    weightedModeTerm wt U X ι = ∫ z, (Complex.I * (wt ι z.2 : ℂ)
      * cdot (modeVel ι U z.1 z.2) (modeVel ι X z.1 z.2)).re ∂slab :=
  (integral_prod _ (integrable_weightedMode hPars wt hwm hB hU hX ι)).symm

theorem weightedModeTerm_sub_le (hPars : ModeSquareSumHolds) (wt : ℤ × ℤ → Space → ℝ)
    (hwm : ∀ ι, Measurable (wt ι)) {B : ℝ} (hB : ∀ ι y, |wt ι y| ≤ B) {U X Y : ℝ → Space → Space}
    (hU : IsSquareField U) (hX : IsSquareField X) (hY : IsSquareField Y) (ι : ℤ × ℤ) {t : ℝ} (ht : 0 < t) :
    |weightedModeTerm wt U X ι - weightedModeTerm wt U Y ι| ≤
      B / 2 * (t * ∫ z, cnormSq (modeVel ι U z.1 z.2) ∂slab
        + (∫ z, cnormSq (modeVel ι X z.1 z.2 - modeVel ι Y z.1 z.2) ∂slab) / t) := by
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB ι 0)
  have hiU := integrable_cnormSq_modeVel hPars hU ι
  have hiD := integrable_cnormSq_modeVel_sub hPars hX hY ι
  have hiX := integrable_weightedMode hPars wt hwm hB hU hX ι
  have hiY := integrable_weightedMode hPars wt hwm hB hU hY ι
  have hg : Integrable (fun z : ℝ × Space => B / 2 * (t * cnormSq (modeVel ι U z.1 z.2)
      + cnormSq (modeVel ι X z.1 z.2 - modeVel ι Y z.1 z.2) / t)) slab :=
    ((hiU.const_mul t).add (hiD.div_const t)).const_mul (B / 2)
  rw [weightedModeTerm_eq hPars wt hwm hB hU hX, weightedModeTerm_eq hPars wt hwm hB hU hY,
    ← integral_sub hiX hiY]
  refine (abs_integral_le_integral_abs).trans ?_
  have hle : ∫ z, |(Complex.I * (wt ι z.2 : ℂ) * cdot (modeVel ι U z.1 z.2) (modeVel ι X z.1 z.2)).re
      - (Complex.I * (wt ι z.2 : ℂ) * cdot (modeVel ι U z.1 z.2) (modeVel ι Y z.1 z.2)).re| ∂slab ≤
      ∫ z, B / 2 * (t * cnormSq (modeVel ι U z.1 z.2)
        + cnormSq (modeVel ι X z.1 z.2 - modeVel ι Y z.1 z.2) / t) ∂slab := by
    refine integral_mono (hiX.sub hiY).abs hg fun z => ?_
    dsimp only
    rw [← Complex.sub_re, ← mul_sub, cdot_sub_right]
    have h1 := abs_re_weighted_le (wt ι z.2) (modeVel ι U z.1 z.2) (modeVel ι X z.1 z.2 - modeVel ι Y z.1 z.2) ht
    have h2 := cnormSq_nonneg (modeVel ι U z.1 z.2)
    have h3 := cnormSq_nonneg (modeVel ι X z.1 z.2 - modeVel ι Y z.1 z.2)
    have h4 : 0 ≤ (t * cnormSq (modeVel ι U z.1 z.2) + cnormSq (modeVel ι X z.1 z.2 - modeVel ι Y z.1 z.2) / t) / 2 :=
      by positivity
    have h5 := mul_le_mul_of_nonneg_right (hB ι z.2) h4
    calc _ ≤ _ := h1
      _ ≤ _ := h5
      _ = _ := by ring
  refine hle.trans (le_of_eq ?_)
  rw [integral_const_mul, integral_add (hiU.const_mul t) (hiD.div_const t), integral_const_mul, integral_div]

theorem weightedMode_bound (hPars : ModeSquareSumHolds) (wt : ℤ × ℤ → Space → ℝ)
    (hwm : ∀ ι, Measurable (wt ι)) {B : ℝ} (hB : ∀ ι y, |wt ι y| ≤ B) {U : ℝ → Space → Space}
    (hU : IsSquareField U) :
    ∃ K, ∀ X Y : ℝ → Space → Space, IsSquareField X → IsSquareField Y →
      Summable (fun ι => weightedModeTerm wt U X ι) ∧
      Summable (fun ι => |weightedModeTerm wt U X ι - weightedModeTerm wt U Y ι|) ∧
      ∑' ι, |weightedModeTerm wt U X ι - weightedModeTerm wt U Y ι|
        ≤ K * Real.sqrt (periodLIntegral (fun σ y => ‖X σ y - Y σ y‖ ^ 2)).toReal := by
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB (0, 0) 0)
  set u := (periodLIntegral (fun σ y => ‖U σ y‖ ^ 2)).toReal with hu
  have hu0 : 0 ≤ u := ENNReal.toReal_nonneg
  refine ⟨B / 2 * (u + 1), fun X Y hX hY => ?_⟩
  have hAU := hasSum_cnormSq_modeVel hPars hU
  have hAX := hasSum_cnormSq_modeVel hPars hX
  have hD := hasSum_cnormSq_modeVel_sub hPars hX hY
  set d := (periodLIntegral (fun σ y => ‖X σ y - Y σ y‖ ^ 2)).toReal with hd
  have hd0 : 0 ≤ d := ENNReal.toReal_nonneg
  have hsum1 : Summable (fun ι => weightedModeTerm wt U X ι) := by
    refine Summable.of_norm_bounded (((hAU.summable).add (hAX.summable)).mul_left B) fun ι => ?_
    rw [Real.norm_eq_abs, weightedModeTerm_eq hPars wt hwm hB hU hX]
    have hiU := integrable_cnormSq_modeVel hPars hU ι
    have hiX := integrable_cnormSq_modeVel hPars hX ι
    refine (abs_integral_le_integral_abs).trans ?_
    rw [← integral_add hiU hiX, ← integral_const_mul]
    refine integral_mono (integrable_weightedMode hPars wt hwm hB hU hX ι).abs
      ((hiU.add hiX).const_mul B) fun z => ?_
    have h1 := abs_re_weighted_le (wt ι z.2) (modeVel ι U z.1 z.2) (modeVel ι X z.1 z.2) one_pos
    have h2 := cnormSq_nonneg (modeVel ι U z.1 z.2)
    have h3 := cnormSq_nonneg (modeVel ι X z.1 z.2)
    simp only [one_mul, div_one] at h1
    have h4 : |wt ι z.2| * ((cnormSq (modeVel ι U z.1 z.2) + cnormSq (modeVel ι X z.1 z.2)) / 2) ≤
        B * (cnormSq (modeVel ι U z.1 z.2) + cnormSq (modeVel ι X z.1 z.2)) :=
      mul_le_mul (hB ι z.2) (by linarith) (by positivity) hB0
    show _ ≤ B * (cnormSq (modeVel ι U z.1 z.2) + cnormSq (modeVel ι X z.1 z.2))
    linarith
  have hg : ∀ t : ℝ, 0 < t → HasSum (fun ι => B / 2 * (t * ∫ z, cnormSq (modeVel ι U z.1 z.2) ∂slab
      + (∫ z, cnormSq (modeVel ι X z.1 z.2 - modeVel ι Y z.1 z.2) ∂slab) / t)) (B / 2 * (t * u + d / t)) :=
    fun t _ => ((hAU.mul_left t).add (hD.div_const t)).mul_left (B / 2)
  have hsum2 : Summable (fun ι => |weightedModeTerm wt U X ι - weightedModeTerm wt U Y ι|) :=
    Summable.of_nonneg_of_le (fun ι => abs_nonneg _)
      (fun ι => weightedModeTerm_sub_le hPars wt hwm hB hU hX hY ι one_pos) (hg 1 one_pos).summable
  have hbnd : ∀ t : ℝ, 0 < t → ∑' ι, |weightedModeTerm wt U X ι - weightedModeTerm wt U Y ι| ≤
      B / 2 * (t * u + d / t) := fun t ht =>
    hasSum_le (fun ι => weightedModeTerm_sub_le hPars wt hwm hB hU hX hY ι ht) hsum2.hasSum (hg t ht)
  refine ⟨hsum1, hsum2, ?_⟩
  set S := ∑' ι, |weightedModeTerm wt U X ι - weightedModeTerm wt U Y ι| with hS
  rcases hd0.eq_or_lt with h0 | hpos
  · rw [← h0, Real.sqrt_zero, mul_zero]
    by_contra hneg'
    have hneg : 0 < S := lt_of_not_ge hneg'
    have hc : 0 < B / 2 * u + 1 := by positivity
    have ht : 0 < S / (B / 2 * u + 1) := div_pos hneg hc
    have h1 := hbnd _ ht
    rw [← h0, zero_div, add_zero] at h1
    have h2 : (B / 2 * u + 1) * (S / (B / 2 * u + 1)) = S := mul_div_cancel₀ _ hc.ne'
    nlinarith
  · have hs : 0 < Real.sqrt d := Real.sqrt_pos.2 hpos
    have h1 := hbnd _ hs
    rw [Real.div_sqrt] at h1
    calc S ≤ _ := h1
      _ = B / 2 * (u + 1) * Real.sqrt d := by ring

theorem weightedMode_tendsto (hPars : ModeSquareSumHolds) (wt : ℤ × ℤ → Space → ℝ)
    (hwm : ∀ ι, Measurable (wt ι)) {B : ℝ} (hB : ∀ ι y, |wt ι y| ≤ B) {U Y : ℝ → Space → Space}
    (hU : IsSquareField U) (hY : IsSquareField Y) {X : ℕ → ℝ → Space → Space}
    (hX : ∀ n, IsSquareField (X n))
    (hlim : Filter.Tendsto (fun n => periodLIntegral (fun σ y => ‖X n σ y - Y σ y‖ ^ 2)) Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun n => ∑' ι, weightedModeTerm wt U (X n) ι) Filter.atTop
      (nhds (∑' ι, weightedModeTerm wt U Y ι)) := by
  obtain ⟨K, hK⟩ := weightedMode_bound hPars wt hwm hB hU
  have h0 : Filter.Tendsto (fun n => (periodLIntegral (fun σ y => ‖X n σ y - Y σ y‖ ^ 2)).toReal)
      Filter.atTop (nhds 0) := by
    have h := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hlim
    rw [ENNReal.toReal_zero] at h
    exact h
  have hd : Filter.Tendsto (fun n => Real.sqrt (periodLIntegral (fun σ y => ‖X n σ y - Y σ y‖ ^ 2)).toReal)
      Filter.atTop (nhds 0) := by
    have h := (Real.continuous_sqrt.tendsto 0).comp h0
    rw [Real.sqrt_zero] at h
    exact h
  have hKd : Filter.Tendsto (fun n => K * Real.sqrt (periodLIntegral (fun σ y => ‖X n σ y - Y σ y‖ ^ 2)).toReal)
      Filter.atTop (nhds 0) := by
    have h := hd.const_mul K
    rw [mul_zero] at h
    exact h
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hKd
  obtain ⟨h1, h2, h3⟩ := hK (X n) Y (hX n) hY
  obtain ⟨h1', -, -⟩ := hK Y Y hY hY
  rw [← h1.tsum_sub h1']
  refine (norm_tsum_le_tsum_norm ?_).trans ?_
  · simpa only [Real.norm_eq_abs] using h2
  · simpa only [Real.norm_eq_abs] using h3

theorem isSquareField_of_continuous {X : ℝ → Space → Space}
    (hc : Continuous (fun z : ℝ × Space => X z.1 z.2)) (hp : IsTimePeriodic X)
    (hs : ∃ R, ∀ σ y, R < ‖y‖ → X σ y = 0) : IsSquareField X := by
  refine ⟨hc.aestronglyMeasurable, hp, ?_⟩
  obtain ⟨R, hR⟩ := hs
  have hK : IsCompact (Set.Icc (0 : ℝ) 1 ×ˢ Metric.closedBall (0 : Space) R) :=
    isCompact_Icc.prod (isCompact_closedBall _ _)
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hc.continuousOn
  have hKm : MeasurableSet (Set.Icc (0 : ℝ) 1 ×ˢ Metric.closedBall (0 : Space) R) :=
    measurableSet_Icc.prod Metric.isClosed_closedBall.measurableSet
  have hm : AEStronglyMeasurable (fun z : ℝ × Space => ‖X z.1 z.2‖ ^ 2) slab :=
    (hc.aestronglyMeasurable.norm.pow 2).mono_ac slab_ac
  rw [periodLIntegral_eq_slab (fun σ y => ‖X σ y‖ ^ 2) hm]
  have hfin : slab (Set.Icc (0 : ℝ) 1 ×ˢ Metric.closedBall (0 : Space) R) < ⊤ := by
    rw [Measure.prod_prod, Measure.restrict_apply measurableSet_Icc, Set.inter_self, Real.volume_Icc]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (isCompact_closedBall _ _).measure_lt_top
  calc ∫⁻ z, ENNReal.ofReal (‖X z.1 z.2‖ ^ 2) ∂slab
      ≤ ∫⁻ z, (Set.Icc (0 : ℝ) 1 ×ˢ Metric.closedBall (0 : Space) R).indicator
          (fun _ => ENNReal.ofReal (C ^ 2)) z ∂slab := by
        refine lintegral_mono_ae ?_
        filter_upwards [slab_ae_mem] with z hz
        by_cases hy : ‖z.2‖ ≤ R
        · have hzK : z ∈ Set.Icc (0 : ℝ) 1 ×ˢ Metric.closedBall (0 : Space) R :=
            ⟨hz, by rw [Metric.mem_closedBall, dist_zero_right]; exact hy⟩
          rw [Set.indicator_of_mem hzK]
          refine ENNReal.ofReal_le_ofReal ?_
          have h := hC z hzK
          have h0 := norm_nonneg (X z.1 z.2)
          nlinarith
        · rw [hR z.1 z.2 (lt_of_not_ge hy), norm_zero]
          simp
    _ = ENNReal.ofReal (C ^ 2) * slab (Set.Icc (0 : ℝ) 1 ×ˢ Metric.closedBall (0 : Space) R) :=
        lintegral_indicator_const hKm _
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin

end ModeL2Internal

end Coercive

end Breakdown
