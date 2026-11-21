import Breakdown.Cert.CoerciveNodes

open scoped ENNReal
open MeasureTheory

noncomputable section

namespace Breakdown

namespace Coercive

private lemma continuous_coord (i : Fin 3) : Continuous (fun y : Space => y i) :=
  (EuclideanSpace.proj i : Space →L[ℝ] ℝ).continuous

private lemma continuous_axialRot_pair : Continuous (fun p : ℝ × Space => axialRot p.1 p.2) := by
  have h0 : Continuous (fun p : ℝ × Space => p.2 0) := (continuous_coord 0).comp continuous_snd
  have h1 : Continuous (fun p : ℝ × Space => p.2 1) := (continuous_coord 1).comp continuous_snd
  have h2 : Continuous (fun p : ℝ × Space => p.2 2) := (continuous_coord 2).comp continuous_snd
  have hc : Continuous (fun p : ℝ × Space => Real.cos p.1) := Real.continuous_cos.comp continuous_fst
  have hs : Continuous (fun p : ℝ × Space => Real.sin p.1) := Real.continuous_sin.comp continuous_fst
  unfold axialRot
  exact ((((hc.mul h0).sub (hs.mul h1)).smul continuous_const).add
    (((hs.mul h0).add (hc.mul h1)).smul continuous_const)).add (h2.smul continuous_const)

private lemma measurePreserving_shiftRot (hR : AxialRotationHolds) (τ φ : ℝ) :
    MeasurePreserving (fun z : ℝ × Space => (z.1 + τ, axialRot φ z.2)) volume volume := by
  obtain ⟨R, hRy⟩ := hR.1 φ
  have h1 : MeasurePreserving (Prod.map (· + τ) R) ((volume : Measure ℝ).prod (volume : Measure Space))
      ((volume : Measure ℝ).prod (volume : Measure Space)) :=
    (measurePreserving_add_right (volume : Measure ℝ) τ).prod R.measurePreserving
  have h2 : (fun z : ℝ × Space => (z.1 + τ, axialRot φ z.2)) = Prod.map (· + τ) R := by
    funext z
    simp [Prod.map, hRy]
  rw [h2, Measure.volume_eq_prod]
  exact h1

private lemma quasiMeasurePreserving_shiftRot (hR : AxialRotationHolds) (ν : Measure (ℝ × ℝ)) [SFinite ν] :
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
    rw [(measurePreserving_shiftRot hR b.1 b.2).measure_preimage hN.nullMeasurableSet, h0]
  simp [hz]

private lemma quasiMeasurePreserving_shiftRot_nested (hR : AxialRotationHolds) (ν₁ ν₂ : Measure ℝ)
    [SFinite ν₁] [SFinite ν₂] :
    Measure.QuasiMeasurePreserving
      (fun p : ((ℝ × Space) × ℝ) × ℝ => (p.1.1.1 + p.1.2, axialRot p.2 p.1.1.2))
      (((volume : Measure (ℝ × Space)).prod ν₁).prod ν₂) volume :=
  (quasiMeasurePreserving_shiftRot hR (ν₁.prod ν₂)).comp
    (measurePreserving_prodAssoc (volume : Measure (ℝ × Space)) ν₁ ν₂).quasiMeasurePreserving

private lemma aestronglyMeasurable_modeAverage (ι : ℤ × ℤ) (f : ((ℝ × Space) × ℝ) × ℝ → ℝ)
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

private lemma lintegral_periodic_shift (h : ℝ → ℝ≥0∞) (hp : Function.Periodic h 1) (τ : ℝ) :
    ∫⁻ σ in Set.Icc (0 : ℝ) 1, h (σ + τ) = ∫⁻ σ in Set.Icc (0 : ℝ) 1, h σ := by
  rw [← setLIntegral_congr (Ioc_ae_eq_Icc (a := (0 : ℝ)) (b := 1)),
    ← setLIntegral_congr (Ioc_ae_eq_Icc (a := (0 : ℝ)) (b := 1))]
  have hpre : (fun σ : ℝ => σ + τ) ⁻¹' Set.Ioc τ (τ + 1) = Set.Ioc 0 1 := by
    ext σ
    simp only [Set.mem_preimage, Set.mem_Ioc]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨by linarith, by linarith⟩
    · rintro ⟨h1, h2⟩
      exact ⟨by linarith, by linarith⟩
  have hmp := measurePreserving_add_right (volume : Measure ℝ) τ
  have h1 := hmp.setLIntegral_comp_preimage_emb (measurableEmbedding_addRight τ) h (Set.Ioc τ (τ + 1))
  rw [hpre] at h1
  rw [h1]
  have hl : ∀ t : ℝ, ∫⁻ σ in Set.Ioc t (t + 1), h σ = ∫⁻ b : UnitAddCircle, hp.lift b := by
    intro t
    rw [← UnitAddCircle.lintegral_preimage t]
    rfl
  have h0 := hl 0
  rw [zero_add] at h0
  rw [hl τ, h0]

private lemma sum_norm_sq_orthonormalBasis (A : Space →L[ℝ] Space) (b : OrthonormalBasis (Fin 3) ℝ Space) :
    ∑ j, ‖A (b j)‖ ^ 2 = ∑ i, ‖(ContinuousLinearMap.adjoint A) (unitVector i)‖ ^ 2 := by
  let e := EuclideanSpace.basisFun (Fin 3) ℝ
  have he : ∀ i, e i = unitVector i := fun i => by simp [e, unitVector]
  calc ∑ j, ‖A (b j)‖ ^ 2 = ∑ j, ∑ i, ‖inner ℝ (e i) (A (b j))‖ ^ 2 := by
        simp_rw [e.sum_sq_norm_inner_right]
    _ = ∑ i, ∑ j, ‖inner ℝ ((ContinuousLinearMap.adjoint A) (e i)) (b j)‖ ^ 2 := by
        rw [Finset.sum_comm]
        simp_rw [ContinuousLinearMap.adjoint_inner_left]
    _ = ∑ i, ‖(ContinuousLinearMap.adjoint A) (unitVector i)‖ ^ 2 := by
        simp_rw [b.sum_sq_norm_inner_left, he]

private lemma matSq_rot (A : Space →L[ℝ] Space) (R : Space ≃ₗᵢ[ℝ] Space) :
    ∑ j, ‖A (R (unitVector j))‖ ^ 2 = matSq A := by
  let e := EuclideanSpace.basisFun (Fin 3) ℝ
  have he : ∀ i, e i = unitVector i := fun i => by simp [e, unitVector]
  have h1 := sum_norm_sq_orthonormalBasis A (e.map R)
  have h2 := sum_norm_sq_orthonormalBasis A e
  simp only [OrthonormalBasis.map_apply, he] at h1 h2
  unfold matSq
  rw [h1, ← h2]

private lemma aestronglyMeasurable_comp_shiftRot (hR : AxialRotationHolds)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (c : ℝ → E → ℝ)
    (hc : Continuous (fun p : ℝ × E => c p.1 p.2)) (Y : ℝ → Space → E)
    (hY : AEStronglyMeasurable (fun z : ℝ × Space => Y z.1 z.2) volume)
    (ν : Measure (ℝ × ℝ)) [SFinite ν] :
    AEStronglyMeasurable
      (fun p : (ℝ × Space) × (ℝ × ℝ) => c p.2.2 (Y (p.1.1 + p.2.1) (axialRot p.2.2 p.1.2)))
      ((volume : Measure (ℝ × Space)).prod ν) := by
  have h1 := hY.comp_quasiMeasurePreserving (quasiMeasurePreserving_shiftRot hR ν)
  have h2 : AEStronglyMeasurable (fun p : (ℝ × Space) × (ℝ × ℝ) => p.2.2)
      ((volume : Measure (ℝ × Space)).prod ν) := continuous_snd.snd.aestronglyMeasurable
  have h3 := hc.comp_aestronglyMeasurable (h2.prodMk h1)
  exact h3

private lemma aestronglyMeasurable_comp_shiftRot_nested (hR : AxialRotationHolds)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (c : ℝ → E → ℝ)
    (hc : Continuous (fun p : ℝ × E => c p.1 p.2)) (Y : ℝ → Space → E)
    (hY : AEStronglyMeasurable (fun z : ℝ × Space => Y z.1 z.2) volume) :
    AEStronglyMeasurable
      (fun p : ((ℝ × Space) × ℝ) × ℝ => c p.2 (Y (p.1.1.1 + p.1.2) (axialRot p.2 p.1.1.2)))
      (((volume : Measure (ℝ × Space)).prod volume).prod volume) := by
  have h1 := hY.comp_quasiMeasurePreserving
    (quasiMeasurePreserving_shiftRot_nested hR (volume : Measure ℝ) (volume : Measure ℝ))
  have h2 : AEStronglyMeasurable (fun p : ((ℝ × Space) × ℝ) × ℝ => p.2)
      (((volume : Measure (ℝ × Space)).prod volume).prod volume) := continuous_snd.aestronglyMeasurable
  have h3 := hc.comp_aestronglyMeasurable (h2.prodMk h1)
  exact h3

private lemma lintegral_shiftRot (hR : AxialRotationHolds) (f : ℝ → Space → ℝ≥0∞)
    (hf : AEMeasurable (fun z : ℝ × Space => f z.1 z.2) volume) (hfp : ∀ σ y, f (σ + 1) y = f σ y)
    (τ φ : ℝ) :
    ∫⁻ z, f (z.1 + τ) (axialRot φ z.2) ∂((volume.restrict (Set.Icc (0 : ℝ) 1)).prod (volume : Measure Space)) =
      ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, f σ y := by
  have hac : (volume.restrict (Set.Icc (0 : ℝ) 1)).prod (volume : Measure Space) ≪ (volume : Measure (ℝ × Space)) :=
    (Measure.absolutelyContinuous_of_le Measure.restrict_le_self).prod Measure.AbsolutelyContinuous.rfl
  have hm : AEMeasurable (fun z : ℝ × Space => f (z.1 + τ) (axialRot φ z.2))
      ((volume.restrict (Set.Icc (0 : ℝ) 1)).prod (volume : Measure Space)) := by
    have h := hf.comp_quasiMeasurePreserving (measurePreserving_shiftRot hR τ φ).quasiMeasurePreserving
    exact h.mono_ac hac
  rw [lintegral_prod _ hm]
  obtain ⟨R, hRy⟩ := hR.1 φ
  have hinner : ∀ σ : ℝ, ∫⁻ y, f (σ + τ) (axialRot φ y) = ∫⁻ y, f (σ + τ) y := fun σ => by
    simp_rw [← hRy]
    exact R.measurePreserving.lintegral_comp_emb R.toHomeomorph.measurableEmbedding (fun y => f (σ + τ) y)
  simp_rw [hinner]
  exact lintegral_periodic_shift (fun σ => ∫⁻ y, f σ y) (fun σ => by simp only [hfp]) τ


private lemma aemeasurable_rect (hR : AxialRotationHolds)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (N : E → ℝ) (hNc : Continuous N)
    (Y : ℝ → Space → E) (hY : AEStronglyMeasurable (fun z : ℝ × Space => Y z.1 z.2) volume) :
    AEMeasurable (fun p : (ℝ × Space) × (ℝ × ℝ) =>
      ENNReal.ofReal (N (Y (p.1.1 + p.2.1) (axialRot p.2.2 p.1.2))))
      (((volume.restrict (Set.Icc (0 : ℝ) 1)).prod (volume : Measure Space)).prod
        ((volume.restrict (Set.Icc (0 : ℝ) 1)).prod (volume.restrict (Set.Icc (0 : ℝ) (2 * Real.pi))))) := by
  have hNc' : Continuous (fun p : ℝ × E => N p.2) := hNc.comp continuous_snd
  have hac1 : (volume.restrict (Set.Icc (0 : ℝ) 1)).prod (volume : Measure Space) ≪ (volume : Measure (ℝ × Space)) :=
    (Measure.absolutelyContinuous_of_le Measure.restrict_le_self).prod Measure.AbsolutelyContinuous.rfl
  have hac2 : ((volume.restrict (Set.Icc (0 : ℝ) 1)).prod (volume : Measure Space)).prod
      ((volume.restrict (Set.Icc (0 : ℝ) 1)).prod (volume.restrict (Set.Icc (0 : ℝ) (2 * Real.pi)))) ≪
      (volume : Measure (ℝ × Space)).prod
        ((volume.restrict (Set.Icc (0 : ℝ) 1)).prod (volume.restrict (Set.Icc (0 : ℝ) (2 * Real.pi)))) :=
    hac1.prod Measure.AbsolutelyContinuous.rfl
  have h := aestronglyMeasurable_comp_shiftRot hR (fun _ e => N e) hNc' Y hY
    ((volume.restrict (Set.Icc (0 : ℝ) 1)).prod (volume.restrict (Set.Icc (0 : ℝ) (2 * Real.pi))))
  exact ENNReal.measurable_ofReal.comp_aemeasurable (h.mono_ac hac2).aemeasurable

private lemma lintegral_rect (hR : AxialRotationHolds)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (N : E → ℝ) (hNc : Continuous N)
    (Y : ℝ → Space → E) (hY : AEStronglyMeasurable (fun z : ℝ × Space => Y z.1 z.2) volume)
    (hYp : IsTimePeriodic Y) :
    ∫⁻ z, ∫⁻ q, ENNReal.ofReal (N (Y (z.1 + q.1) (axialRot q.2 z.2)))
        ∂((volume.restrict (Set.Icc (0 : ℝ) 1)).prod (volume.restrict (Set.Icc (0 : ℝ) (2 * Real.pi))))
        ∂((volume.restrict (Set.Icc (0 : ℝ) 1)).prod (volume : Measure Space)) =
      ENNReal.ofReal (2 * Real.pi) * periodLIntegral (fun σ y => N (Y σ y)) := by
  have hNf := aemeasurable_rect hR N hNc Y hY
  have hYN : AEMeasurable (fun z : ℝ × Space => ENNReal.ofReal (N (Y z.1 z.2))) volume :=
    ENNReal.measurable_ofReal.comp_aemeasurable (hNc.comp_aestronglyMeasurable hY).aemeasurable
  rw [lintegral_lintegral_swap hNf]
  have hq : ∀ q : ℝ × ℝ, ∫⁻ z, ENNReal.ofReal (N (Y (z.1 + q.1) (axialRot q.2 z.2)))
      ∂((volume.restrict (Set.Icc (0 : ℝ) 1)).prod (volume : Measure Space)) =
      periodLIntegral (fun σ y => N (Y σ y)) := fun q =>
    lintegral_shiftRot hR (fun σ y => ENNReal.ofReal (N (Y σ y))) hYN
      (fun σ y => by simp only [hYp σ y]) q.1 q.2
  simp_rw [hq]
  rw [lintegral_const, ← Set.univ_prod_univ, Measure.prod_prod, Measure.restrict_apply_univ,
    Measure.restrict_apply_univ, Real.volume_Icc, Real.volume_Icc, sub_zero, sub_zero, ENNReal.ofReal_one,
    one_mul, mul_comm]

private lemma ae_rect_lt_top (hR : AxialRotationHolds)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (N : E → ℝ) (hNc : Continuous N)
    (Y : ℝ → Space → E) (hY : AEStronglyMeasurable (fun z : ℝ × Space => Y z.1 z.2) volume)
    (hYp : IsTimePeriodic Y) (hfin : periodLIntegral (fun σ y => N (Y σ y)) < ⊤) :
    ∀ᵐ z ∂((volume.restrict (Set.Icc (0 : ℝ) 1)).prod (volume : Measure Space)),
      ∫⁻ q, ENNReal.ofReal (N (Y (z.1 + q.1) (axialRot q.2 z.2)))
        ∂((volume.restrict (Set.Icc (0 : ℝ) 1)).prod (volume.restrict (Set.Icc (0 : ℝ) (2 * Real.pi)))) < ⊤ := by
  refine ae_lt_top' (aemeasurable_rect hR N hNc Y hY).lintegral_prod_right' ?_
  rw [lintegral_rect hR N hNc Y hY hYp]
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin.ne

private lemma modeSquareSum_generic (hR : AxialRotationHolds) (hT : TorusSquareSumHolds)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {β : Type*} [Fintype β]
    (c : β → ℝ → E → ℝ) (hc : ∀ b, Continuous (fun p : ℝ × E => c b p.1 p.2))
    (N : E → ℝ) (hN : ∀ φ e, ∑ b, c b φ e ^ 2 = N e)
    (Y : ℝ → Space → E) (hY : AEStronglyMeasurable (fun z : ℝ × Space => Y z.1 z.2) volume)
    (hYp : IsTimePeriodic Y) (hfin : periodLIntegral (fun σ y => N (Y σ y)) < ⊤) :
    periodLIntegral (fun σ y => N (Y σ y)) =
      ∑' ι : ℤ × ℤ, ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y,
        ENNReal.ofReal (∑ b, ‖modeAverage ι (fun τ φ (_ : Unit) => c b φ (Y (σ + τ) (axialRot φ y))) ()‖ ^ 2) := by
  have hNnn : ∀ e, 0 ≤ N e := fun e => (hN 0 e) ▸ Finset.sum_nonneg (fun b _ => sq_nonneg _)
  have hNc : Continuous N := by
    have he : N = fun e => ∑ b, c b 0 e ^ 2 := funext fun e => (hN 0 e).symm
    rw [he]
    refine continuous_finsetSum _ (fun b _ => ?_)
    have h := (hc b).comp (continuous_const.prodMk continuous_id : Continuous (fun e : E => ((0 : ℝ), e)))
    exact h.pow 2
  have hNc' : Continuous (fun p : ℝ × E => N p.2) := hNc.comp continuous_snd
  have hac1 : (volume.restrict (Set.Icc (0 : ℝ) 1)).prod (volume : Measure Space) ≪ (volume : Measure (ℝ × Space)) :=
    (Measure.absolutelyContinuous_of_le Measure.restrict_le_self).prod Measure.AbsolutelyContinuous.rfl
  have hac2 : ((volume.restrict (Set.Icc (0 : ℝ) 1)).prod (volume : Measure Space)).prod
      ((volume.restrict (Set.Icc (0 : ℝ) 1)).prod (volume.restrict (Set.Icc (0 : ℝ) (2 * Real.pi)))) ≪
      (volume : Measure (ℝ × Space)).prod
        ((volume.restrict (Set.Icc (0 : ℝ) 1)).prod (volume.restrict (Set.Icc (0 : ℝ) (2 * Real.pi)))) :=
    hac1.prod Measure.AbsolutelyContinuous.rfl
  have hJint := lintegral_rect hR N hNc Y hY hYp
  have hJfin := ae_rect_lt_top hR N hNc Y hY hYp hfin
  have hsec : ∀ᵐ z ∂((volume.restrict (Set.Icc (0 : ℝ) 1)).prod (volume : Measure Space)), ∀ b,
      AEStronglyMeasurable (fun q : ℝ × ℝ => c b q.2 (Y (z.1 + q.1) (axialRot q.2 z.2)))
        ((volume.restrict (Set.Icc (0 : ℝ) 1)).prod (volume.restrict (Set.Icc (0 : ℝ) (2 * Real.pi)))) := by
    refine ae_all_iff.2 fun b => ?_
    have h := aestronglyMeasurable_comp_shiftRot hR (c b) (hc b) Y hY
      ((volume.restrict (Set.Icc (0 : ℝ) 1)).prod (volume.restrict (Set.Icc (0 : ℝ) (2 * Real.pi))))
    exact (h.mono_ac hac2).prodMk_left
  have hpt : ∀ᵐ z ∂((volume.restrict (Set.Icc (0 : ℝ) 1)).prod (volume : Measure Space)),
      ∑' ι : ℤ × ℤ, ENNReal.ofReal (∑ b,
        ‖modeAverage ι (fun τ φ (_ : Unit) => c b φ (Y (z.1 + τ) (axialRot φ z.2))) ()‖ ^ 2) =
      ENNReal.ofReal (1 / (2 * Real.pi)) * ∫⁻ q, ENNReal.ofReal (N (Y (z.1 + q.1) (axialRot q.2 z.2)))
        ∂((volume.restrict (Set.Icc (0 : ℝ) 1)).prod (volume.restrict (Set.Icc (0 : ℝ) (2 * Real.pi)))) := by
    filter_upwards [hJfin, hsec] with z hz hzb
    have hm2 : ∀ b, AEMeasurable (fun q : ℝ × ℝ => ENNReal.ofReal (c b q.2 (Y (z.1 + q.1) (axialRot q.2 z.2)) ^ 2))
        ((volume.restrict (Set.Icc (0 : ℝ) 1)).prod (volume.restrict (Set.Icc (0 : ℝ) (2 * Real.pi)))) :=
      fun b => ENNReal.measurable_ofReal.comp_aemeasurable ((hzb b).aemeasurable.pow_const 2)
    have hle : ∀ b (q : ℝ × ℝ), c b q.2 (Y (z.1 + q.1) (axialRot q.2 z.2)) ^ 2 ≤
        N (Y (z.1 + q.1) (axialRot q.2 z.2)) := fun b q => by
      rw [← hN q.2]
      exact Finset.single_le_sum (f := fun b' => c b' q.2 (Y (z.1 + q.1) (axialRot q.2 z.2)) ^ 2)
        (fun b' _ => sq_nonneg _) (Finset.mem_univ b)
    have hTb : ∀ b, ∑' ι : ℤ × ℤ, ENNReal.ofReal
        (‖modeAverage ι (fun τ φ (_ : Unit) => c b φ (Y (z.1 + τ) (axialRot φ z.2))) ()‖ ^ 2) =
        ENNReal.ofReal (1 / (2 * Real.pi)) * ∫⁻ q, ENNReal.ofReal (c b q.2 (Y (z.1 + q.1) (axialRot q.2 z.2)) ^ 2)
          ∂((volume.restrict (Set.Icc (0 : ℝ) 1)).prod (volume.restrict (Set.Icc (0 : ℝ) (2 * Real.pi)))) := by
      intro b
      have hfinb : (∫⁻ τ in Set.Icc (0 : ℝ) 1, ∫⁻ φ in Set.Icc (0 : ℝ) (2 * Real.pi),
          ENNReal.ofReal (c b φ (Y (z.1 + τ) (axialRot φ z.2)) ^ 2)) < ⊤ := by
        rw [← lintegral_prod _ (hm2 b)]
        refine lt_of_le_of_lt (lintegral_mono fun q => ENNReal.ofReal_le_ofReal (hle b q)) hz
      have h := hT (fun τ φ => c b φ (Y (z.1 + τ) (axialRot φ z.2))) (hzb b) hfinb
      rw [h, lintegral_prod _ (hm2 b)]
    calc ∑' ι : ℤ × ℤ, ENNReal.ofReal (∑ b,
          ‖modeAverage ι (fun τ φ (_ : Unit) => c b φ (Y (z.1 + τ) (axialRot φ z.2))) ()‖ ^ 2)
        = ∑' ι : ℤ × ℤ, ∑ b, ENNReal.ofReal
          (‖modeAverage ι (fun τ φ (_ : Unit) => c b φ (Y (z.1 + τ) (axialRot φ z.2))) ()‖ ^ 2) := by
          refine tsum_congr fun ι => ?_
          exact ENNReal.ofReal_sum_of_nonneg (fun b _ => sq_nonneg _)
      _ = ∑ b, ∑' ι : ℤ × ℤ, ENNReal.ofReal
          (‖modeAverage ι (fun τ φ (_ : Unit) => c b φ (Y (z.1 + τ) (axialRot φ z.2))) ()‖ ^ 2) :=
          Summable.tsum_finsetSum (fun b _ => ENNReal.summable)
      _ = ∑ b, ENNReal.ofReal (1 / (2 * Real.pi)) * ∫⁻ q, ENNReal.ofReal (c b q.2 (Y (z.1 + q.1) (axialRot q.2 z.2)) ^ 2)
          ∂((volume.restrict (Set.Icc (0 : ℝ) 1)).prod (volume.restrict (Set.Icc (0 : ℝ) (2 * Real.pi)))) :=
          Finset.sum_congr rfl (fun b _ => hTb b)
      _ = ENNReal.ofReal (1 / (2 * Real.pi)) * ∫⁻ q, ∑ b, ENNReal.ofReal (c b q.2 (Y (z.1 + q.1) (axialRot q.2 z.2)) ^ 2)
          ∂((volume.restrict (Set.Icc (0 : ℝ) 1)).prod (volume.restrict (Set.Icc (0 : ℝ) (2 * Real.pi)))) := by
          rw [← Finset.mul_sum, lintegral_finsetSum' _ (fun b _ => hm2 b)]
      _ = _ := by
          congr 1
          refine lintegral_congr fun q => ?_
          rw [← ENNReal.ofReal_sum_of_nonneg (fun b _ => sq_nonneg _), hN]
  have hSm : ∀ ι : ℤ × ℤ, AEMeasurable (fun z : ℝ × Space => ENNReal.ofReal (∑ b,
      ‖modeAverage ι (fun τ φ (_ : Unit) => c b φ (Y (z.1 + τ) (axialRot φ z.2))) ()‖ ^ 2))
      ((volume.restrict (Set.Icc (0 : ℝ) 1)).prod (volume : Measure Space)) := by
    intro ι
    have hb : ∀ b, AEStronglyMeasurable (fun z : ℝ × Space =>
        modeAverage ι (fun τ φ (_ : Unit) => c b φ (Y (z.1 + τ) (axialRot φ z.2))) ()) volume := fun b =>
      by
        have h := aestronglyMeasurable_modeAverage ι
          (fun p : ((ℝ × Space) × ℝ) × ℝ => c b p.2 (Y (p.1.1.1 + p.1.2) (axialRot p.2 p.1.1.2)))
          (aestronglyMeasurable_comp_shiftRot_nested hR (c b) (hc b) Y hY)
        exact h
    have hs : AEStronglyMeasurable (fun z : ℝ × Space => ∑ b,
        ‖modeAverage ι (fun τ φ (_ : Unit) => c b φ (Y (z.1 + τ) (axialRot φ z.2))) ()‖ ^ 2) volume :=
by
      have h := Finset.aestronglyMeasurable_fun_sum (μ := (volume : Measure (ℝ × Space))) (Finset.univ : Finset β)
        (fun b _ => (hb b).norm.pow 2)
      exact h
    exact ENNReal.measurable_ofReal.comp_aemeasurable (hs.aemeasurable.mono_ac hac1)
  have hconst : ENNReal.ofReal (1 / (2 * Real.pi)) * ENNReal.ofReal (2 * Real.pi) = 1 := by
    rw [← ENNReal.ofReal_mul (by positivity), one_div, inv_mul_cancel₀ (by positivity), ENNReal.ofReal_one]
  symm
  calc ∑' ι : ℤ × ℤ, ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y,
        ENNReal.ofReal (∑ b, ‖modeAverage ι (fun τ φ (_ : Unit) => c b φ (Y (σ + τ) (axialRot φ y))) ()‖ ^ 2)
      = ∑' ι : ℤ × ℤ, ∫⁻ z, ENNReal.ofReal (∑ b,
          ‖modeAverage ι (fun τ φ (_ : Unit) => c b φ (Y (z.1 + τ) (axialRot φ z.2))) ()‖ ^ 2)
          ∂((volume.restrict (Set.Icc (0 : ℝ) 1)).prod (volume : Measure Space)) :=
        tsum_congr fun ι => (lintegral_prod _ (hSm ι)).symm
    _ = ∫⁻ z, ∑' ι : ℤ × ℤ, ENNReal.ofReal (∑ b,
          ‖modeAverage ι (fun τ φ (_ : Unit) => c b φ (Y (z.1 + τ) (axialRot φ z.2))) ()‖ ^ 2)
          ∂((volume.restrict (Set.Icc (0 : ℝ) 1)).prod (volume : Measure Space)) :=
        (lintegral_tsum hSm).symm
    _ = ∫⁻ z, ENNReal.ofReal (1 / (2 * Real.pi)) * ∫⁻ q, ENNReal.ofReal (N (Y (z.1 + q.1) (axialRot q.2 z.2)))
          ∂((volume.restrict (Set.Icc (0 : ℝ) 1)).prod (volume.restrict (Set.Icc (0 : ℝ) (2 * Real.pi))))
          ∂((volume.restrict (Set.Icc (0 : ℝ) 1)).prod (volume : Measure Space)) :=
        lintegral_congr_ae hpt
    _ = ENNReal.ofReal (1 / (2 * Real.pi)) * (ENNReal.ofReal (2 * Real.pi) * periodLIntegral (fun σ y => N (Y σ y))) := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, hJint]
    _ = periodLIntegral (fun σ y => N (Y σ y)) := by
        rw [← mul_assoc, hconst, one_mul]

private lemma sum_sq_axialRot_coord (hR : AxialRotationHolds) (φ : ℝ) (x : Space) :
    ∑ i : Fin 3, axialRot (-φ) x i ^ 2 = ‖x‖ ^ 2 := by
  obtain ⟨R, hRy⟩ := hR.1 (-φ)
  rw [← hRy, ← R.norm_map x, EuclideanSpace.norm_sq_eq]
  simp only [Real.norm_eq_abs, sq_abs]

private lemma continuous_rotCoord (i : Fin 3) :
    Continuous (fun p : ℝ × Space => axialRot (-p.1) p.2 i) := by
  have h1 : Continuous (fun p : ℝ × Space => (-p.1, p.2)) := continuous_fst.neg.prodMk continuous_snd
  have h2 := continuous_axialRot_pair.comp h1
  have h3 := (continuous_coord i).comp h2
  exact h3

private lemma continuous_rotGrad (ij : Fin 3 × Fin 3) :
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

private lemma continuous_rotSecondDeriv (ijl : Fin 3 × Fin 3 × Fin 3) :
    Continuous (fun p : ℝ × (Space →L[ℝ] Space →L[ℝ] Space) =>
      axialRot (-p.1) (p.2 (axialRot p.1 (unitVector ijl.2.1)) (axialRot p.1 (unitVector ijl.2.2))) ijl.1) := by
  have h0 : Continuous (fun p : ℝ × (Space →L[ℝ] Space →L[ℝ] Space) => (p.1, unitVector ijl.2.1)) :=
    continuous_fst.prodMk continuous_const
  have h0' : Continuous (fun p : ℝ × (Space →L[ℝ] Space →L[ℝ] Space) => (p.1, unitVector ijl.2.2)) :=
    continuous_fst.prodMk continuous_const
  have h1 := continuous_axialRot_pair.comp h0
  have h1' := continuous_axialRot_pair.comp h0'
  have h2 : Continuous (fun p : ℝ × (Space →L[ℝ] Space →L[ℝ] Space) =>
      p.2 (axialRot p.1 (unitVector ijl.2.1)) (axialRot p.1 (unitVector ijl.2.2))) :=
    (continuous_snd.clm_apply h1).clm_apply h1'
  have h3 : Continuous (fun p : ℝ × (Space →L[ℝ] Space →L[ℝ] Space) =>
      (-p.1, p.2 (axialRot p.1 (unitVector ijl.2.1)) (axialRot p.1 (unitVector ijl.2.2)))) :=
    continuous_fst.neg.prodMk h2
  have h4 := continuous_axialRot_pair.comp h3
  have h5 := (continuous_coord ijl.1).comp h4
  exact h5

private lemma sum_sq_rotGrad (hR : AxialRotationHolds) (φ : ℝ) (A : Space →L[ℝ] Space) :
    ∑ ij : Fin 3 × Fin 3, axialRot (-φ) (A (axialRot φ (unitVector ij.2))) ij.1 ^ 2 = matSq A := by
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  simp_rw [sum_sq_axialRot_coord hR]
  obtain ⟨R, hRy⟩ := hR.1 φ
  simp_rw [← hRy]
  exact matSq_rot A R

private lemma sum_sq_rotSecondDeriv (hR : AxialRotationHolds) (φ : ℝ) (H : Space →L[ℝ] Space →L[ℝ] Space) :
    ∑ ijl : Fin 3 × Fin 3 × Fin 3,
      axialRot (-φ) (H (axialRot φ (unitVector ijl.2.1)) (axialRot φ (unitVector ijl.2.2))) ijl.1 ^ 2 =
      secondDerivSq H := by
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  simp_rw [Fintype.sum_prod_type]
  simp_rw [sum_sq_axialRot_coord hR]
  obtain ⟨R, hRy⟩ := hR.1 φ
  simp_rw [← hRy]
  have h1 : ∀ j : Fin 3, ∑ l : Fin 3, ‖H (R (unitVector j)) (R (unitVector l))‖ ^ 2 =
      ∑ l : Fin 3, ‖H (R (unitVector j)) (unitVector l)‖ ^ 2 := fun j => by
    rw [matSq_rot (H (R (unitVector j))) R]
    rfl
  simp_rw [h1]
  rw [Finset.sum_comm]
  have h2 : ∀ l : Fin 3, ∑ j : Fin 3, ‖H (R (unitVector j)) (unitVector l)‖ ^ 2 =
      ∑ j : Fin 3, ‖H (unitVector j) (unitVector l)‖ ^ 2 := fun l => by
    have h := matSq_rot (H.flip (unitVector l)) R
    simp only [ContinuousLinearMap.flip_apply] at h
    rw [h]
    unfold matSq
    simp only [ContinuousLinearMap.flip_apply]
  simp_rw [h2]
  unfold secondDerivSq
  exact Finset.sum_comm

private lemma velSquareSum (hT : TorusSquareSumHolds) (hR : AxialRotationHolds) (X : ℝ → Space → Space)
    (hX : AEStronglyMeasurable (fun z : ℝ × Space => X z.1 z.2) volume) (hXp : IsTimePeriodic X)
    (hfin : periodLIntegral (fun σ y => ‖X σ y‖ ^ 2) < ⊤) :
    periodLIntegral (fun σ y => ‖X σ y‖ ^ 2) =
      ∑' ι : ℤ × ℤ, ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ENNReal.ofReal (cnormSq (modeVel ι X σ y)) := by
  have h := modeSquareSum_generic hR hT (fun i φ e => axialRot (-φ) e i) continuous_rotCoord
    (fun e => ‖e‖ ^ 2) (sum_sq_axialRot_coord hR) X hX hXp hfin
  exact h

private lemma gradSquareSum (hT : TorusSquareSumHolds) (hR : AxialRotationHolds)
    (G : ℝ → Space → (Space →L[ℝ] Space))
    (hG : AEStronglyMeasurable (fun z : ℝ × Space => G z.1 z.2) volume) (hGp : IsTimePeriodic G)
    (hfin : periodLIntegral (fun σ y => matSq (G σ y)) < ⊤) :
    periodLIntegral (fun σ y => matSq (G σ y)) =
      ∑' ι : ℤ × ℤ, ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ENNReal.ofReal (cnormSq (modeGrad ι G σ y)) := by
  have h := modeSquareSum_generic hR hT
    (fun (ij : Fin 3 × Fin 3) φ (A : Space →L[ℝ] Space) => axialRot (-φ) (A (axialRot φ (unitVector ij.2))) ij.1)
    continuous_rotGrad matSq (sum_sq_rotGrad hR) G hG hGp hfin
  exact h

private lemma secondDerivSquareSum (hT : TorusSquareSumHolds) (hR : AxialRotationHolds)
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space))
    (hH : AEStronglyMeasurable (fun z : ℝ × Space => H z.1 z.2) volume) (hHp : IsTimePeriodic H)
    (hfin : periodLIntegral (fun σ y => secondDerivSq (H σ y)) < ⊤) :
    periodLIntegral (fun σ y => secondDerivSq (H σ y)) =
      ∑' ι : ℤ × ℤ, ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ENNReal.ofReal (cnormSq (modeSecondDeriv ι H σ y)) := by
  have h := modeSquareSum_generic hR hT
    (fun (ijl : Fin 3 × Fin 3 × Fin 3) φ (B : Space →L[ℝ] Space →L[ℝ] Space) =>
      axialRot (-φ) (B (axialRot φ (unitVector ijl.2.1)) (axialRot φ (unitVector ijl.2.2))) ijl.1)
    continuous_rotSecondDeriv secondDerivSq (sum_sq_rotSecondDeriv hR) H hH hHp hfin
  exact h

private abbrev slabMeasure : Measure (ℝ × Space) :=
  (volume.restrict (Set.Icc (0 : ℝ) 1)).prod (volume : Measure Space)

private abbrev rectMeasure : Measure (ℝ × ℝ) :=
  (volume.restrict (Set.Icc (0 : ℝ) 1)).prod (volume.restrict (Set.Icc (0 : ℝ) (2 * Real.pi)))

private lemma slab_ac : slabMeasure ≪ (volume : Measure (ℝ × Space)) :=
  (Measure.absolutelyContinuous_of_le Measure.restrict_le_self).prod Measure.AbsolutelyContinuous.rfl

private lemma period_eq_slab (f : ℝ → Space → ℝ)
    (hf : AEStronglyMeasurable (fun z : ℝ × Space => f z.1 z.2) slabMeasure) :
    periodLIntegral f = ∫⁻ z, ENNReal.ofReal (f z.1 z.2) ∂slabMeasure :=
  (lintegral_prod _ (ENNReal.measurable_ofReal.comp_aemeasurable hf.aemeasurable)).symm

private lemma integrable_slab (f : ℝ → Space → ℝ)
    (hf : AEStronglyMeasurable (fun z : ℝ × Space => f z.1 z.2) slabMeasure) (hnn : ∀ σ y, 0 ≤ f σ y)
    (hfin : periodLIntegral f < ⊤) : Integrable (fun z : ℝ × Space => f z.1 z.2) slabMeasure := by
  rw [period_eq_slab f hf] at hfin
  exact (lintegral_ofReal_ne_top_iff_integrable hf (ae_of_all _ fun z => hnn z.1 z.2)).1 hfin.ne

private lemma period_lt_top_of_integrable (f : ℝ → Space → ℝ)
    (hf : AEStronglyMeasurable (fun z : ℝ × Space => f z.1 z.2) slabMeasure) (hnn : ∀ σ y, 0 ≤ f σ y)
    (hi : Integrable (fun z : ℝ × Space => f z.1 z.2) slabMeasure) : periodLIntegral f < ⊤ := by
  rw [period_eq_slab f hf]
  exact lt_top_iff_ne_top.2 ((lintegral_ofReal_ne_top_iff_integrable hf (ae_of_all _ fun z => hnn z.1 z.2)).2 hi)

private lemma integral_slab (f : ℝ → Space → ℝ)
    (hf : AEStronglyMeasurable (fun z : ℝ × Space => f z.1 z.2) slabMeasure) (hnn : ∀ σ y, 0 ≤ f σ y) :
    ∫ z, f z.1 z.2 ∂slabMeasure = (periodLIntegral f).toReal := by
  rw [period_eq_slab f hf]
  exact integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun z => hnn z.1 z.2) hf

private lemma integrable_of_sq_lintegral (f : ℝ × ℝ → ℝ) (hf : AEStronglyMeasurable f rectMeasure)
    (h2 : ∫⁻ q, ENNReal.ofReal (f q ^ 2) ∂rectMeasure < ⊤) : Integrable f rectMeasure := by
  have hsq : Integrable (fun q => f q ^ 2) rectMeasure :=
    (lintegral_ofReal_ne_top_iff_integrable (hf.pow 2) (ae_of_all _ fun q => sq_nonneg _)).1 h2.ne
  refine (hsq.add (integrable_const (1 : ℝ))).mono hf (ae_of_all _ fun q => ?_)
  simp only [Pi.add_apply, Real.norm_eq_abs]
  rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ f q ^ 2 + 1)]
  nlinarith [sq_abs (f q), abs_nonneg (f q), sq_nonneg (|f q| - 1)]

private lemma integrable_rect_phase (ι : ℤ × ℤ) (F : ℝ → ℝ → ℝ)
    (hF : Integrable (fun q : ℝ × ℝ => F q.1 q.2) rectMeasure) :
    Integrable (fun q : ℝ × ℝ =>
      Complex.exp (-(((2 * Real.pi * ι.1 * q.1 + ι.2 * q.2 : ℝ) : ℂ) * Complex.I)) * ((F q.1 q.2 : ℝ) : ℂ))
      ((volume.restrict (Set.Ioc (0 : ℝ) 1)).prod (volume.restrict (Set.Ioc (0 : ℝ) (2 * Real.pi)))) := by
  rw [Measure.restrict_congr_set (Ioc_ae_eq_Icc (a := (0 : ℝ)) (b := 1)),
    Measure.restrict_congr_set (Ioc_ae_eq_Icc (a := (0 : ℝ)) (b := 2 * Real.pi))]
  have hc : Integrable (fun q : ℝ × ℝ => ((F q.1 q.2 : ℝ) : ℂ)) rectMeasure := hF.ofReal
  refine hc.mono ((Continuous.aestronglyMeasurable (by fun_prop)).mul hc.aestronglyMeasurable)
    (ae_of_all _ fun q => ?_)
  rw [norm_mul, ← neg_mul, ← Complex.ofReal_neg, Complex.norm_exp_ofReal_mul_I, one_mul]

private lemma modeAverage_add (ι : ℤ × ℤ) (f g : ℝ → ℝ → ℝ)
    (hf : Integrable (fun q : ℝ × ℝ => f q.1 q.2) rectMeasure)
    (hg : Integrable (fun q : ℝ × ℝ => g q.1 q.2) rectMeasure) :
    modeAverage ι (fun τ φ (_ : Unit) => f τ φ + g τ φ) () =
      modeAverage ι (fun τ φ (_ : Unit) => f τ φ) () + modeAverage ι (fun τ φ (_ : Unit) => g τ φ) () := by
  unfold modeAverage
  simp only [intervalIntegral.integral_of_le zero_le_one,
    intervalIntegral.integral_of_le (by positivity : (0 : ℝ) ≤ 2 * Real.pi)]
  rw [← mul_add]
  congr 1
  have h := integral_integral_add (integrable_rect_phase ι f hf) (integrable_rect_phase ι g hg)
  refine Eq.trans ?_ h
  refine integral_congr_ae (ae_of_all _ fun τ => integral_congr_ae (ae_of_all _ fun φ => ?_))
  dsimp only
  push_cast
  ring

private lemma modeAverage_sub (ι : ℤ × ℤ) (f g : ℝ → ℝ → ℝ)
    (hf : Integrable (fun q : ℝ × ℝ => f q.1 q.2) rectMeasure)
    (hg : Integrable (fun q : ℝ × ℝ => g q.1 q.2) rectMeasure) :
    modeAverage ι (fun τ φ (_ : Unit) => f τ φ - g τ φ) () =
      modeAverage ι (fun τ φ (_ : Unit) => f τ φ) () - modeAverage ι (fun τ φ (_ : Unit) => g τ φ) () := by
  unfold modeAverage
  simp only [intervalIntegral.integral_of_le zero_le_one,
    intervalIntegral.integral_of_le (by positivity : (0 : ℝ) ≤ 2 * Real.pi)]
  rw [← mul_sub]
  congr 1
  have h := integral_integral_sub (integrable_rect_phase ι f hf) (integrable_rect_phase ι g hg)
  refine Eq.trans ?_ h
  refine integral_congr_ae (ae_of_all _ fun τ => integral_congr_ae (ae_of_all _ fun φ => ?_))
  dsimp only
  push_cast
  ring

private lemma modeVel_apply (ι : ℤ × ℤ) (Z : ℝ → Space → Space) (σ : ℝ) (y : Space) (i : Fin 3) :
    modeVel ι Z σ y i = modeAverage ι (fun τ φ (_ : Unit) => axialRot (-φ) (Z (σ + τ) (axialRot φ y)) i) () :=
  rfl

private lemma axialRot_add (hR : AxialRotationHolds) (φ : ℝ) (a b : Space) :
    axialRot φ (a + b) = axialRot φ a + axialRot φ b := by
  obtain ⟨R, hRy⟩ := hR.1 φ
  rw [← hRy, ← hRy, ← hRy, map_add]

private lemma axialRot_sub (hR : AxialRotationHolds) (φ : ℝ) (a b : Space) :
    axialRot φ (a - b) = axialRot φ a - axialRot φ b := by
  obtain ⟨R, hRy⟩ := hR.1 φ
  rw [← hRy, ← hRy, ← hRy, map_sub]

private lemma modeVel_add (hR : AxialRotationHolds) (X Y : ℝ → Space → Space) (ι : ℤ × ℤ) (σ : ℝ) (y : Space)
    (hXi : ∀ i : Fin 3, Integrable (fun q : ℝ × ℝ => axialRot (-q.2) (X (σ + q.1) (axialRot q.2 y)) i) rectMeasure)
    (hYi : ∀ i : Fin 3, Integrable (fun q : ℝ × ℝ => axialRot (-q.2) (Y (σ + q.1) (axialRot q.2 y)) i) rectMeasure) :
    modeVel ι (fun s x => X s x + Y s x) σ y = modeVel ι X σ y + modeVel ι Y σ y := by
  funext i
  rw [Pi.add_apply, modeVel_apply, modeVel_apply, modeVel_apply]
  simp only [axialRot_add hR, PiLp.add_apply]
  exact modeAverage_add ι (fun τ φ => axialRot (-φ) (X (σ + τ) (axialRot φ y)) i)
    (fun τ φ => axialRot (-φ) (Y (σ + τ) (axialRot φ y)) i) (hXi i) (hYi i)

private lemma modeVel_sub (hR : AxialRotationHolds) (X Y : ℝ → Space → Space) (ι : ℤ × ℤ) (σ : ℝ) (y : Space)
    (hXi : ∀ i : Fin 3, Integrable (fun q : ℝ × ℝ => axialRot (-q.2) (X (σ + q.1) (axialRot q.2 y)) i) rectMeasure)
    (hYi : ∀ i : Fin 3, Integrable (fun q : ℝ × ℝ => axialRot (-q.2) (Y (σ + q.1) (axialRot q.2 y)) i) rectMeasure) :
    modeVel ι (fun s x => X s x - Y s x) σ y = modeVel ι X σ y - modeVel ι Y σ y := by
  funext i
  rw [Pi.sub_apply, modeVel_apply, modeVel_apply, modeVel_apply]
  simp only [axialRot_sub hR, PiLp.sub_apply]
  exact modeAverage_sub ι (fun τ φ => axialRot (-φ) (X (σ + τ) (axialRot φ y)) i)
    (fun τ φ => axialRot (-φ) (Y (σ + τ) (axialRot φ y)) i) (hXi i) (hYi i)

private lemma re_cdot_eq (a b : Fin 3 → ℂ) : (cdot a b).re = (cnormSq (a + b) - cnormSq (a - b)) / 4 := by
  unfold cdot cnormSq
  rw [Complex.re_sum, ← Finset.sum_sub_distrib, Finset.sum_div]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Pi.add_apply, Pi.sub_apply, Complex.sq_norm, Complex.normSq_add, Complex.normSq_sub]
  ring

private lemma inner_eq_quarter (x y : Space) : inner ℝ x y = (‖x + y‖ ^ 2 - ‖x - y‖ ^ 2) / 4 := by
  rw [norm_add_sq_real, norm_sub_sq_real]
  ring

private lemma norm_add_sq_le (x y : Space) : ‖x + y‖ ^ 2 ≤ 2 * ‖x‖ ^ 2 + 2 * ‖y‖ ^ 2 := by
  nlinarith [norm_add_sq_real x y, norm_sub_sq_real x y, sq_nonneg ‖x - y‖]

private lemma norm_sub_sq_le (x y : Space) : ‖x - y‖ ^ 2 ≤ 2 * ‖x‖ ^ 2 + 2 * ‖y‖ ^ 2 := by
  nlinarith [norm_add_sq_real x y, norm_sub_sq_real x y, sq_nonneg ‖x + y‖]

private lemma aestronglyMeasurable_cnormSq_modeVel (hR : AxialRotationHolds) (Z : ℝ → Space → Space)
    (hZ : AEStronglyMeasurable (fun z : ℝ × Space => Z z.1 z.2) volume) (ι : ℤ × ℤ) :
    AEStronglyMeasurable (fun z : ℝ × Space => cnormSq (modeVel ι Z z.1 z.2)) volume := by
  have hb : ∀ i : Fin 3, AEStronglyMeasurable (fun z : ℝ × Space =>
      modeAverage ι (fun τ φ (_ : Unit) => axialRot (-φ) (Z (z.1 + τ) (axialRot φ z.2)) i) ()) volume := fun i => by
    have h := aestronglyMeasurable_modeAverage ι
      (fun p : ((ℝ × Space) × ℝ) × ℝ => axialRot (-p.2) (Z (p.1.1.1 + p.1.2) (axialRot p.2 p.1.1.2)) i)
      (aestronglyMeasurable_comp_shiftRot_nested hR (fun φ e => axialRot (-φ) e i) (continuous_rotCoord i) Z hZ)
    exact h
  have h := Finset.aestronglyMeasurable_fun_sum (μ := (volume : Measure (ℝ × Space))) (Finset.univ : Finset (Fin 3))
    (fun i _ => (hb i).norm.pow 2)
  exact h

private lemma ae_integrable_comp (hR : AxialRotationHolds) (Z : ℝ → Space → Space)
    (hZ : AEStronglyMeasurable (fun z : ℝ × Space => Z z.1 z.2) volume) (hZp : IsTimePeriodic Z)
    (hZf : periodLIntegral (fun σ y => ‖Z σ y‖ ^ 2) < ⊤) :
    ∀ᵐ z ∂slabMeasure, ∀ i : Fin 3,
      Integrable (fun q : ℝ × ℝ => axialRot (-q.2) (Z (z.1 + q.1) (axialRot q.2 z.2)) i) rectMeasure := by
  have hac2 : slabMeasure.prod rectMeasure ≪ (volume : Measure (ℝ × Space)).prod rectMeasure :=
    slab_ac.prod Measure.AbsolutelyContinuous.rfl
  have hsec : ∀ᵐ z ∂slabMeasure, ∀ i : Fin 3,
      AEStronglyMeasurable (fun q : ℝ × ℝ => axialRot (-q.2) (Z (z.1 + q.1) (axialRot q.2 z.2)) i) rectMeasure := by
    refine ae_all_iff.2 fun i => ?_
    have h := aestronglyMeasurable_comp_shiftRot hR (fun φ e => axialRot (-φ) e i) (continuous_rotCoord i) Z hZ
      rectMeasure
    exact (h.mono_ac hac2).prodMk_left
  have hfin := ae_rect_lt_top hR (fun e : Space => ‖e‖ ^ 2) (continuous_norm.pow 2) Z hZ hZp hZf
  filter_upwards [hfin, hsec] with z hz hzi i
  refine integrable_of_sq_lintegral _ (hzi i) (lt_of_le_of_lt (lintegral_mono fun q => ENNReal.ofReal_le_ofReal ?_) hz)
  rw [← sum_sq_axialRot_coord hR q.2]
  exact Finset.single_le_sum (f := fun j => axialRot (-q.2) (Z (z.1 + q.1) (axialRot q.2 z.2)) j ^ 2)
    (fun j _ => sq_nonneg _) (Finset.mem_univ i)

private lemma modeVel_facts (hT : TorusSquareSumHolds) (hR : AxialRotationHolds) (Z : ℝ → Space → Space)
    (hZ : AEStronglyMeasurable (fun z : ℝ × Space => Z z.1 z.2) volume) (hZp : IsTimePeriodic Z)
    (hZf : periodLIntegral (fun σ y => ‖Z σ y‖ ^ 2) < ⊤) :
    (∀ ι : ℤ × ℤ, Integrable (fun z : ℝ × Space => cnormSq (modeVel ι Z z.1 z.2)) slabMeasure) ∧
    HasSum (fun ι : ℤ × ℤ => ∫ z, cnormSq (modeVel ι Z z.1 z.2) ∂slabMeasure)
      (periodLIntegral (fun σ y => ‖Z σ y‖ ^ 2)).toReal := by
  have hP := velSquareSum hT hR Z hZ hZp hZf
  have hm : ∀ ι : ℤ × ℤ, AEStronglyMeasurable (fun z : ℝ × Space => cnormSq (modeVel ι Z z.1 z.2)) slabMeasure :=
    fun ι => (aestronglyMeasurable_cnormSq_modeVel hR Z hZ ι).mono_ac slab_ac
  have hnn : ∀ ι : ℤ × ℤ, ∀ σ y, 0 ≤ cnormSq (modeVel ι Z σ y) := fun ι σ y =>
    Finset.sum_nonneg fun i _ => sq_nonneg _
  have hA : ∀ ι : ℤ × ℤ, periodLIntegral (fun σ y => cnormSq (modeVel ι Z σ y)) ≠ ⊤ := fun ι =>
    ne_top_of_le_ne_top hZf.ne (hP ▸ ENNReal.le_tsum ι)
  refine ⟨fun ι => integrable_slab _ (hm ι) (hnn ι) (lt_top_iff_ne_top.2 (hA ι)), ?_⟩
  have hfun : (fun ι : ℤ × ℤ => ∫ z, cnormSq (modeVel ι Z z.1 z.2) ∂slabMeasure) =
      fun ι => (periodLIntegral (fun σ y => cnormSq (modeVel ι Z σ y))).toReal :=
    funext fun ι => integral_slab _ (hm ι) (hnn ι)
  have hP' : periodLIntegral (fun σ y => ‖Z σ y‖ ^ 2) =
      ∑' ι : ℤ × ℤ, periodLIntegral (fun σ y => cnormSq (modeVel ι Z σ y)) := hP
  rw [hfun, hP', ENNReal.tsum_toReal_eq hA]
  exact (ENNReal.summable_toReal (hP' ▸ hZf.ne)).hasSum

private lemma polarSquareSum (hT : TorusSquareSumHolds) (hR : AxialRotationHolds) (X Y : ℝ → Space → Space)
    (hX : AEStronglyMeasurable (fun z : ℝ × Space => X z.1 z.2) volume)
    (hY : AEStronglyMeasurable (fun z : ℝ × Space => Y z.1 z.2) volume)
    (hXp : IsTimePeriodic X) (hYp : IsTimePeriodic Y)
    (hXf : periodLIntegral (fun σ y => ‖X σ y‖ ^ 2) < ⊤) (hYf : periodLIntegral (fun σ y => ‖Y σ y‖ ^ 2) < ⊤) :
    HasSum (fun ι : ℤ × ℤ => ∫ σ in Set.Icc (0 : ℝ) 1, ∫ y, (cdot (modeVel ι X σ y) (modeVel ι Y σ y)).re)
      (∫ σ in Set.Icc (0 : ℝ) 1, ∫ y, inner ℝ (X σ y) (Y σ y)) := by
  have hS : AEStronglyMeasurable (fun z : ℝ × Space => X z.1 z.2 + Y z.1 z.2) volume := hX.add hY
  have hD : AEStronglyMeasurable (fun z : ℝ × Space => X z.1 z.2 - Y z.1 z.2) volume := hX.sub hY
  have hSp : IsTimePeriodic (fun s x => X s x + Y s x) := fun σ y => by
    show X (σ + 1) y + Y (σ + 1) y = X σ y + Y σ y
    rw [hXp σ y, hYp σ y]
  have hDp : IsTimePeriodic (fun s x => X s x - Y s x) := fun σ y => by
    show X (σ + 1) y - Y (σ + 1) y = X σ y - Y σ y
    rw [hXp σ y, hYp σ y]
  have hnX : AEStronglyMeasurable (fun z : ℝ × Space => ‖X z.1 z.2‖ ^ 2) slabMeasure :=
    (hX.norm.pow 2).mono_ac slab_ac
  have hnY : AEStronglyMeasurable (fun z : ℝ × Space => ‖Y z.1 z.2‖ ^ 2) slabMeasure :=
    (hY.norm.pow 2).mono_ac slab_ac
  have hnS : AEStronglyMeasurable (fun z : ℝ × Space => ‖X z.1 z.2 + Y z.1 z.2‖ ^ 2) slabMeasure :=
    (hS.norm.pow 2).mono_ac slab_ac
  have hnD : AEStronglyMeasurable (fun z : ℝ × Space => ‖X z.1 z.2 - Y z.1 z.2‖ ^ 2) slabMeasure :=
    (hD.norm.pow 2).mono_ac slab_ac
  have hiX := integrable_slab (fun σ y => ‖X σ y‖ ^ 2) hnX (fun σ y => sq_nonneg _) hXf
  have hiY := integrable_slab (fun σ y => ‖Y σ y‖ ^ 2) hnY (fun σ y => sq_nonneg _) hYf
  have hbound : Integrable (fun z : ℝ × Space => 2 * ‖X z.1 z.2‖ ^ 2 + 2 * ‖Y z.1 z.2‖ ^ 2) slabMeasure :=
    (hiX.const_mul 2).add (hiY.const_mul 2)
  have hiS : Integrable (fun z : ℝ × Space => ‖X z.1 z.2 + Y z.1 z.2‖ ^ 2) slabMeasure := by
    refine hbound.mono hnS (ae_of_all _ fun z => ?_)
    rw [Real.norm_of_nonneg (sq_nonneg _), Real.norm_of_nonneg (by positivity)]
    exact norm_add_sq_le _ _
  have hiD : Integrable (fun z : ℝ × Space => ‖X z.1 z.2 - Y z.1 z.2‖ ^ 2) slabMeasure := by
    refine hbound.mono hnD (ae_of_all _ fun z => ?_)
    rw [Real.norm_of_nonneg (sq_nonneg _), Real.norm_of_nonneg (by positivity)]
    exact norm_sub_sq_le _ _
  have hSf : periodLIntegral (fun σ y => ‖X σ y + Y σ y‖ ^ 2) < ⊤ :=
    period_lt_top_of_integrable (fun σ y => ‖X σ y + Y σ y‖ ^ 2) hnS (fun σ y => sq_nonneg _) hiS
  have hDf : periodLIntegral (fun σ y => ‖X σ y - Y σ y‖ ^ 2) < ⊤ :=
    period_lt_top_of_integrable (fun σ y => ‖X σ y - Y σ y‖ ^ 2) hnD (fun σ y => sq_nonneg _) hiD
  obtain ⟨hmS, hsumS⟩ := modeVel_facts hT hR (fun s x => X s x + Y s x) hS hSp hSf
  obtain ⟨hmD, hsumD⟩ := modeVel_facts hT hR (fun s x => X s x - Y s x) hD hDp hDf
  have hae : ∀ᵐ z ∂slabMeasure, ∀ ι : ℤ × ℤ,
      (cdot (modeVel ι X z.1 z.2) (modeVel ι Y z.1 z.2)).re =
        (cnormSq (modeVel ι (fun s x => X s x + Y s x) z.1 z.2) -
          cnormSq (modeVel ι (fun s x => X s x - Y s x) z.1 z.2)) / 4 := by
    filter_upwards [ae_integrable_comp hR X hX hXp hXf, ae_integrable_comp hR Y hY hYp hYf] with z hzX hzY ι
    rw [re_cdot_eq, modeVel_add hR X Y ι z.1 z.2 hzX hzY, modeVel_sub hR X Y ι z.1 z.2 hzX hzY]
  have hpair : ∀ ι : ℤ × ℤ,
      ∫ σ in Set.Icc (0 : ℝ) 1, ∫ y, (cdot (modeVel ι X σ y) (modeVel ι Y σ y)).re =
        ((∫ z, cnormSq (modeVel ι (fun s x => X s x + Y s x) z.1 z.2) ∂slabMeasure) -
          ∫ z, cnormSq (modeVel ι (fun s x => X s x - Y s x) z.1 z.2) ∂slabMeasure) / 4 := by
    intro ι
    have hq : Integrable (fun z : ℝ × Space => (cnormSq (modeVel ι (fun s x => X s x + Y s x) z.1 z.2) -
        cnormSq (modeVel ι (fun s x => X s x - Y s x) z.1 z.2)) / 4) slabMeasure :=
      ((hmS ι).sub (hmD ι)).div_const 4
    have hre : Integrable (fun z : ℝ × Space => (cdot (modeVel ι X z.1 z.2) (modeVel ι Y z.1 z.2)).re)
        slabMeasure := hq.congr (hae.mono fun z h => (h ι).symm)
    calc ∫ σ in Set.Icc (0 : ℝ) 1, ∫ y, (cdot (modeVel ι X σ y) (modeVel ι Y σ y)).re
        = ∫ z, (cdot (modeVel ι X z.1 z.2) (modeVel ι Y z.1 z.2)).re ∂slabMeasure :=
          (integral_prod _ hre).symm
      _ = ∫ z, (cnormSq (modeVel ι (fun s x => X s x + Y s x) z.1 z.2) -
          cnormSq (modeVel ι (fun s x => X s x - Y s x) z.1 z.2)) / 4 ∂slabMeasure :=
          integral_congr_ae (hae.mono fun z h => h ι)
      _ = _ := by rw [integral_div, integral_sub (hmS ι) (hmD ι)]
  have hval : ∫ σ in Set.Icc (0 : ℝ) 1, ∫ y, inner ℝ (X σ y) (Y σ y) =
      ((periodLIntegral (fun σ y => ‖X σ y + Y σ y‖ ^ 2)).toReal -
        (periodLIntegral (fun σ y => ‖X σ y - Y σ y‖ ^ 2)).toReal) / 4 := by
    have hq : Integrable (fun z : ℝ × Space => (‖X z.1 z.2 + Y z.1 z.2‖ ^ 2 - ‖X z.1 z.2 - Y z.1 z.2‖ ^ 2) / 4)
        slabMeasure := (hiS.sub hiD).div_const 4
    calc ∫ σ in Set.Icc (0 : ℝ) 1, ∫ y, inner ℝ (X σ y) (Y σ y)
        = ∫ σ in Set.Icc (0 : ℝ) 1, ∫ y, (‖X σ y + Y σ y‖ ^ 2 - ‖X σ y - Y σ y‖ ^ 2) / 4 := by
          simp_rw [inner_eq_quarter]
      _ = ∫ z, (‖X z.1 z.2 + Y z.1 z.2‖ ^ 2 - ‖X z.1 z.2 - Y z.1 z.2‖ ^ 2) / 4 ∂slabMeasure :=
          (integral_prod _ hq).symm
      _ = ((∫ z, ‖X z.1 z.2 + Y z.1 z.2‖ ^ 2 ∂slabMeasure) - ∫ z, ‖X z.1 z.2 - Y z.1 z.2‖ ^ 2 ∂slabMeasure) / 4 := by
          rw [integral_div, integral_sub hiS hiD]
      _ = _ := by
          rw [integral_slab (fun σ y => ‖X σ y + Y σ y‖ ^ 2) hnS (fun σ y => sq_nonneg _),
            integral_slab (fun σ y => ‖X σ y - Y σ y‖ ^ 2) hnD (fun σ y => sq_nonneg _)]
  rw [funext hpair, hval]
  exact (hsumS.sub hsumD).div_const 4

theorem modeSquareSumHolds_of (hT : TorusSquareSumHolds) (hR : AxialRotationHolds) : ModeSquareSumHolds :=
  ⟨fun X hX hXp hXf => velSquareSum hT hR X hX hXp hXf,
    fun G hG hGp hGf => gradSquareSum hT hR G hG hGp hGf,
    fun H hH hHp hHf => secondDerivSquareSum hT hR H hH hHp hHf,
    fun X Y hX hY hXp hYp hXf hYf => polarSquareSum hT hR X Y hX hY hXp hYp hXf hYf⟩

end Coercive

end Breakdown
