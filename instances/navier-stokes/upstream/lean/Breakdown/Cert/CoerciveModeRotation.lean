import Breakdown.Cert.CoercivePerturbationFacts

open scoped ENNReal
open MeasureTheory

noncomputable section

namespace Breakdown

namespace Coercive

namespace Internal.ModeRotation

def expFactor (ι : ℤ × ℤ) (τ φ : ℝ) : ℂ :=
  Complex.exp (-(((2 * Real.pi * ι.1 * τ + ι.2 * φ : ℝ) : ℂ) * Complex.I))

abbrev boxMeasure : Measure (ℝ × ℝ) :=
  (volume.restrict (Set.Ioc (0 : ℝ) 1)).prod (volume.restrict (Set.Ioc (0 : ℝ) (2 * Real.pi)))

def orbitMap (p : ℝ × ℝ) (z : ℝ × Space) : ℝ × Space := (z.1 + p.1, axialRot p.2 z.2)

theorem modeAverage_eq {β : Type*} (ι : ℤ × ℤ) (f : ℝ → ℝ → β → ℝ) (b : β) :
    modeAverage ι f b = (1 / (2 * Real.pi) : ℂ) * ∫ τ in (0 : ℝ)..1, ∫ φ in (0 : ℝ)..(2 * Real.pi),
      expFactor ι τ φ * ((f τ φ b : ℝ) : ℂ) := rfl

theorem norm_expFactor (ι : ℤ × ℤ) (τ φ : ℝ) : ‖expFactor ι τ φ‖ = 1 := by
  unfold expFactor
  rw [← neg_mul, ← Complex.ofReal_neg, Complex.norm_exp_ofReal_mul_I]

theorem continuous_expFactor (ι : ℤ × ℤ) : Continuous (fun p : ℝ × ℝ => expFactor ι p.1 p.2) := by
  unfold expFactor
  fun_prop

theorem expFactor_sub (ι : ℤ × ℤ) (τ φ ψ : ℝ) :
    expFactor ι τ (φ - ψ) = Complex.exp (((ι.2 * ψ : ℝ) : ℂ) * Complex.I) * expFactor ι τ φ := by
  unfold expFactor
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem expFactor_add_period (ι : ℤ × ℤ) (τ φ : ℝ) :
    expFactor ι τ (φ + 2 * Real.pi) = expFactor ι τ φ := by
  unfold expFactor
  have h : -(((2 * Real.pi * ι.1 * τ + ι.2 * (φ + 2 * Real.pi) : ℝ) : ℂ) * Complex.I) =
      -(((2 * Real.pi * ι.1 * τ + ι.2 * φ : ℝ) : ℂ) * Complex.I) +
        ((-ι.2 : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
    push_cast
    ring
  rw [h, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

theorem integral_shift (ι : ℤ × ℤ) (τ ψ : ℝ) (q : ℝ → ℂ) (hq : Function.Periodic q (2 * Real.pi)) :
    ∫ φ in (0 : ℝ)..(2 * Real.pi), expFactor ι τ φ * q (φ + ψ) =
      Complex.exp (((ι.2 * ψ : ℝ) : ℂ) * Complex.I) *
        ∫ φ in (0 : ℝ)..(2 * Real.pi), expFactor ι τ φ * q φ := by
  have h1 : (fun φ => expFactor ι τ φ * q (φ + ψ)) =
      fun φ => (fun x => expFactor ι τ (x - ψ) * q x) (φ + ψ) := by
    funext φ
    simp only [add_sub_cancel_right]
  have hper : Function.Periodic (fun x => expFactor ι τ (x - ψ) * q x) (2 * Real.pi) := by
    intro x
    simp only
    rw [show x + 2 * Real.pi - ψ = (x - ψ) + 2 * Real.pi by ring, expFactor_add_period, hq x]
  rw [h1, intervalIntegral.integral_comp_add_right (fun x => expFactor ι τ (x - ψ) * q x) ψ,
    zero_add, add_comm (2 * Real.pi) ψ, hper.intervalIntegral_add_eq ψ 0, zero_add,
    ← intervalIntegral.integral_const_mul]
  congr 1
  funext x
  rw [expFactor_sub]
  ring

theorem iter_eq_prod (h : ℝ → ℝ → ℂ) (hi : Integrable (fun p : ℝ × ℝ => h p.1 p.2) boxMeasure) :
    ∫ τ in (0 : ℝ)..1, ∫ φ in (0 : ℝ)..(2 * Real.pi), h τ φ = ∫ p, h p.1 p.2 ∂boxMeasure := by
  rw [integral_prod _ hi, intervalIntegral.integral_of_le zero_le_one]
  congr 1
  funext τ
  rw [intervalIntegral.integral_of_le (by positivity)]

theorem modeAverage_sum {κ : Type*} [Fintype κ] (ι : ℤ × ℤ) (r : κ → ℝ) (a : κ → ℝ → ℝ → ℝ)
    (ha : ∀ j, Integrable (fun p : ℝ × ℝ => a j p.1 p.2) boxMeasure) :
    ∫ τ in (0 : ℝ)..1, ∫ φ in (0 : ℝ)..(2 * Real.pi),
        expFactor ι τ φ * ((∑ j, r j * a j τ φ : ℝ) : ℂ) =
      ∑ j, (r j : ℂ) * ∫ τ in (0 : ℝ)..1, ∫ φ in (0 : ℝ)..(2 * Real.pi),
        expFactor ι τ φ * ((a j τ φ : ℝ) : ℂ) := by
  have hint : ∀ j, Integrable (fun p : ℝ × ℝ => expFactor ι p.1 p.2 * ((a j p.1 p.2 : ℝ) : ℂ))
      boxMeasure := by
    intro j
    refine (ha j).norm.mono' ((continuous_expFactor ι).aestronglyMeasurable.mul
      (Complex.continuous_ofReal.comp_aestronglyMeasurable (ha j).1)) ?_
    refine Filter.Eventually.of_forall fun p => ?_
    simp only [norm_mul, norm_expFactor, one_mul, Complex.norm_real, le_refl]
  have hfun : (fun p : ℝ × ℝ => expFactor ι p.1 p.2 * ((∑ j, r j * a j p.1 p.2 : ℝ) : ℂ)) =
      fun p => ∑ j, (r j : ℂ) * (expFactor ι p.1 p.2 * ((a j p.1 p.2 : ℝ) : ℂ)) := by
    funext p
    push_cast
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  have hsum : Integrable (fun p : ℝ × ℝ => expFactor ι p.1 p.2 * ((∑ j, r j * a j p.1 p.2 : ℝ) : ℂ))
      boxMeasure := by
    rw [hfun]
    exact integrable_finsetSum _ fun j _ => (hint j).const_mul _
  calc ∫ τ in (0 : ℝ)..1, ∫ φ in (0 : ℝ)..(2 * Real.pi),
        expFactor ι τ φ * ((∑ j, r j * a j τ φ : ℝ) : ℂ)
      = ∫ p, expFactor ι p.1 p.2 * ((∑ j, r j * a j p.1 p.2 : ℝ) : ℂ) ∂boxMeasure :=
        iter_eq_prod (fun τ φ => expFactor ι τ φ * ((∑ j, r j * a j τ φ : ℝ) : ℂ)) hsum
    _ = ∫ p, ∑ j, (r j : ℂ) * (expFactor ι p.1 p.2 * ((a j p.1 p.2 : ℝ) : ℂ)) ∂boxMeasure := by
        rw [hfun]
    _ = ∑ j, (r j : ℂ) * ∫ p, expFactor ι p.1 p.2 * ((a j p.1 p.2 : ℝ) : ℂ) ∂boxMeasure := by
        rw [integral_finsetSum _ fun j _ => (hint j).const_mul _]
        exact Finset.sum_congr rfl fun j _ => integral_const_mul _ _
    _ = _ := by
        refine Finset.sum_congr rfl fun j _ => ?_
        congr 1
        exact (iter_eq_prod (fun τ φ => expFactor ι τ φ * ((a j τ φ : ℝ) : ℂ)) (hint j)).symm

theorem coord_sum (a : Fin 3) (r : Fin 3 → ℝ) (Y : Fin 3 → Space) :
    (∑ c, r c • Y c) a = ∑ c, r c * Y c a := by
  simp

theorem axialRot_apply (φ : ℝ) (x : Space) (i : Fin 3) :
    axialRot φ x i = ∑ j : Fin 3, axialRot φ (unitVector j) i * x j := by
  fin_cases i <;> simp [axialRot, unitVector, Fin.sum_univ_three]; ring

theorem axialRot_eq_sum (φ : ℝ) (x : Space) :
    axialRot φ x = ∑ c : Fin 3, x c • axialRot φ (unitVector c) := by
  ext i
  rw [coord_sum, axialRot_apply φ x i]
  exact Finset.sum_congr rfl fun c _ => mul_comm _ _

theorem axialRot_sum_apply (hRot : AxialRotationHolds) (φ : ℝ) (r : Fin 3 → ℝ) (Z : Fin 3 → Space)
    (a : Fin 3) : axialRot φ (∑ c, r c • Z c) a = ∑ c, r c * axialRot φ (Z c) a := by
  obtain ⟨R, hR⟩ := hRot.1 φ
  simp_rw [← hR, map_sum, map_smul]
  exact coord_sum a r (fun c => R (Z c))

theorem norm_axialRot (hRot : AxialRotationHolds) (φ : ℝ) (y : Space) : ‖axialRot φ y‖ = ‖y‖ := by
  obtain ⟨R, hR⟩ := hRot.1 φ
  rw [← hR, R.norm_map]

theorem axialRot_sub_period (hRot : AxialRotationHolds) (φ : ℝ) (y : Space) :
    axialRot (φ - 2 * Real.pi) y = axialRot φ y := by
  have h := hRot.2.2.2.1 (φ - 2 * Real.pi) y
  rw [sub_add_cancel] at h
  exact h.symm

theorem axialRot_cancel (hRot : AxialRotationHolds) (ψ : ℝ) (x : Space) :
    axialRot ψ (axialRot (-ψ) x) = x := by
  rw [← hRot.2.1, add_neg_cancel, hRot.2.2.1]

theorem axialRot_neg_comp (hRot : AxialRotationHolds) (φ ψ : ℝ) (w : Space) :
    axialRot (-φ) w = axialRot ψ (axialRot (-(φ + ψ)) w) := by
  rw [← hRot.2.1]
  congr 1
  ring

theorem continuous_axialRot : Continuous (fun q : ℝ × Space => axialRot q.1 q.2) := by
  unfold axialRot
  fun_prop

theorem continuous_orbitMap : Continuous (Function.uncurry orbitMap) := by
  show Continuous (fun w : (ℝ × ℝ) × (ℝ × Space) => (w.2.1 + w.1.1, axialRot w.1.2 w.2.2))
  unfold axialRot
  fun_prop

theorem orbitMap_eq (hRot : AxialRotationHolds) (p : ℝ × ℝ) :
    ∃ R : Space ≃ₗᵢ[ℝ] Space, orbitMap p = Prod.map (· + p.1) R := by
  obtain ⟨R, hR⟩ := hRot.1 p.2
  exact ⟨R, funext fun z => by rw [orbitMap, Prod.map_apply, hR]⟩

theorem measurePreserving_orbitMap (hRot : AxialRotationHolds) (p : ℝ × ℝ) :
    MeasurePreserving (orbitMap p) volume volume := by
  obtain ⟨R, hR⟩ := orbitMap_eq hRot p
  rw [hR, Measure.volume_eq_prod]
  exact (measurePreserving_add_right volume p.1).prod R.measurePreserving

theorem measurableEmbedding_orbitMap (hRot : AxialRotationHolds) (p : ℝ × ℝ) :
    MeasurableEmbedding (orbitMap p) := by
  obtain ⟨R, hR⟩ := orbitMap_eq hRot p
  rw [hR]
  exact ((MeasurableEquiv.addRight p.1).prodCongr R.toHomeomorph.toMeasurableEquiv).measurableEmbedding

theorem orbitMap_mem (hRot : AxialRotationHolds) {p : ℝ × ℝ} (hp : p.1 ∈ Set.Ioc (0 : ℝ) 1) {N : ℝ}
    {z : ℝ × Space} (hz : z ∈ Metric.closedBall (0 : ℝ × Space) N) :
    orbitMap p z ∈ Metric.closedBall (0 : ℝ × Space) (N + 1) := by
  rw [mem_closedBall_zero_iff] at hz ⊢
  have h1 : ‖z.1‖ ≤ N := (norm_fst_le z).trans hz
  have h2 : ‖z.2‖ ≤ N := (norm_snd_le z).trans hz
  have h3 : ‖axialRot p.2 z.2‖ = ‖z.2‖ := norm_axialRot hRot _ _
  have h4 : ‖p.1‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_of_pos hp.1]
    exact hp.2
  show ‖((z.1 + p.1, axialRot p.2 z.2) : ℝ × Space)‖ ≤ N + 1
  rw [Prod.norm_def]
  exact max_le ((norm_add_le _ _).trans (by linarith)) (by linarith)

theorem ae_integrable_orbit (hRot : AxialRotationHolds) {X : Type*} [NormedAddCommGroup X]
    {u : ℝ × Space → X} (hu : LocallyIntegrable u volume) :
    ∀ᵐ z : ℝ × Space, Integrable (fun p : ℝ × ℝ => u (orbitMap p z)) boxMeasure := by
  have hS : MeasurePreserving (fun w : (ℝ × ℝ) × (ℝ × Space) => (w.1, orbitMap w.1 w.2))
      (boxMeasure.prod volume) (boxMeasure.prod volume) :=
    (MeasurePreserving.id boxMeasure).skew_product continuous_orbitMap.measurable
      (Filter.Eventually.of_forall fun p => (measurePreserving_orbitMap hRot p).map_eq)
  have hF : AEStronglyMeasurable (fun w : (ℝ × ℝ) × (ℝ × Space) => u (orbitMap w.1 w.2))
      (boxMeasure.prod volume) :=
    (hu.aestronglyMeasurable.comp_snd).comp_measurePreserving hS
  have hF' : AEStronglyMeasurable (fun w : (ℝ × Space) × (ℝ × ℝ) => u (orbitMap w.2 w.1))
      ((volume : Measure (ℝ × Space)).prod boxMeasure) := hF.prod_swap
  have hslice := hF'.prodMk_left
  have hbox : boxMeasure Set.univ < ⊤ := by
    show ((volume.restrict (Set.Ioc (0 : ℝ) 1)).prod
      (volume.restrict (Set.Ioc (0 : ℝ) (2 * Real.pi)))) Set.univ < ⊤
    rw [← Set.univ_prod_univ, Measure.prod_prod, Measure.restrict_apply_univ,
      Measure.restrict_apply_univ, Real.volume_Ioc, Real.volume_Ioc]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top
  have hboxmem : ∀ᵐ p ∂boxMeasure, p ∈ Set.Ioc (0 : ℝ) 1 ×ˢ Set.Ioc (0 : ℝ) (2 * Real.pi) := by
    show ∀ᵐ p ∂((volume.restrict (Set.Ioc (0 : ℝ) 1)).prod
      (volume.restrict (Set.Ioc (0 : ℝ) (2 * Real.pi)))), _
    rw [Measure.prod_restrict]
    exact ae_restrict_mem (measurableSet_Ioc.prod measurableSet_Ioc)
  have hfin : ∀ N : ℕ, ∀ᵐ z : ℝ × Space, z ∈ Metric.closedBall (0 : ℝ × Space) N →
      ∫⁻ p, ‖u (orbitMap p z)‖ₑ ∂boxMeasure < ⊤ := by
    intro N
    rw [← ae_restrict_iff' Metric.isClosed_closedBall.measurableSet]
    have hK' : ∫⁻ w in Metric.closedBall (0 : ℝ × Space) ((N : ℝ) + 1), ‖u w‖ₑ < ⊤ :=
      (hu.integrableOn_isCompact (isCompact_closedBall _ _)).2
    have hp : ∀ p : ℝ × ℝ, p ∈ Set.Ioc (0 : ℝ) 1 ×ˢ Set.Ioc (0 : ℝ) (2 * Real.pi) →
        ∫⁻ z in Metric.closedBall (0 : ℝ × Space) N, ‖u (orbitMap p z)‖ₑ ≤
          ∫⁻ w in Metric.closedBall (0 : ℝ × Space) ((N : ℝ) + 1), ‖u w‖ₑ := by
      intro p hp
      rw [← lintegral_indicator Metric.isClosed_closedBall.measurableSet,
        ← lintegral_indicator Metric.isClosed_closedBall.measurableSet,
        ← (measurePreserving_orbitMap hRot p).lintegral_comp_emb (measurableEmbedding_orbitMap hRot p)
          ((Metric.closedBall (0 : ℝ × Space) ((N : ℝ) + 1)).indicator fun w => ‖u w‖ₑ)]
      refine lintegral_mono fun z => ?_
      by_cases hz : z ∈ Metric.closedBall (0 : ℝ × Space) N
      · rw [Set.indicator_of_mem hz, Set.indicator_of_mem (orbitMap_mem hRot hp.1 hz)]
      · rw [Set.indicator_of_notMem hz]
        simp
    have hle : ∫⁻ z in Metric.closedBall (0 : ℝ × Space) N, ∫⁻ p, ‖u (orbitMap p z)‖ₑ ∂boxMeasure ≤
        ∫⁻ _p, (∫⁻ w in Metric.closedBall (0 : ℝ × Space) ((N : ℝ) + 1), ‖u w‖ₑ) ∂boxMeasure := by
      rw [lintegral_lintegral_swap ?_]
      · refine lintegral_mono_ae ?_
        filter_upwards [hboxmem] with p hpm
        exact hp p hpm
      · have e : (volume.restrict (Metric.closedBall (0 : ℝ × Space) N)).prod boxMeasure =
            ((volume : Measure (ℝ × Space)).prod boxMeasure).restrict
              (Metric.closedBall (0 : ℝ × Space) N ×ˢ Set.univ) := by
          rw [← Measure.prod_restrict, Measure.restrict_univ]
        rw [e]
        exact hF'.enorm.restrict
    refine ae_lt_top' (hF'.enorm.lintegral_prod_right'.restrict) ?_
    refine (lt_of_le_of_lt hle ?_).ne
    rw [lintegral_const]
    exact ENNReal.mul_lt_top hK' hbox
  have hall := ae_all_iff.2 hfin
  filter_upwards [hall, hslice] with z h1 h2
  obtain ⟨N, hN⟩ := exists_nat_ge ‖z‖
  exact ⟨h2, h1 N (mem_closedBall_zero_iff.2 hN)⟩


theorem integrable_velComponent (hRot : AxialRotationHolds) {v : ℝ → Space → Space} {z : ℝ × Space}
    (hz : Integrable (fun p : ℝ × ℝ => v (z.1 + p.1) (axialRot p.2 z.2)) boxMeasure) (j : Fin 3) :
    Integrable (fun p : ℝ × ℝ => axialRot (-p.2) (v (z.1 + p.1) (axialRot p.2 z.2)) j) boxMeasure := by
  refine hz.norm.mono' ?_ (Filter.Eventually.of_forall fun p => ?_)
  · have hc : Continuous (fun q : (ℝ × ℝ) × Space => axialRot (-q.1.2) q.2 j) := by
      unfold axialRot
      fun_prop
    have hm : AEStronglyMeasurable (fun p : ℝ × ℝ => (p, v (z.1 + p.1) (axialRot p.2 z.2)))
        boxMeasure := aestronglyMeasurable_id.prodMk hz.1
    have h2 := hc.comp_aestronglyMeasurable hm
    exact h2
  · exact (PiLp.norm_apply_le _ j).trans (norm_axialRot hRot _ _).le

theorem integrable_gradComponent (hRot : AxialRotationHolds) {G : ℝ → Space → (Space →L[ℝ] Space)}
    {z : ℝ × Space} (hz : Integrable (fun p : ℝ × ℝ => G (z.1 + p.1) (axialRot p.2 z.2)) boxMeasure)
    (ac : Fin 3 × Fin 3) :
    Integrable (fun p : ℝ × ℝ =>
      axialRot (-p.2) (G (z.1 + p.1) (axialRot p.2 z.2) (axialRot p.2 (unitVector ac.2))) ac.1)
      boxMeasure := by
  refine hz.norm.mono' ?_ (Filter.Eventually.of_forall fun p => ?_)
  · have hc : Continuous (fun q : (ℝ × ℝ) × (Space →L[ℝ] Space) =>
        axialRot (-q.1.2) (q.2 (axialRot q.1.2 (unitVector ac.2))) ac.1) := by
      unfold axialRot
      fun_prop
    have hm : AEStronglyMeasurable (fun p : ℝ × ℝ => (p, G (z.1 + p.1) (axialRot p.2 z.2)))
        boxMeasure := aestronglyMeasurable_id.prodMk hz.1
    have h2 := hc.comp_aestronglyMeasurable hm
    exact h2
  · refine (PiLp.norm_apply_le _ ac.1).trans ?_
    rw [norm_axialRot hRot]
    refine ((G (z.1 + p.1) (axialRot p.2 z.2)).le_opNorm _).trans ?_
    rw [norm_axialRot hRot, unitVector, PiLp.norm_single, norm_one, mul_one]

theorem modeVel_rotation_of (hRot : AxialRotationHolds) {v : ℝ → Space → Space} (ι : ℤ × ℤ) (ψ : ℝ)
    {z : ℝ × Space} (hz : Integrable (fun p : ℝ × ℝ => v (z.1 + p.1) (axialRot p.2 z.2)) boxMeasure) :
    modeVel ι v z.1 (axialRot ψ z.2) =
      fun i => Complex.exp (((ι.2 * ψ : ℝ) : ℂ) * Complex.I) * rotC ψ (modeVel ι v z.1 z.2) i := by
  funext i
  have hq : ∀ τ, Function.Periodic
      (fun φ => ((axialRot ψ (axialRot (-φ) (v (z.1 + τ) (axialRot φ z.2))) i : ℝ) : ℂ))
      (2 * Real.pi) := by
    intro τ φ
    simp only [show -(φ + 2 * Real.pi) = -φ - 2 * Real.pi by ring, axialRot_sub_period hRot,
      hRot.2.2.2.1]
  have hsplit : ∀ τ φ, ((axialRot ψ (axialRot (-φ) (v (z.1 + τ) (axialRot φ z.2))) i : ℝ) : ℂ) =
      ((∑ j : Fin 3, axialRot ψ (unitVector j) i *
        axialRot (-φ) (v (z.1 + τ) (axialRot φ z.2)) j : ℝ) : ℂ) := by
    intro τ φ
    rw [axialRot_apply ψ _ i]
  have e := modeAverage_sum ι (fun j => axialRot ψ (unitVector j) i)
    (fun j τ φ => axialRot (-φ) (v (z.1 + τ) (axialRot φ z.2)) j) (integrable_velComponent hRot hz)
  calc modeVel ι v z.1 (axialRot ψ z.2) i
      = (1 / (2 * Real.pi) : ℂ) * ∫ τ in (0 : ℝ)..1, ∫ φ in (0 : ℝ)..(2 * Real.pi),
          expFactor ι τ φ * ((axialRot ψ (axialRot (-(φ + ψ))
            (v (z.1 + τ) (axialRot (φ + ψ) z.2))) i : ℝ) : ℂ) := by
        unfold modeVel
        rw [modeAverage_eq]
        congr 1
        refine intervalIntegral.integral_congr fun τ _ => ?_
        refine intervalIntegral.integral_congr fun φ _ => ?_
        simp only
        rw [← axialRot_neg_comp hRot φ ψ, hRot.2.1 φ ψ z.2]
    _ = (1 / (2 * Real.pi) : ℂ) * ∫ τ in (0 : ℝ)..1, Complex.exp (((ι.2 * ψ : ℝ) : ℂ) * Complex.I) *
          ∫ φ in (0 : ℝ)..(2 * Real.pi),
            expFactor ι τ φ * ((axialRot ψ (axialRot (-φ) (v (z.1 + τ) (axialRot φ z.2))) i : ℝ) : ℂ) := by
        congr 1
        refine intervalIntegral.integral_congr fun τ _ => ?_
        exact integral_shift ι τ ψ
          (fun φ => ((axialRot ψ (axialRot (-φ) (v (z.1 + τ) (axialRot φ z.2))) i : ℝ) : ℂ)) (hq τ)
    _ = Complex.exp (((ι.2 * ψ : ℝ) : ℂ) * Complex.I) * ((1 / (2 * Real.pi) : ℂ) *
          ∫ τ in (0 : ℝ)..1, ∫ φ in (0 : ℝ)..(2 * Real.pi),
            expFactor ι τ φ * ((∑ j : Fin 3, axialRot ψ (unitVector j) i *
              axialRot (-φ) (v (z.1 + τ) (axialRot φ z.2)) j : ℝ) : ℂ)) := by
        rw [intervalIntegral.integral_const_mul]
        simp_rw [hsplit]
        ring
    _ = Complex.exp (((ι.2 * ψ : ℝ) : ℂ) * Complex.I) * ((1 / (2 * Real.pi) : ℂ) *
          ∑ j : Fin 3, ((axialRot ψ (unitVector j) i : ℝ) : ℂ) *
            ∫ τ in (0 : ℝ)..1, ∫ φ in (0 : ℝ)..(2 * Real.pi),
              expFactor ι τ φ * ((axialRot (-φ) (v (z.1 + τ) (axialRot φ z.2)) j : ℝ) : ℂ)) := by
        rw [e]
    _ = _ := by
        unfold rotC
        congr 1
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        unfold modeVel
        rw [modeAverage_eq]
        ring

theorem modeGrad_rotation_of (hRot : AxialRotationHolds) {G : ℝ → Space → (Space →L[ℝ] Space)}
    (ι : ℤ × ℤ) (ψ : ℝ) {z : ℝ × Space}
    (hz : Integrable (fun p : ℝ × ℝ => G (z.1 + p.1) (axialRot p.2 z.2)) boxMeasure) :
    modeGrad ι G z.1 (axialRot ψ z.2) =
      fun ij => Complex.exp (((ι.2 * ψ : ℝ) : ℂ) * Complex.I) * rotCMat ψ (modeGrad ι G z.1 z.2) ij := by
  funext ij
  obtain ⟨i, j⟩ := ij
  have hq : ∀ τ, Function.Periodic
      (fun φ => ((axialRot ψ (axialRot (-φ) (G (z.1 + τ) (axialRot φ z.2)
        (axialRot φ (axialRot (-ψ) (unitVector j))))) i : ℝ) : ℂ)) (2 * Real.pi) := by
    intro τ φ
    simp only [show -(φ + 2 * Real.pi) = -φ - 2 * Real.pi by ring, axialRot_sub_period hRot,
      hRot.2.2.2.1]
  have hsplit : ∀ τ φ, ((axialRot ψ (axialRot (-φ) (G (z.1 + τ) (axialRot φ z.2)
        (axialRot φ (axialRot (-ψ) (unitVector j))))) i : ℝ) : ℂ) =
      ((∑ ac : Fin 3 × Fin 3, (axialRot ψ (unitVector ac.1) i * axialRot (-ψ) (unitVector j) ac.2) *
        axialRot (-φ) (G (z.1 + τ) (axialRot φ z.2) (axialRot φ (unitVector ac.2))) ac.1 : ℝ) : ℂ) := by
    intro τ φ
    congr 1
    rw [axialRot_apply ψ _ i, axialRot_eq_sum φ (axialRot (-ψ) (unitVector j))]
    simp_rw [map_sum, map_smul]
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [axialRot_sum_apply hRot, Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    dsimp only
    ring
  have e := modeAverage_sum ι
    (fun ac : Fin 3 × Fin 3 => axialRot ψ (unitVector ac.1) i * axialRot (-ψ) (unitVector j) ac.2)
    (fun ac τ φ => axialRot (-φ) (G (z.1 + τ) (axialRot φ z.2) (axialRot φ (unitVector ac.2))) ac.1)
    (integrable_gradComponent hRot hz)
  calc modeGrad ι G z.1 (axialRot ψ z.2) (i, j)
      = (1 / (2 * Real.pi) : ℂ) * ∫ τ in (0 : ℝ)..1, ∫ φ in (0 : ℝ)..(2 * Real.pi),
          expFactor ι τ φ * ((axialRot ψ (axialRot (-(φ + ψ)) (G (z.1 + τ) (axialRot (φ + ψ) z.2)
            (axialRot (φ + ψ) (axialRot (-ψ) (unitVector j))))) i : ℝ) : ℂ) := by
        unfold modeGrad
        rw [modeAverage_eq]
        congr 1
        refine intervalIntegral.integral_congr fun τ _ => ?_
        refine intervalIntegral.integral_congr fun φ _ => ?_
        simp only
        rw [← axialRot_neg_comp hRot φ ψ, hRot.2.1 φ ψ z.2, hRot.2.1 φ ψ, axialRot_cancel hRot]
    _ = (1 / (2 * Real.pi) : ℂ) * ∫ τ in (0 : ℝ)..1, Complex.exp (((ι.2 * ψ : ℝ) : ℂ) * Complex.I) *
          ∫ φ in (0 : ℝ)..(2 * Real.pi),
            expFactor ι τ φ * ((axialRot ψ (axialRot (-φ) (G (z.1 + τ) (axialRot φ z.2)
              (axialRot φ (axialRot (-ψ) (unitVector j))))) i : ℝ) : ℂ) := by
        congr 1
        refine intervalIntegral.integral_congr fun τ _ => ?_
        exact integral_shift ι τ ψ
          (fun φ => ((axialRot ψ (axialRot (-φ) (G (z.1 + τ) (axialRot φ z.2)
            (axialRot φ (axialRot (-ψ) (unitVector j))))) i : ℝ) : ℂ)) (hq τ)
    _ = Complex.exp (((ι.2 * ψ : ℝ) : ℂ) * Complex.I) * ((1 / (2 * Real.pi) : ℂ) *
          ∫ τ in (0 : ℝ)..1, ∫ φ in (0 : ℝ)..(2 * Real.pi),
            expFactor ι τ φ * ((∑ ac : Fin 3 × Fin 3,
              (axialRot ψ (unitVector ac.1) i * axialRot (-ψ) (unitVector j) ac.2) *
              axialRot (-φ) (G (z.1 + τ) (axialRot φ z.2) (axialRot φ (unitVector ac.2))) ac.1 : ℝ) : ℂ)) := by
        rw [intervalIntegral.integral_const_mul]
        simp_rw [hsplit]
        ring
    _ = Complex.exp (((ι.2 * ψ : ℝ) : ℂ) * Complex.I) * ((1 / (2 * Real.pi) : ℂ) *
          ∑ ac : Fin 3 × Fin 3,
            ((axialRot ψ (unitVector ac.1) i * axialRot (-ψ) (unitVector j) ac.2 : ℝ) : ℂ) *
            ∫ τ in (0 : ℝ)..1, ∫ φ in (0 : ℝ)..(2 * Real.pi),
              expFactor ι τ φ * ((axialRot (-φ) (G (z.1 + τ) (axialRot φ z.2)
                (axialRot φ (unitVector ac.2))) ac.1 : ℝ) : ℂ)) := by
        rw [e]
    _ = _ := by
        unfold rotCMat
        congr 1
        rw [Finset.mul_sum, Fintype.sum_prod_type]
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => ?_
        unfold modeGrad
        rw [modeAverage_eq]
        push_cast
        ring

end Internal.ModeRotation

open Internal.ModeRotation in
theorem modeRotationHolds_of (hRot : AxialRotationHolds) (hLoc : PerturbationLocalIntegrabilityHolds) :
    ModeRotationHolds := by
  intro Γ P v G H g hv ι ψ
  obtain ⟨hlv, hlG, -⟩ := hLoc Γ P v G H g hv
  refine ⟨?_, ?_⟩
  · filter_upwards [ae_integrable_orbit hRot hlv] with z hz
    exact modeVel_rotation_of hRot ι ψ hz
  · filter_upwards [ae_integrable_orbit hRot hlG] with z hz
    exact modeGrad_rotation_of hRot ι ψ hz

end Coercive

end Breakdown
