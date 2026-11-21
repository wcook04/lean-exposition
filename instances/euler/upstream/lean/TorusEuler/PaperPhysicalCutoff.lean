import TorusEuler.HierarchyPhysicalPressureBounds
import TorusEuler.TruncatedChildStage

/-! The physical cutoff, pressure, and residual of Proposition 5.11. -/

open Filter MeasureTheory Set UnitAddTorus
open scoped ContDiff InnerProductSpace Topology

namespace TorusEuler

noncomputable section

local notation "Slab(" T ")" => Icc (0 : ℝ) T
local notation "Lift(" T ")" => Set.prod (Icc (0 : ℝ) T) (univ : Set Vec3)

/-- The time-uniform spatial half-Hölder norm on the closed slab. -/
def slabSpatialHolderHalfNorm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (T : ℝ) (m : ℕ) (u : ℝ → Vec3 → E) : ℝ :=
  ⨆ t : Slab(T), spatialHolderHalfNorm m (u t)

private theorem slice_smooth {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {T t : ℝ} {f : ℝ → Vec3 → E}
    (hf : ContDiffOn ℝ ∞ (Function.uncurry f) Lift(T)) (ht : t ∈ Slab(T)) :
    ContDiff ℝ ∞ (f t) :=
  contDiffOn_univ.mp (hf.comp (contDiff_const.prodMk contDiff_id).contDiffOn
    (fun x _ => ⟨ht, mem_univ x⟩))

private theorem hessianSub {p q : Vec3 → ℝ} (hp : ContDiff ℝ 2 p) (hq : ContDiff ℝ 2 q) (x : Vec3) :
    fderiv ℝ (gradient (p - q)) x = fderiv ℝ (gradient p) x - fderiv ℝ (gradient q) x := by
  have hH := fderiv_gradient_add_three_pressures hq (hp.sub hq)
    (contDiff_const : ContDiff ℝ 2 (0 : Vec3 → ℝ)) x
  change fderiv ℝ (gradient (q + (p - q) + (0 : Vec3 → ℝ))) x =
    fderiv ℝ (gradient q) x + fderiv ℝ (gradient (p - q)) x +
      fderiv ℝ (gradient (0 : Vec3 → ℝ)) x at hH
  have hsum : q + (p - q) + (0 : Vec3 → ℝ) = p := by abel
  rw [hsum] at hH
  rw [show gradient (0 : Vec3 → ℝ) = 0 from gradient_fun_const' (0 : ℝ),
    fderiv_zero, Pi.zero_apply, add_zero] at hH
  rw [hH]
  abel

/-- The normalized smooth periodic Poisson pressure is unique. This
applies to the pressure in Proposition 5.11 at each time of the slab. -/
theorem periodicPoissonPressure_unique {p q : Vec3 → ℝ}
    (hp : ContDiff ℝ ∞ p) (hq : ContDiff ℝ ∞ q)
    (hpper : SpatiallyPeriodic p) (hqper : SpatiallyPeriodic q)
    (hpmean : (∫ x in centeredCell, p x) = 0) (hqmean : (∫ x in centeredCell, q x) = 0)
    (hEq : ∀ x, divergence (gradient p) x = divergence (gradient q) x) : p = q := by
  let r : EndpointSmoothPotential := ⟨p - q, hp.sub hq,
    fun n x => by simp only [Pi.sub_apply, hpper n x, hqper n x]⟩
  have hGrad (f : Vec3 → ℝ) (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (gradient f) :=
    (InnerProductSpace.toDual ℝ Vec3).symm.contDiff.comp (hf.fderiv_right (m := ∞) (by simp))
  have hrGrad : gradient r.lift = gradient p - gradient q := by
    funext x
    change gradient (p - q) x = gradient p x - gradient q x
    simp only [gradient, fderiv_sub (hp.differentiable (by simp) x)
      (hq.differentiable (by simp) x), map_sub]
  have hDiv (x : Vec3) : divergence (gradient r.lift) x = 0 := by
    rw [hrGrad]
    have hdiff : divergence (gradient p - gradient q) x =
        divergence (gradient p) x - divergence (gradient q) x := by
      simp only [divergence, fderiv_sub ((hGrad p hp).differentiable (by simp) x)
        ((hGrad q hq).differentiable (by simp) x), _root_.sub_apply, PiLp.sub_apply,
        Finset.sum_sub_distrib]
    rw [hdiff, hEq x, sub_self]
  have hz : gradient r.lift = 0 :=
    (periodicLerayHolderLift_eq_self_of_divergence_free (hGrad r.lift r.smooth)
      (r.periodic.gradient (r.smooth.differentiable (by simp))) hDiv).symm.trans
      (periodicLerayHolderLift_gradient_eq_zero r)
  have hD (x : Vec3) : fderiv ℝ r.lift x = 0 := by
    apply (InnerProductSpace.toDual ℝ Vec3).symm.injective
    change gradient r.lift x = (InnerProductSpace.toDual ℝ Vec3).symm 0
    rw [map_zero]
    exact congrFun hz x
  have hConst : r.lift = fun _ => r.lift 0 :=
    funext fun x => is_const_of_fderiv_eq_zero (r.smooth.differentiable (by simp)) hD x (0 : Vec3)
  have hmean : (∫ x in centeredCell, r.lift x) = 0 := by
    change (∫ x in centeredCell, p x - q x) = _
    rw [integral_sub (hp.continuous.continuousOn.integrableOn_compact isCompact_centeredCell)
      (hq.continuous.continuousOn.integrableOn_compact isCompact_centeredCell), hpmean, hqmean, sub_self]
  have hcell : centeredCell ∈ 𝓝 (0 : Vec3) := by
    apply mem_of_superset (Metric.ball_mem_nhds (0 : Vec3) (show 0 < 1 / 2 by norm_num))
    intro x hx j
    have hnorm : ‖x‖ < (1 : ℝ) / 2 := by simpa only [Metric.mem_ball, dist_zero_right] using hx
    exact abs_le.mp ((PiLp.norm_apply_le x j).trans hnorm.le)
  have hV : (volume : Measure Vec3).real centeredCell ≠ 0 :=
    (ENNReal.toReal_pos (Measure.measure_pos_of_mem_nhds volume hcell).ne'
      isCompact_centeredCell.measure_ne_top).ne'
  rw [hConst, setIntegral_const, smul_eq_mul] at hmean
  have hzero := (mul_eq_zero.mp hmean).resolve_left hV
  funext x
  have h := congrFun hConst x
  change p x - q x = r.lift 0 at h
  exact sub_eq_zero.mp (h.trans hzero)

/-- Proposition 5.11 with the actual real cutoff and mean-zero Poisson
pressure. The constants are fixed before the slab and the approximation.
The sum of the two time norms has the stated single residual-plus-tail
majorant. -/
theorem paperProposition511_physicalCutoff {ψ : Vec3 → ℝ}
    (hEven : Function.Even ψ) (hSupport : ∀ ξ, 2 < ‖ξ‖ → ψ ξ = 0)
    (hSmooth : ContDiff ℝ ∞ ψ) (hUnit : ∀ ξ, ‖ξ‖ ≤ 1 → ψ ξ = 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ P : ℕ, 2 ≤ P → ∃ K : ℝ, 0 ≤ K ∧
      ∀ {T Λ stepBound : ℝ} {V RV : Velocity} {pU : Pressure}
        (_hT : 0 < T) (_hΛ : 1 ≤ Λ) (approximatePressure : ℝ → EndpointSmoothPotential),
        ContDiffOn ℝ ∞ (Function.uncurry V) Lift(T) →
        ContDiffOn ℝ ∞ (Function.uncurry RV) Lift(T) →
        (∀ t ∈ Slab(T), SpatiallyPeriodic (V t)) →
        (∀ t ∈ Slab(T), SpatiallyPeriodic (RV t)) →
        (∀ t ∈ Slab(T), Function.Odd (V t)) →
        (∀ t ∈ Slab(T), ∀ x, divergence (V t) x = 0) →
        (∀ t ∈ Slab(T), ∀ x, momentumResidual (Slab(T)) V (fun r => (approximatePressure r).lift) t x = RV t x) →
        (∀ t ∈ Slab(T), ContDiff ℝ 2 (pU t)) →
        (∀ t ∈ Slab(T), ∀ x v, ⟪v, fderiv ℝ (gradient ((approximatePressure t).lift - pU t)) x v⟫_ℝ ≤
          stepBound * ‖v‖ ^ 2) →
        ∃ s : TruncatedChildStage T Λ ψ V RV,
          let ε := Λ ^ ((2 : ℤ) - P) * (1 + slabSpatialHolderHalfNorm T P V) ^ 2
          let e := C * slabSpatialHolderHalfNorm T 1 RV + K * ε
          (∀ t ∈ Slab(T), Function.Odd (s.residual t) ∧
            (∀ x, divergence (s.residual t) x = 0) ∧
            ∃ r : C(UnitAddTorus (Fin 3), Vec3),
              (∀ x, r (toUnitTorus x) = s.residual t x) ∧ RealTorusFourierBand (4 * Λ) r) ∧
          slabSpatialHolderHalfNorm T 2 (fun t => s.velocity t - V t) ≤ K * ε ∧
          slabSpatialHolderHalfNorm T 1 s.residual +
            slabSpatialHolderHalfNorm T 0 (fun t => fderiv ℝ (gradient (s.pressure t - (approximatePressure t).lift))) ≤ e ∧
          ∀ t ∈ Slab(T), ∀ x v, ⟪v, fderiv ℝ (gradient (s.pressure t - pU t)) x v⟫_ℝ ≤
            (stepBound + e) * ‖v‖ ^ 2 := by
  obtain ⟨C, hC, hBounds⟩ := TruncatedChildStage.exists_cutoffBounds hSupport hSmooth hUnit
  refine ⟨2 * C, by positivity, fun P hP => ?_⟩
  obtain ⟨K, hK, hQuant⟩ := hBounds P hP
  refine ⟨2 * K, by positivity, ?_⟩
  intro T Λ stepBound V RV pU hT hΛ approximatePressure hV hRV hVper hRVper hVodd hVdiv hMom hUreg hApprox
  obtain ⟨s⟩ := nonempty_truncatedChildStage (Λ := Λ) hT approximatePressure hV hRV hVper hRVper hVodd hVdiv hMom hEven
  let M := slabSpatialHolderHalfNorm T P V
  let R := slabSpatialHolderHalfNorm T 1 RV
  let ε := Λ ^ ((2 : ℤ) - P) * (1 + M) ^ 2
  let e := C * R + K * ε
  have hTsub : Nonempty (Slab(T)) := ⟨⟨0, le_rfl, hT.le⟩⟩
  obtain ⟨MV, hMV⟩ := exists_spatialHolderHalfNorm_bound_of_contDiffOn_periodic hT hV hVper P
  obtain ⟨MR, hMR⟩ := exists_spatialHolderHalfNorm_bound_of_contDiffOn_periodic hT hRV hRVper 1
  have hVpoint (t : ℝ) (ht : t ∈ Slab(T)) : spatialHolderHalfNorm P (V t) ≤ M :=
    le_ciSup ⟨MV, forall_mem_range.mpr fun r : Slab(T) => (hMV r r.property).2⟩ (⟨t, ht⟩ : Slab(T))
  have hRpoint (t : ℝ) (ht : t ∈ Slab(T)) : spatialHolderHalfNorm 1 (RV t) ≤ R :=
    le_ciSup ⟨MR, forall_mem_range.mpr fun r : Slab(T) => (hMR r r.property).2⟩ (⟨t, ht⟩ : Slab(T))
  have hVnonneg (t : ℝ) (ht : t ∈ Slab(T)) : 0 ≤ spatialHolderHalfNorm P (V t) :=
    (norm_nonneg _).trans (norm_iteratedFDeriv_le_spatialHolderHalfNorm (hMV t ht).1 (Nat.zero_le _) 0)
  have hRnonneg : 0 ≤ R :=
    (norm_nonneg _).trans ((norm_iteratedFDeriv_le_spatialHolderHalfNorm
      (hMR 0 ⟨le_rfl, hT.le⟩).1 (Nat.zero_le _) 0).trans (hRpoint 0 ⟨le_rfl, hT.le⟩))
  have hεnonneg : 0 ≤ ε := by
    have hΛ₀ : 0 ≤ Λ := zero_le_one.trans hΛ
    dsimp only [ε]
    positivity
  have hεpoint (t : ℝ) (ht : t ∈ Slab(T)) : s.truncationError P t ≤ ε := by
    refine mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ?_ ?_ _) (by
      have hΛ₀ : 0 ≤ Λ := zero_le_one.trans hΛ
      positivity)
    · linarith only [hVnonneg t ht]
    · exact add_le_add le_rfl (hVpoint t ht)
  have hb := hQuant hT hΛ s approximatePressure hV hRV hVdiv hMom
  have hBound (t : ℝ) (ht : t ∈ Slab(T)) : C * spatialHolderHalfNorm 1 (RV t) + K * s.truncationError P t ≤ e :=
    add_le_add (mul_le_mul_of_nonneg_left (hRpoint t ht) hC) (mul_le_mul_of_nonneg_left (hεpoint t ht) hK)
  have hDouble : e + e = (2 * C) * R + (2 * K) * ε := by dsimp only [e]; ring
  refine ⟨s, ?_⟩
  change (∀ t ∈ Slab(T), _) ∧ _ ≤ (2 * K) * ε ∧ _ + _ ≤ (2 * C) * R + (2 * K) * ε ∧ _
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro t ht
    obtain ⟨r, _, hr, hband, _, _⟩ := s.residual_projectedData hT (zero_le_one.trans hΛ) ht
    exact ⟨s.odd_residual hT (zero_le_one.trans hΛ) ht, s.divergence_free_residual hT ht, r, hr, hband⟩
  · refine ciSup_le fun t : Slab(T) => (hb.tail_two t t.property).trans ?_
    exact (mul_le_mul_of_nonneg_left (hεpoint t t.property) hK).trans (by nlinarith only [mul_nonneg hK hεnonneg])
  · rw [← hDouble]
    exact add_le_add (ciSup_le fun t : Slab(T) => ((hb.residual t t.property).2).trans (hBound t t.property))
      (ciSup_le fun t : Slab(T) => (hb.pressure t t.property).trans (hBound t t.property))
  · intro t ht x v
    have hp := slice_smooth s.smooth_pressure ht
    have hDiff := TruncatedChildStage.pressureHessian_le_of_cutoff hp (approximatePressure t).smooth (s.periodic_pressure t ht)
      (approximatePressure t).periodic ((hb.pressure t ht).trans (hBound t ht)) x v
    have hUpper := hApprox t ht x v
    rw [hessianSub ((approximatePressure t).smooth.of_le (by simp)) (hUreg t ht), sub_apply, inner_sub_right] at hUpper
    have hMain : ⟪v, fderiv ℝ (gradient (s.pressure t - pU t)) x v⟫_ℝ ≤
        (stepBound + e) * ‖v‖ ^ 2 := by
      rw [hessianSub (hp.of_le (by simp)) (hUreg t ht), sub_apply, inner_sub_right]
      nlinarith only [hDiff, hUpper]
    exact hMain.trans (mul_le_mul_of_nonneg_right
      (add_le_add le_rfl (calc
        e ≤ e + e := le_add_of_nonneg_right (add_nonneg (mul_nonneg hC hRnonneg) (mul_nonneg hK hεnonneg))
        _ = _ := hDouble)) (sq_nonneg _))

end

end TorusEuler
