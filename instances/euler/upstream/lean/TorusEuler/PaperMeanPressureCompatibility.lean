import TorusEuler.PaperMeanStatements
import TorusEuler.TruncatedParentProjectedMomentum

/-! Compatibility of the Leray-compressed inverse with the periodic pressure equation. -/

open Filter MeasureTheory Set
open scoped ContDiff InnerProductSpace Topology

namespace TorusEuler

noncomputable section

local notation "A" => UnitAddTorus (Fin 3)
local notation "C½" => HalfHolder A Vec3
local notation "K½" => HalfHolder A (Vec3 →L[ℝ] Vec3)
local notation "S" => endpointHalfHolderSolenoidal
local notation "P" => endpointStrongSpatialProjection

/-- The spatial Leray projection kills the gradient of any periodic (C^1)
potential whose gradient belongs to the spatial Hölder space. -/
theorem paperMean_projection_C1_gradient_zero (g : C½) (q : Vec3 → ℝ)
    (hq₁ : ContDiff ℝ 1 q) (hqper : SpatiallyPeriodic q)
    (hq : ∀ x, HalfHolder.eval (toUnitTorus x) g = gradient q x) :
    P g = 0 := by
  obtain ⟨p, hp⟩ := hqper.exists_continuousTorusFunction hq₁.continuous
  let d := endpointHalfHolderToContinuous g
  have hpEq : (fun x => p (toUnitTorus x)) = q := funext hp
  have hp₁ : ContDiff ℝ 1 (fun x => p (toUnitTorus x)) := by rwa [hpEq]
  have hd (x : Vec3) : d (toUnitTorus x) = gradient (fun y => p (toUnitTorus y)) x := by
    rw [hpEq]
    exact hq x
  let ψ := dyadicMultiplierCutoff
  let Λ (n : ℕ) := (n : ℝ) + 1
  let qn (n : ℕ) : EndpointSmoothPotential :=
    ⟨fun x => realScalarFourierCutoff ψ (Λ n) p (toUnitTorus x),
      Complex.reCLM.contDiff.comp
        (contDiff_lift_smoothFourierCutoff ψ (Λ n) (fun a => (p a : ℂ))),
      fun j _ => congrArg (realScalarFourierCutoff ψ (Λ n) p)
        ((toUnitTorus_eq_iff _ _).mpr ⟨j, rfl⟩)⟩
  let Gn n := endpointPotentialGradient (qn n)
  have hn (n : ℕ) (x : Vec3) :
      Gn n (toUnitTorus x) = realVectorFourierCutoff ψ (Λ n) d (toUnitTorus x) := by
    rw [show Gn n = endpointPotentialGradient (qn n) from rfl, endpointPotentialGradient_toUnitTorus]
    exact (congrFun (realVectorFourierCutoff_gradient ψ (Λ n) p d hp₁ hd) x).symm
  have happrox := periodicRealPartVector.uniformContinuous.comp_tendstoUniformly
    (tendstoUniformly_lift_smoothFourierCutoff
      (fun ξ hξ => dyadicMultiplierCutoff_zero ξ hξ.le) dyadicMultiplierCutoff_smooth
      (dyadicMultiplierCutoff_unit 0 (by simp)) (endpointComplexifyContinuous d))
  change TendstoUniformly (fun (n : ℕ) x => realVectorFourierCutoff ψ (Λ n) d (toUnitTorus x))
    (fun x => periodicRealPartVector (endpointComplexifyContinuous d (toUnitTorus x))) atTop at happrox
  have hre (a : A) : periodicRealPartVector (endpointComplexifyContinuous d a) = d a :=
    periodicRealPartVector_complexifyVector _
  simp_rw [hre, ← hn] at happrox
  have ht : Tendsto Gn atTop (𝓝 d) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    filter_upwards [Metric.tendstoUniformly_iff.mp happrox (ε / 2) (half_pos hε)] with n hn'
    apply lt_of_le_of_lt _ (half_lt_self hε)
    apply (ContinuousMap.dist_le (half_pos hε).le).mpr
    intro a
    obtain ⟨x, rfl⟩ := toUnitTorus_surjective a
    rw [dist_comm]
    exact (hn' x).le
  let Q := endpointWeakSpatialProjection.comp (ContinuousMap.toLp (E := Vec3) 2 unitTorusMeasure ℝ)
  have hzero (n : ℕ) : Q (Gn n) = 0 := by
    let w := (Gn n).toLp 2 unitTorusMeasure ℝ
    let : CompleteSpace endpointSpatialSolenoidal := isClosed_endpointSpatialSolenoidal.completeSpace_coe
    change endpointSpatialSolenoidal.orthogonalProjectionOnto w = 0
    apply Submodule.orthogonalProjectionOnto_eq_zero_iff.mpr
    apply (endpointSpatialSolenoidal.mem_orthogonal' w).mpr
    intro v hv
    rw [L2.inner_def]
    have hEq := (ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) unitTorusMeasure
      (Gn n)).mono fun a ha => congrArg (fun x : Vec3 => ⟪x, v a⟫_ℝ) ha
    exact (integral_congr_ae hEq).trans ((mem_endpointSpatialSolenoidal v).mp hv (qn n))
  have hlim := (Q.continuous.tendsto d).comp ht
  have hlim' : Tendsto (fun n : ℕ => Q (Gn n)) atTop (𝓝 (0 : endpointSpatialSolenoidal)) :=
    tendsto_const_nhds.congr fun n => (hzero n).symm
  have hdzero : Q d = 0 := tendsto_nhds_unique hlim hlim'
  change endpointWeakSpatialProjection ((endpointHalfHolderToContinuous g).toLp 2 unitTorusMeasure ℝ) = 0 at hdzero
  rw [endpointHalfHolderToContinuous_toLp, endpointStrongSpatialProjection_agrees_weak] at hdzero
  apply endpointSolenoidalEmbedding_injective
  rw [map_zero]
  exact hdzero

/-- A solution of (4.9) in the original periodic pressure formulation
is a solution of the compressed equation used by the inverse. -/
def PaperMeanIntegratedSolution.of_pressure_equation {T : ℝ} {K Ω : ℝ → K½} {src : ℝ → C½}
    (v : ℝ → S) (c : S) (hv : ContinuousOn v (Icc 0 T)) (hEnd : endpointPrimitive v T = 0)
    (φ : Pressure) (Gφ : ℝ → C½)
    (hφ : ∀ t ∈ Icc 0 T, SpatiallyPeriodic (φ t) ∧ ContDiff ℝ 1 (φ t) ∧
      ∀ x, HalfHolder.eval (toUnitTorus x) (Gφ t) = gradient (φ t) x)
    (hEq : ∀ t ∈ Icc 0 T, paperMeanIntegratedMomentum K Ω src v t = (c : C½) + Gφ t) :
    PaperMeanIntegratedSolution T K Ω src where
  velocity := v
  constant := c
  continuous := hv
  terminal := hEnd
  projected := by
    intro t ht
    obtain ⟨hp, h₁, hg⟩ := hφ t ht
    rw [hEq t ht, map_add, paperMean_projection_C1_gradient_zero (Gφ t) (φ t) h₁ hp hg, add_zero]
    apply Subtype.ext
    exact (endpointStrongSpatialLeray_fixed_iff c.val).2 c.property


/-- A represented Hölder gradient makes its potential continuously differentiable. -/
theorem paperMean_contDiff_one_of_hasGradientAt (g : C½) (q : Vec3 → ℝ)
    (h : ∀ x, HasGradientAt q (HalfHolder.eval (toUnitTorus x) g) x) :
    ContDiff ℝ 1 q := by
  apply contDiff_one_iff_fderiv.mpr
  refine ⟨fun x => (h x).hasFDerivAt.differentiableAt, ?_⟩
  have heq : fderiv ℝ q = fun x =>
      InnerProductSpace.toDual ℝ Vec3 (endpointHalfHolderToContinuous g (toUnitTorus x)) :=
    funext fun x => (h x).hasFDerivAt.fderiv
  rw [heq]
  exact (InnerProductSpace.toDual ℝ Vec3).continuous.comp
    ((endpointHalfHolderToContinuous g).continuous.comp isOpenQuotientMap_toUnitTorus.continuous)

/-- The gradient in (4.9) is unique as a continuous Hölder curve on the slab
once the velocity and the solenoidal constant agree. -/
theorem PaperMeanIntegratedSolution.pressure_gradient_eq_on {T : ℝ} {K Ω : ℝ → K½}
    {src : ℝ → C½} {v w : ℝ → S} {c k : S} {Gφ Gψ : ℝ → C½}
    (hv : EqOn v w (Icc 0 T)) (hc : c = k)
    (hφ : ∀ t ∈ Icc 0 T, paperMeanIntegratedMomentum K Ω src v t = (c : C½) + Gφ t)
    (hψ : ∀ t ∈ Icc 0 T, paperMeanIntegratedMomentum K Ω src w t = (k : C½) + Gψ t) :
    EqOn Gφ Gψ (Icc 0 T) := by
  intro t ht
  have hI : endpointPrimitive (fun r => (Ω r).coefficientMul (v r).val) t =
      endpointPrimitive (fun r => (Ω r).coefficientMul (w r).val) t := by
    apply intervalIntegral.integral_congr
    rw [uIcc_of_le ht.1]
    intro r hr
    change (Ω r).coefficientMul (v r).val = (Ω r).coefficientMul (w r).val
    rw [hv (Icc_subset_Icc_right ht.2 hr)]
  have hEq : paperMeanIntegratedMomentum K Ω src v t =
      paperMeanIntegratedMomentum K Ω src w t := by
    unfold paperMeanIntegratedMomentum
    rw [hv ht, hI]
  rw [hφ t ht, hψ t ht, hc] at hEq
  exact add_left_cancel hEq

/-- If the kinetic coefficient starts at the identity and the integrated source
vanishes initially, the solenoidal constant equals the initial velocity. -/
theorem PaperMeanIntegratedSolution.constant_eq_initial {T : ℝ} {K Ω : ℝ → K½}
    {src : ℝ → C½} (hT : 0 ≤ T) (s : PaperMeanIntegratedSolution T K Ω src)
    (hK : ∀ a, HalfHolder.eval a (K 0) = ContinuousLinearMap.id ℝ Vec3) (hsrc : src 0 = 0) :
    s.constant = s.velocity 0 := by
  have hmul : (K 0).coefficientMul (s.velocity 0).val = (s.velocity 0).val := by
    apply HalfHolder.ext
    intro a
    rw [HalfHolder.eval_coefficientMul, hK, ContinuousLinearMap.id_apply]
  have hp := s.projected 0 ⟨le_rfl, hT⟩
  simp only [paperMeanIntegratedMomentum, endpointPrimitive, intervalIntegral.integral_same,
    sub_zero, hsrc, add_zero, hmul] at hp
  rw [← hp]
  exact Subtype.ext ((endpointStrongSpatialLeray_fixed_iff _).2 (s.velocity 0).property)


/-- Two mean-zero potentials with the same represented gradient coincide. -/
theorem paperMean_normalized_potential_eq (G : C½) {φ ψ : Vec3 → ℝ}
    (hφ : ∀ x, HasGradientAt φ (HalfHolder.eval (toUnitTorus x) G) x)
    (hψ : ∀ x, HasGradientAt ψ (HalfHolder.eval (toUnitTorus x) G) x)
    (mφ : (∫ x in centeredCell, φ x) = 0) (mψ : (∫ x in centeredCell, ψ x) = 0) :
    φ = ψ := by
  let k : ℝ := φ 0 - ψ 0
  have hφd : Differentiable ℝ φ := fun x => (hφ x).hasFDerivAt.differentiableAt
  have hψd : Differentiable ℝ ψ := fun x => (hψ x).hasFDerivAt.differentiableAt
  have heq : (fun x => φ x - ψ x) = fun _ => k := by
    apply eq_of_fderiv_eq (hφd.sub hψd) (differentiable_const k) _ 0 rfl
    intro x
    rw [((hφ x).hasFDerivAt.sub (hψ x).hasFDerivAt).fderiv, sub_self, fderiv_fun_const, Pi.zero_apply]
  have hI : (∫ x in centeredCell, φ x - ψ x) = 0 := by
    rw [integral_sub (hφd.continuous.continuousOn.integrableOn_compact isCompact_centeredCell)
      (hψd.continuous.continuousOn.integrableOn_compact isCompact_centeredCell), mφ, mψ, sub_zero]
  rw [heq] at hI
  let : IsProbabilityMeasure unitTorusMeasure :=
    inferInstanceAs (IsProbabilityMeasure (Measure.pi fun _ : Fin 3 =>
      (AddCircle.haarAddCircle : Measure UnitAddCircle)))
  have hvol : (volume : Measure Vec3).real centeredCell = 1 := by
    have h := torusIntegral_eq_centeredCell (fun _ => (1 : ℝ))
    simpa only [integral_const, setIntegral_const, measureReal_def, Measure.restrict_apply_univ,
      measure_univ, ENNReal.toReal_one, smul_eq_mul, mul_one] using h.symm
  have hk : k = 0 := by simpa only [setIntegral_const, hvol, one_smul] using hI
  exact funext fun x => sub_eq_zero.mp ((congrFun heq x).trans hk)


local instance paperPressureSolenoidalNormedGroup : NormedAddCommGroup S := inferInstance
local instance paperPressureSolenoidalNormedSpace : NormedSpace ℝ S := inferInstance

set_option maxHeartbeats 1800000 in
/-- A solenoidal displacement with zero endpoint values and the original
periodic-pressure equation gives a solution in the inverse's domain. -/
theorem PaperMeanIntegratedSolution.exists_of_displacement_pressure_equation
    {T : ℝ} {K Ω : ℝ → K½} {src : ℝ → C½} (hT : 0 ≤ T)
    (z v : ℝ → S) (c : S) (hv : ContinuousOn v (Icc 0 T))
    (hz : ∀ t ∈ Icc 0 T, HasDerivWithinAt z (v t) (Icc 0 T) t)
    (h0 : z 0 = 0) (hEnd : z T = 0) (φ : Pressure) (Gφ : ℝ → C½)
    (hφ : ∀ t ∈ Icc 0 T, SpatiallyPeriodic (φ t) ∧
      ∀ x, HasGradientAt (φ t) (HalfHolder.eval (toUnitTorus x) (Gφ t)) x)
    (hEq : ∀ t ∈ Icc 0 T, paperMeanIntegratedMomentum K Ω src v t = (c : C½) + Gφ t) :
    ∃ s : PaperMeanIntegratedSolution T K Ω src,
      s.velocity = v ∧ s.constant = c ∧ EqOn (endpointPrimitive s.velocity) z (Icc 0 T) := by
  let : CompleteSpace S := isClosed_endpointHalfHolderSolenoidal.completeSpace_coe
  have hZ : EqOn (endpointPrimitive v) z (Icc 0 T) := by
    intro t ht
    have hI : Icc (0 : ℝ) t ⊆ Icc 0 T := Icc_subset_Icc_right ht.2
    apply Subtype.ext
    apply HalfHolder.ext
    intro a
    let ev : S →L[ℝ] Vec3 := (HalfHolder.eval a).comp endpointHalfHolderSolenoidal.subtypeL
    have hDeriv (r : ℝ) (hr : r ∈ Icc 0 T) :
        HasDerivWithinAt (fun u => ev (z u)) (ev (v r)) (Icc 0 T) r :=
      ev.hasFDerivAt.comp_hasDerivWithinAt r (hz r hr)
    have hzc : ContinuousOn (fun r => ev (z r)) (Icc 0 T) := fun r hr =>
      (hDeriv r hr).continuousWithinAt
    have hInt : IntervalIntegrable v volume 0 t :=
      (hv.mono hI).intervalIntegrable_of_Icc ht.1
    have hIntEv : IntervalIntegrable (fun r => ev (v r)) volume 0 t :=
      (ev.continuous.comp_continuousOn (hv.mono hI)).intervalIntegrable_of_Icc ht.1
    change ev (∫ r in (0 : ℝ)..t, v r) = ev (z t)
    rw [← ev.intervalIntegral_comp_comm hInt, intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
      ht.1 (hzc.mono hI) (fun r hr => (hDeriv r (hI (Ioo_subset_Icc_self hr))).hasDerivAt
        (mem_of_superset (isOpen_Ioo.mem_nhds hr) (Ioo_subset_Icc_self.trans hI))) hIntEv,
      h0, map_zero, sub_zero]
  let u := PaperMeanIntegratedSolution.of_pressure_equation v c hv
    ((hZ ⟨hT, le_rfl⟩).trans hEnd) φ Gφ
    (fun t ht => ⟨(hφ t ht).1, paperMean_contDiff_one_of_hasGradientAt (Gφ t) (φ t) (hφ t ht).2,
      fun x => ((hφ t ht).2 x).gradient.symm⟩) hEq
  exact ⟨u, rfl, rfl, hZ⟩

end

end TorusEuler
