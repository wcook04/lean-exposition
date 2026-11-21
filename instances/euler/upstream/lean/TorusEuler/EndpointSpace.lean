import TorusEuler.TorusFourier
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.MeasureTheory.Integral.Prod

open MeasureTheory Set
open scoped ContDiff InnerProductSpace

namespace TorusEuler

/-- The product of restricted time volume and spatial Haar probability. -/
noncomputable def endpointTorusMeasure (T : ℝ) : Measure (ℝ × UnitAddTorus (Fin 3)) :=
  (volume.restrict (Ioc 0 T)).prod unitTorusMeasure

noncomputable abbrev EndpointTorusL2 (T : ℝ) := Lp Vec3 2 (endpointTorusMeasure T)

instance endpointTorusMeasure_finite (T : ℝ) : IsFiniteMeasure (endpointTorusMeasure T) := by
  unfold endpointTorusMeasure unitTorusMeasure
  infer_instance

/-- Scalar factors for the time-mean and distributional divergence tests. -/
abbrev EndpointBoundedTest (α : Type*) [MeasurableSpace α] :=
  { f : α → ℝ // Measurable f ∧ ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C }

/-- A smooth periodic scalar potential on the Euclidean lift of the torus. -/
structure EndpointSmoothPotential where
  lift : Vec3 → ℝ
  smooth : ContDiff ℝ ∞ lift
  periodic : SpatiallyPeriodic lift

theorem isOpenQuotientMap_toUnitTorus : IsOpenQuotientMap toUnitTorus := by
  have h : IsOpenQuotientMap
      (Pi.map fun _ : Fin 3 => fun x : ℝ => (x : UnitAddCircle)) :=
    IsOpenQuotientMap.piMap fun _ => QuotientAddGroup.isOpenQuotientMap_mk
  exact h.comp (PiLp.homeomorph 2 (fun _ : Fin 3 => ℝ)).isOpenQuotientMap

private theorem EndpointSmoothPotential.periodic_gradient (p : EndpointSmoothPotential) :
    SpatiallyPeriodic (gradient p.lift) := by
  intro n x
  let a := latticeVector n
  have hf := ((p.smooth.differentiable (by simp)) (x + a)).hasFDerivAt
  have h := hf.comp x ((hasFDerivAt_id x).add_const a)
  have heq : (fun z => p.lift (z + a)) = p.lift := funext (p.periodic n)
  change HasFDerivAt (fun z => p.lift (z + a)) _ x at h
  rw [heq, ContinuousLinearMap.comp_id] at h
  exact congrArg (InnerProductSpace.toDual ℝ Vec3).symm h.fderiv.symm

/-- The gradient on the torus obtained from the gradient of a smooth periodic lift. -/
noncomputable def endpointPotentialGradient (p : EndpointSmoothPotential) :
    C(UnitAddTorus (Fin 3), Vec3) := by
  let h := p.periodic_gradient.existsUnique_torusFunction
  let g := h.exists.choose
  have hg : ∀ x, g (toUnitTorus x) = gradient p.lift x := h.exists.choose_spec
  refine ⟨g, isOpenQuotientMap_toUnitTorus.continuous_comp_iff.mp ?_⟩
  change Continuous (fun x => g (toUnitTorus x))
  simp only [hg]
  exact (InnerProductSpace.toDual ℝ Vec3).symm.continuous.comp
    ((p.smooth.of_le (show (1 : WithTop ℕ∞) ≤ ∞ by simp)).continuous_fderiv (by simp))

@[simp]
theorem endpointPotentialGradient_toUnitTorus (p : EndpointSmoothPotential) (x : Vec3) :
    endpointPotentialGradient p (toUnitTorus x) = gradient p.lift x :=
  p.periodic_gradient.existsUnique_torusFunction.exists.choose_spec x

private theorem memLp_endpointMeanTest (T : ℝ) (i : Fin 3)
    (φ : EndpointBoundedTest (UnitAddTorus (Fin 3))) :
    MemLp (fun q : ℝ × UnitAddTorus (Fin 3) => φ.val q.2 • EuclideanSpace.single i (1 : ℝ))
      2 (endpointTorusMeasure T) := by
  obtain ⟨C, hC⟩ := φ.property.2
  refine MemLp.of_bound ?_ (C * ‖EuclideanSpace.single i (1 : ℝ)‖) ?_
  · exact (((φ.property.1.comp measurable_snd).aestronglyMeasurable).smul
      aestronglyMeasurable_const)
  · exact ae_of_all _ fun q => by
      rw [norm_smul]
      exact mul_le_mul_of_nonneg_right (hC q.2) (norm_nonneg _)

private theorem memLp_endpointDivergenceTest (T : ℝ)
    (η : EndpointBoundedTest ℝ) (p : EndpointSmoothPotential) :
    MemLp (fun q : ℝ × UnitAddTorus (Fin 3) => η.val q.1 • endpointPotentialGradient p q.2)
      2 (endpointTorusMeasure T) := by
  obtain ⟨C, hC⟩ := η.property.2
  obtain ⟨D, hD⟩ := isCompact_univ.exists_bound_of_continuousOn
    (endpointPotentialGradient p).continuous.continuousOn
  refine MemLp.of_bound ?_ (C * D) ?_
  · exact (((η.property.1.comp measurable_fst).aestronglyMeasurable).smul
      (((endpointPotentialGradient p).continuous.measurable.comp measurable_snd).aestronglyMeasurable))
  · exact ae_of_all _ fun q => by
      rw [norm_smul]
      exact mul_le_mul (hC q.1) (hD q.2 (mem_univ _)) (norm_nonneg _)
        ((norm_nonneg _).trans (hC q.1))

/-- The componentwise time-mean test against a spatial scalar. -/
noncomputable def endpointTorusMeanTest (T : ℝ) (i : Fin 3)
    (φ : EndpointBoundedTest (UnitAddTorus (Fin 3))) : EndpointTorusL2 T →L[ℝ] ℝ :=
  innerSL ℝ ((memLp_endpointMeanTest T i φ).toLp _)

/-- The weak spatial divergence test against a separated time factor and potential. -/
noncomputable def endpointTorusDivergenceTest (T : ℝ)
    (η : EndpointBoundedTest ℝ) (p : EndpointSmoothPotential) : EndpointTorusL2 T →L[ℝ] ℝ :=
  innerSL ℝ ((memLp_endpointDivergenceTest T η p).toLp _)

private theorem endpointTorus_inner_test_eq (T : ℝ)
    {f : ℝ × UnitAddTorus (Fin 3) → Vec3} (hf : MemLp f 2 (endpointTorusMeasure T))
    (v : EndpointTorusL2 T) :
    innerSL ℝ (hf.toLp f) v = ∫ q, ⟪f q, v q⟫_ℝ ∂endpointTorusMeasure T := by
  rw [innerSL_apply_apply, L2.inner_def]
  exact integral_congr_ae (hf.coeFn_toLp.mono fun q hq => congrArg (fun z => ⟪z, v q⟫_ℝ) hq)

theorem endpointTorusMeanTest_apply (T : ℝ) (i : Fin 3)
    (φ : EndpointBoundedTest (UnitAddTorus (Fin 3))) (v : EndpointTorusL2 T) :
    endpointTorusMeanTest T i φ v = ∫ q, φ.val q.2 * (v q) i ∂endpointTorusMeasure T := by
  rw [endpointTorusMeanTest, endpointTorus_inner_test_eq T]
  congr 1
  funext q
  simp [real_inner_smul_left, EuclideanSpace.inner_single_left]

theorem endpointTorusDivergenceTest_apply (T : ℝ)
    (η : EndpointBoundedTest ℝ) (p : EndpointSmoothPotential) (v : EndpointTorusL2 T) :
    endpointTorusDivergenceTest T η p v =
      ∫ q, η.val q.1 * ⟪endpointPotentialGradient p q.2, v q⟫_ℝ ∂endpointTorusMeasure T := by
  rw [endpointTorusDivergenceTest, endpointTorus_inner_test_eq T]
  simp only [real_inner_smul_left]

/-- The mean-zero time paths with weakly solenoidal spatial velocity. -/
noncomputable def endpointTorusSpace (T : ℝ) : Submodule ℝ (EndpointTorusL2 T) :=
  (⨅ i, ⨅ φ, (endpointTorusMeanTest T i φ).ker) ⊓
    (⨅ η, ⨅ p, (endpointTorusDivergenceTest T η p).ker)

theorem isClosed_endpointTorusSpace (T : ℝ) :
    IsClosed (endpointTorusSpace T : Set (EndpointTorusL2 T)) := by
  simp only [endpointTorusSpace, Submodule.coe_inf, Submodule.coe_iInf]
  exact (isClosed_iInter fun i => isClosed_iInter fun φ => (endpointTorusMeanTest T i φ).isClosed_ker).inter
    (isClosed_iInter fun η => isClosed_iInter fun p => (endpointTorusDivergenceTest T η p).isClosed_ker)

theorem mem_endpointTorusSpace (T : ℝ) (v : EndpointTorusL2 T) :
    v ∈ endpointTorusSpace T ↔
      (∀ (i : Fin 3) (φ : EndpointBoundedTest (UnitAddTorus (Fin 3))),
        (∫ q, φ.val q.2 * (v q) i ∂endpointTorusMeasure T) = 0) ∧
      (∀ (η : EndpointBoundedTest ℝ) (p : EndpointSmoothPotential),
        (∫ q, η.val q.1 * ⟪endpointPotentialGradient p q.2, v q⟫_ℝ
        ∂endpointTorusMeasure T) = 0) := by
  simp only [endpointTorusSpace, Submodule.mem_inf, Submodule.mem_iInf,
    LinearMap.mem_ker, ContinuousLinearMap.coe_coe, endpointTorusMeanTest_apply, endpointTorusDivergenceTest_apply]

private theorem forall_boundedTest_mul_integral_eq_zero_iff {α : Type*}
    [MeasurableSpace α] {μ : Measure α} {f : α → ℝ} (hf : Integrable f μ) :
    (∀ φ : EndpointBoundedTest α, (∫ x, φ.val x * f x ∂μ) = 0) ↔ f =ᵐ[μ] 0 := by
  constructor
  · intro h
    apply hf.ae_eq_zero_of_forall_setIntegral_eq_zero
    intro s hs _
    let φ : EndpointBoundedTest α :=
      ⟨s.indicator (fun _ => 1), measurable_const.indicator hs, 1, fun x => by
        by_cases hx : x ∈ s <;> simp [hx]⟩
    rw [← integral_indicator hs]
    simpa only [φ, ← indicator_mul_left, one_mul] using h φ
  · intro h φ
    exact (integral_congr_ae (h.mono fun x hx => by
      change f x = 0 at hx
      rw [hx, mul_zero])).trans (integral_zero α ℝ)

private theorem integrable_endpointTorus_inner_test (T : ℝ)
    {f : ℝ × UnitAddTorus (Fin 3) → Vec3} (hf : MemLp f 2 (endpointTorusMeasure T))
    (v : EndpointTorusL2 T) : Integrable (fun q => ⟪f q, v q⟫_ℝ) (endpointTorusMeasure T) :=
  (L2.integrable_inner (hf.toLp f) v).congr
    (hf.coeFn_toLp.mono fun q hq => congrArg (fun z => ⟪z, v q⟫_ℝ) hq)

/-- The time-mean tests detect the vanishing time integral at almost every label. -/
theorem endpointTorusMeanTests_iff_ae_zero (T : ℝ) (v : EndpointTorusL2 T) :
    (∀ i φ, endpointTorusMeanTest T i φ v = 0) ↔
      (fun a => ∫ t in Ioc (0 : ℝ) T, v (t, a)) =ᵐ[unitTorusMeasure] 0 := by
  have hv : Integrable v (endpointTorusMeasure T) := (Lp.memLp v).integrable one_le_two
  have hmean (i : Fin 3) :
      Integrable (fun a => (∫ t in Ioc (0 : ℝ) T, v (t, a)) i) unitTorusMeasure := by
    simpa only [EuclideanSpace.inner_single_left, map_one, one_mul] using
      hv.integral_prod_right.const_inner (𝕜 := ℝ) (EuclideanSpace.single i (1 : ℝ))
  have htest (i : Fin 3) (φ : EndpointBoundedTest (UnitAddTorus (Fin 3))) :
      endpointTorusMeanTest T i φ v =
        ∫ a, φ.val a * (∫ t in Ioc (0 : ℝ) T, v (t, a)) i ∂unitTorusMeasure := by
    have hprod : Integrable (fun q : ℝ × UnitAddTorus (Fin 3) => φ.val q.2 * (v q) i)
        (endpointTorusMeasure T) := by
      simpa only [real_inner_smul_left, EuclideanSpace.inner_single_left, map_one, one_mul] using
        integrable_endpointTorus_inner_test T (memLp_endpointMeanTest T i φ) v
    rw [endpointTorusMeanTest_apply]
    change (∫ q, _ ∂(volume.restrict (Ioc (0 : ℝ) T)).prod unitTorusMeasure) = _
    rw [integral_prod_symm _ hprod]
    apply integral_congr_ae
    filter_upwards [hv.prod_left_ae] with a ha
    rw [integral_const_mul]
    congr 1
    simpa only [EuclideanSpace.inner_single_left, map_one, one_mul] using
      integral_inner (𝕜 := ℝ) ha (EuclideanSpace.single i (1 : ℝ))
  simp_rw [htest, forall_boundedTest_mul_integral_eq_zero_iff (hmean _)]
  change (∀ i : Fin 3, ∀ᵐ a ∂unitTorusMeasure, (∫ t in Ioc (0 : ℝ) T, v (t, a)) i = 0) ↔
    ∀ᵐ a ∂unitTorusMeasure, (∫ t in Ioc (0 : ℝ) T, v (t, a)) = 0
  rw [← Filter.eventually_all]
  apply Filter.eventually_congr
  filter_upwards with a
  exact ⟨fun h => PiLp.ext fun i => h i, fun h i => congrArg (fun z : Vec3 => z i) h⟩

/-- At each fixed smooth periodic potential, the divergence tests detect the spatial
pairing's vanishing at almost every time. -/
theorem endpointTorusDivergenceTests_iff_ae_zero (T : ℝ) (v : EndpointTorusL2 T)
    (p : EndpointSmoothPotential) :
    (∀ η, endpointTorusDivergenceTest T η p v = 0) ↔
      (fun t => ∫ a, ⟪endpointPotentialGradient p a, v (t, a)⟫_ℝ ∂unitTorusMeasure) =ᵐ[
        volume.restrict (Ioc (0 : ℝ) T)] 0 := by
  let g : ℝ × UnitAddTorus (Fin 3) → ℝ := fun q => ⟪endpointPotentialGradient p q.2, v q⟫_ℝ
  let one : EndpointBoundedTest ℝ := ⟨fun _ => 1, measurable_const, 1, fun _ => by simp⟩
  have hg : Integrable g (endpointTorusMeasure T) := by
    simpa only [g, one, one_smul] using
      integrable_endpointTorus_inner_test T (memLp_endpointDivergenceTest T one p) v
  have htest (η : EndpointBoundedTest ℝ) :
      endpointTorusDivergenceTest T η p v =
        ∫ t in Ioc (0 : ℝ) T, η.val t * ∫ a, g (t, a) ∂unitTorusMeasure := by
    have hprod : Integrable (fun q : ℝ × UnitAddTorus (Fin 3) => η.val q.1 * g q)
        (endpointTorusMeasure T) := by
      simpa only [g, real_inner_smul_left] using
        integrable_endpointTorus_inner_test T (memLp_endpointDivergenceTest T η p) v
    rw [endpointTorusDivergenceTest_apply]
    change (∫ q, η.val q.1 * g q ∂(volume.restrict (Ioc (0 : ℝ) T)).prod unitTorusMeasure) = _
    rw [integral_prod _ hprod]
    simp only [g, integral_const_mul]
  simp_rw [htest]
  exact forall_boundedTest_mul_integral_eq_zero_iff hg.integral_prod_left

/-- Membership imposes zero time integral at almost every label and vanishing
spatial gradient pairing at almost every time for each smooth periodic test. -/
theorem mem_endpointTorusSpace_iff_slices (T : ℝ) (v : EndpointTorusL2 T) :
    v ∈ endpointTorusSpace T ↔
      ((fun a => ∫ t in Ioc (0 : ℝ) T, v (t, a)) =ᵐ[unitTorusMeasure] 0) ∧
      ∀ p : EndpointSmoothPotential,
        (fun t => ∫ a, ⟪endpointPotentialGradient p a, v (t, a)⟫_ℝ ∂unitTorusMeasure) =ᵐ[
          volume.restrict (Ioc (0 : ℝ) T)] 0 := by
  simp only [endpointTorusSpace, Submodule.mem_inf, Submodule.mem_iInf,
    LinearMap.mem_ker, ContinuousLinearMap.coe_coe, endpointTorusMeanTests_iff_ae_zero]
  rw [forall_comm (α := EndpointBoundedTest ℝ) (β := EndpointSmoothPotential)]
  simp only [endpointTorusDivergenceTests_iff_ae_zero]

end TorusEuler
