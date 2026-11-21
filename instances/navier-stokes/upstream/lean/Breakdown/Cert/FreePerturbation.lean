import Breakdown.Cert.FreeTransport

open scoped ContDiff ENNReal Topology
open MeasureTheory Filter

noncomputable section

namespace Breakdown.Cert

open Freq

namespace Internal.FreePerturbation

theorem ae_prod_of_ae_ae {F : Type*} [NormedAddCommGroup F] {f f' : ℝ × Space → F}
    (hf : AEStronglyMeasurable f volume) (hf' : AEStronglyMeasurable f' volume)
    (h : ∀ᵐ σ : ℝ, ∀ᵐ y : Space, f (σ, y) = f' (σ, y)) : f =ᵐ[volume] f' := by
  rw [Measure.volume_eq_prod] at hf hf' ⊢
  have e1 := hf.ae_eq_mk
  have e2 := hf'.ae_eq_mk
  have hs : MeasurableSet {z | hf.mk f z = hf'.mk f' z} :=
    hf.stronglyMeasurable_mk.measurableSet_eq_fun hf'.stronglyMeasurable_mk
  have hm : ∀ᵐ z ∂((volume : Measure ℝ).prod (volume : Measure Space)), hf.mk f z = hf'.mk f' z := by
    rw [Measure.ae_prod_iff_ae_ae hs]
    filter_upwards [Measure.ae_ae_eq_curry_of_prod e1, Measure.ae_ae_eq_curry_of_prod e2, h] with σ h1 h2 h3
    filter_upwards [h1, h2, h3] with y a b c
    simp only [Function.curry_apply] at a b
    rw [← a, ← b, c]
  filter_upwards [e1, e2, hm] with z a b c
  rw [a, b, c]

theorem shiftLp_ae (a : ℝ) (w : HH) : ∀ᵐ t : TimeCircle,
    ((shiftLp a : HH →L[ℝ] HH) w : TimeCircle → HBar) t = (w : TimeCircle → HBar) (t + a) := by
  have hw : (shiftLp a : HH →L[ℝ] HH) w = Lp.compMeasurePreserving (fun t : TimeCircle => t + (a : TimeCircle))
      (measurePreserving_add_right volume (a : TimeCircle)) w := rfl
  rw [hw]
  exact Lp.coeFn_compMeasurePreserving _ _

theorem rotHH_ae (R : Space ≃ₗᵢ[ℝ] Space) (w : HH) :
    ∀ᵐ t : TimeCircle, ((rotHH R w : HH) : TimeCircle → HBar) t = rotX R ((w : TimeCircle → HBar) t) :=
  ContinuousLinearMap.coeFn_compLpL _ _

theorem gradCLM_ae (u : XX) :
    ∀ᵐ t : TimeCircle, ((gradCLM u : HH) : TimeCircle → HBar) t = gradPart ((u : TimeCircle → XBar) t) :=
  ContinuousLinearMap.coeFn_compLpL _ _

theorem ae_add_circle {p : TimeCircle → Prop} (a : ℝ) (h : ∀ᵐ t : TimeCircle, p t) :
    ∀ᵐ t : TimeCircle, p (t + (a : TimeCircle)) :=
  (measurePreserving_add_right (volume : Measure TimeCircle) (a : TimeCircle)).quasiMeasurePreserving.ae h

theorem shift_eq_rot {u : XX} {Γ : Set Symmetry} (hu : IsInvariantXX Γ u) {γ : Symmetry} (hγ : γ ∈ Γ) :
    (shiftLp γ.2 : HH →L[ℝ] HH) (gradCLM u) = rotHH γ.1 (gradCLM u) := by
  have h0 : gradCLM u ∈ LinearMap.ker
      (((shiftLp γ.2 : HH →L[ℝ] HH) - rotHH γ.1 : HH →L[ℝ] HH) : HH →ₗ[ℝ] HH) :=
    (Submodule.mem_iInf _).1 ((Submodule.mem_iInf _).1 hu γ) hγ
  have h2 : (shiftLp γ.2 : HH →L[ℝ] HH) (gradCLM u) - rotHH γ.1 (gradCLM u) = 0 :=
    LinearMap.mem_ker.1 h0
  exact sub_eq_zero.1 h2

theorem shift_slices_circle {u : XX} {Γ : Set Symmetry} (hu : IsInvariantXX Γ u) {γ : Symmetry}
    (hγ : γ ∈ Γ) : ∀ᵐ t : TimeCircle, gradPart ((u : TimeCircle → XBar) (t + (γ.2 : TimeCircle))) =
      rotX γ.1 (gradPart ((u : TimeCircle → XBar) t)) := by
  filter_upwards [shiftLp_ae γ.2 (gradCLM u), rotHH_ae γ.1 (gradCLM u), gradCLM_ae u,
    ae_add_circle γ.2 (gradCLM_ae u)] with t a b c d
  exact d.symm.trans (a.symm.trans ((congrArg (fun w : HH => (w : TimeCircle → HBar) t)
    (shift_eq_rot hu hγ)).trans (b.trans (congrArg (rotX γ.1) c))))

theorem shift_slices {u : XX} {Γ : Set Symmetry} (hu : IsInvariantXX Γ u) {γ : Symmetry} (hγ : γ ∈ Γ) :
    ∀ᵐ σ : ℝ, gradPart ((u : TimeCircle → XBar) ((σ + γ.2 : ℝ) : TimeCircle)) =
      rotX γ.1 (gradPart ((u : TimeCircle → XBar) (σ : TimeCircle))) := by
  filter_upwards [(ae_coe_iff _).1 (shift_slices_circle hu hγ)] with σ hσ
  exact (congrArg (fun s : TimeCircle => gradPart ((u : TimeCircle → XBar) s))
    (AddCircle.coe_add (1 : ℝ) σ γ.2)).trans hσ

theorem invariant_of_reading {Γ : Set Symmetry} {u : XX} (hu : IsInvariantXX Γ u) {v : VelField}
    {G : GradField} {H : SecondField} (hr : IsReadingOf u v G H) :
    ∀ γ ∈ Γ, ∀ᵐ z : ℝ × Space, v (z.1 + γ.2) (γ.1 z.2) = γ.1 (v z.1 z.2) := by
  intro γ hγ
  have hT : MeasurePreserving (Prod.map (fun σ : ℝ => σ + γ.2) (fun y : Space => γ.1 y))
      (volume : Measure (ℝ × Space)) volume := by
    rw [Measure.volume_eq_prod]
    exact (measurePreserving_add_right volume γ.2).prod γ.1.measurePreserving
  have hm1 : AEStronglyMeasurable (fun z : ℝ × Space => v (z.1 + γ.2) (γ.1 z.2)) volume :=
    hr.measurable_velocity.comp_measurePreserving hT
  have hm2 : AEStronglyMeasurable (fun z : ℝ × Space => γ.1 (v z.1 z.2)) volume :=
    γ.1.continuous.comp_aestronglyMeasurable hr.measurable_velocity
  refine ae_prod_of_ae_ae hm1 hm2 ?_
  have hshift : ∀ᵐ σ : ℝ, v (σ + γ.2) =ᵐ[volume]
      (velocity (gradPart ((u : TimeCircle → XBar) ((σ + γ.2 : ℝ) : TimeCircle))) : Space → Space) :=
    (measurePreserving_add_right volume γ.2).quasiMeasurePreserving.ae hr.velocity_eq
  filter_upwards [hshift, hr.velocity_eq, shift_slices hu hγ] with σ h1 h2 h3
  rw [h3] at h1
  have h4 := h1.trans (velocityCov_holds.1 γ.1 _)
  have h5 : pushForward γ.1 (velocity (gradPart ((u : TimeCircle → XBar) (σ : TimeCircle))) : Space → Space)
      =ᵐ[volume] pushForward γ.1 (v σ) := by
    have h6 := γ.1.symm.measurePreserving.quasiMeasurePreserving.ae_eq_comp h2.symm
    filter_upwards [h6] with y hy
    simp only [pushForward, Function.comp_apply] at hy ⊢
    rw [hy]
  have h7 := γ.1.measurePreserving.quasiMeasurePreserving.ae_eq_comp (h4.trans h5)
  filter_upwards [h7] with y hy
  simp only [Function.comp_apply, pushForward, LinearIsometryEquiv.symm_apply_apply] at hy
  exact hy

theorem divergence_free_of_reading {u : XX} {v : VelField} {G : GradField} {H : SecondField}
    (hr : IsReadingOf u v G H) : ∀ᵐ σ : ℝ, ∀ᵐ y, ∑ i : Fin 3, (G σ y (unitVector i)) i = 0 := by
  filter_upwards [hr.velocity_eq, hr.weak_gradient] with σ h1 h2
  filter_upwards [ae_all_iff.2 (column_ae_eq_partialX _ h2 h1),
    partialX_divergence (gradPart ((u : TimeCircle → XBar) (σ : TimeCircle)))] with y hy h0
  simp only [hy]
  exact h0

theorem sixth_power_of_reading {u : XX} {v : VelField} {G : GradField} {H : SecondField}
    (hr : IsReadingOf u v G H) : ∀ᵐ σ : ℝ, ∫⁻ y, ENNReal.ofReal (‖v σ y‖ ^ 6) < ⊤ := by
  filter_upwards [hr.velocity_eq] with σ h1
  rw [lintegral_congr_ae (h1.mono fun y hy => by rw [hy])]
  exact Internal.SliceFields.lintegral_sixth_lt_top _

theorem gradient_finite_of_reading {u : XX} {v : VelField} {G : GradField} {H : SecondField}
    (hr : IsReadingOf u v G H) : periodLIntegral (fun σ y => matSq (G σ y)) < ⊤ := by
  refine periodLIntegral_lt_top_of_slices
    (fun i : Fin 3 => ContinuousLinearMap.compLpL 2 volume ((partialX i).comp gradPart) u) _ ?_
  have hc : ∀ i : Fin 3, ∀ᵐ σ : ℝ,
      (ContinuousLinearMap.compLpL 2 volume ((partialX i).comp gradPart) u (σ : TimeCircle) : L2R) =
        partialX i (gradPart ((u : TimeCircle → XBar) (σ : TimeCircle))) := fun i =>
    (ae_coe_iff _).1 (ContinuousLinearMap.coeFn_compLpL _ u)
  filter_upwards [hr.velocity_eq, hr.weak_gradient, ae_all_iff.2 hc] with σ h1 h2 h3
  filter_upwards [ae_all_iff.2 (column_ae_eq_partialX _ h2 h1)] with y hy
  simp only [matSq, hy, h3]

theorem coe_circleRep (t : TimeCircle) : ((circleRep t : ℝ) : TimeCircle) = t :=
  AddCircle.coe_equivIco

theorem toLpOrZero_eq_of_ae {F' : Space → Space} (w : L2R) (h : F' =ᵐ[volume] (w : Space → Space)) :
    toLpOrZero 2 F' = w := by
  have hm : MemLp F' 2 volume := (Lp.memLp w).ae_eq h.symm
  unfold toLpOrZero
  rw [dif_pos hm]
  exact Lp.ext (hm.coeFn_toLp.trans h)

theorem circleLpOrZero_eq_of_ae {F' : TimeCircle → HBar} (w : HH)
    (h : F' =ᵐ[volume] (w : TimeCircle → HBar)) : circleLpOrZero F' = w := by
  have hm : MemLp F' 2 volume := (Lp.memLp w).ae_eq h.symm
  unfold circleLpOrZero
  rw [dif_pos hm]
  exact Lp.ext (hm.coeFn_toLp.trans h)

theorem physToHH_fullField (hProj : ProjectionHolds) {f : HH} {u : XX} {v : VelField} {G : GradField}
    {H : SecondField} (hr : IsReadingOf u v G H) {g : ℝ → Space → Space} (hg : IsTransportPart f u g) :
    physToHH (fullField g H) = f := by
  have hper : IsTimePeriodic (fullField g H) := (isPeriodicField_fullField hr hg).2.1
  have hs : ∀ᵐ t : TimeCircle, fullField g H (circleRep t) =ᵐ[volume]
      (toPhysH ((f : TimeCircle → HBar) t) : Space → Space) := by
    refine (ae_coe_iff _).2 ?_
    filter_upwards [fullField_slices hr hg] with σ hσ
    rw [JointRepresentativeInternal.periodic_of_coe_eq hper (coe_circleRep (σ : TimeCircle))]
    exact hσ
  have hae : (onCircle fun σ => solField (fullField g H σ)) =ᵐ[volume] (f : TimeCircle → HBar) := by
    filter_upwards [hs] with t ht
    show solProj (toLpOrZero 2 (fullField g H (circleRep t))) = (f : TimeCircle → HBar) t
    rw [toLpOrZero_eq_of_ae _ ht]
    exact hProj.2.2.2 _
  exact circleLpOrZero_eq_of_ae f hae

theorem integral_fullField {u : XX} {v : VelField} {G : GradField} {H : SecondField}
    (hr : IsReadingOf u v G H) {g : ℝ → Space → Space}
    (hgm : AEStronglyMeasurable (fun z : ℝ × Space => g z.1 z.2) volume) (hgp : IsTimePeriodic g)
    (hgf : periodLIntegral (fun σ y => ‖g σ y‖ ^ 2) < ⊤) (φ : ℝ → Space → Space)
    (hφ : IsSpaceTimeTestVector φ) :
    ∫ z : ℝ × Space, inner ℝ (fullField g H z.1 z.2) (φ z.1 z.2) =
      ∫ z : ℝ × Space, (inner ℝ (g z.1 z.2) (φ z.1 z.2)
        + matInner (G z.1 z.2) (fderiv ℝ (φ z.1) z.2)) := by
  have hφc : Continuous (fun z : ℝ × Space => φ z.1 z.2) := hφ.1.continuous
  have i1 := integrable_inner_of_periodic hgm hgp hgf hφc hφ.2
  have i2 := integrable_inner_of_periodic (F := fun σ y => secondDerivTrace (H σ y))
    (continuous_secondDerivTrace.comp_aestronglyMeasurable hr.measurable_second)
    (fun σ y => by simp only [hr.periodic_second σ y]) (sumSecondPartials_finite_of_reading hr) hφc hφ.2
  obtain ⟨i3, e3⟩ := integral_matInner_eq hr φ hφ
  have e0 : (fun z : ℝ × Space => inner ℝ (fullField g H z.1 z.2) (φ z.1 z.2)) =
      fun z => inner ℝ (g z.1 z.2) (φ z.1 z.2) - inner ℝ (secondDerivTrace (H z.1 z.2)) (φ z.1 z.2) :=
    funext fun z => inner_sub_left _ _ _
  rw [e0, integral_sub i1 i2, integral_add i1 i3, e3, sub_eq_add_neg]

theorem weakEquation_of_reading (hProj : ProjectionHolds) (hTest : TestPairingHolds) (f : HH) (u : XX)
    {v : VelField} {G : GradField} {H : SecondField} (hr : IsReadingOf u v G H) {g : ℝ → Space → Space}
    (hg : IsTransportPart f u g) (φ : ℝ → Space → Space) (hφ : IsSpaceTimeTestField φ) :
    ∫ z : ℝ × Space, (inner ℝ (g z.1 z.2) (φ z.1 z.2)
      + matInner (G z.1 z.2) (fderiv ℝ (φ z.1) z.2)) = inner ℝ f (testInHH φ) := by
  have h := hTest (fullField g H) (isPeriodicField_fullField hr hg) φ hφ
  rw [physToHH_fullField hProj hr hg] at h
  rw [h, integral_fullField hr hg.1 hg.2.1 (derivative_finite_of_transportPart hg) φ ⟨hφ.1, hφ.2.1⟩]

end Internal.FreePerturbation

open Internal.FreePerturbation

theorem freePerturbationHolds_of (h1 : FreeInvHolds) (h2 : FreeEquivariantHolds)
    (_h3 : ReadingExistsHolds) (h4 : ProjectionHolds) (h5 : TestPairingHolds)
    (h6 : PropagatorBoundHolds) (h7 : GradInvHolds) (h8 : GraphClosedHolds) : FreePerturbationHolds := by
  intro Γ P hP f hf v G H hr
  obtain ⟨g, hg⟩ := exists_transportPart f (freeInv P f)
  refine ⟨g, ⟨hr.measurable_velocity, hr.measurable_gradient, hr.measurable_second, hg.1,
    hr.periodic_velocity, hr.periodic_gradient, hr.periodic_second, hg.2.1, hr.weak_gradient,
    hr.weak_second, divergence_free_of_reading hr, sixth_power_of_reading hr,
    gradient_finite_of_reading hr, sumSecondPartials_finite_of_reading hr,
    derivative_finite_of_transportPart hg, fun φ hφ => transport_of_reading h1 h4 h6 h7 h8 hP f hr hg φ hφ,
    invariant_of_reading (h2 Γ P hP f hf) hr⟩, fun φ hφ => weakEquation_of_reading h4 h5 f _ hr hg φ hφ⟩

end Breakdown.Cert
