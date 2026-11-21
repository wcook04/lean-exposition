import TorusEuler.EndpointSpace
import Mathlib.MeasureTheory.Integral.DivergenceTheorem

open MeasureTheory Set
open scoped ContDiff InnerProductSpace

namespace TorusEuler

private theorem centeredCell_eq_preimage_box :
    centeredCell = WithLp.ofLp ⁻¹' Icc (fun _ : Fin 3 => -(1 / 2 : ℝ)) (fun _ => 1 / 2) := by
  ext x
  constructor
  · intro hx
    exact ⟨fun i => (hx i).1, fun i => (hx i).2⟩
  · intro hx i
    exact ⟨hx.1 i, hx.2 i⟩

private theorem continuous_divergence_of_contDiff {v : Vec3 → Vec3} (hv : ContDiff ℝ 1 v) :
    Continuous (divergence v) := by
  have hv' : Continuous (fderiv ℝ v) := hv.continuous_fderiv (by simp)
  unfold divergence
  exact continuous_finsetSum _ fun i _ =>
    (PiLp.continuous_apply 2 _ i).comp (hv'.clm_apply continuous_const)

/-- The divergence of a continuously differentiable periodic field has zero cell integral. -/
theorem integral_divergence_centeredCell_eq_zero {v : Vec3 → Vec3}
    (hv : ContDiff ℝ 1 v) (hp : SpatiallyPeriodic v) :
    (∫ x in centeredCell, divergence v x) = 0 := by
  let e : Vec3 ≃L[ℝ] (Fin 3 → ℝ) := PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)
  let a : Fin 3 → ℝ := fun _ => -(1 / 2)
  let b : Fin 3 → ℝ := fun _ => 1 / 2
  let V : (Fin 3 → ℝ) → (Fin 3 → ℝ) := fun y => e (v (e.symm y))
  let D : (Fin 3 → ℝ) → (Fin 3 → ℝ) →L[ℝ] (Fin 3 → ℝ) := fun y =>
    (e : Vec3 →L[ℝ] (Fin 3 → ℝ)).comp
      ((fderiv ℝ v (e.symm y)).comp (e.symm : (Fin 3 → ℝ) →L[ℝ] Vec3))
  have hD (y : Fin 3 → ℝ) : HasFDerivAt V (D y) y :=
    e.hasFDerivAt.comp y (((hv.differentiable (by simp) (e.symm y)).hasFDerivAt).comp y
      e.symm.hasFDerivAt)
  have htrace (y : Fin 3 → ℝ) :
      (∑ i : Fin 3, D y (Pi.single i 1) i) = divergence v (e.symm y) := by
    unfold divergence
    apply Finset.sum_congr rfl
    intro i _
    have he : e.symm (Pi.single i 1) = EuclideanSpace.single i (1 : ℝ) := by
      change e.symm (e (EuclideanSpace.single i (1 : ℝ))) = EuclideanSpace.single i 1
      exact e.symm_apply_apply _
    change (fderiv ℝ v (e.symm y) (e.symm (Pi.single i 1))) i = _
    rw [he]
  have hint : IntegrableOn (fun y => ∑ i : Fin 3, D y (Pi.single i 1) i) (Icc a b) := by
    simp_rw [htrace]
    exact (((continuous_divergence_of_contDiff hv).comp e.symm.continuous).continuousOn).integrableOn_compact
      isCompact_Icc
  have hface (i : Fin 3) (y : Fin 2 → ℝ) :
      V (i.insertNth (b i) y) i = V (i.insertNth (a i) y) i := by
    have hshift : e.symm (i.insertNth (b i) y) =
        e.symm (i.insertNth (a i) y) + latticeVector (Pi.single i 1) := by
      apply PiLp.ext
      intro j
      change (i.insertNth (b i) y : Fin 3 → ℝ) j =
        (i.insertNth (a i) y : Fin 3 → ℝ) j + ((Pi.single i 1 : Fin 3 → ℤ) j : ℝ)
      by_cases hij : j = i
      · subst j
        norm_num [a, b]
      · obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq hij
        simp
    change (v (e.symm (i.insertNth (b i) y))) i = (v (e.symm (i.insertNth (a i) y))) i
    rw [hshift, hp]
  have hpres : MeasurePreserving e volume volume := PiLp.volume_preserving_ofLp (Fin 3)
  have hcell : e ⁻¹' Icc a b = centeredCell := centeredCell_eq_preimage_box.symm
  calc
    (∫ x in centeredCell, divergence v x) = ∫ y in Icc a b, divergence v (e.symm y) := by
      rw [← hpres.setIntegral_preimage_emb e.toHomeomorph.measurableEmbedding, hcell]
      simp only [e.symm_apply_apply]
    _ = ∫ y in Icc a b, ∑ i : Fin 3, D y (Pi.single i 1) i := by simp_rw [htrace]
    _ = 0 := by
      rw [integral_divergence_of_hasFDerivAt_off_countable a b (fun i => by norm_num [a, b]) V D
        ∅ Set.countable_empty
        ((e.continuous.comp (hv.continuous.comp e.symm.continuous)).continuousOn)
        (fun y _ => hD y) hint]
      exact Finset.sum_eq_zero (fun i _ => by simp_rw [hface, sub_self])

private theorem divergence_smul {p : Vec3 → ℝ} {v : Vec3 → Vec3} {x : Vec3}
    (hp : DifferentiableAt ℝ p x) (hv : DifferentiableAt ℝ v x) :
    divergence (fun y => p y • v y) x = ⟪gradient p x, v x⟫_ℝ + p x * divergence v x := by
  have hbasis : (∑ i : Fin 3, (v x) i • EuclideanSpace.single i (1 : ℝ)) = v x := by
    simpa only [EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply] using
      (EuclideanSpace.basisFun (Fin 3) ℝ).sum_repr (v x)
  have hsum : (∑ i : Fin 3, fderiv ℝ p x (EuclideanSpace.single i 1) * (v x) i) =
      fderiv ℝ p x (v x) := by
    conv_rhs => rw [← hbasis, map_sum]
    simp only [map_smul, smul_eq_mul, mul_comm]
  unfold divergence
  rw [fderiv_fun_smul hp hv, inner_gradient_left, Finset.mul_sum]
  simp only [add_apply, smul_apply,
    ContinuousLinearMap.smulRight_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul,
    Finset.sum_add_distrib, hsum, add_comm]

/-- Periodic integration by parts for the divergence of the Euclidean lift. -/
theorem integral_gradient_pair_centeredCell {p : Vec3 → ℝ} {v : Vec3 → Vec3}
    (hp : ContDiff ℝ 1 p) (hv : ContDiff ℝ 1 v)
    (hpp : SpatiallyPeriodic p) (hvp : SpatiallyPeriodic v) :
    (∫ x in centeredCell, ⟪gradient p x, v x⟫_ℝ) =
      -(∫ x in centeredCell, p x * divergence v x) := by
  have hcell : IsCompact centeredCell := by
    rw [centeredCell_eq_preimage_box]
    exact (PiLp.homeomorph 2 (fun _ : Fin 3 => ℝ)).isCompact_preimage.mpr isCompact_Icc
  have hgrad : Continuous (gradient p) := (InnerProductSpace.toDual ℝ Vec3).symm.continuous.comp
    (hp.continuous_fderiv (by simp))
  have hpair : IntegrableOn (fun x => ⟪gradient p x, v x⟫_ℝ) centeredCell :=
    (hgrad.inner hv.continuous).continuousOn.integrableOn_compact hcell
  have hprod : IntegrableOn (fun x => p x * divergence v x) centeredCell :=
    (hp.continuous.mul (continuous_divergence_of_contDiff hv)).continuousOn.integrableOn_compact hcell
  have hperiodic : SpatiallyPeriodic (fun x => p x • v x) := by
    intro n x
    change p (x + latticeVector n) • v (x + latticeVector n) = p x • v x
    rw [hpp n x, hvp n x]
  have hpoint (x : Vec3) := divergence_smul (hp.differentiable (by simp) x)
    (hv.differentiable (by simp) x)
  have hzero := integral_divergence_centeredCell_eq_zero (hp.smul hv) hperiodic
  change (∫ x in centeredCell, divergence (fun y => p y • v y) x) = 0 at hzero
  simp_rw [hpoint] at hzero
  rw [integral_add hpair hprod] at hzero
  exact eq_neg_of_add_eq_zero_left hzero

/-- A torus field with a continuously differentiable divergence-free lift annihilates smooth gradients. -/
theorem endpointTorusGradientPairing_eq_zero_of_divergence_free
    {g : UnitAddTorus (Fin 3) → Vec3} {v : Vec3 → Vec3} (hv : ContDiff ℝ 1 v)
    (hrep : ∀ x, g (toUnitTorus x) = v x) (hdiv : ∀ x, divergence v x = 0)
    (p : EndpointSmoothPotential) :
    (∫ a, ⟪endpointPotentialGradient p a, g a⟫_ℝ ∂unitTorusMeasure) = 0 := by
  have hvp : SpatiallyPeriodic v := by
    intro n x
    rw [← hrep, ← hrep, (toUnitTorus_eq_iff _ _).mpr ⟨n, rfl⟩]
  rw [torusIntegral_eq_centeredCell]
  simp only [endpointPotentialGradient_toUnitTorus, hrep]
  rw [integral_gradient_pair_centeredCell (p.smooth.of_le (by simp)) hv p.periodic hvp]
  simp only [hdiv, mul_zero, integral_zero, neg_zero]

private theorem contDiff_divergence {v : Vec3 → Vec3} (hv : ContDiff ℝ ∞ v) :
    ContDiff ℝ ∞ (divergence v) := by
  unfold divergence
  apply ContDiff.sum
  intro i _
  exact (PiLp.proj 2 (fun _ : Fin 3 => ℝ) i).contDiff.comp
    ((hv.contDiff_fderiv_apply (m := ∞) (by simp)).comp (contDiff_id.prodMk contDiff_const))

private theorem spatiallyPeriodic_divergence {v : Vec3 → Vec3} (hv : Differentiable ℝ v)
    (hvp : SpatiallyPeriodic v) : SpatiallyPeriodic (divergence v) := by
  intro n x
  let a := latticeVector n
  have h := (hv (x + a)).hasFDerivAt.comp x ((hasFDerivAt_id x).add_const a)
  have hvEq : (fun y => v (y + a)) = v := funext (hvp n)
  change HasFDerivAt (fun y => v (y + a)) _ x at h
  rw [hvEq, ContinuousLinearMap.comp_id] at h
  have hderiv : fderiv ℝ v (x + latticeVector n) = fderiv ℝ v x := h.fderiv.symm
  simp only [divergence, hderiv]

/-- For a smooth lift, annihilating all smooth gradients is equivalent to pointwise vanishing
of its divergence. -/
theorem endpointTorusGradientPairing_iff_divergence_free
    {g : UnitAddTorus (Fin 3) → Vec3} {v : Vec3 → Vec3} (hv : ContDiff ℝ ∞ v)
    (hrep : ∀ x, g (toUnitTorus x) = v x) :
    (∀ p : EndpointSmoothPotential,
      (∫ a, ⟪endpointPotentialGradient p a, g a⟫_ℝ ∂unitTorusMeasure) = 0) ↔
    ∀ x, divergence v x = 0 := by
  refine ⟨fun h => ?_, fun hdiv p =>
    endpointTorusGradientPairing_eq_zero_of_divergence_free (hv.of_le (by simp)) hrep hdiv p⟩
  have hvp : SpatiallyPeriodic v := by
    intro n x
    rw [← hrep, ← hrep, (toUnitTorus_eq_iff _ _).mpr ⟨n, rfl⟩]
  let p : EndpointSmoothPotential :=
    ⟨divergence v, contDiff_divergence hv, spatiallyPeriodic_divergence (hv.differentiable (by simp)) hvp⟩
  obtain ⟨q, hq, _⟩ := p.periodic.existsUnique_torusFunction
  have hqc : Continuous q := isOpenQuotientMap_toUnitTorus.continuous_comp_iff.mp (by
    change Continuous (fun x => q (toUnitTorus x))
    simp only [hq]
    exact p.smooth.continuous)
  have hpair := h p
  rw [torusIntegral_eq_centeredCell] at hpair
  simp only [endpointPotentialGradient_toUnitTorus, hrep] at hpair
  have hparts := integral_gradient_pair_centeredCell (p.smooth.of_le (by simp)) (hv.of_le (by simp))
    p.periodic hvp
  rw [hpair, zero_eq_neg] at hparts
  have hsq : (∫ a, (q a) ^ 2 ∂unitTorusMeasure) = 0 := by
    rw [torusIntegral_eq_centeredCell]
    simpa only [hq, p, sq] using hparts
  have hInt : Integrable (fun a => (q a) ^ 2) unitTorusMeasure := by
    rw [← integrableOn_univ]
    exact (hqc.pow 2).continuousOn.integrableOn_compact isCompact_univ
  have hae := (integral_eq_zero_iff_of_nonneg (fun a => sq_nonneg (q a)) hInt).mp hsq
  have heq : (fun a => (q a) ^ 2) = (0 : UnitAddTorus (Fin 3) → ℝ) :=
    (Continuous.ae_eq_iff_eq unitTorusMeasure (hqc.pow 2) continuous_const).mp hae
  intro x
  have hx : (divergence v x) ^ 2 = 0 := by
    simpa only [hq, p, Pi.zero_apply] using congrFun heq (toUnitTorus x)
  exact sq_eq_zero_iff.mp hx

/-- Joint velocities represented at almost every time by divergence-free lifts pass all weak
spatial gradient tests. -/
theorem endpointTorusDivergenceTests_of_ae_smooth_slices {T : ℝ} (v : EndpointTorusL2 T)
    (h : ∀ᵐ t ∂volume.restrict (Ioc (0 : ℝ) T),
      ∃ (g : UnitAddTorus (Fin 3) → Vec3) (w : Vec3 → Vec3),
        (fun a => v (t, a)) =ᵐ[unitTorusMeasure] g ∧
        ContDiff ℝ 1 w ∧ (∀ x, g (toUnitTorus x) = w x) ∧ (∀ x, divergence w x = 0)) :
    ∀ η p, endpointTorusDivergenceTest T η p v = 0 := by
  intro η p
  refine (endpointTorusDivergenceTests_iff_ae_zero T v p).mpr ?_ η
  filter_upwards [h] with t ht
  obtain ⟨g, w, hwrep, hw, hrep, hdiv⟩ := ht
  change (∫ a, ⟪endpointPotentialGradient p a, v (t, a)⟫_ℝ ∂unitTorusMeasure) = 0
  rw [integral_congr_ae (hwrep.mono fun a ha => congrArg (fun z => ⟪endpointPotentialGradient p a, z⟫_ℝ) ha)]
  exact endpointTorusGradientPairing_eq_zero_of_divergence_free hw hrep hdiv p

/-- A joint `L²` representative with divergence-free lifts passes all weak spatial gradient tests. -/
theorem endpointTorusDivergenceTests_toLp_of_lift {T : ℝ}
    {g : ℝ × UnitAddTorus (Fin 3) → Vec3} (hg : MemLp g 2 (endpointTorusMeasure T))
    (h : ∀ᵐ t ∂volume.restrict (Ioc (0 : ℝ) T), ∃ w : Vec3 → Vec3,
      ContDiff ℝ 1 w ∧ (∀ x, g (t, toUnitTorus x) = w x) ∧ (∀ x, divergence w x = 0)) :
    ∀ η p, endpointTorusDivergenceTest T η p (hg.toLp g) = 0 := by
  apply endpointTorusDivergenceTests_of_ae_smooth_slices
  have hrep : ∀ᵐ t ∂volume.restrict (Ioc (0 : ℝ) T),
      ∀ᵐ a ∂unitTorusMeasure, hg.toLp g (t, a) = g (t, a) :=
    Measure.ae_ae_of_ae_prod hg.coeFn_toLp
  filter_upwards [h, hrep] with t ht htrep
  obtain ⟨w, hw, hrepw, hdiv⟩ := ht
  exact ⟨fun a => g (t, a), w, htrep, hw, hrepw, hdiv⟩

end TorusEuler
